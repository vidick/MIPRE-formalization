/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Cost.Succinct
import MIPRE.Foundations.Cost.Clocked
import MIPRE.Foundations.Cost.Threshold
import MIPRE.Foundations.Cost.Growth
import MIPRE.Foundations.Cost.Kleene
import MIPRE.Foundations.Cost.Partrec
import MIPRE.Foundations.Cost.FromPartrec
import MIPRE.Foundations.Cost.Universal
import Mathlib.Computability.Halting
import Mathlib.Data.ENat.Lattice

/-!
# The recursive compression lemma

The abstract compression lemma of Marks–Nezhadi–Yuen ("The recursive compression
method for proving undecidability results"), in the variant with compression
parameter `n` ([MNY, Lemma 5.1]) used by this project — blueprint
`lem:recursive-compression` — together with the halting-problem corollary in the form
consumed by `MIPRE.HaltingGameValue`. The adapted notion of succinct description
(blueprint `def:succinct`, [MNY, Definition 2.4]) is `Cost.IsSuccinctDesc` in
`Cost/Succinct.lean`.

Everything is stated in the ambient cost model (`Cost.Basic`): programs are
`Cost.Prog`, "polynomial-time computable" is `Cost.PolyTimeFun`, runtimes are
`Cost.Eval`. The proof is the fixed-point construction of [MNY, Lemma 3.1/5.1] and uses
precisely the toolkit of `Cost.Toolkit`: `hardcode` (efficient s-m-n) and `PolyTimeFun.smn`
to build the self-referential decider, a `ClockedUniversalMachine` to run "`e` for `log n`
steps" (`PolyTimeFun.haltsWithin`), a `UniversalMachine` to answer bit-queries within the
succinctness budget (`Prog.bitQueryProg`), and `efficient_fixed_point` to close the
self-reference; the time-transfer clauses are what make the constructed program a
*succinct* description at every recursion level (`planning/compression-track.md`, K3).

## Departures from the paper's statement and proof

* **Succinctness time bound.** [MNY, Definition 2.4] requires `runtime(e, m) ≤ n` for
  *all* `m`. In any cost model that charges to read its input (ours does), that bound is
  vacuous for `|m| > n`; we require `≤ (n + 1) * (Nat.size m + 1) ^ 2` instead. Any
  `poly(n, |m|)` bound would do; the choice only shifts polynomial overheads inside the
  proof, but it must be fixed consistently with the compression theorem for games
  (`thm:compression`) whose output verifiers are what get succinctly described. The
  quadratic factor in `|m|` is what the bit-query program `Cost.Prog.bitAtProg` achieves:
  in the list language, a zero test or a decrement of the binary index copies the index,
  so each of the `|y|` steps of the walk costs `O(size y + |m| ^ 2)`
  (`Cost.Prog.bitAtIter_le`). **Design knob (K-D5) — revisit when `thm:compression` is
  stated.**
* **The next level is `2 n + 1`, not `n + 1`.** The paper's decider at level `n` compresses
  a description of the string at level `n + 1`. Incrementing a binary numeral needs a carry
  propagation; prepending a `true` bit is one node (`PolyTimeFun.next`). The argument is
  unchanged: the levels `n, 2n + 1, 4n + 3, …` still grow without bound, and
  `Nat.size (2 n + 1) = Nat.size n + 1` keeps every overhead polynomial in
  `esize e + Nat.size n`.
* **The threshold** is `r e = 2 ^ (K + 1 + esize e)` for a constant `K` obtained from the
  overhead polynomial by `exists_threshold` (`Cost/Growth.lean`): above it, the polynomial
  overhead in `esize e + Nat.size n` is at most `n + 1`. It is computed by
  `PolyTimeFun.threshold K`.
* **The instantiation** (blueprint `rem:compression-abstract`): `A` = descriptions of
  normal form verifier games with a perfect PCC strategy, and `f = MIPRE.entRequirement
  (·, 1/2) : _ → ℕ∞` composed with the interpretation of descriptions as games. The `ℕ∞`
  codomain here matches `entRequirement`.
-/

namespace MIPRE.Cost

open Polynomial

/-! ## The self-referential decider -/

/-- The decider of the recursive compression argument, as a polynomial-time function of
`(c', (e, n))`: if `e` halts on the empty input within `Nat.size n` steps, the fixed string
`y₀`; otherwise `Compr` applied to the succinct description `(hardcode β ((c', e), 2n + 1),
n)` — where `β` is the bit-query program — with parameter `n`. The self-referential program
`c` of the proof is a Kleene fixed point of `c' ↦ hardcode (decFun …).code (encode c')`, so
that `c` on `(e, n)` computes `decFun (c, (e, n))`, and the hardcoded description is of
the string that `c` itself computes at the next level. -/
noncomputable def decFun (U : UniversalMachine) (UT : ClockedUniversalMachine)
    (Compr : PolyTimeFun ((Prog × ℕ) × ℕ) BitStr) (y₀ : BitStr) :
    PolyTimeFun (Prog × (Prog × ℕ)) BitStr :=
  PolyTimeFun.ite ((PolyTimeFun.haltsWithin UT).comp PolyTimeFun.snd)
    (PolyTimeFun.const y₀)
    (Compr.comp (PolyTimeFun.pair
      (PolyTimeFun.pair
        ((PolyTimeFun.smn ((Prog × Prog) × ℕ)).comp
          (PolyTimeFun.pair (PolyTimeFun.const (Prog.bitQueryProg U.univ))
            (PolyTimeFun.pair
              (PolyTimeFun.pair PolyTimeFun.fst (PolyTimeFun.fst.comp PolyTimeFun.snd))
              (PolyTimeFun.next.comp (PolyTimeFun.snd.comp PolyTimeFun.snd)))))
        (PolyTimeFun.snd.comp PolyTimeFun.snd))
      (PolyTimeFun.snd.comp PolyTimeFun.snd)))

theorem decFun_apply (U : UniversalMachine) (UT : ClockedUniversalMachine)
    (Compr : PolyTimeFun ((Prog × ℕ) × ℕ) BitStr) (y₀ : BitStr) (c' e : Prog) (n : ℕ) :
    decFun U UT Compr y₀ (c', (e, n)) =
      if (evalWithin e .nil (Nat.size n)).isSome then y₀
      else Compr ((hardcode (Prog.bitQueryProg U.univ) (encode ((c', e), 2 * n + 1)), n), n) :=
  rfl

/-! ## The compression lemma -/

/-- **Recursive compression lemma** ([MNY, Lemma 5.1]; blueprint
`lem:recursive-compression`).

Data: `f : {0,1}* → ℕ∞`, a nonempty language `A` on which `f` is finite, and a
*polynomial-time* compression procedure `Compr` taking a (claimed) succinct
description `(c, m)` and a target parameter `n`, such that whenever `(c, m)`
genuinely describes `x`:

1. `f (Compr ((c, m), n)) ≥ max (f x) n`, and
2. `x ∈ A → Compr ((c, m), n) ∈ A`.

Conclusion: a polynomial-time reduction `g` from the halting problem (of the ambient
model, on the empty input `nil`) to `A`, with `f (g e) = ∞` on non-halting `e`.

There are no computability assumptions on `f`, and no assumptions on the output of
`Compr` off succinct descriptions (but `Compr` is total and fast everywhere —
[MNY, §7] shows this is essential). The finiteness hypothesis `hA` is part of the
statement of [MNY] (it makes the two conclusions exclusive) but is not needed for the
proof. -/
theorem recursive_compression
    (f : BitStr → ℕ∞) (A : Set BitStr)
    (y₀ : BitStr) (hy₀ : y₀ ∈ A)
    (_hA : ∀ x ∈ A, f x < ⊤)
    (Compr : PolyTimeFun ((Prog × ℕ) × ℕ) BitStr)
    (hCompr : ∀ (c : Prog) (m : ℕ) (x : BitStr) (n : ℕ),
      IsSuccinctDesc c m x →
        (max (f x) (n : ℕ∞) ≤ f (Compr ((c, m), n))) ∧
        (x ∈ A → Compr ((c, m), n) ∈ A)) :
    ∃ g : PolyTimeFun Prog BitStr,
      ∀ e : Prog,
        (Halts e .nil → g e ∈ A) ∧
        (¬ Halts e .nil → f (g e) = ⊤) := by
  obtain ⟨U⟩ := exists_efficient_universal
  obtain ⟨UT⟩ := exists_clocked_universal
  -- the decider, kept opaque through its functional equation
  obtain ⟨dec, hdec⟩ : ∃ dec : PolyTimeFun (Prog × (Prog × ℕ)) BitStr, ∀ c' e n,
      dec (c', (e, n)) = if (evalWithin e .nil (Nat.size n)).isSome then y₀
        else Compr ((hardcode (Prog.bitQueryProg U.univ) (encode ((c', e), 2 * n + 1)), n), n) :=
    ⟨decFun U UT Compr y₀, decFun_apply U UT Compr y₀⟩
  -- the self-reference: `c` on `(e, n)` computes `dec (c, (e, n))`
  obtain ⟨F, hF⟩ : ∃ F : PolyTimeFun Prog Prog, ∀ c', F c' = hardcode dec.code (encode c') :=
    ⟨(PolyTimeFun.smn Prog).comp (PolyTimeFun.pair (PolyTimeFun.const dec.code)
      (PolyTimeFun.id Prog)), fun _ => rfl⟩
  obtain ⟨c, p, hc, -, hc_time⟩ := efficient_fixed_point F
  -- the time bound of `c`
  obtain ⟨cB, hcB⟩ : ∃ cB : Polynomial ℕ, ∀ x, cB.eval x =
      p.eval (2 * x + dec.timeBound.eval (x + (esize c + 1)) + (esize c + 5)) :=
    ⟨p.comp (C 2 * X + dec.timeBound.comp (X + C (esize c + 1)) + C (esize c + 5)),
      fun x => by simp [Polynomial.eval_comp]⟩
  have c_runs : ∀ e n, ∃ t ≤ cB.eval (esize e + esize n + 1),
      c.Runs (encode (e, n)) (encode (dec (c, (e, n)))) t := by
    intro e n
    obtain ⟨t₀, ht₀, h₀⟩ := dec.computes (c, (e, n))
    have h₁ := hardcode_time dec.closed (d := encode c) (x := encode (e, n)) h₀
    rw [← hF c] at h₁
    obtain ⟨t', ht', h'⟩ := hc_time _ _ _ h₁
    refine ⟨t', ?_, h'⟩
    rw [hcB]
    refine ht'.trans (polynomial_eval_mono p ?_)
    have hm := polynomial_eval_mono dec.timeBound
      (show esize (c, (e, n)) ≤ esize e + esize n + 1 + (esize c + 1) by
        simp only [esize_prod]; omega)
    have e1 : (encode (e, n)).size = esize e + esize n + 1 := rfl
    have e2 : (encode c).size = esize c := rfl
    omega
  -- `c` as a polynomial-time function of `(e, n)`
  obtain ⟨cFun, hcFun⟩ : ∃ cFun : PolyTimeFun (Prog × ℕ) BitStr, ∀ q, cFun q = dec (c, q) :=
    ⟨{ toFun := fun q => dec (c, q)
       code := c
       closed := hc
       timeBound := cB
       computes := fun q => by
         obtain ⟨e, n⟩ := q
         obtain ⟨t, ht, h⟩ := c_runs e n
         exact ⟨t, by rw [esize_prod]; exact ht, h⟩ }, fun _ => rfl⟩
  -- the overhead polynomial in `x = esize e + Nat.size n`, and the threshold constant
  obtain ⟨Q₁, hQ₁⟩ : ∃ Q₁ : Polynomial ℕ, ∀ x, Q₁.eval x = cB.eval (5 * x + 6) :=
    ⟨cB.comp (C 5 * X + C 6), fun x => by simp [Polynomial.eval_comp]⟩
  obtain ⟨Q₂, hQ₂⟩ : ∃ Q₂ : Polynomial ℕ, ∀ x, Q₂.eval x =
      (bitQueryBound U).eval (Q₁.eval x + 5 * x + (esize c + 6)) + 5 * x + (esize c + 12) :=
    ⟨(bitQueryBound U).comp (Q₁ + C 5 * X + C (esize c + 6)) + C 5 * X + C (esize c + 12),
      fun x => by simp [Polynomial.eval_comp]⟩
  obtain ⟨K, hK⟩ := exists_threshold (Q₁ + Q₂)
  -- above the threshold, `c` at level `2n + 1` is fast and its output is succinctly
  -- described by the hardcoded bit-query program with parameter `n`
  have key : ∀ e n, 2 ^ (K + 1 + esize e) ≤ n →
      IsSuccinctDesc (hardcode (Prog.bitQueryProg U.univ) (encode ((c, e), 2 * n + 1))) n
        (dec (c, (e, 2 * n + 1))) := by
    intro e n hn
    obtain ⟨t, ht, hrun⟩ := c_runs e (2 * n + 1)
    have hQ := hK (esize e) n hn
    rw [Polynomial.eval_add, hQ₁, hQ₂, hQ₁] at hQ
    have hsz : esize (2 * n + 1) ≤ 4 * Nat.size n + 5 := by
      have := esize_nat_le (2 * n + 1)
      rw [size_two_mul_add_one] at this
      omega
    have ht₁ : t ≤ cB.eval (5 * (esize e + Nat.size n) + 6) :=
      ht.trans (polynomial_eval_mono cB (by omega))
    have hpow : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
    refine isSuccinctDesc_hardcode U c e (2 * n + 1) n _ hrun (by omega) ?_
    have hb := polynomial_eval_mono (bitQueryBound U)
      (show esize c + esize e + esize (2 * n + 1) + t ≤
        cB.eval (5 * (esize e + Nat.size n) + 6) + 5 * (esize e + Nat.size n) + (esize c + 6)
        by omega)
    omega
  -- the reduction
  refine ⟨cFun.comp (PolyTimeFun.pair (PolyTimeFun.id Prog) (PolyTimeFun.threshold K)),
    fun e => ?_⟩
  have hg : cFun.comp (PolyTimeFun.pair (PolyTimeFun.id Prog) (PolyTimeFun.threshold K)) e =
      dec (c, (e, 2 ^ (K + 1 + esize e))) := by
    rw [PolyTimeFun.comp_apply, PolyTimeFun.pair_apply, hcFun, PolyTimeFun.id_apply,
      PolyTimeFun.threshold_apply]
  rw [hg]
  refine ⟨fun hh => ?_, fun hnh => ?_⟩
  · -- halting `e`: above `2 ^ T`, the decider returns `y₀`; below, `Compr` preserves `A`
    obtain ⟨r₀, T, hT⟩ := hh
    have htrue : ∀ n, T ≤ Nat.size n → (evalWithin e .nil (Nat.size n)).isSome = true :=
      fun n hn => (evalWithin_isSome_iff _ _ _).2 ⟨r₀, T, hn, hT⟩
    have hmem : ∀ k n, 2 ^ (K + 1 + esize e) ≤ n → 2 ^ T ≤ n + k → dec (c, (e, n)) ∈ A := by
      intro k
      induction k with
      | zero =>
        intro n _ hk
        have hd := hdec c e n
        rw [htrue n (Nat.lt_size.mpr (by simpa using hk)).le, if_pos rfl] at hd
        rw [hd]
        exact hy₀
      | succ k ih =>
        intro n hn hk
        have hd := hdec c e n
        cases hb : (evalWithin e .nil (Nat.size n)).isSome with
        | true =>
          rw [hb, if_pos rfl] at hd
          rw [hd]
          exact hy₀
        | false =>
          rw [hb, if_neg Bool.false_ne_true] at hd
          rw [hd]
          exact (hCompr _ _ _ n (key e n hn)).2 (ih (2 * n + 1) (by omega) (by omega))
    exact hmem (2 ^ T) _ le_rfl (Nat.le_add_left _ _)
  · -- non-halting `e`: the decider always compresses, and `f` grows without bound
    have hfalse : ∀ n, (evalWithin e .nil (Nat.size n)).isSome = false := fun n => by
      rw [Bool.eq_false_iff]
      intro h
      obtain ⟨r, t, -, hr⟩ := (evalWithin_isSome_iff _ _ _).1 h
      exact hnh ⟨r, t, hr⟩
    have hstep : ∀ n : ℕ, 2 ^ (K + 1 + esize e) ≤ n →
        ((n : ℕ) : ℕ∞) ≤ f (dec (c, (e, n))) ∧
          f (dec (c, (e, 2 * n + 1))) ≤ f (dec (c, (e, n))) := by
      intro n hn
      have hd := hdec c e n
      rw [hfalse n, if_neg Bool.false_ne_true] at hd
      have := (hCompr _ _ _ n (key e n hn)).1
      rw [← hd] at this
      exact ⟨le_trans (le_max_right _ _) this, le_trans (le_max_left _ _) this⟩
    have hgrow : ∀ k n : ℕ, 2 ^ (K + 1 + esize e) ≤ n →
        ((n + k : ℕ) : ℕ∞) ≤ f (dec (c, (e, n))) := by
      intro k
      induction k with
      | zero => intro n hn; simpa using (hstep n hn).1
      | succ k ih =>
        intro n hn
        have h1 := ih (2 * n + 1) (by omega)
        have h2 := (hstep n hn).2
        refine le_trans ?_ (h1.trans h2)
        exact_mod_cast (show n + (k + 1) ≤ 2 * n + 1 + k by omega)
    rw [ENat.eq_top_iff_forall_ge]
    intro m
    exact le_trans (by exact_mod_cast Nat.le_add_left m (2 ^ (K + 1 + esize e)))
      (hgrow m _ le_rfl)

/-! ## Interface with Mathlib computability

The project's headline statement (`MIPRE.HaltingGameValue`) is phrased for
`Nat.Partrec.Code` and Mathlib's `Computable`. Two bridges close the gap, both
computability-only (no time bounds): ambient evaluation is partial recursive, so a
polynomial-time function of the model is Mathlib-computable on computably encoded inputs
(`PolyTimeFun.computable_comp`, `Cost/Partrec.lean`), and the halting problem of
`Nat.Partrec.Code` compiles into the model along a map that is computable on descriptions
(`exists_compile`, `Cost/FromPartrec.lean`). Both work at the level of `Data`: no
`Primcodable` instance for `Prog` is needed, since programs are their own descriptions. -/

/-- The compression lemma, repackaged against Mathlib's halting problem — the form that
will feed `MIPRE.HaltingGameValue.halting_reduces_to_gameValue` once `A` and `f` are
instantiated with normal-form-verifier games and the entanglement requirement (blueprint
`rem:compression-abstract` and `thm:halting`). -/
theorem recursive_compression_halting
    (f : BitStr → ℕ∞) (A : Set BitStr)
    (y₀ : BitStr) (hy₀ : y₀ ∈ A)
    (hA : ∀ x ∈ A, f x < ⊤)
    (Compr : PolyTimeFun ((Prog × ℕ) × ℕ) BitStr)
    (hCompr : ∀ (c : Prog) (m : ℕ) (x : BitStr) (n : ℕ),
      IsSuccinctDesc c m x →
        (max (f x) (n : ℕ∞) ≤ f (Compr ((c, m), n))) ∧
        (x ∈ A → Compr ((c, m), n) ∈ A)) :
    ∃ g : Nat.Partrec.Code → BitStr, Computable g ∧
      ∀ pc : Nat.Partrec.Code,
        ((pc.eval 0).Dom → g pc ∈ A) ∧
        (¬(pc.eval 0).Dom → f (g pc) = ⊤) := by
  obtain ⟨g, hg⟩ := recursive_compression f A y₀ hy₀ hA Compr hCompr
  obtain ⟨compile, hc, hspec⟩ := exists_compile
  refine ⟨fun pc => g (compile pc),
    PolyTimeFun.computable_comp g compile hc Data.primrec_decode_bitStr.to_comp, fun pc => ?_⟩
  exact ⟨fun h => (hg _).1 ((hspec pc).2 h), fun h => (hg _).2 fun h' => h ((hspec pc).1 h')⟩

end MIPRE.Cost
