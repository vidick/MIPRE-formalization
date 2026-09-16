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
# The abstract compression lemmas

Two abstract compression lemmas, each turning a compression procedure on succinct
descriptions into a reduction from the halting problem, together with their halting-problem
corollaries in the form consumed by `MIPRE.HaltingGameValue`:

* `recursive_compression`: the lemma of Marks–Nezhadi–Yuen ("The recursive compression
  method for proving undecidability results"), in the variant with compression parameter
  `n` ([MNY, Lemma 5.1]) — blueprint `lem:recursive-compression` — whose hypothesis is the
  growth of a measure `f` (the entanglement requirement, in the pipeline of [JNVWY]);
* `compressibility_criterion`: Lin's compression criterion (MIP^co = coRE) — blueprint
  `lem:compressible-criterion` — whose hypothesis is the preservation of two classes, in
  value form, plus the semidecidability of the complement of the second. This is the lemma
  the value-form pipeline of the blueprint uses. The adapted notion of succinct description
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
* **The instantiation** (blueprint `rem:compression-abstract`) uses the per-level form
  `compressibility_criterion_levels`: `A n` = descriptions of `n`-bounded normal form
  verifiers whose `n`-th game has a value-`1` PCC strategy, `B n` = those with value at most
  `1/2` at index `n`, and `S` = the enumeration of strategies of value above `1/2`
  (blueprint `lem:value-lower-approx`, `MIPRE.exists_semidecider_lt_quantumValue`) on the
  tabulated `n`-th game. The compressor cannot read the succinct description it is handed —
  a bit query costs up to `n`, its own time is polylogarithmic in `n` — so it embeds the
  description into a decider that reads it at game time, with the verifier it describes
  frozen at index `2n + 1`; that is what the size slack `2 · |c| ≤ n` and the level
  bookkeeping of the per-level form are for. For `recursive_compression`,
  `f = MIPRE.entRequirement (·, 1/2) : _ → ℕ∞`; the `ℕ∞` codomain there matches
  `entRequirement`.
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

/-! ## Lin's compressibility criterion

The value-form abstract lemma (blueprint `lem:compressible-criterion`): Lin's compression
criterion for `RE`-complete problems ([Lin, MIP^co = coRE, "Compression criteria for
RE-complete problems", direction (3) ⇒ (1)]), in the succinct-description formulation of
[MNY]. Compared with `recursive_compression`, the growth hypothesis on a measure `f` is
replaced by a second preserved class `B` whose complement is semidecidable, and the
self-referential decider gains a *search branch*: at level `n` it also runs, for
`Nat.size n` steps, the semidecision procedure on the string at the *start* of the
recursion. The start level `m` is carried as data next to the level `n` (the decider's input
is `(c', (e, (m, n)))`), so that the decider's code does not depend on the threshold, which is
chosen afterwards from the decider's time bound exactly as in `recursive_compression`.

The lemma is proved in a *per-level* form (`compressibility_criterion_levels`): the classes
`A n`, `B n` are indexed by the level, the semidecider runs on `(x, n)`, and the compression
hypothesis is only required of short descriptions with parameter the level, transferring the
class at level `2n + 1` to the class at level `n` — precisely what the proof uses. The
level-free statement (`compressibility_criterion`) is its special case. -/

/-- The levels of the recursion started at `R`: `R, 2R + 1, 4R + 3, …`. -/
def levels (R : ℕ) : ℕ → ℕ
  | 0 => R
  | k + 1 => 2 * levels R k + 1

@[simp] theorem levels_zero (R : ℕ) : levels R 0 = R := rfl

@[simp] theorem levels_succ (R k : ℕ) : levels R (k + 1) = 2 * levels R k + 1 := rfl

theorem le_levels (R : ℕ) : ∀ k, R ≤ levels R k
  | 0 => le_rfl
  | k + 1 => (le_levels R k).trans (by rw [levels_succ]; omega)

theorem levels_mono (R : ℕ) {j k : ℕ} (h : j ≤ k) : levels R j ≤ levels R k :=
  monotone_nat_of_le_succ (fun n => by rw [levels_succ]; omega) h

theorem two_pow_le_levels {R : ℕ} (hR : 1 ≤ R) : ∀ k, 2 ^ k ≤ levels R k
  | 0 => by simpa using hR
  | k + 1 => by
    have := two_pow_le_levels hR k
    rw [pow_succ, levels_succ]
    omega

namespace Prog

/-- The program of the search branch. On the pair `(d, input)` with
`d = encode ((c', (e, (m, m))), m)` (the input is ignored), run `univ` on the first component
of `d` — that is, `c'` on `encode (e, (m, m))`, the string at the start level `m` — and then
`S` on the pair of the result with the start level `m`. Hardcoding `d`
(`hardcode (searchProg univ S) d`) gives the program the search branch tests for halting. -/
def searchProg (univ S : Prog) : Prog :=
  .elim 0 .nil (.elim 0 .nil
    (.let_ (callVar 0 univ) (.let_ (.cons (.var 0) (.var 2)) (callVar 0 S))))

theorem searchProg_wellScoped {univ S : Prog} (hU : univ.WellScoped 1) (hS : S.WellScoped 1) :
    (searchProg univ S).WellScoped 1 :=
  ⟨Nat.zero_lt_one, trivial, by omega, trivial, callVar_wellScoped (by omega) hU,
    ⟨show 0 < 6 by omega, show 2 < 6 by omega⟩, callVar_wellScoped (by omega) hS⟩

/-- Forward: if `c'` on `encode (e, (m, m))` produces `x` and `S` halts on `(x, m)`, then the
hardcoded search program halts on the empty input. -/
theorem searchProg_runs (U : UniversalMachine) {S : Prog} (hS : S.WellScoped 1)
    {c' e : Prog} {m : ℕ} {x r : Data} {tx ts : ℕ}
    (hx : c'.Runs (encode (e, (m, m))) x tx) (hSr : S.Runs (.cons x (encode m)) r ts) :
    ∃ T, (hardcode (searchProg U.univ S) (encode ((c', (e, (m, m))), m))).Runs .nil r T := by
  obtain ⟨tU, -, hU⟩ := U.time_le c' (encode (e, (m, m))) x tx hx
  have s1 := callVar_eval
    (env := [encode (c', (e, (m, m))), encode m, encode ((c', (e, (m, m))), m), Data.nil,
      Data.cons (encode ((c', (e, (m, m))), m)) Data.nil])
    (i := 0) U.closed (v := .cons (encode c') (encode (e, (m, m)))) (by simp [encode_prod]) hU
  have s2 := callVar_eval
    (env := Data.cons x (encode m) :: x :: [encode (c', (e, (m, m))), encode m,
      encode ((c', (e, (m, m))), m), Data.nil, Data.cons (encode ((c', (e, (m, m))), m)) Data.nil])
    (i := 0) hS (v := .cons x (encode m)) (by simp) hSr
  have hrun : (searchProg U.univ S).Runs (.cons (encode ((c', (e, (m, m))), m)) .nil) r _ :=
    Eval.elim_cons (env := [Data.cons (encode ((c', (e, (m, m))), m)) Data.nil]) (i := 0)
      (n := .nil) (a := encode ((c', (e, (m, m))), m)) (b := .nil) (by simp)
      (Eval.elim_cons (i := 0) (n := .nil) (a := encode (c', (e, (m, m)))) (b := encode m)
        (by simp [encode_prod])
        (Eval.let_ s1 (Eval.let_ (Eval.cons (Eval.var_of_get (i := 0) (v := x) (by simp))
          (Eval.var_of_get (i := 2) (v := encode m) (by simp))) s2)))
  exact ⟨_, hardcode_time (searchProg_wellScoped U.closed hS) hrun⟩

/-- Backward: a run of the hardcoded search program on the empty input yields a run of `c'`
on `encode (e, (m, m))` to some `x` such that `S` halts on `(x, m)`. -/
theorem searchProg_halts_of (U : UniversalMachine) {S : Prog} (hS : S.WellScoped 1)
    {c' e : Prog} {m : ℕ} {r : Data} {T : ℕ}
    (h : (hardcode (searchProg U.univ S) (encode ((c', (e, (m, m))), m))).Runs .nil r T) :
    ∃ x tx, c'.Runs (encode (e, (m, m))) x tx ∧ Halts S (.cons x (encode m)) := by
  obtain ⟨T', -, h'⟩ := hardcode_time_rev (searchProg_wellScoped U.closed hS) h
  change Eval [Data.cons (encode ((c', (e, (m, m))), m)) Data.nil] (.elim 0 .nil _) r T' at h'
  cases h' with
  | elim_nil hget _ => simp at hget
  | elim_cons hget h₁ =>
    rw [Env.get_cons_zero] at hget
    obtain ⟨rfl, rfl⟩ := Data.cons.inj hget
    cases h₁ with
    | elim_nil hget₂ _ => simp [encode_prod] at hget₂
    | elim_cons hget₂ h₂ =>
      rw [Env.get_cons_zero, encode_prod] at hget₂
      obtain ⟨rfl, rfl⟩ := Data.cons.inj hget₂
      cases h₂ with
      | let_ h₃ h₄ =>
        obtain ⟨tU, -, hU⟩ := callVar_runs_rev U.closed h₃
        rw [Env.get_cons_zero] at hU
        obtain ⟨tx, hx⟩ := U.halts_of c' (encode (e, (m, m))) _ tU hU
        cases h₄ with
        | let_ h₅ h₆ =>
          cases h₅ with
          | cons h₅₁ h₅₂ =>
            cases h₅₁
            cases h₅₂
            obtain ⟨ts, -, hSr⟩ := callVar_runs_rev hS h₆
            simp only [Env.get_cons_zero, Env.get_cons_succ] at hSr
            exact ⟨_, tx, hx, _, ts, hSr⟩

end Prog

/-- The decider of the compressibility-criterion argument, as a polynomial-time function of
`(c', (e, (m, n)))`: if `e` halts on the empty input within `Nat.size n` steps, the fixed
string `yYes`; else if the search program for the string at the start level `m` halts within
`Nat.size n` steps, the fixed string `yNo`; otherwise `Compr` applied to the succinct
description `hardcode β ((c', e), (m, 2n + 1))` — where `β` is the bit-query program — with
parameter `n`. As for `decFun`, the self-referential program `c` of the proof is a Kleene
fixed point of `c' ↦ hardcode (decFunV …).code (encode c')`. -/
noncomputable def decFunV (U : UniversalMachine) (UT : ClockedUniversalMachine) (S : Prog)
    (Compr : PolyTimeFun (Prog × ℕ) BitStr) (yYes yNo : BitStr) :
    PolyTimeFun (Prog × (Prog × (ℕ × ℕ))) BitStr :=
  PolyTimeFun.ite
    ((PolyTimeFun.haltsWithin UT).comp
      (PolyTimeFun.pair (PolyTimeFun.fst.comp PolyTimeFun.snd)
        (PolyTimeFun.snd.comp (PolyTimeFun.snd.comp PolyTimeFun.snd))))
    (PolyTimeFun.const yYes)
    (PolyTimeFun.ite
      ((PolyTimeFun.haltsWithin UT).comp
        (PolyTimeFun.pair
          ((PolyTimeFun.smn ((Prog × (Prog × (ℕ × ℕ))) × ℕ)).comp
            (PolyTimeFun.pair (PolyTimeFun.const (Prog.searchProg U.univ S))
              (PolyTimeFun.pair
                (PolyTimeFun.pair PolyTimeFun.fst
                  (PolyTimeFun.pair (PolyTimeFun.fst.comp PolyTimeFun.snd)
                    (PolyTimeFun.pair
                      (PolyTimeFun.fst.comp (PolyTimeFun.snd.comp PolyTimeFun.snd))
                      (PolyTimeFun.fst.comp (PolyTimeFun.snd.comp PolyTimeFun.snd)))))
                (PolyTimeFun.fst.comp (PolyTimeFun.snd.comp PolyTimeFun.snd)))))
          (PolyTimeFun.snd.comp (PolyTimeFun.snd.comp PolyTimeFun.snd))))
      (PolyTimeFun.const yNo)
      (Compr.comp (PolyTimeFun.pair
        ((PolyTimeFun.smn ((Prog × Prog) × (ℕ × ℕ))).comp
          (PolyTimeFun.pair (PolyTimeFun.const (Prog.bitQueryProg U.univ))
            (PolyTimeFun.pair
              (PolyTimeFun.pair PolyTimeFun.fst (PolyTimeFun.fst.comp PolyTimeFun.snd))
              (PolyTimeFun.pair
                (PolyTimeFun.fst.comp (PolyTimeFun.snd.comp PolyTimeFun.snd))
                (PolyTimeFun.next.comp
                  (PolyTimeFun.snd.comp (PolyTimeFun.snd.comp PolyTimeFun.snd)))))))
        (PolyTimeFun.snd.comp (PolyTimeFun.snd.comp PolyTimeFun.snd)))))

theorem decFunV_apply (U : UniversalMachine) (UT : ClockedUniversalMachine) (S : Prog)
    (Compr : PolyTimeFun (Prog × ℕ) BitStr) (yYes yNo : BitStr) (c' e : Prog) (m n : ℕ) :
    decFunV U UT S Compr yYes yNo (c', (e, (m, n))) =
      if (evalWithin e .nil (Nat.size n)).isSome then yYes
      else if (evalWithin (hardcode (Prog.searchProg U.univ S) (encode ((c', (e, (m, m))), m)))
          .nil (Nat.size n)).isSome then yNo
      else Compr (hardcode (Prog.bitQueryProg U.univ) (encode ((c', e), (m, 2 * n + 1))), n) :=
  rfl

/-- **Compressibility criterion, per level** (Lin; blueprint `lem:compressible-criterion`),
the value-form abstract compression lemma in the form an instantiation by gap-preserving
compression can meet.

Data: two families of languages `A n`, `B n` indexed by the level `n` of the recursion, with
distinguished elements `yYes ∈ A n` and `yNo ∈ B n` at every level `n ≥ n₀`; a semidecision
procedure `S` for the complement of `B` (a closed program halting on `encode (x, n)` exactly
when `x ∉ B n`); and a *polynomial-time* compression procedure `Compr` taking a (claimed)
succinct description `c` with parameter `n` — the level — such that whenever `n ≥ n₀`, `c` is
short (`2 · |c| ≤ n`) and genuinely describes `x` with parameter `n`:

1. `x ∈ A (2n + 1) → Compr (c, n) ∈ A n`, and
2. `x ∈ B (2n + 1) → Compr (c, n) ∈ B n`.

Conclusion: a polynomial-time reduction `g` from the halting problem (of the ambient model,
on the empty input `nil`) and a constant `K` such that, with `R e = 2 ^ (K + 1 + |e|)` (a level
at least `n₀`), `g e ∈ A (R e)` on halting `e` and `g e ∈ B (R e)` on non-halting `e`.

The level bookkeeping is what an instantiation needs. The compressor is polynomial-time in
the *size* of its input `(c, n)`, that is, polylogarithmic in `n`, while a bit query to `c`
costs up to `n` — so `Compr` cannot read the string `x` it is compressing, only embed `c` into
its output for a later reader (a decider at index `n`, whose time budget is polynomial in
`n`); the slack `2 · |c| ≤ n` is what lets that output stay short. And the hypothesis relates
the class of `x` at level `2n + 1` to the class of the output at level `n`, which is exactly
what the proof uses: at level `n` the self-referential decider compresses the string it
itself computes at level `2n + 1`. See the module docstring for the reading of the levels
in the instantiation. Nothing is demanded of `Compr` off short genuine descriptions above
`n₀`, but it is total and fast everywhere.

There is no measure and no growth hypothesis: the self-referential decider at level `n`
compresses the next level `2n + 1`, unless `e` halts within `Nat.size n` steps (output
`yYes`) or the semidecision procedure, run on the string at the start level of the
recursion, halts within `Nat.size n` steps (output `yNo`). Non-halting `e`: if the start
string were outside `B`, the search branch would eventually fire, and preservation of `B`
down the levels would put the start string in `B`. Halting `e`: the search branch can never
fire before `e` halts, by the same downward argument, so preservation of `A` down from the
level where `e` halts applies. -/
theorem compressibility_criterion_levels
    (A B : ℕ → Set BitStr) (n₀ : ℕ)
    (yYes : BitStr) (hyes : ∀ n, n₀ ≤ n → yYes ∈ A n)
    (yNo : BitStr) (hno : ∀ n, n₀ ≤ n → yNo ∈ B n)
    (S : Prog) (hSws : S.WellScoped 1)
    (hS : ∀ (x : BitStr) (n : ℕ), Halts S (encode (x, n)) ↔ x ∉ B n)
    (Compr : PolyTimeFun (Prog × ℕ) BitStr)
    (hCompr : ∀ (c : Prog) (x : BitStr) (n : ℕ), n₀ ≤ n → 2 * esize c ≤ n →
      IsSuccinctDesc c n x → x.length ≤ n + 1 →
        (x ∈ A (2 * n + 1) → Compr (c, n) ∈ A n) ∧ (x ∈ B (2 * n + 1) → Compr (c, n) ∈ B n)) :
    ∃ (g : PolyTimeFun Prog BitStr) (K : ℕ),
      ∀ e : Prog, n₀ ≤ 2 ^ (K + 1 + esize e) ∧
        (Halts e .nil → g e ∈ A (2 ^ (K + 1 + esize e))) ∧
        (¬ Halts e .nil → g e ∈ B (2 ^ (K + 1 + esize e))) := by
  obtain ⟨U⟩ := exists_efficient_universal
  obtain ⟨UT⟩ := exists_clocked_universal
  -- the decider, kept opaque through its functional equation
  obtain ⟨dec, hdec⟩ : ∃ dec : PolyTimeFun (Prog × (Prog × (ℕ × ℕ))) BitStr, ∀ c' e m n,
      dec (c', (e, (m, n))) =
        if (evalWithin e .nil (Nat.size n)).isSome then yYes
        else if (evalWithin (hardcode (Prog.searchProg U.univ S) (encode ((c', (e, (m, m))), m)))
            .nil (Nat.size n)).isSome then yNo
        else Compr (hardcode (Prog.bitQueryProg U.univ) (encode ((c', e), (m, 2 * n + 1))),
          n) :=
    ⟨decFunV U UT S Compr yYes yNo, decFunV_apply U UT S Compr yYes yNo⟩
  -- the self-reference: `c` on `q` computes `dec (c, q)`
  obtain ⟨F, hF⟩ : ∃ F : PolyTimeFun Prog Prog, ∀ c', F c' = hardcode dec.code (encode c') :=
    ⟨(PolyTimeFun.smn Prog).comp (PolyTimeFun.pair (PolyTimeFun.const dec.code)
      (PolyTimeFun.id Prog)), fun _ => rfl⟩
  obtain ⟨c, p, hc, -, hc_time⟩ := efficient_fixed_point F
  -- the time bound of `c`
  obtain ⟨cB, hcB⟩ : ∃ cB : Polynomial ℕ, ∀ x, cB.eval x =
      p.eval (2 * x + dec.timeBound.eval (x + (esize c + 1)) + (esize c + 5)) :=
    ⟨p.comp (C 2 * X + dec.timeBound.comp (X + C (esize c + 1)) + C (esize c + 5)),
      fun x => by simp [Polynomial.eval_comp]⟩
  have c_runs : ∀ q : Prog × (ℕ × ℕ), ∃ t ≤ cB.eval (esize q),
      c.Runs (encode q) (encode (dec (c, q))) t := by
    intro q
    obtain ⟨t₀, ht₀, h₀⟩ := dec.computes (c, q)
    have h₁ := hardcode_time dec.closed (d := encode c) (x := encode q) h₀
    rw [← hF c] at h₁
    obtain ⟨t', ht', h'⟩ := hc_time _ _ _ h₁
    refine ⟨t', ?_, h'⟩
    rw [hcB]
    refine ht'.trans (polynomial_eval_mono p ?_)
    have hm := polynomial_eval_mono dec.timeBound
      (show esize (c, q) ≤ esize q + (esize c + 1) by simp only [esize_prod]; omega)
    have e1 : (encode q).size = esize q := rfl
    have e2 : (encode c).size = esize c := rfl
    omega
  -- `c` as a polynomial-time function of `q = (e, (m, n))`
  obtain ⟨cFun, hcFun⟩ : ∃ cFun : PolyTimeFun (Prog × (ℕ × ℕ)) BitStr,
      ∀ q, cFun q = dec (c, q) :=
    ⟨{ toFun := fun q => dec (c, q)
       code := c
       closed := hc
       timeBound := cB
       computes := fun q => c_runs q }, fun _ => rfl⟩
  -- the overhead polynomials in `x = esize e + Nat.size n`, and the threshold constant:
  -- `Q₁` bounds the run of `c` at level `2n + 1`, `Q₂` the bit-query overhead, `Q₃` twice
  -- the size of the hardcoded bit-query program
  obtain ⟨Q₁, hQ₁⟩ : ∃ Q₁ : Polynomial ℕ, ∀ x, Q₁.eval x = cB.eval (9 * x + 8) :=
    ⟨cB.comp (C 9 * X + C 8), fun x => by simp [Polynomial.eval_comp]⟩
  obtain ⟨Q₂, hQ₂⟩ : ∃ Q₂ : Polynomial ℕ, ∀ x, Q₂.eval x =
      (bitQueryBound U).eval (Q₁.eval x + 9 * x + (esize c + 7)) + 9 * x + (esize c + 13) :=
    ⟨(bitQueryBound U).comp (Q₁ + C 9 * X + C (esize c + 7)) + C 9 * X + C (esize c + 13),
      fun x => by simp [Polynomial.eval_comp]⟩
  obtain ⟨Q₃, hQ₃⟩ : ∃ Q₃ : Polynomial ℕ, ∀ x, Q₃.eval x =
      2 * (esize (Prog.bitQueryProg U.univ) + esize c + 9 * x + 44) + 1 :=
    ⟨C 2 * (C (esize (Prog.bitQueryProg U.univ) + esize c + 44) + C 9 * X) + C 1,
      fun x => by simp; ring⟩
  obtain ⟨K₀, hK₀⟩ := exists_threshold (Q₁ + Q₂ + Q₃)
  -- the threshold constant also puts every level above `n₀`
  obtain ⟨K, hK, hKn₀⟩ : ∃ K : ℕ,
      (∀ x n : ℕ, 2 ^ (K + 1 + x) ≤ n → (Q₁ + Q₂ + Q₃).eval (x + Nat.size n) ≤ n + 1) ∧
      ∀ x n : ℕ, 2 ^ (K + 1 + x) ≤ n → n₀ ≤ n := by
    refine ⟨K₀ + Nat.size n₀, fun x n hn => hK₀ x n ?_, fun x n hn => ?_⟩
    · exact le_trans (Nat.pow_le_pow_right two_pos (by omega)) hn
    · exact le_trans (Nat.lt_size_self n₀).le
        (le_trans (Nat.pow_le_pow_right two_pos (by omega)) hn)
  -- above the threshold `R = 2 ^ (K + 1 + esize e)`, which is also the start level, `c` at
  -- level `2n + 1` is fast and its output is succinctly described by the hardcoded bit-query
  -- program with parameter `n`; that program is short, and the level is at least `n₀`
  have key : ∀ e n, 2 ^ (K + 1 + esize e) ≤ n →
      n₀ ≤ n ∧
      2 * esize (hardcode (Prog.bitQueryProg U.univ)
        (encode ((c, e), (2 ^ (K + 1 + esize e), 2 * n + 1)))) ≤ n ∧
      IsSuccinctDesc (hardcode (Prog.bitQueryProg U.univ)
          (encode ((c, e), (2 ^ (K + 1 + esize e), 2 * n + 1)))) n
        (dec (c, (e, (2 ^ (K + 1 + esize e), 2 * n + 1)))) ∧
      (dec (c, (e, (2 ^ (K + 1 + esize e), 2 * n + 1)))).length ≤ n + 1 := by
    intro e n hn
    obtain ⟨t, ht, hrun⟩ := c_runs (e, (2 ^ (K + 1 + esize e), 2 * n + 1))
    have hQ := hK (esize e) n hn
    rw [Polynomial.eval_add, Polynomial.eval_add, hQ₁, hQ₂, hQ₁, hQ₃] at hQ
    have hlt : K + 1 + esize e < Nat.size n := Nat.lt_size.mpr hn
    have hsm : esize (2 ^ (K + 1 + esize e)) ≤ 4 * Nat.size n + 1 := by
      have h1 := esize_nat_le (2 ^ (K + 1 + esize e))
      rw [Nat.size_pow] at h1
      omega
    have hsz : esize (2 * n + 1) ≤ 4 * Nat.size n + 5 := by
      have := esize_nat_le (2 * n + 1)
      rw [size_two_mul_add_one] at this
      omega
    have hsize : esize (hardcode (Prog.bitQueryProg U.univ)
        (encode ((c, e), (2 ^ (K + 1 + esize e), 2 * n + 1)))) ≤
        esize (Prog.bitQueryProg U.univ) + esize c + 9 * (esize e + Nat.size n) + 44 := by
      rw [hardcode_size]
      have hd : (encode ((c, e), (2 ^ (K + 1 + esize e), 2 * n + 1))).size =
          esize ((c, e), (2 ^ (K + 1 + esize e), 2 * n + 1)) := rfl
      rw [hd]
      simp only [esize_prod]
      omega
    refine ⟨hKn₀ (esize e) n hn, by omega, ?_⟩
    have ht₁ : t ≤ cB.eval (9 * (esize e + Nat.size n) + 8) := by
      refine ht.trans (polynomial_eval_mono cB ?_)
      simp only [esize_prod]
      omega
    have hpow : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
    -- the run producing `x` costs at most `n + 1`, so `x` is that short: the bound
    -- `IsSuccinctDesc` records is `2 ^ n`, which is what obligation O4 then cannot use
    have hxlen : (dec (c, (e, (2 ^ (K + 1 + esize e), 2 * n + 1)))).length ≤ n + 1 :=
      (length_le_esize_bitStr _).trans (hrun.size_le.trans (by omega))
    refine ⟨?_, hxlen⟩
    refine isSuccinctDesc_hardcode U c e (2 ^ (K + 1 + esize e), 2 * n + 1) n _ hrun
      (by omega) ?_
    have hb := polynomial_eval_mono (bitQueryBound U)
      (show esize c + esize e + esize (2 ^ (K + 1 + esize e), 2 * n + 1) + t ≤
        cB.eval (9 * (esize e + Nat.size n) + 8) + 9 * (esize e + Nat.size n) + (esize c + 7)
        by simp only [esize_prod]; omega)
    simp only [esize_prod] at hb ⊢
    omega
  -- the reduction: the string at level `R = 2 ^ (K + 1 + esize e)` of the recursion started
  -- at `R`
  refine ⟨cFun.comp (PolyTimeFun.pair (PolyTimeFun.id Prog)
    (PolyTimeFun.pair (PolyTimeFun.threshold K) (PolyTimeFun.threshold K))), K, fun e => ?_⟩
  have hg : cFun.comp (PolyTimeFun.pair (PolyTimeFun.id Prog)
      (PolyTimeFun.pair (PolyTimeFun.threshold K) (PolyTimeFun.threshold K))) e =
      dec (c, (e, (2 ^ (K + 1 + esize e), 2 ^ (K + 1 + esize e)))) := by
    rw [PolyTimeFun.comp_apply, PolyTimeFun.pair_apply, PolyTimeFun.pair_apply, hcFun,
      PolyTimeFun.id_apply, PolyTimeFun.threshold_apply]
  rw [hg]
  have key' := key e
  have hR1 : 1 ≤ 2 ^ (K + 1 + esize e) := Nat.one_le_two_pow
  have hRn₀ : n₀ ≤ 2 ^ (K + 1 + esize e) := hKn₀ (esize e) _ le_rfl
  generalize hR : 2 ^ (K + 1 + esize e) = R at key' hR1 hRn₀ ⊢
  -- the level of every step of the recursion is at least `n₀`
  have hlev : ∀ j, n₀ ≤ levels R j := fun j => hRn₀.trans (le_levels R j)
  -- the clocked halting test is monotone in the budget
  have hmono : ∀ (q : Prog) (k k' : ℕ), k ≤ k' → (evalWithin q .nil k).isSome = true →
      (evalWithin q .nil k').isSome = true := by
    intro q k k' hkk' h
    obtain ⟨r, t, ht, hr⟩ := (evalWithin_isSome_iff _ _ _).1 h
    exact (evalWithin_isSome_iff _ _ _).2 ⟨r, t, ht.trans hkk', hr⟩
  -- the search branch, both ways: it fires only if the start string is outside `B R`, and it
  -- eventually fires if the start string is outside `B R`
  have hsearch_of : ∀ k, (evalWithin (hardcode (Prog.searchProg U.univ S)
      (encode ((c, (e, (R, R))), R))) .nil k).isSome = true → dec (c, (e, (R, R))) ∉ B R := by
    intro k h
    obtain ⟨r, t, -, hrun⟩ := (evalWithin_isSome_iff _ _ _).1 h
    obtain ⟨x, tx, hx, hSx⟩ := Prog.searchProg_halts_of U hSws hrun
    obtain ⟨t', -, hc'⟩ := c_runs (e, (R, R))
    obtain ⟨rfl, -⟩ := Eval.deterministic hx hc'
    exact (hS _ _).1 hSx
  have hsearch_fires : dec (c, (e, (R, R))) ∉ B R → ∃ T₀, ∀ k, T₀ ≤ k →
      (evalWithin (hardcode (Prog.searchProg U.univ S) (encode ((c, (e, (R, R))), R))) .nil
        k).isSome = true := by
    intro hnB
    obtain ⟨r, ts, hSr⟩ := (hS _ _).2 hnB
    obtain ⟨t', -, hc'⟩ := c_runs (e, (R, R))
    obtain ⟨T₀, hT₀⟩ := Prog.searchProg_runs U hSws hc' hSr
    exact ⟨T₀, fun k hk => (evalWithin_isSome_iff _ _ _).2 ⟨r, T₀, hk, hT₀⟩⟩
  refine ⟨hRn₀, fun hh => ?_, fun hnh => ?_⟩
  · -- halting `e`
    obtain ⟨r₀, T, hT⟩ := hh
    have htrue : ∀ n, T ≤ Nat.size n → (evalWithin e .nil (Nat.size n)).isSome = true :=
      fun n hn => (evalWithin_isSome_iff _ _ _).2 ⟨r₀, T, hn, hT⟩
    -- below a level where the search fires while `e` has not yet halted, every level of the
    -- recursion is in `B`
    have hB : ∀ j₀, (evalWithin e .nil (Nat.size (levels R j₀))).isSome = false →
        (evalWithin (hardcode (Prog.searchProg U.univ S) (encode ((c, (e, (R, R))), R))) .nil
          (Nat.size (levels R j₀))).isSome = true →
        ∀ i j, j + i = j₀ → dec (c, (e, (R, levels R j))) ∈ B (levels R j) := by
      intro j₀ hnot hfire i
      induction i with
      | zero =>
        intro j hj
        rw [Nat.add_zero] at hj
        subst hj
        rw [hdec, hnot, if_neg Bool.false_ne_true, hfire, if_pos rfl]
        exact hno _ (hlev _)
      | succ i ih =>
        intro j hj
        have hjle : Nat.size (levels R j) ≤ Nat.size (levels R j₀) :=
          Nat.size_le_size (levels_mono R (by omega))
        have hd := hdec c e R (levels R j)
        cases hb₁ : (evalWithin e .nil (Nat.size (levels R j))).isSome with
        | true =>
          exfalso
          rw [hmono e _ _ hjle hb₁] at hnot
          exact absurd hnot (by decide)
        | false =>
          rw [hb₁, if_neg Bool.false_ne_true] at hd
          cases hb₂ : (evalWithin (hardcode (Prog.searchProg U.univ S)
              (encode ((c, (e, (R, R))), R))) .nil (Nat.size (levels R j))).isSome with
          | true =>
            rw [hb₂, if_pos rfl] at hd
            rw [hd]
            exact hno _ (hlev _)
          | false =>
            rw [hb₂, if_neg Bool.false_ne_true] at hd
            rw [hd]
            have hnext := ih (j + 1) (by omega)
            rw [levels_succ] at hnext
            obtain ⟨h₀, h₁, h₂, h₃⟩ := key' (levels R j) (le_levels R j)
            exact (hCompr _ _ _ h₀ h₁ h₂ h₃).2 hnext
    -- from a level where `e` has halted, every level of the recursion is in `A`
    have hA : ∀ k j, T ≤ Nat.size (levels R (j + k)) →
        dec (c, (e, (R, levels R j))) ∈ A (levels R j) := by
      intro k
      induction k with
      | zero =>
        intro j hj
        rw [Nat.add_zero] at hj
        rw [hdec, htrue _ hj, if_pos rfl]
        exact hyes _ (hlev _)
      | succ k ih =>
        intro j hj
        have hd := hdec c e R (levels R j)
        cases hb₁ : (evalWithin e .nil (Nat.size (levels R j))).isSome with
        | true =>
          rw [hb₁, if_pos rfl] at hd
          rw [hd]
          exact hyes _ (hlev _)
        | false =>
          rw [hb₁, if_neg Bool.false_ne_true] at hd
          cases hb₂ : (evalWithin (hardcode (Prog.searchProg U.univ S)
              (encode ((c, (e, (R, R))), R))) .nil (Nat.size (levels R j))).isSome with
          | true =>
            exfalso
            have hRB := hB j hb₁ hb₂ j 0 (by omega)
            rw [levels_zero] at hRB
            exact hsearch_of _ hb₂ hRB
          | false =>
            rw [hb₂, if_neg Bool.false_ne_true] at hd
            rw [hd]
            have hnext := ih (j + 1) (by rw [show j + 1 + k = j + (k + 1) by omega]; exact hj)
            rw [levels_succ] at hnext
            obtain ⟨h₀, h₁, h₂, h₃⟩ := key' (levels R j) (le_levels R j)
            exact (hCompr _ _ _ h₀ h₁ h₂ h₃).1 hnext
    obtain ⟨k, hk⟩ : ∃ k, T ≤ Nat.size (levels R k) := by
      refine ⟨T, ?_⟩
      have h1 := Nat.size_le_size (two_pow_le_levels hR1 T)
      rw [Nat.size_pow] at h1
      omega
    have hfin := hA k 0 (by simpa using hk)
    rw [levels_zero] at hfin
    exact hfin
  · -- non-halting `e`
    have hfalse : ∀ n, (evalWithin e .nil (Nat.size n)).isSome = false := fun n => by
      rw [Bool.eq_false_iff]
      intro h
      obtain ⟨r, t, -, hr⟩ := (evalWithin_isSome_iff _ _ _).1 h
      exact hnh ⟨r, t, hr⟩
    by_contra hnB
    obtain ⟨T₀, hT₀⟩ := hsearch_fires hnB
    -- from a level where the search fires, every level of the recursion is in `B`
    have hB : ∀ k j, T₀ ≤ Nat.size (levels R (j + k)) →
        dec (c, (e, (R, levels R j))) ∈ B (levels R j) := by
      intro k
      induction k with
      | zero =>
        intro j hj
        rw [Nat.add_zero] at hj
        rw [hdec, hfalse (levels R j), if_neg Bool.false_ne_true, hT₀ _ hj, if_pos rfl]
        exact hno _ (hlev _)
      | succ k ih =>
        intro j hj
        have hd := hdec c e R (levels R j)
        rw [hfalse (levels R j), if_neg Bool.false_ne_true] at hd
        cases hb₂ : (evalWithin (hardcode (Prog.searchProg U.univ S)
            (encode ((c, (e, (R, R))), R))) .nil (Nat.size (levels R j))).isSome with
        | true =>
          rw [hb₂, if_pos rfl] at hd
          rw [hd]
          exact hno _ (hlev _)
        | false =>
          rw [hb₂, if_neg Bool.false_ne_true] at hd
          rw [hd]
          have hnext := ih (j + 1) (by rw [show j + 1 + k = j + (k + 1) by omega]; exact hj)
          rw [levels_succ] at hnext
          obtain ⟨h₀, h₁, h₂, h₃⟩ := key' (levels R j) (le_levels R j)
          exact (hCompr _ _ _ h₀ h₁ h₂ h₃).2 hnext
    obtain ⟨k, hk⟩ : ∃ k, T₀ ≤ Nat.size (levels R k) := by
      refine ⟨T₀, ?_⟩
      have h1 := Nat.size_le_size (two_pow_le_levels hR1 T₀)
      rw [Nat.size_pow] at h1
      omega
    have hfin := hB k 0 (by simpa using hk)
    rw [levels_zero] at hfin
    exact hnB hfin

/-- **Compressibility criterion** (Lin; blueprint `lem:compressible-criterion`), the
value-form abstract compression lemma in its level-free form: the special case of
`compressibility_criterion_levels` with the same classes at every level and a compressor
that receives the parameter of the succinct description separately from the level.

Data: two languages `A`, `B` with distinguished elements `yYes ∈ A` and `yNo ∈ B`; a
semidecision procedure `S` for the complement of `B` (a closed program halting on `encode x`
exactly when `x ∉ B`); and a *polynomial-time* compression procedure `Compr` taking a
(claimed) succinct description `(c, m)` and a target parameter `n`, such that whenever
`(c, m)` genuinely describes `x`:

1. `x ∈ A → Compr ((c, m), n) ∈ A`, and
2. `x ∈ B → Compr ((c, m), n) ∈ B`.

Conclusion: a polynomial-time reduction `g` from the halting problem (of the ambient model,
on the empty input `nil`) with `g e ∈ A` on halting `e` and `g e ∈ B` on non-halting `e`.
This is the form of [Lin], [MNY]; the per-level form is the one the instantiation by
gap-preserving compression can satisfy (blueprint `rem:compression-abstract`). -/
theorem compressibility_criterion
    (A B : Set BitStr)
    (yYes : BitStr) (hyes : yYes ∈ A) (yNo : BitStr) (hno : yNo ∈ B)
    (S : Prog) (hSws : S.WellScoped 1) (hS : ∀ x : BitStr, Halts S (encode x) ↔ x ∉ B)
    (Compr : PolyTimeFun ((Prog × ℕ) × ℕ) BitStr)
    (hCompr : ∀ (c : Prog) (m : ℕ) (x : BitStr) (n : ℕ),
      IsSuccinctDesc c m x →
        (x ∈ A → Compr ((c, m), n) ∈ A) ∧ (x ∈ B → Compr ((c, m), n) ∈ B)) :
    ∃ g : PolyTimeFun Prog BitStr,
      ∀ e : Prog,
        (Halts e .nil → g e ∈ A) ∧
        (¬ Halts e .nil → g e ∈ B) := by
  -- the semidecider on pairs `(x, n)`: project to `x`
  have hS' : ∀ (x : BitStr) (n : ℕ), Halts (.let_ Prog.fstProg S) (encode (x, n)) ↔ x ∉ B := by
    intro x n
    rw [← hS x]
    have hpre := Prog.fstProg_runs (encode x) (encode n)
    constructor
    · rintro ⟨r, t, h⟩
      cases h with
      | let_ h₁ h₂ =>
        obtain ⟨rfl, -⟩ := h₁.deterministic hpre
        exact ⟨r, _, Eval.of_append_of_wellScoped (env := [_]) (extra := [_]) h₂ hSws⟩
    · rintro ⟨r, t, h⟩
      exact ⟨r, _, Eval.let_ hpre (Eval.append_of_wellScoped h hSws _)⟩
  obtain ⟨g, K, hg⟩ := compressibility_criterion_levels (fun _ => A) (fun _ => B) 0
    yYes (fun _ _ => hyes) yNo (fun _ _ => hno) (.let_ Prog.fstProg S)
    ⟨Prog.fstProg_wellScoped, hSws.mono (by omega) _⟩ hS'
    (Compr.comp (PolyTimeFun.pair (PolyTimeFun.id _) PolyTimeFun.snd))
    (fun c x n _ _ hsucc _ => by simpa using hCompr c n x n hsucc)
  exact ⟨g, fun e => ⟨(hg e).2.1, (hg e).2.2⟩⟩

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

/-- The compressibility criterion, repackaged against Mathlib's halting problem — the form
that feeds `MIPRE.HaltingGameValue.halting_reduces_to_gameValue` once `A` and `B` are
instantiated with normal-form-verifier games having a perfect PCC strategy, respectively
value at most `1/2` (blueprint `rem:compression-abstract` and `thm:halting`). -/
theorem compressibility_criterion_halting
    (A B : Set BitStr)
    (yYes : BitStr) (hyes : yYes ∈ A) (yNo : BitStr) (hno : yNo ∈ B)
    (S : Prog) (hSws : S.WellScoped 1) (hS : ∀ x : BitStr, Halts S (encode x) ↔ x ∉ B)
    (Compr : PolyTimeFun ((Prog × ℕ) × ℕ) BitStr)
    (hCompr : ∀ (c : Prog) (m : ℕ) (x : BitStr) (n : ℕ),
      IsSuccinctDesc c m x →
        (x ∈ A → Compr ((c, m), n) ∈ A) ∧ (x ∈ B → Compr ((c, m), n) ∈ B)) :
    ∃ g : Nat.Partrec.Code → BitStr, Computable g ∧
      ∀ pc : Nat.Partrec.Code,
        ((pc.eval 0).Dom → g pc ∈ A) ∧
        (¬(pc.eval 0).Dom → g pc ∈ B) := by
  obtain ⟨g, hg⟩ := compressibility_criterion A B yYes hyes yNo hno S hSws hS Compr hCompr
  obtain ⟨compile, hc, hspec⟩ := exists_compile
  refine ⟨fun pc => g (compile pc),
    PolyTimeFun.computable_comp g compile hc Data.primrec_decode_bitStr.to_comp, fun pc => ?_⟩
  exact ⟨fun h => (hg _).1 ((hspec pc).2 h), fun h => (hg _).2 fun h' => h ((hspec pc).1 h')⟩

end MIPRE.Cost
