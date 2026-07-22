/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Cost.Toolkit
import Mathlib.Computability.Halting
import Mathlib.Data.ENat.Lattice

/-!
# The recursive compression lemma

The abstract compression lemma of Marks–Nezhadi–Yuen ("The recursive compression
method for proving undecidability results"), in the variant with compression
parameter `n` ([MNY, Lemma 5.1]) used by this project — blueprint
`lem:recursive-compression` — together with the adapted notion of succinct
description (blueprint `def:succinct`, [MNY, Definition 2.4]) and the
halting-problem corollary in the form consumed by `MIPRE.HaltingGameValue`.

Everything is stated in the ambient cost model (`Cost.Basic`): programs are
`Turing.ToPartrec.Code`, "polynomial-time computable" is `Cost.PolyTimeFun`,
runtimes are `Cost.TimedEval`. The proof is the fixed-point construction of
[MNY, Lemma 3.1/5.1] and uses precisely the toolkit of `Cost.Toolkit`:
`hardcode` (efficient s-m-n) and `smn_polyTime` to build the self-referential
decider, `exists_clocked_universal` to run "`e` for `log n` steps" and to answer
bit-queries within the succinctness budget, and `efficient_fixed_point` to close
the self-reference; the time-transfer clauses are what make the constructed
program a *succinct* description at every recursion level.

## Departures from the paper's statement

* **Succinctness time bound.** [MNY, Definition 2.4] requires
  `runtime(e, m) ≤ n` for *all* `m`. In any cost model that charges to read its
  input (ours does), that bound is vacuous for `|m| > n`; we require
  `≤ (n + 1) * (Nat.size m + 1)` instead. Any `poly(n, |m|)` bound would do; the
  choice only shifts polynomial overheads inside the proof, but it must be fixed
  consistently with the compression theorem for games (`thm:compression`) whose
  output verifiers are what get succinctly described. **Design knob — revisit
  when `thm:compression` is stated.**
* **The instantiation** (blueprint `rem:compression-abstract`): `A` = descriptions
  of normal form verifier games with a perfect PCC strategy, and
  `f = MIPRE.entRequirement (·, 1/2) : _ → ℕ∞` composed with the interpretation of
  descriptions as games. The `ℕ∞` codomain here matches `entRequirement`.
-/

namespace MIPRE.Cost

open Turing.ToPartrec

/-! ## Succinct descriptions ([MNY, Definition 2.4]; blueprint `def:succinct`) -/

/-- The answer a succinct description must give to the bit-query `m` about the
string `x`: the `m`-th bit for `m < |x|`, and the out-of-range marker `2`
otherwise. -/
def bitQueryAnswer (x : BitStr) (m : ℕ) : ℕ :=
  if h : m < x.length then (x.get ⟨m, h⟩).toNat else 2

/-- `(c, n)` **succinctly describes** the bit string `x`: `x` has length at most
`2 ^ n`, and `c` answers every bit-query `m` (presented in binary) within cost
`(n + 1) * (|m| + 1)`.

[MNY, Definition 2.4], with the time bound adapted as discussed in the module
docstring. The pair `(c, n)` is exponentially smaller than `x` itself; a
compression procedure's guarantees are only required on genuine succinct
descriptions, but it must *run* (in polynomial time) on all inputs. -/
def IsSuccinctDesc (c : Code) (n : ℕ) (x : BitStr) : Prop :=
  x.length ≤ 2 ^ n ∧
    ∀ m : ℕ, ∃ t ≤ (n + 1) * (Nat.size m + 1),
      TimedEval c (encode m) [bitQueryAnswer x m] t

/-! ## The compression lemma -/

/-- **Recursive compression lemma** ([MNY, Lemma 5.1]; blueprint
`lem:recursive-compression`).

Data: `f : {0,1}* → ℕ∞`, a nonempty language `A` on which `f` is finite, and a
*polynomial-time* compression procedure `Compr` taking a (claimed) succinct
description `(c, m)` and a target parameter `n`, such that whenever `(c, m)`
genuinely describes `x`:

1. `f (Compr ((c, m), n)) ≥ max (f x) n`, and
2. `x ∈ A → Compr ((c, m), n) ∈ A`.

Conclusion: a polynomial-time reduction `g` from the halting problem (of the
ambient model, on the empty input) to `A`, with `f (g e) = ∞` on non-halting `e`.

There are no computability assumptions on `f`, and no assumptions on the output
of `Compr` off succinct descriptions (but `Compr` is total and fast everywhere —
[MNY, §7] shows this is essential). -/
theorem recursive_compression
    (f : BitStr → ℕ∞) (A : Set BitStr)
    (y₀ : BitStr) (hy₀ : y₀ ∈ A)
    (hA : ∀ x ∈ A, f x < ⊤)
    (Compr : PolyTimeFun ((Code × ℕ) × ℕ) BitStr)
    (hCompr : ∀ (c : Code) (m : ℕ) (x : BitStr) (n : ℕ),
      IsSuccinctDesc c m x →
        (max (f x) (n : ℕ∞) ≤ f (Compr ((c, m), n))) ∧
        (x ∈ A → Compr ((c, m), n) ∈ A)) :
    ∃ g : PolyTimeFun Code BitStr,
      ∀ e : Code,
        ((e.eval []).Dom → g e ∈ A) ∧
        (¬(e.eval []).Dom → f (g e) = ⊤) := by
  sorry

/-! ## Interface with Mathlib computability

The project's headline statement (`MIPRE.HaltingGameValue`) is phrased for
`Nat.Partrec.Code` and Mathlib's `Computable`. Two bridges close the gap; both
are computability-only (no time bounds) and should come from Mathlib's
`Turing.ToPartrec`/`PartrecBasis` machinery. -/

/-- `Turing.ToPartrec.Code` is primitively codable (structural Gödel numbering,
e.g. through `Code.encodeList`; routine). Mathlib does not provide this instance;
it is needed only for the computability bridges below — never for a time bound. -/
instance : Primcodable Code := by
  sorry

/-- Ambient programs compute partial recursive functions; consequently
`PolyTimeFun.toFun` is `Computable` for encoded types. Stated here in the one
instance the project needs. -/
theorem PolyTimeFun.toFun_computable (F : PolyTimeFun Code BitStr) :
    Computable F.toFun := by
  sorry

/-- The halting problem transfers from `Nat.Partrec.Code` to the ambient model
along a computable compilation. (Constructive content: a structural translation
of `Nat.Partrec.Code` into `ToPartrec.Code`, as in Mathlib's `exists_code`, made
into a function.) -/
theorem exists_compile :
    ∃ compile : Nat.Partrec.Code → Code, Computable compile ∧
      ∀ pc : Nat.Partrec.Code,
        ((compile pc).eval []).Dom ↔ (pc.eval 0).Dom := by
  sorry

/-- The compression lemma, repackaged against Mathlib's halting problem — the form
that will feed `MIPRE.HaltingGameValue.halting_reduces_to_gameValue` once `A` and
`f` are instantiated with normal-form-verifier games and the entanglement
requirement (blueprint `rem:compression-abstract` and `thm:halting`). -/
theorem recursive_compression_halting
    (f : BitStr → ℕ∞) (A : Set BitStr)
    (y₀ : BitStr) (hy₀ : y₀ ∈ A)
    (hA : ∀ x ∈ A, f x < ⊤)
    (Compr : PolyTimeFun ((Code × ℕ) × ℕ) BitStr)
    (hCompr : ∀ (c : Code) (m : ℕ) (x : BitStr) (n : ℕ),
      IsSuccinctDesc c m x →
        (max (f x) (n : ℕ∞) ≤ f (Compr ((c, m), n))) ∧
        (x ∈ A → Compr ((c, m), n) ∈ A)) :
    ∃ g : Nat.Partrec.Code → BitStr, Computable g ∧
      ∀ pc : Nat.Partrec.Code,
        ((pc.eval 0).Dom → g pc ∈ A) ∧
        (¬(pc.eval 0).Dom → f (g pc) = ⊤) := by
  sorry -- compose `recursive_compression` with `exists_compile` and
        -- `PolyTimeFun.toFun_computable`

end MIPRE.Cost
