/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Tactic/
QuantumNonneg.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Basic.SubMeasurementFamilies

@[expose] public section

/-!
# Conservative nonnegativity tactic for the symmetric model

This file provides the opt-in tactic `sym_nonneg` for recurring LDT goals of
shape `0 ≤ ...` involving positive effects, tensor placements, and
expectation values in a symmetric model `S : SymModel 𝔓 K`: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Tactic/QuantumNonneg.lean` in the port of
`planning/c6b-plan.md` (milestone M0, section "Port conventions").  The tactic intentionally
does **not** register any global `@[positivity]` extensions: callers must import this module
and invoke the tactic at the proof sites where they want the controlled automation.

The vendored tactic is called `quantum_nonneg`. That syntax is in the import closure of every
port file and keeps calling the vendored matrix lemmas, so the port's macro has a name of its
own; it is the vendored macro with each lemma replaced by its fully qualified
`MIPRE.LIDT.Co` counterpart (the placement lemmas of `Co/Basic/QuantumState.lean`, the
submeasurement lemmas of `Co/Basic/SubMeasurementCore.lean`), plus one fallback, `map_nonneg`,
for a positive operator pushed along an order-preserving map other than the two placements
(a `SubMeas.map` along any ⋆-homomorphism, for instance).

The search is deliberately shallow.  It tries the local wrappers used throughout
the LDT quantum layer, decomposes finite sums and nonnegative scalar multiples,
and leaves scalar side goals to `positivity`/`nlinarith`.  Since `S.opTensor A B` is the
abbreviation `S.L A * S.R B`, a product `S.L A * S.R B` needs no rewrite before the tactic
(the vendored callers rewrite with `leftTensor_mul_rightTensor_eq_opTensor` first; doing so
here is harmless).

## Not ported

The vendored file declares no theorem or definition, only the syntax node `quantumNonneg` of
`quantum_nonneg`; its counterpart is the syntax node `symNonneg` of `sym_nonneg`, renamed
because the vendored syntax is in the import closure. The vendored example is translated below,
with the call sites listed there.
-/

/--
`sym_nonneg` proves small, canonical nonnegativity goals in the LDT quantum
layer of the symmetric model.

It is meant for goals built from:
* positive expectation lemmas (`SymModel.ev_adjoint_self_nonneg`,
  `SymModel.ev_nonneg_of_psd`),
* tensor positivity (`SymModel.opTensor_nonneg`, `SymModel.leftTensor_nonneg`,
  `SymModel.rightTensor_nonneg`, and `map_nonneg` for any other order-preserving map),
* Hermitian sandwich positivity (`IsSelfAdjoint.conjugate_nonneg`),
* finite sums and nonnegative scalar multiples, and
* scalar leaves discharged by `positivity`/`nlinarith`.

This is a conservative tactic macro rather than global automation; it should be
used explicitly at representative proof sites and extended only after measuring
performance on the affected files.
-/
syntax (name := symNonneg) "sym_nonneg" : tactic

macro_rules
  | `(tactic| sym_nonneg) => `(tactic|
    first
    | assumption
    | with_reducible apply _root_.MIPRE.LIDT.Co.SymModel.ev_nonneg_of_psd; sym_nonneg
    | with_reducible exact _root_.MIPRE.LIDT.Co.SymModel.ev_adjoint_self_nonneg _ _
    | with_reducible exact star_mul_self_nonneg _
    | with_reducible apply _root_.MIPRE.LIDT.Co.SymModel.opTensor_nonneg <;> sym_nonneg
    | with_reducible apply _root_.MIPRE.LIDT.Co.SymModel.leftTensor_nonneg; sym_nonneg
    | with_reducible apply _root_.MIPRE.LIDT.Co.SymModel.rightTensor_nonneg; sym_nonneg
    | with_reducible apply _root_.IsSelfAdjoint.conjugate_nonneg
      · sym_nonneg
      · first
        | assumption
        | exact _root_.MIPRE.LIDT.Co.SubMeas.outcome_hermitian _ _
        | simp [*]
    | with_reducible apply Finset.sum_nonneg; intro _ _; sym_nonneg
    | with_reducible_and_instances apply smul_nonneg <;> sym_nonneg
    | exact zero_le_one
    | with_reducible exact _root_.MIPRE.LIDT.Co.SubMeas.outcome_pos _ _
    | with_reducible exact _root_.MIPRE.LIDT.Co.SubMeas.total_nonneg _
    | with_reducible apply _root_.map_nonneg; sym_nonneg
    | positivity
    | nlinarith)

section Examples

namespace MIPRE.LIDT.Co

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (S : SymModel 𝔓 K)

example (X Y : 𝔓) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    0 ≤ S.ev (S.opTensor X Y) := by
  sym_nonneg

/- The goals of the vendored call sites, translated: the outcome positivity of
`diagonalSandwichFamily` and `heterogeneousDiagonalSandwichFamily`
(`Preliminaries/Defs.lean`, with and without the vendored rewrite), of `totalSandwichFamily` and
`heterogeneousTotalSandwichFamily`, and `ev_leftTensor_mul_rightTensor_nonneg`
(`Preliminaries/ComparisonCore.lean`). -/

example {Question Outcome : Type*} [Fintype Outcome]
    (A : IdxSubMeas Question Outcome 𝔓) (B : IdxMeas Question Outcome 𝔓) (q : Question)
    (a : Outcome) :
    0 ≤ S.L ((A q).outcome a) * S.R ((B q).outcome a) := by
  rw [S.leftTensor_mul_rightTensor_eq_opTensor]
  sym_nonneg

example {Question Outcome : Type*} [Fintype Outcome]
    (A : IdxSubMeas Question Outcome 𝔓) (B : IdxMeas Question Outcome 𝔓) (q : Question)
    (a : Outcome) :
    0 ≤ S.L ((A q).outcome a) * S.R ((B q).outcome a) := by
  sym_nonneg

example {Question Outcome : Type*} [Fintype Outcome]
    (A : IdxSubMeas Question Outcome 𝔓) (B : IdxMeas Question Outcome 𝔓) (q : Question)
    (a : Outcome) :
    0 ≤ S.L (A q).total * S.R ((B q).outcome a) := by
  rw [S.leftTensor_mul_rightTensor_eq_opTensor]
  sym_nonneg

example {X Y : 𝔓} (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    0 ≤ S.ev (S.L X * S.R Y) := by
  rw [S.leftTensor_mul_rightTensor_eq_opTensor]
  sym_nonneg

example {X Y : 𝔓} (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    0 ≤ S.ev (S.L X * S.R Y) := by
  sym_nonneg

/- Further shapes: squares, sums, scalar multiples, sandwiches, and images of submeasurements
under the placements. -/

example (M : K →L[ℂ] K) : 0 ≤ S.ev (star M * M) := by
  sym_nonneg

example {α : Type*} [Fintype α] (A : SubMeas α 𝔓) (c : ℝ) (hc : 0 ≤ c) :
    0 ≤ ∑ a, c • S.R (A.outcome a) := by
  sym_nonneg

example {α : Type*} [Fintype α] (A : SubMeas α 𝔓) (B : SubMeas α 𝔓) (a b : α) :
    0 ≤ A.outcome a * B.outcome b * A.outcome a := by
  sym_nonneg

example {α : Type*} [Fintype α] (A : SubMeas α 𝔓) (a : α) :
    0 ≤ (A.map S.L).outcome a := by
  sym_nonneg

example {α : Type*} [Fintype α] (A : SubMeas α 𝔓) (a : α) :
    0 ≤ S.ev ((S.rightPlacedSubMeas A).outcome a) := by
  sym_nonneg

end MIPRE.LIDT.Co

end Examples

end
