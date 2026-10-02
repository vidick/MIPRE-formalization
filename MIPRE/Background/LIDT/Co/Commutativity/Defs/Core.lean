/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/Defs/Core.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored
file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.CommutativityPoints.Defs
public import MIPRE.Background.LIDT.Co.Test.StrategyPolynomialFamilies
public import MIPRE.Background.LIDT.MIPStarRE.LDT.Commutativity.Defs.Core

@[expose] public section

/-!
# Section 11 commutativity: core definitions

The operator families of the evaluated-slice, full-slice and stability steps of the Section 11
commutativity argument: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/Defs/Core.lean` in the port of
`planning/c6b-plan.md` (milestone M7, section "Port conventions").

A polynomial family `family : IdxPolyFamily params 𝔓` lives in the local C*-algebra `𝔓` (the
vendored `Op ι`), and a strategy is a `SymStrat params.next 𝔓 K`. The vendored placements
`leftPlacedSubMeas (ιB := ι)`, `OpFamily.leftPlacedOpFamily (ιB := ι)` and
`rightPlacedSubMeas (ιA := ι)` are the model's `S.leftPlacedSubMeas`,
`OpFamily.leftPlacedOpFamily S` and `S.rightPlacedSubMeas`. The definitions that already take a
strategy (`evaluatedSliceProductLeft`, `fullSliceProductRight`, …) place by `strategy.state`, so
their vendored signatures are unchanged; the three that place without one
(`leftOrderedProductOpFamily`, `evaluatedPointFamilyLeft`, `evaluatedPointFamilyRight`) take the
symmetric model `S` as an explicit first argument, as M1's `tensorProductSubMeas` does
(`planning/c6b-plan.md`, "Departures in M1"). `appendRightTotalOpFamily` is generic over any
type with a multiplication and `sandwichByOuterSubMeas` over any C*-algebra with its order.

The classical half of the vendored file (the question and outcome types and the evaluation maps
on them) is not ported: this file imports the vendored file and names those declarations through
an explicit `open MIPStarRE.LDT.Commutativity (…)` list.

## New here

`sandwichByOuterSubMeas_sum_outcome`, the identity `∑_{a,b} A_a B_b A_a = ∑_a A_a B A_a` that is
the vendored inline `sum_eq_total` proof of `sandwichByOuterSubMeas`.

## Not ported

- `EvaluatedSliceQuestion`: classical, imported.
- `EvaluatedSliceOutcome`: classical, imported.
- `FullSliceQuestion`: classical, imported.
- `FullSliceOutcome`: classical, imported.
- `StabilityOneOutcome`: classical, imported.
- `StabilityTwoOutcome`: classical, imported.
- `fullSliceQuestionOfEvaluatedSlice`: classical, imported.
- `evaluateFullSliceOutcomeAtQuestion`: classical, imported.
- `evaluateStabilityOneOutcomeAtQuestion`: classical, imported.
- `evaluateStabilityTwoOutcomeAtQuestion`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-points.tex`
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Commutativity

open MIPStarRE.LDT (Parameters FieldModel Point Fq)
open MIPStarRE.LDT.Commutativity (EvaluatedSliceQuestion EvaluatedSliceOutcome FullSliceQuestion
  FullSliceOutcome)
open MIPRE.LIDT.Co.CommutativityPoints (orderedProductOpFamily reversedProductOpFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Ordered product placed on the first factor by the symmetric model `S`:
`(A_a B_b) ⊗ I` is `S.L (A_a * B_b)`. -/
noncomputable def leftOrderedProductOpFamily {α β : Type*} [Fintype α] [Fintype β]
    (S : SymModel 𝔓 K) (A : SubMeas α 𝔓) (B : SubMeas β 𝔓) :
    OpFamily (α × β) (K →L[ℂ] K) :=
  OpFamily.leftPlacedOpFamily S (orderedProductOpFamily A B)

/-- Append a total operator on the right of every outcome operator. -/
noncomputable def appendRightTotalOpFamily {α : Type*} {R : Type*} [Mul R]
    (A : OpFamily α R) (X : R) : OpFamily α R where
  outcome := fun a => A.outcome a * X
  total := A.total * X

omit [StarOrderedRing 𝔓] in
/-- The outcome operators `A_a B_b A_a` of `sandwichByOuterSubMeas` sum to its total
`∑_a A_a (∑_b B_b) A_a`. -/
theorem sandwichByOuterSubMeas_sum_outcome {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α 𝔓) (B : SubMeas β 𝔓) :
    ∑ ab : α × β, A.outcome ab.1 * B.outcome ab.2 * A.outcome ab.1 =
      ∑ a : α, A.outcome a * B.total * A.outcome a := by
  rw [Fintype.sum_prod_type' (fun a b => A.outcome a * B.outcome b * A.outcome a)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_mul, ← Finset.mul_sum, B.sum_eq_total]

/-- Sandwiched product `A_a B_b A_a`.

Its total operator is the sum of sandwiches `∑_a A_a (∑_b B_b) A_a`. -/
noncomputable def sandwichByOuterSubMeas {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α 𝔓) (B : SubMeas β 𝔓) :
    SubMeas (α × β) 𝔓 where
  outcome := fun ab =>
    match ab with
    | (a, b) => A.outcome a * B.outcome b * A.outcome a
  total := ∑ a : α, A.outcome a * B.total * A.outcome a
  outcome_pos := fun ⟨a, b⟩ =>
    IsSelfAdjoint.conjugate_nonneg (B.outcome_pos b) (A.outcome_hermitian a)
  sum_eq_total := sandwichByOuterSubMeas_sum_outcome A B
  total_le_one := calc
    ∑ a : α, A.outcome a * B.total * A.outcome a
      ≤ ∑ a : α, A.outcome a :=
        Finset.sum_le_sum fun a _ =>
          ((IsSelfAdjoint.conjugate_le_conjugate B.total_le_one
            (A.outcome_hermitian a)).trans_eq (by rw [mul_one])).trans
            (sq_le_self (A.outcome_pos a) (A.outcome_le_one a))
    _ = A.total := A.sum_eq_total
    _ ≤ 1 := A.total_le_one

/-- The postprocessed family `((u,x) ↦ G^x_[g(u)=a])`. -/
noncomputable def evaluatedPointFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) :
    IdxSubMeas (Point params.next) (Fq params) 𝔓 :=
  IdxPolyFamily.evaluatedAtNextPoint family

/-- The evaluated family `G^x_[g(u)=a]` placed on the first factor by `S`. -/
noncomputable def evaluatedPointFamilyLeft (S : SymModel 𝔓 K) (params : Parameters)
    [FieldModel params.q] (family : IdxPolyFamily params 𝔓) :
    IdxSubMeas (Point params.next) (Fq params) (K →L[ℂ] K) :=
  fun u => S.leftPlacedSubMeas (evaluatedPointFamily params family u)

/-- The evaluated family `G^x_[g(u)=a]` placed on the second factor by `S`. -/
noncomputable def evaluatedPointFamilyRight (S : SymModel 𝔓 K) (params : Parameters)
    [FieldModel params.q] (family : IdxPolyFamily params 𝔓) :
    IdxSubMeas (Point params.next) (Fq params) (K →L[ℂ] K) :=
  fun u => S.rightPlacedSubMeas (evaluatedPointFamily params family u)

/-- The first evaluated factor `G^x_[g(u)=a]`. -/
noncomputable def evaluatedSliceFirstFactor (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) :
    IdxSubMeas (EvaluatedSliceQuestion params) (Fq params) 𝔓 :=
  fun q => evaluatedPointFamily params family q.1

/-- The second evaluated factor `G^y_[h(v)=b]`. -/
noncomputable def evaluatedSliceSecondFactor (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) :
    IdxSubMeas (EvaluatedSliceQuestion params) (Fq params) 𝔓 :=
  fun q => evaluatedPointFamily params family q.2

/-- The ordered evaluated-slice product `(G^x_[g(u)=a] G^y_[h(v)=b]) ⊗ I`, placed by
`strategy.state.L`. -/
noncomputable def evaluatedSliceProductLeft (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓) :
    IdxOpFamily (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) (K →L[ℂ] K) :=
  fun q =>
    leftOrderedProductOpFamily strategy.state
      (evaluatedSliceFirstFactor params family q)
      (evaluatedSliceSecondFactor params family q)

/-- The reversed evaluated-slice product `(G^y_[h(v)=b] G^x_[g(u)=a]) ⊗ I`, placed by
`strategy.state.L`. -/
noncomputable def evaluatedSliceProductRight (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓) :
    IdxOpFamily (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) (K →L[ℂ] K) :=
  fun q =>
    OpFamily.leftPlacedOpFamily strategy.state <|
      reversedProductOpFamily
        (evaluatedSliceFirstFactor params family q)
        (evaluatedSliceSecondFactor params family q)

/-- The sandwiched evaluated product `G^x_[g(u)=a] G^y_[h(v)=b] G^x_[g(u)=a]` in the local
algebra. The strategy is not used; it is kept for the vendored signature. -/
noncomputable def evaluatedSliceSandwichRaw (params : Parameters) [FieldModel params.q]
    (_strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓) :
    IdxSubMeas (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) 𝔓 :=
  fun q =>
    sandwichByOuterSubMeas
      (evaluatedSliceFirstFactor params family q)
      (evaluatedSliceSecondFactor params family q)

/-- The sandwiched evaluated product `(G^x_[g(u)=a] G^y_[h(v)=b] G^x_[g(u)=a]) ⊗ I`, placed by
`strategy.state.L`. -/
noncomputable def evaluatedSliceSandwichFirstFactor (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓) :
    IdxSubMeas (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) (K →L[ℂ] K) :=
  fun q =>
    strategy.state.leftPlacedSubMeas <|
      evaluatedSliceSandwichRaw params strategy family q

/-- The first full slice measurement `G^x`. -/
def fullSliceFirstFactor (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) :
    IdxSubMeas (FullSliceQuestion params) (MIPStarRE.LDT.Polynomial params) 𝔓 :=
  fun q => (family.meas q.1).toSubMeas

/-- The second full slice measurement `G^y`. -/
def fullSliceSecondFactor (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) :
    IdxSubMeas (FullSliceQuestion params) (MIPStarRE.LDT.Polynomial params) 𝔓 :=
  fun q => (family.meas q.2).toSubMeas

/-- The ordered full-slice product `(G^x_g G^y_h) ⊗ I`, placed by `strategy.state.L`. -/
noncomputable def fullSliceProductLeft (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓) :
    IdxOpFamily (FullSliceQuestion params) (FullSliceOutcome params) (K →L[ℂ] K) :=
  fun q =>
    leftOrderedProductOpFamily strategy.state
      (fullSliceFirstFactor params family q)
      (fullSliceSecondFactor params family q)

/-- The reversed full-slice product `(G^y_h G^x_g) ⊗ I`, placed by `strategy.state.L`. -/
noncomputable def fullSliceProductRight (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓) :
    IdxOpFamily (FullSliceQuestion params) (FullSliceOutcome params) (K →L[ℂ] K) :=
  fun q =>
    OpFamily.leftPlacedOpFamily strategy.state <|
      reversedProductOpFamily
        (fullSliceFirstFactor params family q)
        (fullSliceSecondFactor params family q)

end MIPRE.LIDT.Co.Commutativity

end
