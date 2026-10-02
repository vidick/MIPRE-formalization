/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Test/
StrategyPolynomialFamilies.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored
file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Test.StrategyCore

@[expose] public section

/-!
# Polynomial-family interfaces for the low individual degree test

Packaged slice-indexed polynomial families `x ↦ G^x` with their witness operators and
domination targets, and the predicates (completeness, consistency with points, strong
self-consistency, boundedness) that the induction step asks of them: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Test/StrategyPolynomialFamilies.lean` in the port of
`planning/c6b-plan.md` (milestone M4, section "Port conventions").

A family `IdxPolyFamily params 𝔓` lives in the local C*-algebra `𝔓` (the vendored `Op ι`); the
predicates that read a state take the symmetric model `S : SymModel 𝔓 K` in place of the vendored
`ψ : QuantumState (ι × ι)`, or a symmetric strategy `SymStrat params.next 𝔓 K`, and place the
local operators on the two factors by `S.L` and `S.R` (the vendored `leftTensor (ι₂ := ι)`,
`rightTensor (ι₁ := ι)`).

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-G.tex`
- `references/ldt-paper/ld-pasting.tex`
- `references/ldt-paper/inductive_step.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co

open MIPStarRE.LDT (Parameters FieldModel Point Fq appendPoint truncatePoint pointHeight avgOver
  uniformDistribution uniformDistribution_weight_sum_le_one uniformDistribution_weight_sum_eq_one)

/-! ### Polynomial-family interfaces -/

/-- A packaged family `x ↦ G^x` together with its witness operators and domination targets.

The `witness` and `dominationTarget` fields store the per-slice positive operator
`Z^x` and per-slice, per-polynomial operator `E_u A^{u,x}_{g(u)}` appearing in
the paper's boundedness hypothesis (`references/ldt-paper/commutativity-G.tex`,
item `data-processed-boundedness`). We store these operators explicitly rather
than hiding them behind ambient defaults, so each constructor must choose an
honest witness/target pair.

Callers without access to an ambient strategy can use `ofSliceMeas`, which takes
`Z^x := ∑_g G^x_g` and `dominationTarget x g := G^x_g`. Callers with access to a
symmetric strategy should prefer the constructor `ofSymStrat`,
which derives both fields from the strategy itself. -/
structure IdxPolyFamily (params : Parameters) [FieldModel params.q]
    (𝔓 : Type*) [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓] where
  /-- The slice family `x ↦ G^x` of projective submeasurements. -/
  meas : IdxProjSubMeas (Fq params) (MIPStarRE.LDT.Polynomial params) 𝔓
  /-- The per-slice witness operator `Z^x`. -/
  witness : Fq params → 𝔓
  /-- The per-slice, per-polynomial domination target. -/
  dominationTarget : Fq params → MIPStarRE.LDT.Polynomial params → 𝔓

-- NOTE: no global `Inhabited` instance for `IdxPolyFamily`; without an actual
-- slice family, any default would be a degenerate zero-family placeholder.

namespace IdxPolyFamily

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Honest local constructor when only the slice family `x ↦ G^x` is available.

This uses the slice total `∑_g G^x_g` as the witness operator and the concrete
outcome `G^x_g` as the domination target. -/
def ofSliceMeas {params : Parameters} [FieldModel params.q]
    (meas : IdxProjSubMeas (Fq params) (MIPStarRE.LDT.Polynomial params) 𝔓) :
    IdxPolyFamily params 𝔓 where
  meas := meas
  witness := fun x => (meas x).toSubMeas.total
  dominationTarget := fun x g => (meas x).toSubMeas.outcome g

/-- The slice family of `ofSliceMeas meas` is `meas`. -/
@[simp] lemma ofSliceMeas_meas {params : Parameters} [FieldModel params.q]
    (meas : IdxProjSubMeas (Fq params) (MIPStarRE.LDT.Polynomial params) 𝔓) :
    (ofSliceMeas meas).meas = meas := rfl

/-- The witness of `ofSliceMeas meas` is the slice total. -/
@[simp] lemma ofSliceMeas_witness {params : Parameters} [FieldModel params.q]
    (meas : IdxProjSubMeas (Fq params) (MIPStarRE.LDT.Polynomial params) 𝔓)
    (x : Fq params) :
    (ofSliceMeas meas).witness x = (meas x).toSubMeas.total := rfl

/-- The domination target of `ofSliceMeas meas` is the slice outcome. -/
@[simp] lemma ofSliceMeas_dominationTarget {params : Parameters} [FieldModel params.q]
    (meas : IdxProjSubMeas (Fq params) (MIPStarRE.LDT.Polynomial params) 𝔓)
    (x : Fq params) (g : MIPStarRE.LDT.Polynomial params) :
    (ofSliceMeas meas).dominationTarget x g = (meas x).toSubMeas.outcome g := rfl

/-- The averaged submeasurement `G = E_x G^x`: average the slice
measurements over the uniform distribution on slice heights `x ∈ F_q`. -/
noncomputable def averagedSubMeas {params : Parameters} [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) :
    SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓 :=
  averageIdxSubMeas (uniformDistribution (Fq params))
    (fun x => (family.meas x).toSubMeas)
    (uniformDistribution_weight_sum_le_one (Fq params))

/-- Evaluate the slice family at a point `(u, x)` in `F_q^{m+1}`. -/
noncomputable def evaluatedAtNextPoint {params : Parameters} [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) :
    IdxSubMeas (Point params.next) (Fq params) 𝔓 :=
  fun u =>
    evaluateAt params (truncatePoint params u)
      ((family.meas (pointHeight params u)).toSubMeas)

/-- Averaged point operator `E_u A^u_{h(u)}` appearing in source-style
boundedness assumptions. -/
noncomputable def averagedPointEvaluationOperator {params : Parameters} [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K) (h : MIPStarRE.LDT.Polynomial params) : 𝔓 :=
  averageOperatorOverDistribution (uniformDistribution (Point params))
    (fun u => (strategy.pointMeasurement u).toSubMeas.outcome (h u))

/-- Slice-wise averaged point operator `E_u A^{u,x}_{g(u)}` from the paper's
boundedness hypothesis. -/
noncomputable def averagedSlicePointEvaluationOperator {params : Parameters}
    [FieldModel params.q] (strategy : SymStrat params.next 𝔓 K)
    (x : Fq params) (g : MIPStarRE.LDT.Polynomial params) : 𝔓 :=
  averageOperatorOverDistribution (uniformDistribution (Point params))
    (fun u => (strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome (g u))

/-- Slice-wise averaged total operator `E_u \sum_a A^{u,x}_a`.

For a genuine symmetric strategy this simplifies to `1`, but keeping the
strategy-shaped formula explicit records where the witness comes from. -/
noncomputable def averagedSliceTotalOperator {params : Parameters} [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (x : Fq params) : 𝔓 :=
  averageOperatorOverDistribution (uniformDistribution (Point params))
    (fun u => (strategy.pointMeasurement (appendPoint params u x)).toSubMeas.total)

/-- The slice-wise averaged total operator of a symmetric strategy is `1`. -/
@[simp] theorem averagedSliceTotalOperator_eq_one {params : Parameters} [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (x : Fq params) :
    averagedSliceTotalOperator strategy x = 1 := by
  unfold averagedSliceTotalOperator averageOperatorOverDistribution
  simp only [Measurement.total_eq_one]
  rw [← Finset.sum_smul, uniformDistribution_weight_sum_eq_one (Point params), one_smul]

/-- Paper-facing constructor: bundle a slice submeasurement with a symmetric
strategy so that both the domination target and the witness are derived from the
strategy itself.

Concretely, `dominationTarget x g` is the averaged slice-point evaluation
operator `E_u A^{u,x}_{g(u)}` from `references/ldt-paper/commutativity-G.tex`,
and `witness x` is the corresponding averaged slice-total operator
`E_u \sum_a A^{u,x}_a`. Since point measurements are genuine measurements, this
witness simplifies to `1`, but its stored definition keeps the provenance
explicit. -/
noncomputable def ofSymStrat {params : Parameters} [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (meas : IdxProjSubMeas (Fq params) (MIPStarRE.LDT.Polynomial params) 𝔓) :
    IdxPolyFamily params 𝔓 where
  meas := meas
  witness := averagedSliceTotalOperator strategy
  dominationTarget := fun x g => averagedSlicePointEvaluationOperator strategy x g

/-- The slice family of `ofSymStrat strategy meas` is `meas`. -/
@[simp] lemma ofSymStrat_meas {params : Parameters} [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (meas : IdxProjSubMeas (Fq params) (MIPStarRE.LDT.Polynomial params) 𝔓) :
    (ofSymStrat strategy meas).meas = meas := rfl

/-- The witness of `ofSymStrat strategy meas` is the averaged slice-total operator. -/
theorem ofSymStrat_witness_eq_averagedSliceTotalOperator {params : Parameters}
    [FieldModel params.q] (strategy : SymStrat params.next 𝔓 K)
    (meas : IdxProjSubMeas (Fq params) (MIPStarRE.LDT.Polynomial params) 𝔓)
    (x : Fq params) :
    (ofSymStrat strategy meas).witness x = averagedSliceTotalOperator strategy x := rfl

/-- The witness of `ofSymStrat strategy meas` is `1`. -/
@[simp] lemma ofSymStrat_witness {params : Parameters} [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (meas : IdxProjSubMeas (Fq params) (MIPStarRE.LDT.Polynomial params) 𝔓)
    (x : Fq params) :
    (ofSymStrat strategy meas).witness x = 1 :=
  averagedSliceTotalOperator_eq_one strategy x

/-- The domination target of `ofSymStrat strategy meas` is the averaged slice-point
evaluation operator. -/
@[simp] lemma ofSymStrat_dominationTarget {params : Parameters} [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (meas : IdxProjSubMeas (Fq params) (MIPStarRE.LDT.Polynomial params) 𝔓)
    (x : Fq params) (g : MIPStarRE.LDT.Polynomial params) :
    (ofSymStrat strategy meas).dominationTarget x g =
      averagedSlicePointEvaluationOperator strategy x g := rfl

/-- Completeness of a family: its averaged submeasurement, placed on the first factor, has
mass at least `1 - kappa`. -/
structure Complete {params : Parameters} [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    (S : SymModel 𝔓 K) (kappa : ℝ) : Prop where
  /-- The averaged submeasurement `E_x G^x` has mass at least `1 - kappa`. -/
  averageCompleteness :
    S.CompletenessAtLeast (family.averagedSubMeas.liftLeft S) (1 - kappa)

/-- Consistency of a family with the point measurements of a strategy on `F_q^{m+1}`. -/
structure ConsistentWithPoints {params : Parameters} [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    (strategy : SymStrat params.next 𝔓 K) (zeta : ℝ) : Prop where
  /-- The point measurements and the evaluated family are `zeta`-consistent. -/
  pointConsistency :
    strategy.state.ConsRel (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      family.evaluatedAtNextPoint
      zeta

/-- A family point-consistency witness forces the displayed point-consistency
error parameter `ζ` to be nonnegative. -/
theorem zeta_nonneg_of_consistentWithPoints {params : Parameters} [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    {zeta : ℝ}
    (hcons : family.ConsistentWithPoints strategy zeta) :
    0 ≤ zeta :=
  (strategy.state.bipartiteConsError_nonneg
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      family.evaluatedAtNextPoint).trans
    hcons.pointConsistency.offDiagonalBound

/-- Strong self-consistency of a family: its left and right placements are `zeta`-close in
state-dependent distance, on average over the slices. -/
structure StronglySelfConsistent {params : Parameters} [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    (S : SymModel 𝔓 K) (zeta : ℝ) : Prop where
  /-- The averaged squared distance of `G^x ⊗ I` and `I ⊗ G^x` is at most `zeta`. -/
  sliceSelfConsistency :
    S.SDDRel (uniformDistribution (Fq params))
      (IdxSubMeas.liftLeft S (IdxProjSubMeas.toIdxSubMeas family.meas))
      (IdxSubMeas.liftRight S (IdxProjSubMeas.toIdxSubMeas family.meas))
      zeta

/-- Paper-faithful boundedness input for slice-indexed polynomial families.

This structure encodes the boundedness item in
`references/ldt-paper/commutativity-G.tex` and `references/ldt-paper/ld-pasting.tex`.
It consists of positive witnesses `Z^x`, the averaged residual bound
`E_x ⟨Ψ| (I - G^x) ⊗ Z^x |Ψ⟩ ≤ zeta`, and the domination condition
`Z^x ≥ E_u A^{u,x}_{g(u)}`.

The domination condition is stated directly against the averaged point operator
from the strategy.  It is not mediated through `family.dominationTarget`, so this
public input does not contain an additional identification bridge. -/
structure SliceBoundednessInput {params : Parameters} [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (zeta : ℝ) : Prop where
  /-- Positivity of the slice witnesses `Z^x`. -/
  sliceOpPSD : ∀ x, 0 ≤ family.witness x
  /-- Averaged residual bound `E_x ⟨Ψ| (I - G^x) ⊗ Z^x |Ψ⟩ ≤ zeta`. -/
  sliceBoundedness :
    avgOver (uniformDistribution (Fq params))
      (fun x =>
        strategy.state.ev
          (strategy.state.L (1 - (family.meas x).toSubMeas.total) *
            strategy.state.R (family.witness x))) ≤ zeta
  /-- Paper domination condition `E_u A^{u,x}_{g(u)} ≤ Z^x`. -/
  sliceDominatesAveragedPoint :
    ∀ x : Fq params, ∀ g : MIPStarRE.LDT.Polynomial params,
      averagedSlicePointEvaluationOperator strategy x g ≤ family.witness x

namespace SliceBoundednessInput

/-- The boundedness residual obtained from a concrete slice family `G`.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551`
(`\label{thm:self-improvement-in-induction-section}`), especially the boundedness
field of the slice-wise self-improvement output.

This is the induction-oriented `Z^x ⊗ (I - G^x)` term after replacing the
abstract slice family by the concrete `G`, written in the paper's
`(I - G^x) ⊗ Z^x` orientation. -/
noncomputable def storedResidual {params : Parameters} [FieldModel params.q]
    {strategy : SymStrat params.next 𝔓 K}
    {family : IdxPolyFamily params 𝔓} {zeta : ℝ}
    (_hbound : SliceBoundednessInput strategy family zeta)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (x : Fq params) : ℝ :=
  strategy.state.ev
    (strategy.state.L (1 - (G x).total) * strategy.state.R (family.witness x))

/-- Stored residual half of the boundedness hypothesis.

This is exactly the paper's `(I-G^x) ⊗ Z^x` residual bound from
`references/ldt-paper/commutativity-G.tex`. -/
theorem storedBoundedResidualBound {params : Parameters} [FieldModel params.q]
    {strategy : SymStrat params.next 𝔓 K}
    {family : IdxPolyFamily params 𝔓} {zeta : ℝ}
    (hbound : SliceBoundednessInput strategy family zeta)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hG : ∀ x, G x = (family.meas x).toSubMeas) :
    avgOver (uniformDistribution (Fq params))
      (fun x => hbound.storedResidual G x) ≤ zeta := by
  simpa only [storedResidual, hG] using hbound.sliceBoundedness

/-- Paper-faithful domination half of the boundedness hypothesis.

This is the line `Z^x ≥ E_u A^{u,x}_{g(u)}` from
`references/ldt-paper/commutativity-G.tex`. -/
theorem averagedPoint_le_witness {params : Parameters} [FieldModel params.q]
    {strategy : SymStrat params.next 𝔓 K}
    {family : IdxPolyFamily params 𝔓} {zeta : ℝ}
    (hbound : SliceBoundednessInput strategy family zeta) :
    ∀ x : Fq params, ∀ g : MIPStarRE.LDT.Polynomial params,
      averagedSlicePointEvaluationOperator strategy x g ≤ family.witness x :=
  hbound.sliceDominatesAveragedPoint

end SliceBoundednessInput

end IdxPolyFamily

end MIPRE.LIDT.Co

end
