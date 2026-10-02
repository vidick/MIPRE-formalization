/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/Main/Results.lean, to the symmetric model of `planning/c6b-plan.md`; not a
vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.Main.EvaluatedQuestions
public import MIPRE.Background.LIDT.Co.Commutativity.GCommStability.Scalar.Second
public import MIPRE.Background.LIDT.Co.Commutativity.ScalarApproximation.ProcessedG

@[expose] public section

/-!
# Section 11 commutativity: final results

The top-level `thm:com-main` statement, lifting evaluated commutation back to full-slice
commutation via the two-step Schwartz–Zippel marginalization, and
`lem:normalization-condition`: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/Main/Results.lean` in the port of
`planning/c6b-plan.md` (milestone M7, section "Port conventions").

The conclusions are `SDDOpRel`s of joint operator families on the symmetric model
`strategy.state` of a `SymStrat params.next 𝔓 K`; `lem:normalization-condition` is about local
operators of any C*-algebra `𝔓` with its order, with `star` for the vendored `ᴴ`.

The vendored hypothesis `hnorm : strategy.state.IsNormalized` is dropped from
`comMain_of_commutativityPoints` (where it stood between `gamma zeta` and `hcomm`) and from
`comMain` (between `eps delta gamma zeta` and `hgood`), as the port conventions drop
`hψ : ψ.IsNormalized`: none of the lemmas the proofs compose takes it any more. Callers pass
`params strategy gamma zeta hcomm hgamma_nonneg family hcons hself hbound` and
`params strategy eps delta gamma zeta hgood family hcons hself hbound`. The nonnegativity of
`gamma` in `comMain` is `gamma_nonneg_of_isGood`, which the vendored proof inlines.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-points.tex`
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Commutativity

open MIPStarRE.LDT (Parameters FieldModel uniformDistribution)
open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)
open MIPStarRE.LDT.CommutativityPoints (commutativityPointsError)
open MIPStarRE.LDT.Commutativity (EvaluatedSliceQuestion commDataProcessedGError comMainError)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Paper origin: `references/ldt-paper/commutativity-G.tex`
(`\label{thm:com-main}`).

The paper theorem is formulated directly for the family `family.meas`; any
explicit auxiliary family used by the scalar approximation proof is internal to
the proof. -/
theorem comMain_of_commutativityPoints
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (gamma zeta : ℝ)
    (hcomm :
      strategy.state.SDDOpRel
        (uniformDistribution (PointPairQuestion params.next))
        (CommutativityPoints.pointMeasurementProductLeft params.next strategy)
        (CommutativityPoints.pointMeasurementProductRight params.next strategy)
        (commutativityPointsError params.next gamma))
    (hgamma_nonneg : 0 ≤ gamma)
    (family : IdxPolyFamily params 𝔓)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    ComMainConclusion params strategy family gamma zeta := by
  have hEval :=
    commDataProcessedG_of_commutativityPoints
      params strategy gamma zeta hcomm hgamma_nonneg family hcons hself hbound
  have hSpecialized :
      strategy.state.SDDOpRel
        (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedFromFullSliceProductLeft params strategy family)
        (evaluatedFromFullSliceProductRight params strategy family)
        (commDataProcessedGError params gamma zeta) :=
    ⟨(evaluationSpecialization_sddErrorOp_eq params strategy family).trans_le
      hEval.squaredDistanceBound⟩
  have hzeta_nonneg : 0 ≤ zeta :=
    (strategy.state.sddError_nonneg _ _ _).trans
      hself.sliceSelfConsistency.squaredDistanceBound
  exact
    sddOpRel_of_pullback_fullSliceQuestion params strategy.state.toVecState
      (fullSliceProductLeft params strategy family)
      (fullSliceProductRight params strategy family)
      (comMainError params gamma zeta)
      (fullSliceCommutation_of_evaluated_on_evaluated_questions
        params strategy family gamma zeta hgamma_nonneg hzeta_nonneg hself hSpecialized)

/-- Paper origin: `references/ldt-paper/commutativity-G.tex`
(`\label{thm:com-main}`).

The paper theorem is formulated directly for the family `family.meas`; any
explicit auxiliary family used by the scalar approximation proof is internal to
the proof. -/
theorem comMain
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma zeta : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params 𝔓)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    ComMainConclusion params strategy family gamma zeta :=
  comMain_of_commutativityPoints params strategy gamma zeta
    (CommutativityPoints.commutativityPoints params.next strategy eps delta gamma hgood)
    (gamma_nonneg_of_isGood params.next strategy hgood) family hcons hself hbound

/-- `lem:normalization-condition`. -/
lemma normalizationCondition {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA 𝔓)
    (Q : ProjSubMeas OutcomeB 𝔓) :
    NormalizationConditionStatement P Q where
  sandwichedHermitianSquare :=
    Finset.sum_congr rfl fun a _ => by
      simp only [normalizationConditionSandwichedTotalOperator_hermitian]
  sandwichedBoundedByIdentity := (normalizationConditionSquareFamily P Q).total_le_one

end MIPRE.LIDT.Co.Commutativity

end
