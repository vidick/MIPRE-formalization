/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/ScalarApproximation/PaperChainBasic/PointSwap.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.ScalarApproximation.Core
public import MIPRE.Background.LIDT.Co.Commutativity.EvaluatedSliceCommutation.Consequences
public import MIPRE.Background.LIDT.Co.CommutativityPoints.BridgeTheorems.DropBridges
public import MIPRE.Background.LIDT.Co.Preliminaries.BipartiteSelfConsistency.Core

@[expose] public section

/-!
# Section 11 commutativity: the point-swap bound for the evaluated-slice paper chain

The right-register point-swap estimate used in the paper-faithful scalar chain for
`lem:comm-data-processed-g`: the counterpart of
`Commutativity/ScalarApproximation/PaperChainBasic/PointSwap.lean` under
`MIPRE/Background/LIDT/MIPStarRE/LDT/` in the port of `planning/c6b-plan.md` (milestone M7,
section "Port conventions").

Both lemmas drop the vendored hypothesis `hnorm : strategy.state.IsNormalized`, a theorem of the
model, so the argument order is `params strategy gamma hcomm C hC` and
`params strategy eps delta gamma hgood C hC`. The family `C` is a family of joint operators
`K →L[ℂ] K`, and `hC` is stated with `star`. The swap of the point product from the right to the
left register is `Preliminaries.qSDDCore_rightTensor_eq_leftTensor_of_permInv`, which applies
the model's `S.ev_L_eq_ev_R` in place of the vendored `strategy.permInvState`.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Commutativity

open MIPStarRE.LDT (Parameters FieldModel avgOver avgOver_congr uniformDistribution
  uniformDistribution_weight_sum_le_one)
open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)
open MIPStarRE.LDT.CommutativityPoints (commutativityPointsError)
open MIPStarRE.LDT.Commutativity (EvaluatedSliceQuestion EvaluatedSliceOutcome)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The right-register point swap, from the point commutativity of `thm:commutativity-points`:
for a family `C` with `∑_{ab} C_{ab} C_{ab}^* ≤ 1` at every question, swapping the order of the
two point measurements placed on the right register moves the averaged expectation by at most
`6 √(γ (m + 1))`. -/
lemma evaluatedSlice_phaseFour_pointSwap_right_bound_of_commutativityPoints
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (gamma : ℝ)
    (hcomm :
      strategy.state.SDDOpRel
        (uniformDistribution (PointPairQuestion params.next))
        (CommutativityPoints.pointMeasurementProductLeft params.next strategy)
        (CommutativityPoints.pointMeasurementProductRight params.next strategy)
        (commutativityPointsError params.next gamma))
    (C : EvaluatedSliceQuestion params → EvaluatedSliceOutcome params → K →L[ℂ] K)
    (hC : ∀ q, ∑ ab : EvaluatedSliceOutcome params, C q ab * star (C q ab) ≤ 1) :
    let 𝒟 := uniformDistribution (EvaluatedSliceQuestion params)
    let inserted : EvaluatedSliceQuestion params → ℝ := fun q =>
      ∑ ab : EvaluatedSliceOutcome params,
        strategy.state.ev
          (C q ab *
            strategy.state.R
              (((evaluatedSlicePointMeas params strategy q.2).outcome ab.2) *
               ((evaluatedSlicePointMeas params strategy q.1).outcome ab.1)))
    let swapped : EvaluatedSliceQuestion params → ℝ := fun q =>
      ∑ ab : EvaluatedSliceOutcome params,
        strategy.state.ev
          (C q ab *
            strategy.state.R
              (((evaluatedSlicePointMeas params strategy q.1).outcome ab.1) *
               ((evaluatedSlicePointMeas params strategy q.2).outcome ab.2)))
    |avgOver 𝒟 inserted - avgOver 𝒟 swapped| ≤
      6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : ℝ)) := by
  intro 𝒟 inserted swapped
  let S := strategy.state
  let M := evaluatedSlicePointMeas params strategy
  let Rrev : EvaluatedSliceQuestion params → EvaluatedSliceOutcome params → K →L[ℂ] K :=
    fun q ab => S.R ((M q.2).outcome ab.2 * (M q.1).outcome ab.1)
  let Rord : EvaluatedSliceQuestion params → EvaluatedSliceOutcome params → K →L[ℂ] K :=
    fun q ab => S.R ((M q.1).outcome ab.1 * (M q.2).outcome ab.2)
  have hAB : avgOver 𝒟 (fun q => S.qSDDCore (Rrev q) (Rord q)) ≤
      commutativityPointsError params.next gamma := by
    refine le_of_eq_of_le (avgOver_congr 𝒟 _ _ fun q => ?_)
      (CommutativityPoints.sddOpRel_symm S.toVecState _ _ _ _ hcomm).squaredDistanceBound
    -- The outcome type is ascribed: left to unification, the check takes over 200000 heartbeats.
    refine (Preliminaries.qSDDCore_rightTensor_eq_leftTensor_of_permInv S
      (fun ab : EvaluatedSliceOutcome params => (M q.2).outcome ab.2 * (M q.1).outcome ab.1)
      (fun ab : EvaluatedSliceOutcome params => (M q.1).outcome ab.1 * (M q.2).outcome ab.2)
      ).trans ?_
    exact Finset.sum_congr rfl fun ab _ => by rcases ab with ⟨a, b⟩; rfl
  have hclose :=
    Preliminaries.closenessOfIP S.toVecState 𝒟
      (uniformDistribution_weight_sum_le_one (EvaluatedSliceQuestion params)) Rrev Rord
      (fun q ab (_ : Unit) => C q ab) (commutativityPointsError params.next gamma) hAB
      (fun q => by simpa only [Fintype.sum_unique] using hC q)
  simp only [Fintype.sum_unique] at hclose
  refine hclose.trans ?_
  rw [commutativityPointsError, mul_assoc, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 32)]
  exact mul_le_mul_of_nonneg_right
    (Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (Real.sqrt_nonneg _)

/-- The right-register point swap for a good strategy: `thm:commutativity-points` supplies the
point commutativity of `evaluatedSlice_phaseFour_pointSwap_right_bound_of_commutativityPoints`. -/
lemma evaluatedSlice_phaseFour_pointSwap_right_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (C : EvaluatedSliceQuestion params → EvaluatedSliceOutcome params → K →L[ℂ] K)
    (hC : ∀ q, ∑ ab : EvaluatedSliceOutcome params, C q ab * star (C q ab) ≤ 1) :
    let 𝒟 := uniformDistribution (EvaluatedSliceQuestion params)
    let inserted : EvaluatedSliceQuestion params → ℝ := fun q =>
      ∑ ab : EvaluatedSliceOutcome params,
        strategy.state.ev
          (C q ab *
            strategy.state.R
              (((evaluatedSlicePointMeas params strategy q.2).outcome ab.2) *
               ((evaluatedSlicePointMeas params strategy q.1).outcome ab.1)))
    let swapped : EvaluatedSliceQuestion params → ℝ := fun q =>
      ∑ ab : EvaluatedSliceOutcome params,
        strategy.state.ev
          (C q ab *
            strategy.state.R
              (((evaluatedSlicePointMeas params strategy q.1).outcome ab.1) *
               ((evaluatedSlicePointMeas params strategy q.2).outcome ab.2)))
    |avgOver 𝒟 inserted - avgOver 𝒟 swapped| ≤
      6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : ℝ)) :=
  evaluatedSlice_phaseFour_pointSwap_right_bound_of_commutativityPoints params strategy gamma
    (CommutativityPoints.commutativityPoints params.next strategy eps delta gamma hgood) C hC

end MIPRE.LIDT.Co.Commutativity

end
