/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
MainInductionStep/Theorems/RestrictedProbabilities/Axis.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.MainInductionStep.Theorems.RestrictedProbabilities.Base

@[expose] public section

/-!
# Section 6 — Axis-parallel restricted probability bounds

The axis-parallel part of the restricted-probability bookkeeping for the main induction step:
the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/MainInductionStep/Theorems/RestrictedProbabilities/Axis.lean`
in the port of `planning/c6b-plan.md` (milestone M12, section "Port conventions").

A strategy is a `SymStrat params.next 𝔓 K` (`Co/Test/StrategyCore.lean`), whose state is the
symmetric model `strategy.state : SymModel 𝔓 K`; the vendored `qBipartiteConsDefect
strategy.state A B` is `strategy.state.qBipartiteConsDefect A B` (`Co/Test/Defs.lean`), with the
point answers placed by `S.L` and the line answers by `S.R`, and errors are real numbers (the
vendored `Error := ℝ`). The restricted strategy keeps the state, so every restricted defect is a
defect of `strategy.state`.

The restricted axis-parallel measurement (`restrictAxisParallelMeasurement`, Co
`MainInductionStep/Defs.lean`) is the transport of the ambient one along
`axisLinePolynomialEquiv` up to its total, `1` against the ambient `total`, which equals `1`; so
`restrictedAxisSampleError_eq` is one extensionality step and `SubMeas.postprocess_transport`, as
in the vendored proof. The vendored `avg_congr` steps are written with `avgOver_congr`, and the
`try rfl` steps of the vendored file are gone.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/inductive_step.tex`
- `blueprint/src/chapter/ch10_induction.tex`
-/

namespace MIPRE.LIDT.Co.MainInductionStep

open MIPStarRE.LDT (Parameters FieldModel Point Fq zeroCoord appendPoint embedCoord avgOver
  avgOver_congr avgOver_nonneg avgOver_const_mul avgOver_uniform_comm avgOver_uniform_prod_swap
  uniformDistribution AxisParallelLine AxisLinePolynomial)
open MIPStarRE.LDT.CommutativityPoints (avgOver_uniform_pointNext_decompose)
open MIPStarRE.LDT.MainInductionStep (axisLinePolynomialEquiv sliceTransverseDirectionWeight
  weighted_embedded_average_le_full_average)
open MIPRE.LIDT.Co (SymStrat axisParallelPointAnswerFamily axisParallelLineAnswerFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The axis-parallel defect of the `x`-restricted strategy at the slice sample `(u, i)` is the
ambient defect at the appended point `(u, x)` and the embedded direction `i`. -/
theorem restrictedAxisSampleError_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (x : Fq params)
    (u : Point params)
    (i : Fin params.m) :
    strategy.state.qBipartiteConsDefect
      (RestrictedSymStrat.axisParallelPointAnswerFamily
        (xRestrictedStrategy params strategy x) (u, i))
      (RestrictedSymStrat.axisParallelLineAnswerFamily
        (xRestrictedStrategy params strategy x) (u, i)) =
    strategy.state.qBipartiteConsDefect
      (axisParallelPointAnswerFamily strategy (appendPoint params u x, embedCoord params i))
      (axisParallelLineAnswerFamily strategy (appendPoint params u x, embedCoord params i)) := by
  let ℓ : AxisParallelLine params := { base := u, direction := i }
  have htransport :
      (restrictAxisParallelMeasurement params strategy x ℓ).toSubMeas =
        SubMeas.transport (axisLinePolynomialEquiv params x).symm
          ((strategy.axisParallelMeasurement
            (AxisParallelLine.appendAtHeight params ℓ x)).toSubMeas) :=
    SubMeas.ext (fun _ => rfl)
      (strategy.axisParallelMeasurement (AxisParallelLine.appendAtHeight params ℓ x)).total_eq_one.symm
  have hpost :
      postprocess ((restrictAxisParallelMeasurement params strategy x ℓ).toSubMeas)
          (fun f : AxisLinePolynomial params => f zeroCoord) =
        postprocess
          ((strategy.axisParallelMeasurement
            (AxisParallelLine.appendAtHeight params ℓ x)).toSubMeas)
          (fun f : AxisLinePolynomial params.next => f zeroCoord) := by
    rw [htransport, SubMeas.postprocess_transport]
    rfl
  exact congrArg (strategy.state.qBipartiteConsDefect _) hpost

/-- Per-direction axis-parallel consistency defect of the restricted `x`-slice
strategy at embedded direction `i`, averaged over the slice point space
`Point params`. -/
noncomputable def sliceAxisDirectionError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (x : Fq params)
    (i : Fin params.m) : ℝ :=
  avgOver (uniformDistribution (Point params)) fun u =>
    strategy.state.qBipartiteConsDefect
      (RestrictedSymStrat.axisParallelPointAnswerFamily
        (xRestrictedStrategy params strategy x) (u, i))
      (RestrictedSymStrat.axisParallelLineAnswerFamily
        (xRestrictedStrategy params strategy x) (u, i))

/-- Per-direction axis-parallel consistency defect of the ambient `(m+1)`-dimensional
strategy at direction `i`, averaged over the ambient point space `Point params.next`. -/
noncomputable def axisDirectionError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (i : Fin params.next.m) : ℝ :=
  avgOver (uniformDistribution (Point params.next)) fun u =>
    strategy.state.qBipartiteConsDefect
      (axisParallelPointAnswerFamily strategy (u, i))
      (axisParallelLineAnswerFamily strategy (u, i))

/-- Averaging the restricted per-direction axis-parallel error over the slice height gives the
ambient per-direction error at the embedded direction. -/
theorem sliceAxisDirectionErrorAverage_eq_axisDirectionError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (i : Fin params.m) :
    avgOver (uniformDistribution (Fq params))
      (fun x => sliceAxisDirectionError params strategy x i) =
      axisDirectionError params strategy (embedCoord params i) := by
  let g : Point params.next → ℝ := fun u =>
    strategy.state.qBipartiteConsDefect
      (axisParallelPointAnswerFamily strategy (u, embedCoord params i))
      (axisParallelLineAnswerFamily strategy (u, embedCoord params i))
  refine Eq.trans ?_ (avgOver_uniform_pointNext_decompose params g).symm
  refine avgOver_congr _ _ _ fun x => avgOver_congr _ _ _ fun u => ?_
  exact restrictedAxisSampleError_eq params strategy x u i

/-- The average over slice heights of the restricted axis-parallel failure probability is the
average over embedded directions of the ambient per-direction error. -/
theorem averageRestrictedAxisFailure_eq_embeddedAxisDirections
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) :
    avgOver (uniformDistribution (Fq params))
      (fun x => (xRestrictedStrategy params strategy x).axisParallelFailureProbability) =
    avgOver (uniformDistribution (Fin params.m))
      (fun i => axisDirectionError params strategy (embedCoord params i)) := by
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => (xRestrictedStrategy params strategy x).axisParallelFailureProbability)
      = avgOver (uniformDistribution (Fq params))
          (fun x => avgOver (uniformDistribution (Fin params.m))
            (fun i => sliceAxisDirectionError params strategy x i)) :=
        avgOver_congr _ _ _ fun x =>
          avgOver_uniform_prod_swap (α := Point params) (β := Fin params.m)
            (fun u i => strategy.state.qBipartiteConsDefect
              (RestrictedSymStrat.axisParallelPointAnswerFamily
                (xRestrictedStrategy params strategy x) (u, i))
              (RestrictedSymStrat.axisParallelLineAnswerFamily
                (xRestrictedStrategy params strategy x) (u, i)))
    _ = avgOver (uniformDistribution (Fin params.m))
          (fun i => avgOver (uniformDistribution (Fq params))
            (fun x => sliceAxisDirectionError params strategy x i)) :=
        avgOver_uniform_comm (fun x i => sliceAxisDirectionError params strategy x i)
    _ = avgOver (uniformDistribution (Fin params.m))
          (fun i => axisDirectionError params strategy (embedCoord params i)) :=
        avgOver_congr _ _ _ fun i =>
          sliceAxisDirectionErrorAverage_eq_axisDirectionError params strategy i

/-- The weighted average of the restricted axis-parallel slice errors is bounded
by the ambient axis-parallel test error. -/
theorem weighted_axisParallel_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma) :
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedStrategy params strategy x).axisParallelFailureProbability) ≤ eps := by
  rw [avgOver_const_mul, averageRestrictedAxisFailure_eq_embeddedAxisDirections params strategy]
  refine (weighted_embedded_average_le_full_average params (axisDirectionError params strategy)
    fun i => avgOver_nonneg _ _ fun u => strategy.state.qBipartiteConsDefect_nonneg _ _).trans ?_
  refine le_of_eq_of_le ?_ hgood.axisParallelTest
  exact (avgOver_uniform_prod_swap (α := Point params.next) (β := Fin params.next.m)
    (fun u i => strategy.state.qBipartiteConsDefect
      (axisParallelPointAnswerFamily strategy (u, i))
      (axisParallelLineAnswerFamily strategy (u, i)))).symm

end MIPRE.LIDT.Co.MainInductionStep

end
