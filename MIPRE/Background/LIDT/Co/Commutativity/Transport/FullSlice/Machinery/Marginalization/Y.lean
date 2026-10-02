/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/Transport/FullSlice/Machinery/Marginalization/Y.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.Transport.FullSlice.Machinery.Marginalization.Core

@[expose] public section

/-!
# Full-slice y-marginalization endpoint

The y-side evaluated tensor marginalization block for the `ABAB` full-slice tensor average: the
counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/Transport/FullSlice/Machinery/Marginalization/Y.lean`
in the port of `planning/c6b-plan.md` (milestone M7, section "Port conventions"). It uses the
collision and postprocessing machinery of `Machinery.Marginalization.Core`.

The terms and averages are real expectations `strategy.state.ev …` on the symmetric model of a
strategy `strategy : SymStrat params.next 𝔓 K`, the vendored `leftTensor (ι₂ := ι)` and
`rightTensor (ι₁ := ι)` being `strategy.state.L` and `strategy.state.R`. The vendored
hypothesis `hnorm : strategy.state.IsNormalized` of `fullSliceABAB_tensor_marginalize_y` is a
theorem of the model and is dropped. The reindexing equivalence
`evaluatedSliceQuestionYDataEquiv` is classical and imported from the vendored
`Transport/FullSlice/Averages`, through the mirrored imports.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Commutativity

open MIPStarRE.LDT (Parameters FieldModel Point Fq appendPoint truncatePoint_appendPoint
  pointHeight_appendPoint avgOver avgOver_congr avgOver_add avgOver_nonneg avgOver_uniform_equiv
  avgOver_uniform_prod uniformDistribution)
open MIPStarRE.LDT.Commutativity (EvaluatedSliceQuestion EvaluatedSliceOutcome FullSliceQuestion
  evaluatedSliceQuestionYDataEquiv)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The evaluated `ABA ⊗ B` tensor summand block reindexed as
`((u, (x, y)), v)` and with the outcome sum in y-first order. -/
noncomputable def evaluatedSliceABABtensorYDataTerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (r : (Point params × FullSliceQuestion params) × Point params) : ℝ :=
  let A : SubMeas (Fq params) 𝔓 := evaluateAt params r.1.1 ((family.meas r.1.2.1).toSubMeas)
  let B : SubMeas (Fq params) 𝔓 := evaluateAt params r.2 ((family.meas r.1.2.2).toSubMeas)
  ∑ b : Fq params, ∑ a : Fq params,
    strategy.state.ev
      (strategy.state.L (A.outcome a * B.outcome b * A.outcome a) *
        strategy.state.R (B.outcome b))

/-- The evaluated `ABA ⊗ B` tensor average reindexed as `((u, (x, y)), v)`
and with the outcome sum in y-first order. -/
noncomputable def evaluatedSliceABABtensorYDataAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓) : ℝ :=
  avgOver (uniformDistribution ((Point params × FullSliceQuestion params) × Point params))
    (fun r => evaluatedSliceABABtensorYDataTerm params strategy family r)

/-- Pointwise form of `evaluatedSliceABABtensorAvg_eq_yData`, after expanding the
question reindexing equivalence. -/
lemma evaluatedSliceABABtensorYData_point
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (u : Point params) (x y : Fq params) (v : Point params) :
    (∑ ab : EvaluatedSliceOutcome params,
      strategy.state.ev
        (strategy.state.L
            ((evaluatedSliceFirstFactor params family
                (appendPoint params u x, appendPoint params v y)).outcome ab.1 *
              (evaluatedSliceSecondFactor params family
                (appendPoint params u x, appendPoint params v y)).outcome ab.2 *
              (evaluatedSliceFirstFactor params family
                (appendPoint params u x, appendPoint params v y)).outcome ab.1) *
          strategy.state.R
            ((evaluatedSliceSecondFactor params family
              (appendPoint params u x, appendPoint params v y)).outcome ab.2))) =
      evaluatedSliceABABtensorYDataTerm params strategy family ((u, (x, y)), v) := by
  simp only [evaluatedSliceFirstFactor, evaluatedSliceSecondFactor, evaluatedPointFamily,
    IdxPolyFamily.evaluatedAtNextPoint, truncatePoint_appendPoint, pointHeight_appendPoint]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  rfl

/-- Reindex the evaluated `ABA ⊗ B` tensor average by `((u, (x, y)), v)`
and write the outcome sum in the y-first order used by the generic postprocessing
expansion. -/
lemma evaluatedSliceABABtensorAvg_eq_yData
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓) :
    evaluatedSliceABABtensorAvg params strategy family =
      evaluatedSliceABABtensorYDataAvg params strategy family :=
  (avgOver_uniform_equiv (evaluatedSliceQuestionYDataEquiv params) _).trans
    (avgOver_congr _ _ _ fun r =>
      evaluatedSliceABABtensorYData_point params strategy family r.1.1 r.1.2.1 r.1.2.2 r.2)

/-- Exact y-side postprocessing identity: the fully evaluated `ABA ⊗ B` tensor
average is the x-evaluated/y-full tensor average plus the y-collision residual. -/
lemma evaluatedSliceABABtensor_yEvaluation_eq_xFull_add_collision
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓) :
    evaluatedSliceABABtensorAvg params strategy family =
      xEvaluatedFullSliceABABtensorAvg params strategy family +
        avgOver (uniformDistribution (Point params × FullSliceQuestion params))
          (fun ux => fullSliceABAByCollisionFactored params strategy family ux.1 ux.2) := by
  rw [evaluatedSliceABABtensorAvg_eq_yData, evaluatedSliceABABtensorYDataAvg,
    xEvaluatedFullSliceABABtensorAvg, ← avgOver_add,
    avgOver_uniform_prod (fun ux v => evaluatedSliceABABtensorYDataTerm params strategy family
      (ux, v))]
  refine avgOver_congr _ _ _ fun ux => ?_
  refine (avg_postprocess_sandwichTensor_eq_diag_add_collision strategy.state
    (family.meas ux.2.2).toSubMeas (evaluateAt params ux.1 (family.meas ux.2.1).toSubMeas)
    (fun (v : Point params) (h : MIPStarRE.LDT.Polynomial params) => h v)).trans
    (congrArg (· + _) ?_)
  rw [Fintype.sum_prod_type, Finset.sum_comm]

/-- Y-side tensor marginalization bound for the `ABABtensor` endpoint (the vendored hypothesis
`hnorm : strategy.state.IsNormalized` is a theorem of the model).

This is the Lean-local tensor form of the Schwartz-Zippel step labelled
`eq:numbering-system-diff` after `eq:evaluate-gcom-at-points-part-dos` in the
proof of blueprint theorem `thm:com-main`. -/
lemma fullSliceABAB_tensor_marginalize_y
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓) :
    |xEvaluatedFullSliceABABtensorAvg params strategy family -
        evaluatedSliceABABtensorAvg params strategy family| ≤
      (params.m * params.d : ℝ) / params.q := by
  rw [evaluatedSliceABABtensor_yEvaluation_eq_xFull_add_collision, sub_add_cancel_left, abs_neg,
    abs_of_nonneg (avgOver_nonneg (uniformDistribution (Point params × FullSliceQuestion params))
      _ fun ux => fullSliceABAByCollisionFactored_nonneg params strategy family ux.1 ux.2)]
  exact fullSliceABAB_tensor_marginalize_y_collision_bound params strategy family

end MIPRE.LIDT.Co.Commutativity

end
