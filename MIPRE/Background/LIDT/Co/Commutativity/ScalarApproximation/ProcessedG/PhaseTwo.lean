/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/ScalarApproximation/ProcessedG/PhaseTwo.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.ScalarApproximation.Core
public import MIPRE.Background.LIDT.Co.Commutativity.ScalarApproximation.PaperChainBasic.Normalization
public import MIPRE.Background.LIDT.Co.Commutativity.ScalarApproximation.PaperChainBasic.PointSwap
public import MIPRE.Background.LIDT.Co.Commutativity.ScalarApproximation.PaperChainBasic.Reindexing
public import MIPRE.Background.LIDT.Co.Commutativity.EvaluatedSliceBounds.PhaseOneThree
public import MIPRE.Background.LIDT.Co.Commutativity.GCommStability.Scalar.First

@[expose] public section

/-!
# Phase 2 stability defect infrastructure

Internal helper definitions and lemmas for the Phase 2 scalar bridge in `ProcessedG`: the
counterpart of `Commutativity/ScalarApproximation/ProcessedG/PhaseTwo.lean` under
`MIPRE/Background/LIDT/MIPStarRE/LDT/` in the port of `planning/c6b-plan.md` (milestone M7,
section "Port conventions"). These definitions extract and bound the one-dimensional stability
defect controlled by `gCommStability_scalar` (the paper's `clm:g-comm-stability`), reindex the
question-level defect into the stability defect via finite marginalization, and perform the
subtraction algebra that rewrites the phase-2 insertion/removal difference as the negative
defect.

The defects are real expectations `strategy.state.ev (strategy.state.L … * strategy.state.R …)`
on the symmetric model of the strategy, with the vendored arguments unchanged.
`avgOver_avgOver_phaseTwo_linear` takes the symmetric model `S` where the vendored lemma takes
the state `ψ`, in the same position, with `F`, `P` and `R` in the local algebra `𝔓`.
`postprocess_sandwichByOuter_prod_snd_outcome` is state-free and holds in `𝔓`.

The vendored hypothesis `hnorm : strategy.state.IsNormalized` of
`evaluatedSlice_phaseTwo_stability_defect_bound` is dropped, as the port conventions drop
`hψ : ψ.IsNormalized`: the ported `gCommStability_scalar` takes none. Callers omit that argument,
which stood between `zeta` and `family`.

The proofs are shorter than the vendored ones. The pointwise subtraction of
`evaluatedSlice_phaseTwo_term_diff` is `mul_sub`, the keystone's `leftTensor_mul_leftTensor`,
`leftTensor_sub` and `ev_sub`, and `ring` on the scalars, in place of the Kronecker calc with
`Matrix.smul_kronecker`. `avgOver_avgOver_phaseTwo_linear` pulls the two averages through the
placements with `ev_opTensor_averageOperatorOverDistribution_left`/`_right`. The fiber collapse is
`Finset.sum_fiberwise` after `ev_leftTensor_mul_middle_finset_sum`, and the question average is
split by `avgOver_uniform_prod_swap` directly, without the vendored `Equiv.prodComm` reindex.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Commutativity

open MIPStarRE.LDT (Parameters FieldModel Point Fq appendPoint pointHeight Distribution avgOver
  avgOver_congr avgOver_sub avgOver_sum avgOver_uniform_prod_swap uniformDistribution)
open MIPStarRE.LDT.Commutativity (EvaluatedSliceQuestion)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The scalar defect controlled by `gCommStability_scalar` after averaging out
all evaluated-slice variables except the second slice height `y`.

This is the paper's boundedness witness term for `clm:g-comm-stability`: for a
fixed `y`, `gCommStabilityR params family y` averages the left-register sandwich
`G^{u,x}_a G^y_g G^{u,x}_a`, while
`IdxPolyFamily.averagedSlicePointEvaluationOperator strategy y g` averages the
right-register point answer `A^{v,y}_{g(v)}` over the tail point `v`. -/
noncomputable def evaluatedSlicePhaseTwoStabilityDefect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (y : Fq params) : ℝ :=
  ∑ g : MIPStarRE.LDT.Polynomial params,
    strategy.state.ev
      (strategy.state.L ((gCommStabilityR params family y).outcome g * (1 - (G y).total)) *
        strategy.state.R (IdxPolyFamily.averagedSlicePointEvaluationOperator strategy y g))

/-- Direct `√ζ` control of the phase-2 stability defect.

The remaining bridge from the explicit evaluated-slice difference to this
one-dimensional defect is pure finite reindexing and averaging: expand
`totalSandwichFamily`, decompose the sampled second point as `(v,y)`, collect the
postprocessing fiber `∑_b ∑_{g : g(v)=b}` into `∑_g`, and average the first
sampled point into `gCommStabilityR`. The vendored lemma asks for a normalized state. -/
lemma evaluatedSlice_phaseTwo_stability_defect_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (zeta : ℝ)
    (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    |avgOver (uniformDistribution (Fq params))
      (evaluatedSlicePhaseTwoStabilityDefect params strategy family G)| ≤ Real.sqrt zeta :=
  gCommStability_scalar params strategy zeta family G hG hbound

/-- The still-unmarginalized phase-2 defect at a sampled evaluated-slice question.

This is the exact question-level term obtained after expanding
`totalSandwichFamily` and using
`S * G^y.total - S = -S * (1 - G^y.total)` for the left-register sandwich `S`.
The remaining reindexing residual averages this term to
`evaluatedSlicePhaseTwoStabilityDefect`. -/
noncomputable def evaluatedSlicePhaseTwoQuestionDefect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (q : EvaluatedSliceQuestion params) : ℝ :=
  ∑ b : Fq params, ∑ a : Fq params,
    strategy.state.ev
      (strategy.state.L
          ((((evaluatedSliceFirstFactor params family q).outcome a) *
            ((evaluatedSliceSecondFactor params family q).outcome b) *
            ((evaluatedSliceFirstFactor params family q).outcome a)) *
            (1 - (G (pointHeight params q.2)).total)) *
        strategy.state.R ((evaluatedSlicePointMeas params strategy q.2).outcome b))

/-- Postprocessing a sandwiched product by its second coordinate sums over the
outer outcome.

For the sandwiched submeasurement with outcomes `(a, b)` and effect
`A_a B_b A_a`, the `Prod.snd` postprocessing has outcome `b` equal to
`∑ a, A_a B_b A_a`.  This is the finite-fiber identity used to recognize the
`gCommStabilityR` averaged sandwich. -/
lemma postprocess_sandwichByOuter_prod_snd_outcome
    {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α 𝔓) (B : SubMeas β 𝔓) (b : β) :
    (postprocess (sandwichByOuterSubMeas A B) Prod.snd).outcome b =
      ∑ a : α, A.outcome a * B.outcome b * A.outcome a := by
  classical
  rw [SubMeas.postprocess_outcome, Finset.sum_filter, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun a _ => by simp [sandwichByOuterSubMeas]

/-- Pull two finite averages into a bipartite expectation with averaged operators.

For a fixed polynomial outcome `g`, the left register is averaged over `𝒟Q`
while the right register is averaged over `𝒟V`.  The identity rewrites the
nested scalar average of
`S.ev (S.L (F q g a * R) * S.R (P g v))` into the expectation of
`S.L ((E_q ∑_a F q g a) * R) * S.R (E_v P g v)`, preserving the
outer sum over `g`. -/
lemma avgOver_avgOver_phaseTwo_linear
    {Q V Γ Aidx : Type*} [Fintype Γ] [Fintype Aidx]
    (𝒟Q : Distribution Q) (𝒟V : Distribution V)
    (S : SymModel 𝔓 K)
    (F : Q → Γ → Aidx → 𝔓)
    (P : Γ → V → 𝔓)
    (R : 𝔓) :
    avgOver 𝒟V (fun v =>
        avgOver 𝒟Q (fun q =>
          ∑ g : Γ, ∑ a : Aidx, S.ev (S.L (F q g a * R) * S.R (P g v)))) =
      ∑ g : Γ,
        S.ev
          (S.L ((averageOperatorOverDistribution 𝒟Q (fun q => ∑ a : Aidx, F q g a)) * R) *
            S.R (averageOperatorOverDistribution 𝒟V (fun v => P g v))) := by
  rw [avgOver_congr 𝒟V _ _ fun v => avgOver_sum 𝒟Q fun q g =>
    ∑ a : Aidx, S.ev (S.L (F q g a * R) * S.R (P g v)), avgOver_sum]
  refine Fintype.sum_congr _ _ fun g => ?_
  have hR : averageOperatorOverDistribution 𝒟Q (fun q => ∑ a : Aidx, F q g a) * R =
      averageOperatorOverDistribution 𝒟Q (fun q => ∑ a : Aidx, F q g a * R) := by
    simp only [averageOperatorOverDistribution, Finset.sum_mul, smul_mul_assoc]
  rw [hR]
  refine (avgOver_congr _ _ _ fun v => (avgOver_congr _ _ _ fun q => ?_).trans
    (S.ev_opTensor_averageOperatorOverDistribution_left 𝒟Q _ _).symm).trans
    (S.ev_opTensor_averageOperatorOverDistribution_right 𝒟V _ _).symm
  rw [SymModel.opTensor, ← S.leftTensor_finset_sum, Finset.sum_mul, S.ev_finset_sum]

/-- Reindex the pointwise phase-2 question defect by polynomial outcomes.

When the sampled second point is `appendPoint v y`, the postprocessed slice
outcome `(evaluatedSliceSecondFactor ...).outcome b` is the sum of
`G^y_g` over the fiber `g v = b`.  Expanding this fiber inside the sandwiched
left-register expression and summing over `b` collapses the defect to a
polynomial-indexed sum whose right-register outcome is `A^{v,y}_{g(v)}`. -/
lemma evaluatedSlicePhaseTwoQuestionDefect_append_eq_sum_poly
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (q1 : Point params.next) (v : Point params) (y : Fq params) :
    evaluatedSlicePhaseTwoQuestionDefect params strategy family G
        (q1, appendPoint params v y) =
      ∑ g : MIPStarRE.LDT.Polynomial params, ∑ a : Fq params,
        strategy.state.ev
          (strategy.state.L
              ((((evaluatedPointFamily params family q1).outcome a) *
                ((family.meas y).toSubMeas.outcome g) *
                ((evaluatedPointFamily params family q1).outcome a)) *
                (1 - (G y).total)) *
            strategy.state.R
              ((strategy.pointMeasurement (appendPoint params v y)).outcome (g v))) := by
  let E : Fq params → 𝔓 := fun a => (evaluatedPointFamily params family q1).outcome a
  let P : Fq params → 𝔓 := fun b =>
    (strategy.pointMeasurement (appendPoint params v y)).outcome b
  unfold evaluatedSlicePhaseTwoQuestionDefect
  simp only [evaluatedSliceFirstFactor, evaluatedSliceSecondFactor,
    MIPStarRE.LDT.pointHeight_appendPoint,
    evaluatedPointFamily_appendPoint_outcome params family _ (fun _ => rfl) y v]
  refine (Finset.sum_congr rfl fun b _ => ?_).trans
    (Finset.sum_fiberwise Finset.univ (fun g : MIPStarRE.LDT.Polynomial params => g v)
      fun g => ∑ a : Fq params, strategy.state.ev
        (strategy.state.L ((E a * (family.meas y).toSubMeas.outcome g * E a) * (1 - (G y).total)) *
          strategy.state.R (P (g v))))
  refine (Finset.sum_congr rfl fun a _ =>
    ev_leftTensor_mul_middle_finset_sum _ strategy.state (E a) (E a) _ (P b) _).trans ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun g hg => by rw [(Finset.mem_filter.mp hg).2]

/-- Pointwise algebra for the phase-2 subtraction.

After expanding `totalSandwichFamily`, the inserted summand has the extra factor
`G^y.total` on the left register.  This lemma rewrites the difference with the
removed summand as the negative defect, using the noncommutative identity
`S * T - S = -(S * (1 - T))`. -/
lemma evaluatedSlice_phaseTwo_term_diff
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (q : EvaluatedSliceQuestion params)
    (a b : Fq params) :
    strategy.state.ev
        (strategy.state.L
            (((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b) *
              ((evaluatedSliceFirstFactor params family q).outcome a)) *
          ((Preliminaries.totalSandwichFamily strategy.state
            (evaluatedPointFamily params family)
            (evaluatedSlicePointMeas params strategy) q.2).outcome b)) -
      strategy.state.ev
        (strategy.state.L
            (((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b) *
              ((evaluatedSliceFirstFactor params family q).outcome a)) *
          strategy.state.R ((evaluatedSlicePointMeas params strategy q.2).outcome b)) =
    - strategy.state.ev
        (strategy.state.L
            ((((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b) *
              ((evaluatedSliceFirstFactor params family q).outcome a)) *
              (1 - (G (pointHeight params q.2)).total)) *
          strategy.state.R ((evaluatedSlicePointMeas params strategy q.2).outcome b)) := by
  have htotal : (evaluatedPointFamily params family q.2).total =
      (G (pointHeight params q.2)).total :=
    evaluatedPointFamily_total_eq_G_total params family G hG q.2
  change strategy.state.ev (strategy.state.L _ *
      (strategy.state.L (evaluatedPointFamily params family q.2).total *
        strategy.state.R _)) - _ = _
  rw [htotal, ← mul_assoc, strategy.state.leftTensor_mul_leftTensor, mul_sub, mul_one,
    ← strategy.state.leftTensor_sub, sub_mul, strategy.state.ev_sub]
  ring

/-- Average the pointwise phase-2 algebra over evaluated-slice questions.

This proves the advertised sign rewrite
`avgOver 𝒟 phase1Inserted - avgOver 𝒟 phase2Removed = -avgOver 𝒟 questionDefect`.
It leaves only the finite marginalization from the question-level defect to the
one-dimensional `evaluatedSlicePhaseTwoStabilityDefect`. -/
lemma evaluatedSlice_phaseTwo_avg_diff_eq_neg_questionDefect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hG : ∀ x, G x = (family.meas x).toSubMeas) :
    let 𝒟 := uniformDistribution (EvaluatedSliceQuestion params)
    let inserted : EvaluatedSliceQuestion params → ℝ := fun q =>
      ∑ b : Fq params, ∑ a : Fq params,
        strategy.state.ev
          (strategy.state.L
              (((evaluatedSliceFirstFactor params family q).outcome a) *
                ((evaluatedSliceSecondFactor params family q).outcome b) *
                ((evaluatedSliceFirstFactor params family q).outcome a)) *
            ((Preliminaries.totalSandwichFamily strategy.state
              (evaluatedPointFamily params family)
              (evaluatedSlicePointMeas params strategy) q.2).outcome b))
    let removed : EvaluatedSliceQuestion params → ℝ := fun q =>
      ∑ b : Fq params, ∑ a : Fq params,
        strategy.state.ev
          (strategy.state.L
              (((evaluatedSliceFirstFactor params family q).outcome a) *
                ((evaluatedSliceSecondFactor params family q).outcome b) *
                ((evaluatedSliceFirstFactor params family q).outcome a)) *
            strategy.state.R ((evaluatedSlicePointMeas params strategy q.2).outcome b))
    avgOver 𝒟 inserted - avgOver 𝒟 removed =
      -avgOver 𝒟 (evaluatedSlicePhaseTwoQuestionDefect params strategy family G) := by
  intro 𝒟 inserted removed
  rw [← avgOver_sub]
  calc avgOver 𝒟 (fun q => inserted q - removed q)
      = avgOver 𝒟
          (fun q => -evaluatedSlicePhaseTwoQuestionDefect params strategy family G q) :=
        avgOver_congr 𝒟 _ _ fun q => by
          simp only [inserted, removed, evaluatedSlicePhaseTwoQuestionDefect,
            ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ =>
            evaluatedSlice_phaseTwo_term_diff params strategy family G hG q a b
    _ = -avgOver 𝒟 (evaluatedSlicePhaseTwoQuestionDefect params strategy family G) := by
        simp only [avgOver, mul_neg, Finset.sum_neg_distrib]

/-- Exact finite reindexing identity for the phase-2 scalar bridge.

Paper origin: `references/ldt-paper/commutativity-G.tex:60-83` (upstream), the finite
averaging and reindexing step leading to the scalar `eq:add-an-a` bridge.

This statement contains no analytic estimate.  It says that the question-level
phase-2 defect averages to the one-dimensional scalar defect bounded by
`gCommStability_scalar`.  The proof is only finite marginalization and fiber
bookkeeping: decompose the second sampled point as `(v,y)`, collapse the
postprocessing fibers, and average the first sampled point into
`gCommStabilityR`. -/
lemma evaluatedSlice_phaseTwo_questionDefect_avg_eq_stabilityDefect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
  avgOver (uniformDistribution (EvaluatedSliceQuestion params))
      (evaluatedSlicePhaseTwoQuestionDefect params strategy family G) =
    avgOver (uniformDistribution (Fq params))
      (evaluatedSlicePhaseTwoStabilityDefect params strategy family G) := by
  let defect := evaluatedSlicePhaseTwoQuestionDefect params strategy family G
  have hbody : ∀ y : Fq params,
      avgOver (uniformDistribution (Point params))
          (fun v => avgOver (uniformDistribution (Point params.next))
            (fun q1 => defect (q1, appendPoint params v y))) =
        evaluatedSlicePhaseTwoStabilityDefect params strategy family G y := by
    intro y
    let Ffun : Point params.next → MIPStarRE.LDT.Polynomial params → Fq params → 𝔓 :=
      fun q1 g a =>
        (evaluatedPointFamily params family q1).outcome a *
          ((family.meas y).toSubMeas.outcome g) *
          (evaluatedPointFamily params family q1).outcome a
    let Pfun : MIPStarRE.LDT.Polynomial params → Point params → 𝔓 :=
      fun g v => (strategy.pointMeasurement (appendPoint params v y)).outcome (g v)
    have hFavg : ∀ g : MIPStarRE.LDT.Polynomial params,
        averageOperatorOverDistribution (uniformDistribution (Point params.next))
            (fun q1 => ∑ a : Fq params, Ffun q1 g a) =
          (gCommStabilityR params family y).outcome g := fun g =>
      averageOperatorOverDistribution_congr _ _ _ fun q1 =>
        (postprocess_sandwichByOuter_prod_snd_outcome _ _ g).symm
    calc avgOver (uniformDistribution (Point params))
          (fun v => avgOver (uniformDistribution (Point params.next))
            (fun q1 => defect (q1, appendPoint params v y)))
        = avgOver (uniformDistribution (Point params))
            (fun v => avgOver (uniformDistribution (Point params.next))
              (fun q1 => ∑ g : MIPStarRE.LDT.Polynomial params, ∑ a : Fq params,
                strategy.state.ev
                  (strategy.state.L (Ffun q1 g a * (1 - (G y).total)) *
                    strategy.state.R (Pfun g v)))) :=
          avgOver_congr _ _ _ fun v => avgOver_congr _ _ _ fun q1 =>
            evaluatedSlicePhaseTwoQuestionDefect_append_eq_sum_poly
              params strategy family G q1 v y
      _ = ∑ g : MIPStarRE.LDT.Polynomial params,
            strategy.state.ev
              (strategy.state.L
                  ((averageOperatorOverDistribution (uniformDistribution (Point params.next))
                    (fun q1 => ∑ a : Fq params, Ffun q1 g a)) * (1 - (G y).total)) *
                strategy.state.R
                  (averageOperatorOverDistribution (uniformDistribution (Point params))
                    (fun v => Pfun g v))) :=
          avgOver_avgOver_phaseTwo_linear _ _ strategy.state Ffun Pfun _
      _ = evaluatedSlicePhaseTwoStabilityDefect params strategy family G y :=
          Finset.sum_congr rfl fun g _ => by rw [hFavg g]; rfl
  calc avgOver (uniformDistribution (EvaluatedSliceQuestion params)) defect
      = avgOver (uniformDistribution (Point params.next))
          (fun q2 => avgOver (uniformDistribution (Point params.next))
            (fun q1 => defect (q1, q2))) :=
        avgOver_uniform_prod_swap fun q1 q2 => defect (q1, q2)
    _ = avgOver (uniformDistribution (Fq params))
          (fun y => avgOver (uniformDistribution (Point params))
            (fun v => avgOver (uniformDistribution (Point params.next))
              (fun q1 => defect (q1, appendPoint params v y)))) :=
        MIPStarRE.LDT.CommutativityPoints.avgOver_uniform_pointNext_decompose params _
    _ = avgOver (uniformDistribution (Fq params))
          (evaluatedSlicePhaseTwoStabilityDefect params strategy family G) :=
        avgOver_congr _ _ _ hbody

end MIPRE.LIDT.Co.Commutativity

end
