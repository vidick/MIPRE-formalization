/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/ScalarApproximation/Pointwise.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.ScalarApproximation.Core
public import MIPRE.Background.LIDT.Co.CommutativityPoints.Approximation
public import MIPRE.Background.LIDT.Co.Preliminaries.SelfConsistency.Extensions

@[expose] public section

/-!
# Section 11 commutativity: pointwise scalar approximation

Pointwise overlap terms `⟨Ψ, (I - G^x) ⊗ G^x Ψ⟩` controlling both sides of the `G`-stability
estimate, used as the base for the averaged scalar bound: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/ScalarApproximation/Pointwise.lean` in the
port of `planning/c6b-plan.md` (milestone M7, section "Port conventions").

The overlap term is `strategy.state.ev (strategy.state.L (1 - T) * strategy.state.R T)` on the
symmetric model of the strategy, and `gCommStability_pointwise_sum_bound_core` takes the model
`S : SymModel 𝔓 K` as an explicit first argument in place of the vendored state `ψ`. The
vendored hypothesis `strategy.permInvState` passed to `qBipartiteSSCDefect_eq_half_qSDD_of_proj`
and `Preliminaries.twoNotionsOfSelfConsistencyAfterEvaluation` is gone with those lemmas'
`hperm`; the one swap use left here is `S.ev_L_eq_ev_R` in `gCommStability_ssc_point`, in place of
`strategy.permInvState.swap_ev`.

The proofs are shorter than the vendored ones. The vendored self-adjointness of `G^x` through
`Matrix.PosSemidef` is `IsSelfAdjoint.of_nonneg`; the entrywise Kronecker identity
`(1 - T) ⊗ I = I ⊗ I - T ⊗ I` of `gCommStability_ssc_point` is `S.leftTensor_sub` and
`map_one`; and the sums over outcomes in `gCommStability_pointwise_sum_bound_core` and
`gCommStability_ssc_point` collapse through the keystone's `opTensor_sum_left_univ` and
`opTensor_sum_right_univ`.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Commutativity

open MIPStarRE.LDT (Parameters FieldModel Point Fq truncatePoint pointHeight appendPoint
  truncatePoint_appendPoint pointHeight_appendPoint avgOver avgOver_congr avgOver_const_mul
  avgOver_uniform_equiv avgOver_uniform_prod avgOver_uniform_le_const uniformDistribution)
open MIPStarRE.LDT.Commutativity (EvaluatedSliceQuestion StabilityOneOutcome)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The common overlap term `⟨Ψ, (I - G^x) ⊗ G^x Ψ⟩` controlling both
stability estimates. -/
noncomputable def gCommOverlapTerm
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (x : Fq params) : ℝ :=
  strategy.state.ev
    (strategy.state.L (1 - (G x).total) * strategy.state.R (G x).total)

/-- The slice self-consistency defect of `G` is at most `zeta / 2`. -/
lemma gCommStability_sliceSSC
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (zeta : ℝ)
    (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    strategy.state.BipartiteSSCRel
      (uniformDistribution (Fq params))
      G
      (zeta / 2) := by
  refine ⟨?_⟩
  have hhalf : strategy.state.bipartiteSSCError (uniformDistribution (Fq params)) G =
      (1 / 2 : ℝ) * strategy.state.sddError (uniformDistribution (Fq params))
        (IdxSubMeas.liftLeft strategy.state (IdxProjSubMeas.toIdxSubMeas family.meas))
        (IdxSubMeas.liftRight strategy.state (IdxProjSubMeas.toIdxSubMeas family.meas)) := by
    unfold SymModel.bipartiteSSCError VecState.sddError
    rw [← avgOver_const_mul]
    exact avgOver_congr _ _ _ fun x => by
      rw [hG x]
      exact qBipartiteSSCDefect_eq_half_qSDD_of_proj strategy.state (family.meas x)
  rw [hhalf]
  linarith [hself.sliceSelfConsistency.squaredDistanceBound]

/-- Slice strong self-consistency transfers to the evaluated point family.

The paper invokes the slice self-consistency item after postprocessing a slice
measurement by the predicate `g(truncatePoint u) = a`.  This lemma makes that
implicit data-processing step explicit: projectivity converts the left/right SDD
hypothesis into bipartite strong self-consistency with loss `1/2`,
question-dependent postprocessing converts it back to left/right SDD with the
compensating factor `2`, and uniform reindexing
`Point params.next ≃ Point params × Fq params` averages the height coordinate. -/
lemma evaluatedPointFamily_selfConsistency_of_stronglySelfConsistent
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (zeta : ℝ)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    strategy.state.SDDRel
      (uniformDistribution (Point params.next))
      (evaluatedPointFamilyLeft strategy.state params family)
      (evaluatedPointFamilyRight strategy.state params family)
      zeta := by
  have hsliceSSC := gCommStability_sliceSSC params strategy zeta family
    (IdxProjSubMeas.toIdxSubMeas family.meas) (fun _ => rfl) hself
  let f : Point params → Fq params → ℝ := fun u x =>
    strategy.state.qSDD
      (strategy.state.leftPlacedSubMeas (evaluateAt params u (family.meas x).toSubMeas))
      (strategy.state.rightPlacedSubMeas (evaluateAt params u (family.meas x).toSubMeas))
  have hpost : ∀ u : Point params,
      avgOver (uniformDistribution (Fq params)) (fun x => f u x) ≤ zeta := fun u =>
    ((Preliminaries.twoNotionsOfSelfConsistencyAfterEvaluation strategy.state
      (uniformDistribution (Fq params)) (IdxProjSubMeas.toIdxSubMeas family.meas) (zeta / 2)
      (fun _ g => g u) hsliceSSC).squaredDistanceBound).trans_eq (by ring)
  refine ⟨?_⟩
  calc strategy.state.sddError (uniformDistribution (Point params.next))
        (evaluatedPointFamilyLeft strategy.state params family)
        (evaluatedPointFamilyRight strategy.state params family)
      = avgOver (uniformDistribution (Point params × Fq params)) (fun ux => f ux.1 ux.2) := by
        refine (avgOver_uniform_equiv (MIPStarRE.LDT.CommutativityPoints.pointNextEquiv params)
          _).trans (avgOver_congr _ _ _ fun ux => ?_)
        change strategy.state.qSDD
            (evaluatedPointFamilyLeft strategy.state params family (appendPoint params ux.1 ux.2))
            (evaluatedPointFamilyRight strategy.state params family
              (appendPoint params ux.1 ux.2)) = _
        simp only [evaluatedPointFamilyLeft, evaluatedPointFamilyRight, evaluatedPointFamily,
          IdxPolyFamily.evaluatedAtNextPoint, truncatePoint_appendPoint, pointHeight_appendPoint,
          f]
    _ = avgOver (uniformDistribution (Point params))
          (fun u => avgOver (uniformDistribution (Fq params)) (fun x => f u x)) :=
        avgOver_uniform_prod f
    _ ≤ zeta := avgOver_uniform_le_const _ zeta hpost

/-- A sandwiched product of two submeasurements is controlled by the overlap of
the right-hand total with its complement. The vendored state `ψ` is the symmetric model `S`. -/
lemma gCommStability_pointwise_sum_bound_core
    (S : SymModel 𝔓 K)
    {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α 𝔓)
    (B : SubMeas β 𝔓)
    (hB_sq : B.total * B.total = B.total) :
    (∑ ab : α × β,
        S.ev (S.L ((1 - B.total) * A.outcome ab.1 * (1 - B.total)) * S.R (B.outcome ab.2))) ≤
      S.ev (S.L (1 - B.total) * S.R B.total) := by
  set T := B.total with hT
  have hTc : IsSelfAdjoint (1 - T) :=
    (IsSelfAdjoint.of_nonneg (sub_nonneg.2 B.total_le_one))
  have hsum : (∑ ab : α × β,
      S.ev (S.L ((1 - T) * A.outcome ab.1 * (1 - T)) * S.R (B.outcome ab.2))) =
      S.ev (S.opTensor ((1 - T) * A.total * (1 - T)) T) := by
    rw [← A.sum_eq_total, Finset.mul_sum, Finset.sum_mul, S.opTensor_sum_left_univ, S.ev_sum,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hT, ← B.sum_eq_total, S.opTensor_sum_right_univ, S.ev_sum, B.sum_eq_total]
  have hcollapse : (1 - T) * 1 * (1 - T) = 1 - T := by
    rw [mul_one, sub_mul, one_mul, mul_sub, mul_one, hB_sq, sub_self, sub_zero]
  rw [hsum]
  refine (S.ev_mono _ _ (S.opTensor_mono_left
    (IsSelfAdjoint.conjugate_le_conjugate A.total_le_one hTc) B.total_nonneg)).trans_eq ?_
  rw [hcollapse]

/-- A single stability-one summand is controlled by replacing the inner
evaluated slice sandwich with the corresponding evaluated point outcome. -/
lemma gCommStability_pointwise_summand_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (q : EvaluatedSliceQuestion params)
    (ah : StabilityOneOutcome params) :
    strategy.state.ev
      (strategy.state.L
          ((1 - (G (pointHeight params q.2)).total) *
            (star ((evaluatedSliceSandwichRaw params strategy family q).outcome
              (ah.1, ah.2 (truncatePoint params q.2))) *
              (evaluatedSliceSandwichRaw params strategy family q).outcome
                (ah.1, ah.2 (truncatePoint params q.2))) *
            (1 - (G (pointHeight params q.2)).total)) *
        strategy.state.R ((G (pointHeight params q.2)).outcome ah.2)) ≤
    strategy.state.ev
      (strategy.state.L
          ((1 - (G (pointHeight params q.2)).total) *
            (evaluatedPointFamily params family q.1).outcome ah.1 *
            (1 - (G (pointHeight params q.2)).total)) *
        strategy.state.R ((G (pointHeight params q.2)).outcome ah.2)) := by
  set T := (G (pointHeight params q.2)).total
  set A := evaluatedPointFamily params family q.1
  set P := evaluatedSliceSandwichRaw params strategy family q
  set o : MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params :=
    (ah.1, ah.2 (truncatePoint params q.2))
  have hTc : IsSelfAdjoint (1 - T) :=
    IsSelfAdjoint.of_nonneg (sub_nonneg.2 (G (pointHeight params q.2)).total_le_one)
  have hP_sq_le : star (P.outcome o) * P.outcome o ≤ P.outcome o := by
    rw [P.outcome_hermitian o]
    exact sq_le_self (P.outcome_pos o) (P.outcome_le_one o)
  have hP_le_A : P.outcome o ≤ A.outcome ah.1 :=
    calc P.outcome o = A.outcome ah.1 *
          (evaluatedPointFamily params family q.2).outcome (ah.2 (truncatePoint params q.2)) *
          A.outcome ah.1 := rfl
      _ ≤ A.outcome ah.1 * 1 * A.outcome ah.1 :=
          IsSelfAdjoint.conjugate_le_conjugate
            ((evaluatedPointFamily params family q.2).outcome_le_one _)
            (A.outcome_hermitian ah.1)
      _ = A.outcome ah.1 := by
          rw [mul_one, evaluatedPointFamily_outcome_proj params family q.1 ah.1]
  exact strategy.state.ev_mono _ _ <| strategy.state.opTensor_mono_left
    ((IsSelfAdjoint.conjugate_le_conjugate hP_sq_le hTc).trans
      (IsSelfAdjoint.conjugate_le_conjugate hP_le_A hTc))
    ((G (pointHeight params q.2)).outcome_pos ah.2)

/-- The full stability-one defect is bounded by the overlap term for the
target slice measurement `G^y`. -/
lemma gCommStability_pointwise_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hG : ∀ x, G x = (family.meas x).toSubMeas) :
    ∀ q : EvaluatedSliceQuestion params,
      strategy.state.qSDDOp
        (commDataProcessedGStabilityOneLeft params strategy family G q)
        (commDataProcessedGStabilityOneRight params strategy family G q) ≤
      strategy.state.ev
        (strategy.state.L (1 - (G (pointHeight params q.2)).total) *
          strategy.state.R ((G (pointHeight params q.2)).total)) := by
  intro q
  rw [commDataProcessedGStabilityOne_qSDDOp_expand params strategy family G hG q]
  have hGy_sq : (G (pointHeight params q.2)).total * (G (pointHeight params q.2)).total =
      (G (pointHeight params q.2)).total := by
    rw [hG]
    exact Preliminaries.projSubMeas_total_proj (family.meas (pointHeight params q.2))
  exact (Finset.sum_le_sum fun ah _ =>
    gCommStability_pointwise_summand_bound params strategy family G q ah).trans
    (gCommStability_pointwise_sum_bound_core strategy.state
      (evaluatedPointFamily params family q.1) (G (pointHeight params q.2)) hGy_sq)

/-- The overlap term at `x` is bounded by the bipartite SSC defect of `G x`. -/
lemma gCommStability_ssc_point
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    ∀ x : Fq params,
      gCommOverlapTerm params strategy G x ≤
      strategy.state.qBipartiteSSCDefect (G x) := by
  intro x
  set S := strategy.state
  set T := (G x).total
  have hdiag_le :
      ∑ h : MIPStarRE.LDT.Polynomial params, S.ev (S.opTensor ((G x).outcome h) ((G x).outcome h))
        ≤ S.ev (S.opTensor T T) := by
    calc ∑ h, S.ev (S.opTensor ((G x).outcome h) ((G x).outcome h))
        ≤ ∑ h, S.ev (S.opTensor T ((G x).outcome h)) :=
          Finset.sum_le_sum fun h _ => S.ev_mono _ _ <|
            S.opTensor_mono_left ((G x).outcome_le_total h) ((G x).outcome_pos h)
      _ = S.ev (S.opTensor T T) := by
          rw [← S.ev_sum, ← S.opTensor_sum_right_univ, (G x).sum_eq_total]
  have hover : gCommOverlapTerm params strategy G x = S.ev (S.L T) - S.ev (S.opTensor T T) := by
    change S.ev (S.L (1 - T) * S.R T) = _
    rw [← S.leftTensor_sub, map_one, sub_mul, one_mul, S.ev_sub, S.ev_L_eq_ev_R]
  rw [hover, SymModel.qBipartiteSSCDefect]
  exact le_max_of_le_right (by linarith)

end MIPRE.LIDT.Co.Commutativity

end
