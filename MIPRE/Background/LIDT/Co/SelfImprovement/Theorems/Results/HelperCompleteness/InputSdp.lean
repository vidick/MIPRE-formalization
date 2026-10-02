/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
SelfImprovement/Theorems/Results/HelperCompleteness/InputSdp.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Basic.SubMeasurementFamilies
public import MIPRE.Background.LIDT.Co.GlobalVariance.Defs.Families
public import MIPRE.Background.LIDT.Co.Preliminaries.SelfConsistency.DataProcessing
public import MIPRE.Background.LIDT.MIPStarRE.LDT.SelfImprovement.Theorems.Thresholds.Final
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Statements
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.CommonHelpers

@[expose] public section

/-!
# Helper completeness: input consistency and the SDP bridge

The part of the helper-completeness argument that relates input consistency, SDP dual
feasibility and complementary slackness (the lower-bound calculation at the end of the
completeness proof): the counterpart of the vendored
`SelfImprovement/Theorems/Results/HelperCompleteness/InputSdp.lean` (under
`MIPRE/Background/LIDT/MIPStarRE/LDT/`) in the port of `planning/c6b-plan.md` (milestone M10,
section "Port conventions").

A strategy is a `SymStrat params 𝔓 K`. The SDP witnesses `T : SubMeas (Polynomial params) 𝔓` and
`Z : 𝔓` are local; the joint operators are `strategy.state.L` and `strategy.state.opTensor` in
`K →L[ℂ] K`.

- `input_consistency_match_mass_lower_bound` calls `cons_rel_uniform_full_total_match_mass_lower_bound`
  without the vendored `strategy.isNormalized`, a theorem of the model.
- `sdp_overlap_le_dual_mass` uses dual feasibility `0 ≤ Z - A_g` as an exact operator inequality
  in `𝔓`, placed by `strategy.state.opTensor` through the keystone's `opTensor_mono_left`, then
  `opTensor_le_leftTensor` and `ev_mono`.
- `sdp_complementary_slackness_sum_eq_dual_mass` keeps the vendored per-`h` hypothesis
  `sdpComplementarySlacknessEquation params strategy T Z h`, that is
  `T.outcome h * Z = T.outcome h * averagedPointOperator params strategy h` in `𝔓`, field for
  field with `SdpOptimalPairWithSlackness`; the vendored final `Matrix.one_mul` is `one_mul`.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/self_improvement.tex` lines 406--414
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.SelfImprovement

open MIPStarRE.LDT (Parameters FieldModel Point Fq avgOver uniformDistribution avgOver_congr
  avgOver_sum polynomial_sum_fiberwise)
open MIPRE.LIDT.Co.GlobalVariance (pointConditionedOutcomeOperatorAtPolynomial)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The incoming consistency of the original polynomial measurement gives the
matching-mass lower bound used in the helper-stage completeness proof.

This is the last step of the proof of
`references/ldt-paper/self_improvement.tex`, lines 407--414: after evaluating
the original input measurement `G` at a random point, `ConsRel ... nu` says the
off-diagonal mass is at most `nu`, hence the diagonal matching mass is at least
`1 - nu`. -/
theorem input_consistency_match_mass_lower_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓)
    (nu : ℝ)
    (hcons : strategy.state.ConsRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas) nu) :
    1 - nu ≤
      avgOver (uniformDistribution (Point params)) (fun u =>
        strategy.state.qBipartiteMatchMass
          ((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u)
          ((polynomialEvaluationFamily params G.toSubMeas) u)) :=
  cons_rel_uniform_full_total_match_mass_lower_bound strategy.state
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
    (polynomialEvaluationFamily params G.toSubMeas) nu
    (fun u => (strategy.pointMeasurement u).total_eq_one)
    (fun _ => G.total_eq_one) hcons

/-- Reindex a polynomial sum by the value of the polynomial at a fixed point.

This is the finite fiber decomposition used in the input-mass SDP bridge. The
lemma keeps the `Finset.sum_fiberwise` invocation separate from the tensor
algebra in `input_match_mass_eq_sdp_overlap`. -/
lemma input_sdp_overlap_fiberwise_sum_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (u : Point params) :
    (∑ g : MIPStarRE.LDT.Polynomial params,
        strategy.state.ev
          (strategy.state.opTensor
            (pointConditionedOutcomeOperatorAtPolynomial params strategy g u) (G.outcome g))) =
      ∑ a : Fq params,
        ∑ g ∈ Finset.univ.filter (fun g : MIPStarRE.LDT.Polynomial params => g u = a),
          strategy.state.ev
            (strategy.state.opTensor
              (pointConditionedOutcomeOperatorAtPolynomial params strategy g u)
              (G.outcome g)) :=
  polynomial_sum_fiberwise params u _

/-- The bracketed fiber expression is exactly the bipartite matching mass of
the point measurement against the polynomial measurement evaluated at `u`. -/
lemma input_sdp_bracketed_sum_eq_match_mass
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (u : Point params) :
    (∑ a : Fq params,
        strategy.state.ev
          (strategy.state.opTensor ((strategy.pointMeasurement u).outcome a)
            (∑ g ∈ Finset.univ.filter (fun g : MIPStarRE.LDT.Polynomial params => g u = a),
              G.outcome g))) =
      strategy.state.qBipartiteMatchMass
        ((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u)
        ((polynomialEvaluationFamily params G) u) := by
  unfold SymModel.qBipartiteMatchMass
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [polynomialEvaluationFamily, evaluateAt, SubMeas.postprocess_outcome]
  rfl

/-- Reindex the averaged input-consistency overlap as the SDP overlap
`Σ_g ⟨ψ, A_g ⊗ G_g⟩`.

This is the algebraic content of `references/ldt-paper/self_improvement.tex`,
lines 410--411: the pointwise match mass
`E_u Σ_a ⟨ψ, A^u_a ⊗ G_[g(u)=a] ψ⟩` is the same expression as
`Σ_g ⟨ψ, (E_u A^u_{g(u)}) ⊗ G_g ψ⟩`, after reindexing by the value of `g` at
`u`. -/
theorem input_match_mass_eq_sdp_overlap
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    avgOver (uniformDistribution (Point params)) (fun u =>
        strategy.state.qBipartiteMatchMass
          ((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u)
          ((polynomialEvaluationFamily params G) u)) =
      ∑ g : MIPStarRE.LDT.Polynomial params,
        strategy.state.ev
          (strategy.state.opTensor (averagedPointOperator params strategy g) (G.outcome g)) := by
  set S := strategy.state
  have hpoint (u : Point params) :
      S.qBipartiteMatchMass ((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u)
          ((polynomialEvaluationFamily params G) u) =
        ∑ g : MIPStarRE.LDT.Polynomial params,
          S.ev (S.opTensor (pointConditionedOutcomeOperatorAtPolynomial params strategy g u)
            (G.outcome g)) := by
    rw [input_sdp_overlap_fiberwise_sum_eq, ← input_sdp_bracketed_sum_eq_match_mass]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [S.opTensor_sum_right_finset, VecState.ev_finset_sum]
    refine Finset.sum_congr rfl fun g hg => ?_
    rw [(Finset.mem_filter.1 hg).2.symm]
    rfl
  rw [avgOver_congr _ _ _ hpoint, avgOver_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  exact (S.ev_opTensor_averageOperatorOverDistribution_left (uniformDistribution (Point params))
    (pointConditionedOutcomeOperatorAtPolynomial params strategy g) (G.outcome g)).symm

/-- Dual feasibility upper-bounds the SDP overlap by the dual mass
`⟨ψ, Z ⊗ I ψ⟩`.

This formalizes `references/ldt-paper/self_improvement.tex`, lines 408--410:
since `G` is a submeasurement, `Z ⊗ I` dominates `Z ⊗ G`, and since the SDP
dual is feasible, each `Z` dominates the averaged point operator
`E_u A^u_{g(u)}`. -/
theorem sdp_overlap_le_dual_mass
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (Z : 𝔓)
    (hZ : 0 ≤ Z)
    (hdual :
      ∀ g : MIPStarRE.LDT.Polynomial params,
        0 ≤ sdpDualSlackOperator params strategy Z g) :
    (∑ g : MIPStarRE.LDT.Polynomial params,
        strategy.state.ev
          (strategy.state.opTensor (averagedPointOperator params strategy g) (G.outcome g))) ≤
      strategy.state.ev (strategy.state.L Z) := by
  set S := strategy.state
  calc
    (∑ g : MIPStarRE.LDT.Polynomial params,
        S.ev (S.opTensor (averagedPointOperator params strategy g) (G.outcome g)))
        ≤ ∑ g : MIPStarRE.LDT.Polynomial params, S.ev (S.opTensor Z (G.outcome g)) :=
          Finset.sum_le_sum fun g _ => S.ev_mono _ _
            (S.opTensor_mono_left (sub_nonneg.1 (hdual g)) (G.outcome_pos g))
    _ = S.ev (S.opTensor Z G.total) := by
        rw [← G.sum_eq_total, S.opTensor_sum_right_univ, VecState.ev_sum]
    _ ≤ S.ev (S.L Z) := S.ev_mono _ _ (S.opTensor_le_leftTensor hZ G.total_le_one)

/-- The input-consistency lower bound, after the SDP reindexing and dual
feasibility steps, gives the lower bound on the dual mass used in helper
completeness.

This packages `references/ldt-paper/self_improvement.tex`, lines 406--412,
without asserting the later Cauchy--Schwarz comparison from `Hhat` to `Z` or any
of the projective final-fields transport. -/
theorem input_consistency_dual_mass_lower_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓)
    (Z : 𝔓)
    (nu : ℝ)
    (hZ : 0 ≤ Z)
    (hdual :
      ∀ g : MIPStarRE.LDT.Polynomial params,
        0 ≤ sdpDualSlackOperator params strategy Z g)
    (hcons : strategy.state.ConsRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas) nu) :
    1 - nu ≤ strategy.state.ev (strategy.state.L Z) :=
  ((input_consistency_match_mass_lower_bound params strategy G nu hcons).trans_eq
    (input_match_mass_eq_sdp_overlap params strategy G.toSubMeas)).trans
    (sdp_overlap_le_dual_mass params strategy G.toSubMeas Z hZ hdual)

/-- Complementary slackness converts the averaged-point sum to the dual mass.

This is the exact algebraic replacement used at the end of
`references/ldt-paper/self_improvement.tex`, lines 397--403: after the
Cauchy--Schwarz moves have produced
`Σ_h ⟨ψ, T_h · (E_u A^u_{h(u)}) ⊗ I ψ⟩`, complementary slackness replaces
`T_h · (E_u A^u_{h(u)})` by `T_h · Z`, and the primal completeness
`Σ_h T_h = I` reduces the sum to `⟨ψ, Z ⊗ I ψ⟩`. -/
theorem sdp_complementary_slackness_sum_eq_dual_mass
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (Z : 𝔓)
    (hT_total : T.total = 1)
    (hcomp :
      ∀ h : MIPStarRE.LDT.Polynomial params,
        sdpComplementarySlacknessEquation params strategy T Z h) :
    (∑ h : MIPStarRE.LDT.Polynomial params,
        strategy.state.ev
          (strategy.state.L (T.outcome h * averagedPointOperator params strategy h))) =
      strategy.state.ev (strategy.state.L Z) := by
  set S := strategy.state
  calc
    (∑ h : MIPStarRE.LDT.Polynomial params,
        S.ev (S.L (T.outcome h * averagedPointOperator params strategy h)))
        = ∑ h : MIPStarRE.LDT.Polynomial params, S.ev (S.L (T.outcome h * Z)) :=
          Finset.sum_congr rfl fun h _ => by rw [← hcomp h]
    _ = S.ev (S.L (T.total * Z)) := by
        rw [← VecState.ev_sum, ← T.sum_eq_total, Finset.sum_mul, S.leftTensor_finset_sum]
    _ = S.ev (S.L Z) := by rw [hT_total, one_mul]

end MIPRE.LIDT.Co.SelfImprovement

end
