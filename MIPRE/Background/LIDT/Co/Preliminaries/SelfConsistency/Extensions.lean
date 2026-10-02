/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122),
MIPStarRE/LDT/Preliminaries/SelfConsistency/Extensions.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Preliminaries.BipartiteSelfConsistency.Local
public import MIPRE.Background.LIDT.Co.Preliminaries.SelfConsistency.Core
public import MIPRE.Background.LIDT.Co.Test.StrategyFailures

@[expose] public section

/-!
# Self-consistency: strategy-level extensions

The good-strategy characterization (`lem:good-strategy-characterization`), self-consistency after
evaluation (`prop:two-notions-of-self-consistency-after-evaluation`) and the completeness transfer
from a self-consistent family (`prop:completeness-transfer-self-consistent-A`). This is the
counterpart of `MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/SelfConsistency/Extensions.lean`
in the port of `planning/c6b-plan.md` (milestone M3, section "Port conventions").

The strategy of `goodStrategyCharacterization` is the ported `SymStrat params 𝔓 K`, and its
consistency relations are those of the model `strategy.state`. The two other statements take a
symmetric model `S : SymModel 𝔓 K` in place of the state `ψ : QuantumState (ι × ι)`, as an
explicit first argument, with local families in `𝔓` lifted by `IdxSubMeas.liftLeft S` and
`IdxSubMeas.liftRight S`. The vendored hypotheses `hperm : PermInvState ψ` (of both) and
`hψ : ψ.IsNormalized` (of `completenessTransferSelfConsistentA`) are dropped: swap symmetry
enters through `twoNotionsOfSelfConsistency` and `bipartiteSSC_implies_localSSC_liftLeft`, and
normalization is not used.

The proofs are shorter than the vendored ones. In `twoNotionsOfSelfConsistencyAfterEvaluation`
the monotonicity of the bipartite defect under postprocessing is
`qBipartiteSSCDefect_postprocess_le` (Co `ComparisonCore`). In
`completenessTransferSelfConsistentA` the per-question mass gap is bounded by the local
self-consistency defect plus the two overlap gaps, and the average goes through
`avgOver_sub`, `avgOver_add`, `avgOver_const_mul` and `avgOver_abs_le_sqrt_of_pointwise`, in
place of the vendored unfolding of `avgOver` into finite sums.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/preliminaries.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Preliminaries

open MIPStarRE.LDT (Parameters FieldModel Point AxisParallelTestSample Distribution avgOver
  avgOver_mono avgOver_add avgOver_sub avgOver_const_mul uniformDistribution)
open MIPStarRE.LDT.Preliminaries (avgOver_abs_le_sqrt_of_pointwise)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- `lem:good-strategy-characterization`.

The axis-parallel branch is already definitionally a consistency bound. The
self-consistency branch is the same consistency bound specialized to the point
measurement, since that family is complete. The diagonal branch remains bundled
as `strategy.diagonalFailureProbability` because its sampled question type
depends on the restriction index `j`. -/
theorem goodStrategyCharacterization {params : Parameters} [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K) (eps delta gamma : ℝ) :
    strategy.IsGood eps delta gamma ↔
      strategy.state.ConsRel
        (uniformDistribution (AxisParallelTestSample params))
        (axisParallelPointAnswerFamily strategy)
        (axisParallelLineAnswerFamily strategy)
        eps ∧
      strategy.state.ConsRel
        (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        delta ∧
      strategy.diagonalFailureProbability ≤ gamma := by
  have hself_eq :
      strategy.selfConsistencyFailureProbability =
        strategy.state.bipartiteConsError
          (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) :=
    congrArg (avgOver _) (funext fun u => by
      show max 0 (strategy.state.ev (strategy.state.L (strategy.pointMeasurement u).total) - _) =
        max 0 (strategy.state.ev (strategy.state.L (strategy.pointMeasurement u).total *
          strategy.state.R (strategy.pointMeasurement u).total) - _)
      rw [(strategy.pointMeasurement u).total_eq_one, strategy.state.rightTensor_one, mul_one]
      rfl)
  exact ⟨fun h => ⟨⟨h.axisParallelTest⟩, ⟨hself_eq ▸ h.selfConsistencyTest⟩, h.diagonalLineTest⟩,
    fun ⟨haxis, hself, hdiag⟩ =>
      ⟨haxis.offDiagonalBound, hself_eq ▸ hself.offDiagonalBound, hdiag⟩⟩

/-- `prop:two-notions-of-self-consistency-after-evaluation`.

Question-dependent postprocessing preserves the total mass and can only increase the diagonal
overlap `∑_b ev(A_[f_q(a)=b] ⊗ A_[f_q(a)=b])` (`qBipartiteSSCDefect_postprocess_le`), so bipartite
SSC transfers from `A` to the postprocessed family, to which `twoNotionsOfSelfConsistency`
applies. The vendored lemma asks for a permutation-invariant state. -/
theorem twoNotionsOfSelfConsistencyAfterEvaluation
    {Question α β : Type*} [Fintype α] [Fintype β]
    (S : SymModel 𝔓 K)
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question α 𝔓) (δ : ℝ) (f : Question → α → β) :
    S.BipartiteSSCRel 𝒟 A δ →
      S.SDDRel 𝒟
        (IdxSubMeas.liftLeft S (fun q => postprocess (A q) (f q)))
        (IdxSubMeas.liftRight S (fun q => postprocess (A q) (f q)))
        (2 * δ) := fun ⟨hssc⟩ =>
  twoNotionsOfSelfConsistency S 𝒟 (fun q => postprocess (A q) (f q)) δ
    ⟨(avgOver_mono 𝒟 _ _ fun q => qBipartiteSSCDefect_postprocess_le S (A q) (f q)).trans hssc⟩

/-- `prop:completeness-transfer-self-consistent-A`.

If `A` is `δ`-strongly self-consistent and `A ⊗ I ≈_ε B ⊗ I`, then the mass of `B ⊗ I` is at
least that of `A ⊗ I` minus `δ + 2√ε`. Per question, the mass of `A ⊗ I` exceeds its diagonal
`∑ₐ ev(Aₐ² ⊗ I)` by at most the local self-consistency defect
(`bipartiteSSC_implies_localSSC_liftLeft`), the diagonal of `A` exceeds that of `B` by at most
`2 √(qSDD)` (the two overlap gaps), and the diagonal of `B` is at most its mass. The vendored
lemma asks for a permutation-invariant, normalized state. -/
theorem completenessTransferSelfConsistentA
    {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K)
    (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : IdxSubMeas Question Outcome 𝔓) (δ ε : ℝ) :
    S.BipartiteSSCRel 𝒟 A δ →
    S.SDDRel 𝒟 (IdxSubMeas.liftLeft S A) (IdxSubMeas.liftLeft S B) ε →
      S.idxSubMeasMass 𝒟 (IdxSubMeas.liftLeft S B) ≥
        S.idxSubMeasMass 𝒟 (IdxSubMeas.liftLeft S A) - δ - 2 * Real.sqrt ε := by
  intro hssc ⟨hε⟩
  have hδ := (bipartiteSSC_implies_localSSC_liftLeft S 𝒟 A δ hssc).diagonalOverlapBound
  set LA := IdxSubMeas.liftLeft S A
  set LB := IdxSubMeas.liftLeft S B
  have hgap : ∀ q, S.subMeasMass (LA q) - S.subMeasMass (LB q) ≤
      S.qSSCDefect (LA q) + 2 * Real.sqrt (S.qSDD (LA q) (LB q)) := by
    intro q
    have hdef : S.subMeasMass (LA q) -
        ∑ a, S.ev ((LA q).outcome a * (LA q).outcome a) ≤ S.qSSCDefect (LA q) :=
      le_max_right _ _
    have hB := subMeas_diagMass_le_mass S.toVecState (LB q)
    have hl := (abs_le.mp (question_overlap_gap_left S.toVecState (LA q) (LB q))).2
    have hr := (abs_le.mp (question_overlap_gap_right S.toVecState (LA q) (LB q))).2
    show S.ev (LA q).total - S.ev (LB q).total ≤ _
    unfold VecState.subMeasMass at hdef
    linarith
  have hsqrt :
      avgOver 𝒟 (fun q => Real.sqrt (S.qSDD (LA q) (LB q))) ≤
        Real.sqrt (S.sddError 𝒟 LA LB) :=
    (le_abs_self _).trans (avgOver_abs_le_sqrt_of_pointwise 𝒟 _ _
      (fun q => (abs_of_nonneg (Real.sqrt_nonneg _)).le) (fun q => S.qSDD_nonneg _ _) h𝒟)
  have htotal : S.idxSubMeasMass 𝒟 LA - S.idxSubMeasMass 𝒟 LB ≤ δ + 2 * Real.sqrt ε := by
    show avgOver 𝒟 (fun q => S.subMeasMass (LA q)) -
      avgOver 𝒟 (fun q => S.subMeasMass (LB q)) ≤ _
    rw [← avgOver_sub]
    calc
      _ ≤ avgOver 𝒟 (fun q =>
            S.qSSCDefect (LA q) + 2 * Real.sqrt (S.qSDD (LA q) (LB q))) :=
          avgOver_mono 𝒟 _ _ hgap
      _ = S.sscError 𝒟 LA + 2 * avgOver 𝒟 (fun q => Real.sqrt (S.qSDD (LA q) (LB q))) := by
          rw [avgOver_add, avgOver_const_mul]; rfl
      _ ≤ δ + 2 * Real.sqrt ε :=
          add_le_add hδ (mul_le_mul_of_nonneg_left
            (hsqrt.trans (Real.sqrt_le_sqrt hε)) zero_le_two)
  linarith

end MIPRE.LIDT.Co.Preliminaries

end
