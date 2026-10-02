/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122),
MIPStarRE/LDT/Preliminaries/SelfConsistency/Core.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Preliminaries.BipartiteSelfConsistency.Completion
public import MIPRE.Background.LIDT.Co.Preliminaries.BipartiteSelfConsistency.Local
public import MIPRE.Background.LIDT.Co.Preliminaries.SwitchSandwichPrep.ApproxDelta

@[expose] public section

/-!
# Self-consistency: core squared-mass bounds

The squared-mass lower bound derived from bipartite self-consistency (`prop:cool-prop`), the
missing-mass bound used before `prop:completing-to-measurement`, and the comparison of bipartite
strong self-consistency with diagonal consistency
(`prop:other-two-notions-of-self-consistency`). This is the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/SelfConsistency/Core.lean` in the port of
`planning/c6b-plan.md` (milestone M3, section "Port conventions").

Each statement takes a symmetric model `S : SymModel 𝔓 K` in place of the state
`ψ : QuantumState (ι × ι)`, as an explicit first argument in the namespace `Preliminaries`, with
local operators in `𝔓`. The vendored hypotheses `hperm : PermInvState ψ` (of
`bipartiteSSCSquaredMass` and `completionMissingMassBound`) and `hψ : ψ.IsNormalized` (of
`completionMissingMassBound`) are dropped: swap symmetry enters through
`bipartiteSSC_implies_localSSC_liftLeft`, which uses the model's `S.ev_L_eq_ev_R`, and
normalization is `S.ev_one_of_isNormalized`. The vendored consistency relation of
`otherTwoNotionsOfSelfConsistency` and the two measurement lemmas is the two-space
`@ConsRel … ι ι …`; here it is the model's `S.ConsRel`, both families being local to `𝔓`.

The proof of `otherTwoNotionsOfSelfConsistency` compares `ev(M ⊗ M)` with `ev(M ⊗ I)` through
`S.opTensor_le_leftTensor`, where the vendored proof builds the Kronecker identity
`M ⊗ I - M ⊗ M = M ⊗ (I - M)` and its positivity by hand.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/preliminaries.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Preliminaries

open MIPStarRE.LDT (Distribution avgOver avgOver_mono uniformDistribution)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Squared mass lower bound from bipartite SSC (`prop:cool-prop`).

If `A` is `ζ`-strongly self-consistent, then `∑_a ev(A_a² ⊗ I) ≥ ev(A ⊗ I) - ζ`: bipartite
strong self-consistency gives local strong self-consistency of the left lift
(`bipartiteSSC_implies_localSSC_liftLeft`), whose defect is this gap. The vendored lemma asks
for a permutation-invariant state. -/
theorem bipartiteSSCSquaredMass {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (A : SubMeas Outcome 𝔓) (ζ : ℝ) :
    S.BipartiteSSCRel (uniformDistribution Unit) (constSubMeasFamily A) ζ →
      ∑ a : Outcome, S.ev (S.L (A.outcome a * A.outcome a)) ≥ S.ev (S.L A.total) - ζ := by
  intro hssc
  have hlocal := (bipartiteSSC_implies_localSSC_liftLeft S _ _ ζ hssc).diagonalOverlapBound
  rw [show IdxSubMeas.liftLeft S (constSubMeasFamily A) = constSubMeasFamily (A.liftLeft S)
    from rfl, constFamily_ssc_unit] at hlocal
  have hinner : S.ev (S.L A.total) -
      ∑ a : Outcome, S.ev (S.L (A.outcome a) * S.L (A.outcome a)) ≤ ζ :=
    (le_max_right 0 _).trans hlocal
  simp only [S.leftTensor_mul_leftTensor] at hinner
  linarith

/-- `lem:completion-missing-mass-bound`.

The missing-mass estimate used immediately before `prop:completing-to-measurement`: if `A` is a
`ζ`-strongly self-consistent measurement and its left lift is `δ`-close to that of `B`, then
`ev((I - B)² ⊗ I) ≤ 2√δ + ζ`. The vendored lemma asks for a permutation-invariant, normalized
state. -/
theorem completionMissingMassBound {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K)
    (A : Measurement Outcome 𝔓) (B : SubMeas Outcome 𝔓)
    (δ ζ : ℝ)
    (hssc : S.BipartiteSSCRel (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas) ζ)
    (hclose : S.SDDRel (uniformDistribution Unit)
      (constSubMeasFamily (A.toSubMeas.liftLeft S))
      (constSubMeasFamily (B.liftLeft S)) δ) :
    S.ev (S.L ((1 - B.total) * (1 - B.total))) ≤ 2 * Real.sqrt δ + ζ := by
  have hδ := hclose.squaredDistanceBound
  rw [constFamily_sdd_unit] at hδ
  have hsqrt := Real.sqrt_le_sqrt hδ
  have hdiagA := bipartiteSSCSquaredMass S A.toSubMeas ζ hssc
  simp only [← S.leftTensor_mul_leftTensor] at hdiagA
  have hmassA : S.ev (S.L A.total) = 1 := by
    rw [A.total_eq_one, S.leftTensor_one, S.ev_one_of_isNormalized]
  have hgapA : ∑ a, S.ev (S.L (A.outcome a) * S.L (A.outcome a)) -
      ∑ a, S.ev (S.L (A.outcome a) * S.L (B.outcome a)) ≤
        Real.sqrt (S.qSDD (A.toSubMeas.liftLeft S) (B.liftLeft S)) :=
    (abs_le.mp (question_overlap_gap_left S.toVecState
      (A.toSubMeas.liftLeft S) (B.liftLeft S))).2
  have hgapB : ∑ a, S.ev (S.L (A.outcome a) * S.L (B.outcome a)) -
      ∑ a, S.ev (S.L (B.outcome a) * S.L (B.outcome a)) ≤
        Real.sqrt (S.qSDD (A.toSubMeas.liftLeft S) (B.liftLeft S)) :=
    (abs_le.mp (question_overlap_gap_right S.toVecState
      (A.toSubMeas.liftLeft S) (B.liftLeft S))).2
  have hdiagB : ∑ a, S.ev (S.L (B.outcome a) * S.L (B.outcome a)) ≤ S.ev (S.L B.total) :=
    subMeas_diagMass_le_mass S.toVecState (B.liftLeft S)
  calc S.ev (S.L ((1 - B.total) * (1 - B.total)))
      ≤ S.ev (S.L (1 - B.total)) :=
        S.ev_mono _ _ (S.leftTensor_mono (sq_le_self (sub_nonneg.mpr B.total_le_one)
          (sub_le_self _ B.total_nonneg)))
    _ = 1 - S.ev (S.L B.total) := by
        rw [← S.leftTensor_sub, S.leftTensor_one, S.ev_sub, S.ev_one_of_isNormalized]
    _ ≤ 2 * Real.sqrt δ + ζ := by linarith

/-- `prop:other-two-notions-of-self-consistency`.

Bipartite strong self-consistency of `A` implies its diagonal consistency `A ≃_δ A`: question by
question, the total overlap `ev(A ⊗ A)` is at most `ev(A ⊗ I)` (`S.opTensor_le_leftTensor`,
since `A ≤ I`), and the remaining expression is the bipartite SSC defect. -/
theorem otherTwoNotionsOfSelfConsistency {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K)
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome 𝔓) (δ : ℝ) :
    S.BipartiteSSCRel 𝒟 A δ → S.ConsRel 𝒟 A A δ := fun ⟨hssc⟩ =>
  ⟨(avgOver_mono 𝒟 _ _ fun q =>
    max_le_max le_rfl (sub_le_sub_right (S.ev_mono _ _
      (S.opTensor_le_leftTensor (A q).total_nonneg (A q).total_le_one)) _)).trans hssc⟩

/-- Diagonal consistency for a full measurement is exactly bipartite strong
self-consistency.

This is the converse of `otherTwoNotionsOfSelfConsistency` in the special case
where the indexed family is measurement-valued.  Completeness identifies both
total-mass terms with the identity operator, so the self-`ConsRel` defect
`G ⊗ I ≃ I ⊗ G` and the diagonal SSC defect have the same questionwise
quantity. -/
theorem bipartiteSSCRel_of_consRel_self_measurement {Question Outcome : Type*}
    [Fintype Outcome]
    (S : SymModel 𝔓 K)
    (𝒟 : Distribution Question)
    (A : IdxMeas Question Outcome 𝔓) (δ : ℝ) :
    S.ConsRel 𝒟 (IdxMeas.toIdxSubMeas A) (IdxMeas.toIdxSubMeas A) δ →
      S.BipartiteSSCRel 𝒟 (IdxMeas.toIdxSubMeas A) δ := fun ⟨hcons⟩ =>
  ⟨le_of_eq_of_le (congrArg (avgOver 𝒟) (funext fun q => by
    show max 0 (S.ev (S.L (A q).total) - _) =
      max 0 (S.ev (S.L (A q).total * S.R (A q).total) - _)
    rw [(A q).total_eq_one, S.rightTensor_one, mul_one]; rfl)) hcons⟩

/-- For full measurements, bipartite SSC and diagonal self-consistency are
equivalent. -/
theorem bipartiteSSCRel_iff_consRel_self_measurement {Question Outcome : Type*}
    [Fintype Outcome]
    (S : SymModel 𝔓 K)
    (𝒟 : Distribution Question)
    (A : IdxMeas Question Outcome 𝔓) (δ : ℝ) :
    S.BipartiteSSCRel 𝒟 (IdxMeas.toIdxSubMeas A) δ ↔
      S.ConsRel 𝒟 (IdxMeas.toIdxSubMeas A) (IdxMeas.toIdxSubMeas A) δ :=
  ⟨otherTwoNotionsOfSelfConsistency S 𝒟 (IdxMeas.toIdxSubMeas A) δ,
    bipartiteSSCRel_of_consRel_self_measurement S 𝒟 A δ⟩

end MIPRE.LIDT.Co.Preliminaries

end
