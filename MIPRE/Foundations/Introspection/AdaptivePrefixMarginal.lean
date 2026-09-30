/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.AdaptivePrefixAdvance

@[expose] public section

/-! # Exact marginal error at the next adaptive prefix

Advancing the old prefix and current-coordinate outcome preserves the
squared error exactly: this label map is injective on attainable prefixes,
and all other prefix-conditioned operators vanish. The ideal coarse
marginal is the actual next-prefix measurement.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the state norms are those of an
arbitrary model whose first player holds the matrices over `ι → F` with entries in an algebra `𝒜`,
the register model `Ξ.reg (ι → F)` of the stage error among them; coarse-graining is `fibSumIn`.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Weyl Classical
set_option linter.unusedSectionVars false

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]

theorem fibSum_sqNorm_of_injective_support
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (Ψ : BipartiteModel 𝒞 𝒜 ℬ) (X : I → 𝒜) (f : I → J) (good : I → Prop)
    (hzero : ∀ i, ¬ good i → X i = 0)
    (hinj : ∀ i j, good i → good j → f i = f j → i = j) :
    (∑ b, Ψ.stateSqNorm (fibSumIn X f b)) = ∑ i, Ψ.stateSqNorm (X i) := by
  have hz : Ψ.stateSqNorm (0 : 𝒜) = 0 := by
    simp [BipartiteModel.stateSqNorm, BipartiteModel.stateNorm, StateModel.snorm_zero]
  have hfib (b : J) : Ψ.stateSqNorm (fibSumIn X f b) =
      ∑ i ∈ univ.filter (fun i => f i = b), Ψ.stateSqNorm (X i) := by
    by_cases hex : ∃ i, good i ∧ f i = b
    · obtain ⟨i, hi, hfi⟩ := hex
      have him : i ∈ univ.filter (fun i => f i = b) := by simp [hfi]
      have hother (j : I) (hj : j ∈ univ.filter (fun i => f i = b)) (hji : j ≠ i) :
          X j = 0 := by
        apply hzero j
        intro hgj
        exact hji (hinj j i hgj hi ((mem_filter.mp hj).2.trans hfi.symm))
      rw [fibSumIn, Finset.sum_eq_single_of_mem i him hother,
        Finset.sum_eq_single_of_mem i him (fun j hj hji => by rw [hother j hj hji, hz])]
    · have hother (i : I) (hi : i ∈ univ.filter (fun i => f i = b)) : X i = 0 := by
        apply hzero i
        intro hg
        exact hex ⟨i, hg, (mem_filter.mp hi).2⟩
      have hsum : fibSumIn X f b = 0 := Finset.sum_eq_zero hother
      rw [hsum, hz]
      symm
      exact Finset.sum_eq_zero fun i hi => by rw [hother i hi, hz]
  rw [Finset.sum_congr rfl (fun b _ => hfib b)]
  exact Finset.sum_fiberwise univ f (fun i => Ψ.stateSqNorm (X i))

variable {ι F A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype A] [DecidableEq A] {ℓ : ℕ}

/-- Advancing an arbitrary prefix-conditioned family preserves its total
squared state norm, without a measurement or state normalization premise. -/
theorem advancePrefix_fibSum_sqNorm (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) {ℬ' : Type*} [Ring ℬ'] [StarRing ℬ'] [Algebra ℂ ℬ']
    (Ψ : BipartiteModel 𝒞 (Matrix (ι → F) (ι → F) 𝒜) ℬ')
    (M : (p : (y : ι → F) × (Fin (Fintype.card (P.factorOfPrefix k y)) → F)) →
      Matrix (stageRemaining P k p.1 → F) (stageRemaining P k p.1 → F) 𝒜) :
    (∑ v, Ψ.stateSqNorm (fibSumIn (fun p => prefixResidualOp P k p.1 (M p))
      (fun p => advancePrefix P k p.1 p.2) v)) =
      ∑ p, Ψ.stateSqNorm (prefixResidualOp P k p.1 (M p)) := by
  apply fibSum_sqNorm_of_injective_support Ψ _ _ (fun p => p.1 ∈ prefixOutcomes P k)
  · intro p hp
    exact prefixResidualOp_eq_zero P k p.1 hp (M p)
  · intro p q hp hq he
    have hh := advancePrefix_injective hP k
      (a₁ := ⟨⟨p.1, hp⟩, p.2⟩) (a₂ := ⟨⟨q.1, hq⟩, q.2⟩) he
    exact congrArg
      (fun r : (y : ↥(prefixOutcomes P k)) ×
          (Fin (Fintype.card (P.factorOfPrefix k y)) → F) =>
        (⟨r.1.val, r.2⟩ : (y : ι → F) ×
          (Fin (Fintype.card (P.factorOfPrefix k y)) → F))) hh

/-- The current-stage marginal error is exactly the distance between its
advanced coarse marginal and the actual next-prefix PVM. No coarse-graining
contraction is assumed: the equality follows from attainable-label injectivity. -/
theorem prefixStageMarginalError_reassembled [StarModule ℂ 𝒜] [StarModule ℂ ℬ]
    (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ) (k : ℕ) (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
    (M : (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A →
      Matrix (stageRemaining P k y → F) (stageRemaining P k y → F) 𝒜) :
    prefixStageMarginalError P hP k Ξ M =
      ∑ v, (Ξ.reg (ι → F)).stateSqNorm
        (fibSumIn
          (fun p : (y : ι → F) × (Fin (Fintype.card (P.factorOfPrefix k y)) → F) =>
            prefixResidualOp P k p.1 (∑ a, M p.1 (p.2, a)))
          (fun p => advancePrefix P k p.1 p.2) v -
          smulKron 1 (Honest.hidingPrefixOp P (k + 1) (some v))) := by
  have hh := advancePrefix_fibSum_sqNorm P hP k (Ξ.reg (ι → F))
    (fun p => (∑ a, M p.1 (p.2, a)) -
      registerReadout (stageSplit P hP k p.1) wZ
        (coordinateLinear (CLChecks.stageLinear P k p.1)) p.2)
  simp only [prefixResidualOp_sub, fibSumIn, Finset.sum_sub_distrib,
    Fintype.sum_sigma] at hh
  unfold prefixStageMarginalError
  rw [← hh]
  apply Finset.sum_congr rfl
  intro v _
  rw [advancePrefix_projector_assembly P hP k v]
  rfl

end MIPRE.Introspection

end

end
