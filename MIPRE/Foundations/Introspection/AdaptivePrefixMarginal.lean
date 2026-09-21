/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AdaptivePrefixAdvance

/-! # Exact marginal error at the next adaptive prefix

Advancing the old prefix and current-coordinate outcome preserves the
squared error exactly: this label map is injective on attainable prefixes,
and all other prefix-conditioned operators vanish. The ideal coarse
marginal is the actual next-prefix measurement.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Weyl Classical
set_option linter.unusedSectionVars false

private theorem fibSum_sqNorm_of_injective_support
    {I J D K : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype D] [DecidableEq D] [Fintype K] [DecidableEq K]
    (ψ : D × K → ℂ) (X : I → Matrix D D ℂ) (f : I → J) (good : I → Prop)
    (hzero : ∀ i, ¬ good i → X i = 0)
    (hinj : ∀ i j, good i → good j → f i = f j → i = j) :
    (∑ b, stateSqNorm ψ (fibSum X f b)) = ∑ i, stateSqNorm ψ (X i) := by
  have hz : stateSqNorm ψ (0 : Matrix D D ℂ) = 0 := by
    simp [stateSqNorm, stateNorm, stateVec]
  have hfib (b : J) : stateSqNorm ψ (fibSum X f b) =
      ∑ i ∈ univ.filter (fun i => f i = b), stateSqNorm ψ (X i) := by
    by_cases hex : ∃ i, good i ∧ f i = b
    · obtain ⟨i, hi, hfi⟩ := hex
      have him : i ∈ univ.filter (fun i => f i = b) := by simp [hfi]
      have hother (j : I) (hj : j ∈ univ.filter (fun i => f i = b)) (hji : j ≠ i) :
          X j = 0 := by
        apply hzero j
        intro hgj
        exact hji (hinj j i hgj hi ((mem_filter.mp hj).2.trans hfi.symm))
      rw [fibSum, Finset.sum_eq_single_of_mem i him hother,
        Finset.sum_eq_single_of_mem i him (fun j hj hji => by rw [hother j hj hji, hz])]
    · have hother (i : I) (hi : i ∈ univ.filter (fun i => f i = b)) : X i = 0 := by
        apply hzero i
        intro hg
        exact hex ⟨i, hg, (mem_filter.mp hi).2⟩
      have hsum : fibSum X f b = 0 := Finset.sum_eq_zero hother
      rw [hsum, hz]
      symm
      exact Finset.sum_eq_zero fun i hi => by rw [hother i hi, hz]
  rw [Finset.sum_congr rfl (fun b _ => hfib b)]
  exact Finset.sum_fiberwise univ f (fun i => stateSqNorm ψ (X i))

variable {ι F H K A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A] {ℓ : ℕ}

/-- Advancing an arbitrary prefix-conditioned family preserves its total
squared state norm, without a measurement or state normalization premise. -/
theorem advancePrefix_fibSum_sqNorm (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (ψ : ((ι → F) × H) × K → ℂ)
    (M : (p : (y : ι → F) × (Fin (Fintype.card (P.factorOfPrefix k y)) → F)) →
      Matrix ((stageRemaining P k p.1 → F) × H) ((stageRemaining P k p.1 → F) × H) ℂ) :
    (∑ v, stateSqNorm ψ (fibSum (fun p => prefixResidualOp P k p.1 (M p))
      (fun p => advancePrefix P k p.1 p.2) v)) =
      ∑ p, stateSqNorm ψ (prefixResidualOp P k p.1 (M p)) := by
  apply fibSum_sqNorm_of_injective_support _ _ _ (fun p => p.1 ∈ prefixOutcomes P k)
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
theorem prefixStageMarginalError_reassembled (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ) (ξ : H × K → ℂ)
    (M : (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A →
      Matrix ((stageRemaining P k y → F) × H) ((stageRemaining P k y → F) × H) ℂ) :
    prefixStageMarginalError P hP k ξ M =
      ∑ v, stateSqNorm (registerState (ι → F) ξ)
        (fibSum
          (fun p : (y : ι → F) × (Fin (Fintype.card (P.factorOfPrefix k y)) → F) =>
            prefixResidualOp P k p.1 (∑ a, M p.1 (p.2, a)))
          (fun p => advancePrefix P k p.1 p.2) v -
          aOp (Honest.hidingPrefixOp P (k + 1) (some v))) := by
  have hh := advancePrefix_fibSum_sqNorm P hP k (registerState (ι → F) ξ)
    (fun p => (∑ a, M p.1 (p.2, a)) -
      registerReadout (stageSplit P hP k p.1) wZ
        (coordinateLinear (CLChecks.stageLinear P k p.1)) p.2)
  simp only [prefixResidualOp_sub, fibSum, Finset.sum_sub_distrib,
    Fintype.sum_sigma] at hh
  unfold prefixStageMarginalError
  rw [← hh]
  apply Finset.sum_congr rfl
  intro v _
  rw [advancePrefix_projector_assembly P hP k v]
  rfl

end MIPRE.Introspection

end
