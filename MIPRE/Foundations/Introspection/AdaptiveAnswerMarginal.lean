/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AdaptiveAnswerDecode
import MIPRE.Foundations.Introspection.AdaptivePrefixMarginal

/-! # The stage marginal with its actual malformed-answer mass

The deterministic graph assigns `none` to current coordinate zero. Its
coarse marginal therefore equals the valid reported-prefix marginal plus
the corresponding old-prefix malformed block. Orthogonality of those
blocks charges their entire error to the single reported `none` outcome.
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Matrix Classical Weyl
set_option linter.unusedSectionVars false

variable {ι F H K A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A] {ℓ : ℕ}

/-- The option-valued prefix actually reported by a full Introspect answer. -/
def fullAnswerPrefix (P : CL.CLFun F ι ℓ) (k : ℕ) :
    Option ((ι → F) × A) → Option (ι → F) :=
  Option.map (fun a => P.outputPrefix k a.1)

private theorem prefixResidualOp_zero (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F) :
    prefixResidualOp (H := H) P k y 0 = 0 := by
  ext i j
  simp [prefixResidualOp, registerOp_apply]

theorem stageAnswerRefinement_coarse_marginal (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ)
    (M : (y : ι → F) → Option ((ι → F) × A) →
      Matrix ((stageRemaining P k y → F) × H) _ ℂ)
    (N : Option ((ι → F) × A) → Matrix ((ι → F) × H) _ ℂ)
    (hform : ∀ a, N a = ∑ y, prefixResidualOp P k y (M y a))
    (hsupport : ∀ y x a, P.outputPrefix k x ≠ y → M y (some (x, a)) = 0)
    (v : ι → F) :
    fibSum
      (fun p : (y : ι → F) × (Fin (Fintype.card (P.factorOfPrefix k y)) → F) =>
        prefixResidualOp P k p.1 (∑ a, stageAnswerRefinement P k p.1 (M p.1) (p.2, a)))
      (fun p => advancePrefix P k p.1 p.2) v =
      fibSum N (fullAnswerPrefix P (k + 1)) (some v) +
        prefixResidualOp P k v (M v none) := by
  let C (y : ι → F) (a : Option ((ι → F) × A)) := prefixResidualOp P k y (M y a)
  have hlift (y : ι → F) (p : (Fin (Fintype.card (P.factorOfPrefix k y)) → F) ×
      Option ((ι → F) × A)) :
      prefixResidualOp P k y (stageAnswerRefinement P k y (M y) p) =
        graphRefinement (C y) (stageAnswerCoordinate P k y) p := by
    by_cases hp : p.1 = stageAnswerCoordinate P k y p.2
    · simp [stageAnswerRefinement, graphRefinement, hp, C]
    · simp [stageAnswerRefinement, graphRefinement, hp, prefixResidualOp_zero]
  have hv (y : ι → F) (a : (ι → F) × A) :
      (if advancePrefix P k y (coordinateRestrict (P.factorOfPrefix k y) a.1) = v
        then C y (some a) else 0) =
      if P.outputPrefix (k + 1) a.1 = v then C y (some a) else 0 := by
    by_cases ha : P.outputPrefix k a.1 = y
    · rw [advancePrefix_coordinate_of_outputPrefix hP k y a.1 ha]
    · have hz : C y (some a) = 0 := by
        change prefixResidualOp P k y (M y (some a)) = 0
        rw [hsupport y a.1 a.2 ha, prefixResidualOp_zero]
      simp [hz]
  have hreported : fibSum N (fullAnswerPrefix P (k + 1)) (some v) =
      ∑ a : (ι → F) × A, if P.outputPrefix (k + 1) a.1 = v then N (some a) else 0 := by
    unfold fibSum
    simp only [Finset.sum_filter, Fintype.sum_option]
    simp only [fullAnswerPrefix, Option.map_none, Option.map_some, Option.some.injEq,
      reduceCtorEq, if_false, zero_add]
  calc
    _ = ∑ y, fibSum (graphRefinement (C y) (stageAnswerCoordinate P k y))
        (fun p => advancePrefix P k y p.1) v := by
      unfold fibSum
      simp only [Finset.sum_filter, Fintype.sum_sigma, Fintype.sum_prod_type,
        prefixResidualOp_sum, hlift]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : advancePrefix P k y z = v
      · simp only [if_pos hz]
      · simp only [if_neg hz, Finset.sum_const_zero]
    _ = ∑ y, fibSum (C y)
        (fun a => advancePrefix P k y (stageAnswerCoordinate P k y a)) v := by
      simp only [graphRefinement_fibSum]
    _ = (∑ y, ∑ a : (ι → F) × A,
        if P.outputPrefix (k + 1) a.1 = v then C y (some a) else 0) + C v none := by
      unfold fibSum
      simp only [Finset.sum_filter, Fintype.sum_option]
      change (∑ y, (if advancePrefix P k y 0 = v then C y none else 0) +
        ∑ a : (ι → F) × A,
          if advancePrefix P k y (coordinateRestrict (P.factorOfPrefix k y) a.1) = v
            then C y (some a) else 0) = _
      simp_rw [hv]
      have hz (y : ι → F) : advancePrefix P k y 0 = y := by simp [advancePrefix]
      simp only [hz, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact add_comm _ _
    _ = _ := by
      congr 1
      rw [Finset.sum_comm, hreported]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : P.outputPrefix (k + 1) a.1 = v
      · simp only [if_pos ha]
        exact (hform (some a)).symm
      · simp only [if_neg ha, Finset.sum_const_zero]

theorem fullAnswerPrefix_none (P : CL.CLFun F ι ℓ) (k : ℕ)
    (N : Option ((ι → F) × A) → Matrix ((ι → F) × H) _ ℂ) :
    fibSum N (fullAnswerPrefix P k) none = N none := by
  simp [fibSum, fullAnswerPrefix, Finset.sum_filter]

/-- The true option-valued reported-prefix error controls the mixing
marginal at cost two. The malformed mass is charged once, using exact
orthogonality of its old-prefix blocks. -/
theorem stageAnswerRefinement_marginal_le_reported (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ) (ξ : H × K → ℂ)
    (M : (y : ι → F) → Option ((ι → F) × A) →
      Matrix ((stageRemaining P k y → F) × H) _ ℂ)
    (N : Option ((ι → F) × A) → Matrix ((ι → F) × H) _ ℂ)
    (hform : ∀ a, N a = ∑ y, prefixResidualOp P k y (M y a))
    (hsupport : ∀ y x a, P.outputPrefix k x ≠ y → M y (some (x, a)) = 0) :
    prefixStageMarginalError P hP k ξ (fun y => stageAnswerRefinement P k y (M y)) ≤
      2 * ∑ v, stateSqNorm (registerState (ι → F) ξ)
        (fibSum N (fullAnswerPrefix P (k + 1)) v -
          aOp (Honest.hidingPrefixOp P (k + 1) v)) := by
  let ψ := registerState (ι → F) ξ
  let R (v : ι → F) := fibSum N (fullAnswerPrefix P (k + 1)) (some v)
  let D (v : ι → F) := prefixResidualOp P k v (M v none)
  let J (v : ι → F) := (aOp (Honest.hidingPrefixOp P (k + 1) (some v)) :
    Matrix ((ι → F) × H) _ ℂ)
  have ht := sum_snorm_sq_triangle' ψ
    (fun v => aOp (R v + D v)) (fun v => aOp (R v)) (fun v => aOp (J v))
  have htri : (∑ v, stateSqNorm ψ (R v + D v - J v)) ≤
      2 * ∑ v, stateSqNorm ψ (D v) + 2 * ∑ v, stateSqNorm ψ (R v - J v) := by
    simpa only [stateSqNorm, stateNorm, norm_stateVec_eq_snorm, ← aOp_sub,
      add_sub_cancel_left] using ht
  have hd : (∑ v, stateSqNorm ψ (D v)) = stateSqNorm ψ (N none) := by
    rw [hform none, stateSqNorm_sum_prefixResidualOp P hP]
  have hn : aOp (Honest.hidingPrefixOp P (k + 1) none) =
      (0 : Matrix ((ι → F) × H) _ ℂ) := by
    rw [Honest.hidingPrefixOp_none, aOp_zero]
  rw [prefixStageMarginalError_reassembled]
  simp_rw [stageAnswerRefinement_coarse_marginal P hP k M N hform hsupport]
  change (∑ v, stateSqNorm ψ (R v + D v - J v)) ≤ _
  rw [Fintype.sum_option, fullAnswerPrefix_none, hn, sub_zero, mul_add]
  exact hd ▸ htri

end MIPRE.Introspection
end
