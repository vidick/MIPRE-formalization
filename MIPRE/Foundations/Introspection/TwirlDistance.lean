/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.StateDistance

/-! # Approximate commutation controls twirling in the state-dependent norm

This is the paper's `lem:mixing-U`, with constant one and all outcome sums explicit.
The state need not be invariant under any of the unitaries.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix

variable {dA dB I : Type*} [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB] [Fintype I]

/-- Left multiplication by an isometry preserves the state-dependent squared norm. -/
theorem stateSqNorm_mul_of_isometry (ψ : dA × dB → ℂ)
    (U M : Matrix dA dA ℂ) (hU : Uᴴ * U = 1) :
    stateSqNorm ψ (U * M) = stateSqNorm ψ M := by
  have h : (U * M)ᴴ * (U * M) = Mᴴ * M := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U M,
      hU, Matrix.one_mul]
  rw [stateSqNorm_eq, stateSqNorm_eq, h]

/-- Twirling against a finitely supported probability distribution. -/
def unitaryTwirl (μ : I → ℝ) (U : I → Matrix dA dA ℂ) (M : Matrix dA dA ℂ) :
    Matrix dA dA ℂ := ∑ u, (μ u : ℂ) • (U u * M * (U u)ᴴ)

/-- Jensen and left-unitary invariance bound the twirl error by the commutator error. -/
theorem unitaryTwirl_dist_le (μ : I → ℝ) (hμ0 : ∀ u, 0 ≤ μ u) (hμ1 : ∑ u, μ u = 1)
    (U : I → Matrix dA dA ℂ) (hU : ∀ u, (U u)ᴴ * U u = 1)
    (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) :
    stateSqNorm ψ (unitaryTwirl μ U M - M) ≤
      ∑ u, μ u * stateSqNorm ψ (M * (U u)ᴴ - (U u)ᴴ * M) := by
  classical
  have hconst : (∑ u, (μ u : ℂ) • M) = M := by
    rw [← Finset.sum_smul, ← Complex.ofReal_sum, hμ1, Complex.ofReal_one, one_smul]
  have hJ := stateSqNorm_avg_le hμ0 hμ1 ψ
    (fun u => U u * M * (U u)ᴴ) (fun _ => M) (fun _ => 1) (by simp)
  simp only [mul_one, hconst] at hJ
  refine hJ.trans (le_of_eq ?_)
  unfold stateDist
  apply Finset.sum_congr rfl
  intro u _
  have hUU : U u * (U u)ᴴ = 1 := mul_eq_one_comm.mp (hU u)
  have hdiff : U u * M * (U u)ᴴ - M =
      U u * (M * (U u)ᴴ - (U u)ᴴ * M) := by
    rw [mul_sub, ← Matrix.mul_assoc (U u) (U u)ᴴ M, hUU, Matrix.one_mul,
      Matrix.mul_assoc]
  rw [hdiff, stateSqNorm_mul_of_isometry ψ _ _ (hU u)]

/-- The outcome-summed, question-averaged form, with no alphabet or dimension loss. -/
theorem unitaryTwirl_outcome_dist_le {X A : Type*} [Fintype X] [Fintype A]
    (D : X → ℝ) (hD : ∀ x, 0 ≤ D x)
    (μ : X → I → ℝ) (hμ0 : ∀ x u, 0 ≤ μ x u) (hμ1 : ∀ x, ∑ u, μ x u = 1)
    (U : X → I → Matrix dA dA ℂ) (hU : ∀ x u, (U x u)ᴴ * U x u = 1)
    (ψ : dA × dB → ℂ) (M : X → A → Matrix dA dA ℂ) :
    (∑ x, D x * ∑ a, stateSqNorm ψ (unitaryTwirl (μ x) (U x) (M x a) - M x a)) ≤
      ∑ x, D x * ∑ u, μ x u * ∑ a,
        stateSqNorm ψ (M x a * (U x u)ᴴ - (U x u)ᴴ * M x a) := by
  classical
  calc
    _ ≤ ∑ x, D x * ∑ a, ∑ u, μ x u *
        stateSqNorm ψ (M x a * (U x u)ᴴ - (U x u)ᴴ * M x a) := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (hD x)
      exact Finset.sum_le_sum fun a _ => unitaryTwirl_dist_le (μ x) (hμ0 x) (hμ1 x)
        (U x) (hU x) ψ (M x a)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      congr 1
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun u _ => (Finset.mul_sum _ _ _).symm

end MIPRE.Introspection

end
