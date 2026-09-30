/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.StateDistance

@[expose] public section

/-! # Approximate commutation controls twirling in the state-dependent norm

This is the paper's `lem:mixing-U`, with constant one and all outcome sums explicit.
The state need not be invariant under any of the unitaries.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`), for unitaries and operators
of the first player's algebra. The unitaries are unitary on both sides: in infinite dimension an
isometry `U* U = 1` need not have `U U* = 1`, which the matrix proof took from finite
dimension.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] (Ψ : BipartiteModel 𝒞 𝒜 ℬ)
  {I : Type*} [Fintype I]

/-- Left multiplication by an isometry preserves the state-dependent squared norm. -/
theorem stateSqNorm_mul_of_isometry (U M : 𝒜) (hU : star U * U = 1) :
    Ψ.stateSqNorm (U * M) = Ψ.stateSqNorm M := by
  have h : star (Ψ.πA U) * Ψ.πA U = 1 := by rw [← map_star, ← map_mul, hU, map_one]
  simp only [BipartiteModel.stateSqNorm, BipartiteModel.stateNorm, map_mul,
    Ψ.snorm_mul_of_isometry h]

/-- Twirling against a finitely supported probability distribution. -/
def unitaryTwirl (μ : I → ℝ) (U : I → 𝒜) (M : 𝒜) : 𝒜 :=
  ∑ u, (μ u : ℂ) • (U u * M * star (U u))

/-- Jensen and left-unitary invariance bound the twirl error by the commutator error. -/
theorem unitaryTwirl_dist_le (μ : I → ℝ) (hμ0 : ∀ u, 0 ≤ μ u) (hμ1 : ∑ u, μ u = 1)
    (U : I → 𝒜) (hU : ∀ u, star (U u) * U u = 1) (hU' : ∀ u, U u * star (U u) = 1) (M : 𝒜) :
    Ψ.stateSqNorm (unitaryTwirl μ U M - M) ≤
      ∑ u, μ u * Ψ.stateSqNorm (M * star (U u) - star (U u) * M) := by
  classical
  have hconst : (∑ u, (μ u : ℂ) • M) = M := by
    rw [← Finset.sum_smul, ← Complex.ofReal_sum, hμ1, Complex.ofReal_one, one_smul]
  have hJ := Ψ.stateSqNorm_avg_le hμ0 hμ1
    (fun u => U u * M * star (U u)) (fun _ => M) (fun _ => 1) (by simp)
  simp only [mul_one, hconst] at hJ
  refine hJ.trans (le_of_eq ?_)
  unfold BipartiteModel.stateDist
  apply Finset.sum_congr rfl
  intro u _
  have hUU : U u * star (U u) = 1 := hU' u
  have hdiff : U u * M * star (U u) - M = U u * (M * star (U u) - star (U u) * M) := by
    rw [mul_sub, ← mul_assoc (U u) (star (U u)) M, hUU, one_mul, mul_assoc]
  rw [hdiff, stateSqNorm_mul_of_isometry Ψ _ _ (hU u)]

/-- The outcome-summed, question-averaged form, with no alphabet or dimension loss. -/
theorem unitaryTwirl_outcome_dist_le {X A : Type*} [Fintype X] [Fintype A]
    (D : X → ℝ) (hD : ∀ x, 0 ≤ D x)
    (μ : X → I → ℝ) (hμ0 : ∀ x u, 0 ≤ μ x u) (hμ1 : ∀ x, ∑ u, μ x u = 1)
    (U : X → I → 𝒜) (hU : ∀ x u, star (U x u) * U x u = 1)
    (hU' : ∀ x u, U x u * star (U x u) = 1) (M : X → A → 𝒜) :
    (∑ x, D x * ∑ a, Ψ.stateSqNorm (unitaryTwirl (μ x) (U x) (M x a) - M x a)) ≤
      ∑ x, D x * ∑ u, μ x u * ∑ a,
        Ψ.stateSqNorm (M x a * star (U x u) - star (U x u) * M x a) := by
  classical
  calc
    _ ≤ ∑ x, D x * ∑ a, ∑ u, μ x u *
        Ψ.stateSqNorm (M x a * star (U x u) - star (U x u) * M x a) := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (hD x)
      exact Finset.sum_le_sum fun a _ => unitaryTwirl_dist_le Ψ (μ x) (hμ0 x) (hμ1 x)
        (U x) (hU x) (hU' x) (M x a)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      congr 1
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun u _ => (Finset.mul_sum _ _ _).symm

end MIPRE.Introspection

end

end
