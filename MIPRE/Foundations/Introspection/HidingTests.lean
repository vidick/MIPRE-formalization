/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.SamplingTests

@[expose] public section

/-! # Hiding-test chains after coarse-graining consistency

Coarse-graining is performed on the tests' accepted-answer relations. Only then
are the two cross-party estimates combined into a same-side estimate. This is
the order required to avoid the exponentially large fibre loss discussed in
the paper's corrected proof of `lem:intro-sound-2`.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`).
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Classical

set_option linter.unusedSectionVars false

/-- Telescoping the consecutive differences of a finite operator chain. -/
theorem operator_chain_telescope {R : Type*} [AddCommGroup R] (P : ℕ → R) (n : ℕ) :
    (∑ i ∈ Finset.range n, (P i - P (i + 1))) = P 0 - P n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; abel

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] (Ψ : BipartiteModel 𝒞 𝒜 ℬ)
variable {X Y A B C J : Type*}
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype A] [Fintype B] [Fintype C] [DecidableEq C] [Fintype J] [DecidableEq J]

/-- Two measurements consistent with the same opposite-party measurement are close
on their own side. There is no outcome-cardinality factor. -/
theorem same_side_via_common_other (P Q : C → 𝒜) (R : C → ℬ) :
    (∑ z, Ψ.stateSqNorm (P z - Q z)) ≤
      2 * (∑ z, Ψ.xSqNorm (P z) (R z)) + 2 * ∑ z, Ψ.xSqNorm (Q z) (R z) := by
  have h := Ψ.sum_snorm_sq_triangle univ (fun z => Ψ.πA (P z)) (fun z => Ψ.πB (R z))
    (fun z => Ψ.πA (Q z))
  simp_rw [Ψ.snorm_sub_comm (Ψ.πB (R _)) (Ψ.πA (Q _))] at h
  simpa only [BipartiteModel.xSqNorm, BipartiteModel.xNorm, BipartiteModel.stateSqNorm,
    BipartiteModel.stateNorm, map_sub] using h

/-- The hiding-same test and the common-type consistency test give the required
same-side marginal relation, with explicit loss `4ε/c₁ + 4ε/c₂`. -/
theorem hiding_same_side_estimate [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ]
    [StarOrderedRing ℬ] (G : Game X Y A B) (hΨ : ‖Ψ.ψ‖ = 1)
    (MA : X → POVMIn A 𝒜) (MB : Y → POVMIn B ℬ)
    {ε : ℝ} (hfail : 1 - Ψ.povmValue G MA MB ≤ ε)
    (D : J → ℝ) (hD : ∀ j, 0 ≤ D j) (q₁ q₂ : J → X × Y)
    (hBob : ∀ j, (q₁ j).2 = (q₂ j).2)
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hpush₁ : ∀ p : X × Y, c₁ * ∑ j ∈ univ.filter (fun j => q₁ j = p), D j ≤ G.μ p.1 p.2)
    (hpush₂ : ∀ p : X × Y, c₂ * ∑ j ∈ univ.filter (fun j => q₂ j = p), D j ≤ G.μ p.1 p.2)
    (f₁ f₂ : J → A → C) (g : J → B → C)
    (hcheck₁ : ∀ j a b, G.D (q₁ j).1 (q₁ j).2 a b = true → f₁ j a = g j b)
    (hcheck₂ : ∀ j a b, G.D (q₂ j).1 (q₂ j).2 a b = true → f₂ j a = g j b) :
    (∑ j, D j * ∑ z, Ψ.stateSqNorm
      (((MA (q₁ j).1).map (f₁ j)).op z - ((MA (q₂ j).1).map (f₂ j)).op z)) ≤
        4 * (ε / c₁) + 4 * (ε / c₂) := by
  have h₁ := agreement_subtest_average Ψ G hΨ MA MB hfail D hD q₁ hc₁ hpush₁ f₁ g hcheck₁
  have h₂ := agreement_subtest_average Ψ G hΨ MA MB hfail D hD q₂ hc₂ hpush₂ f₂ g hcheck₂
  have hpoint j := same_side_via_common_other Ψ
    (fun z => ((MA (q₁ j).1).map (f₁ j)).op z)
    (fun z => ((MA (q₂ j).1).map (f₂ j)).op z)
    (fun z => ((MB (q₁ j).2).map (g j)).op z)
  have hsum := Finset.sum_le_sum fun j (_ : j ∈ univ) =>
    mul_le_mul_of_nonneg_left (hpoint j) (hD j)
  simp only [mul_add, Finset.sum_add_distrib,
    mul_left_comm (b := (2 : ℝ)), ← Finset.mul_sum] at hsum
  have hcommon : (∑ j, D j * ∑ z, Ψ.xSqNorm
      (((MA (q₂ j).1).map (f₂ j)).op z) (((MB (q₁ j).2).map (g j)).op z)) =
      ∑ j, D j * ∑ z, Ψ.xSqNorm
        (((MA (q₂ j).1).map (f₂ j)).op z) (((MB (q₂ j).2).map (g j)).op z) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hBob j]
  rw [hcommon] at hsum
  linarith

/-- A chain of `n` hiding levels costs `n` times the sum of its squared edge errors. -/
theorem stateSqNorm_hiding_chain (P : ℕ → 𝒜) (n : ℕ) :
    Ψ.stateSqNorm (P 0 - P n) ≤
      (n : ℝ) * ∑ i ∈ Finset.range n, Ψ.stateSqNorm (P i - P (i + 1)) := by
  have h := Ψ.stateSqNorm_sum_le (fun i : Fin n => P i.val - P (i.val + 1))
  rw [Fin.sum_univ_eq_sum_range (fun i => P i - P (i + 1)) n,
    Fin.sum_univ_eq_sum_range (fun i => Ψ.stateSqNorm (P i - P (i + 1))) n,
    operator_chain_telescope, Fintype.card_fin] at h
  exact h

/-- The averaged hiding chain, with one error bound per edge and no dependence on the
number of outcomes or sampled question seeds. -/
theorem hiding_chain_average (D : J → ℝ) (hD : ∀ j, 0 ≤ D j)
    (P : ℕ → J → C → 𝒜) (n : ℕ) (δ : ℕ → ℝ)
    (hstep : ∀ i < n, (∑ j, D j * ∑ z, Ψ.stateSqNorm (P i j z - P (i + 1) j z)) ≤ δ i) :
    (∑ j, D j * ∑ z, Ψ.stateSqNorm (P 0 j z - P n j z)) ≤
      (n : ℝ) * ∑ i ∈ Finset.range n, δ i := by
  calc
    _ ≤ ∑ j, D j * ∑ z, (n : ℝ) * ∑ i ∈ Finset.range n,
        Ψ.stateSqNorm (P i j z - P (i + 1) j z) := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (hD j)
      exact Finset.sum_le_sum fun z _ => stateSqNorm_hiding_chain Ψ (fun i => P i j z) n
    _ = (n : ℝ) * ∑ i ∈ Finset.range n,
        ∑ j, D j * ∑ z, Ψ.stateSqNorm (P i j z - P (i + 1) j z) := by
      simp_rw [← Finset.mul_sum, mul_left_comm (b := (n : ℝ))]
      rw [← Finset.mul_sum]
      congr 1
      simp_rw [Finset.sum_comm (s := (univ : Finset C)) (t := Finset.range n), Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun i hi => hstep i (Finset.mem_range.mp hi)) (Nat.cast_nonneg n)

/-- With a uniform edge bound, the total hiding-chain error is at most `n² δ`. -/
theorem hiding_chain_uniform (D : J → ℝ) (hD : ∀ j, 0 ≤ D j)
    (P : ℕ → J → C → 𝒜) (n : ℕ) {δ : ℝ}
    (hstep : ∀ i < n, (∑ j, D j * ∑ z, Ψ.stateSqNorm (P i j z - P (i + 1) j z)) ≤ δ) :
    (∑ j, D j * ∑ z, Ψ.stateSqNorm (P 0 j z - P n j z)) ≤ (n : ℝ) ^ 2 * δ := by
  have h := hiding_chain_average Ψ D hD P n (fun _ => δ) hstep
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, pow_two, mul_assoc] using h

end MIPRE.Introspection

end

end
