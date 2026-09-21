/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.SamplingTests

/-! # Hiding-test chains after coarse-graining consistency

Coarse-graining is performed on the tests' accepted-answer relations. Only then
are the two cross-party estimates combined into a same-side estimate. This is
the order required to avoid the exponentially large fibre loss discussed in
the paper's corrected proof of `lem:intro-sound-2`.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical

set_option linter.unusedSectionVars false

variable {X Y A B C J H K : Type*}
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype A] [Fintype B] [Fintype C] [DecidableEq C]
  [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

/-- Two measurements consistent with the same opposite-party measurement are close
on their own side. There is no outcome-cardinality factor. -/
theorem same_side_via_common_other (ψ : H × K → ℂ)
    (P Q : C → Matrix H H ℂ) (R : C → Matrix K K ℂ) :
    (∑ z, stateSqNorm ψ (P z - Q z)) ≤
      2 * (∑ z, xSqNorm ψ (P z) (R z)) + 2 * ∑ z, xSqNorm ψ (Q z) (R z) := by
  have h := sum_snorm_sq_triangle' ψ
    (fun z => (aOp (P z) : Matrix (H × K) (H × K) ℂ))
    (fun z => (bOp (R z) : Matrix (H × K) (H × K) ℂ))
    (fun z => (aOp (Q z) : Matrix (H × K) (H × K) ℂ))
  simp_rw [snorm_sub_comm ψ (bOp (R _)) (aOp (Q _))] at h
  simp_rw [← xSqNorm_eq_snorm_sq] at h
  simpa only [← aOp_sub, stateSqNorm, stateNorm, norm_stateVec_eq_snorm] using h

/-- The hiding-same test and the common-type consistency test give the required
same-side marginal relation, with explicit loss `4ε/c₁ + 4ε/c₂`. -/
theorem hiding_same_side_estimate (G : Game X Y A B) (ψ : H × K → ℂ)
    (hψ : star ψ ⬝ᵥ ψ = 1) (MA : X → POVM A H) (MB : Y → POVM B K)
    {ε : ℝ} (hfail : 1 - povmValue G ψ MA MB ≤ ε)
    (D : J → ℝ) (hD : ∀ j, 0 ≤ D j) (q₁ q₂ : J → X × Y)
    (hBob : ∀ j, (q₁ j).2 = (q₂ j).2)
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hpush₁ : ∀ p : X × Y, c₁ * ∑ j ∈ univ.filter (fun j => q₁ j = p), D j ≤ G.μ p.1 p.2)
    (hpush₂ : ∀ p : X × Y, c₂ * ∑ j ∈ univ.filter (fun j => q₂ j = p), D j ≤ G.μ p.1 p.2)
    (f₁ f₂ : J → A → C) (g : J → B → C)
    (hcheck₁ : ∀ j a b, G.D (q₁ j).1 (q₁ j).2 a b = true → f₁ j a = g j b)
    (hcheck₂ : ∀ j a b, G.D (q₂ j).1 (q₂ j).2 a b = true → f₂ j a = g j b) :
    (∑ j, D j * ∑ z, stateSqNorm ψ
      (((((MA (q₁ j).1).map (f₁ j)).mats z).val) -
        ((((MA (q₂ j).1).map (f₂ j)).mats z).val))) ≤ 4 * (ε / c₁) + 4 * (ε / c₂) := by
  have h₁ := agreement_subtest_average G ψ hψ MA MB hfail D hD q₁ hc₁ hpush₁ f₁ g hcheck₁
  have h₂ := agreement_subtest_average G ψ hψ MA MB hfail D hD q₂ hc₂ hpush₂ f₂ g hcheck₂
  have hpoint j := same_side_via_common_other ψ
    (fun z => (((MA (q₁ j).1).map (f₁ j)).mats z).val)
    (fun z => (((MA (q₂ j).1).map (f₂ j)).mats z).val)
    (fun z => (((MB (q₁ j).2).map (g j)).mats z).val)
  have hsum := Finset.sum_le_sum fun j (_ : j ∈ univ) =>
    mul_le_mul_of_nonneg_left (hpoint j) (hD j)
  simp only [mul_add, Finset.sum_add_distrib,
    mul_left_comm (b := (2 : ℝ)), ← Finset.mul_sum] at hsum
  have hcommon : (∑ j, D j * ∑ z, xSqNorm ψ
      ((((MA (q₂ j).1).map (f₂ j)).mats z).val)
      ((((MB (q₁ j).2).map (g j)).mats z).val)) =
      ∑ j, D j * ∑ z, xSqNorm ψ
        ((((MA (q₂ j).1).map (f₂ j)).mats z).val)
        ((((MB (q₂ j).2).map (g j)).mats z).val) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hBob j]
  rw [hcommon] at hsum
  linarith

/-- Telescoping the consecutive differences of a finite operator chain. -/
theorem operator_chain_telescope (P : ℕ → Matrix H H ℂ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (P i - P (i + 1))) = P 0 - P n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; abel

/-- A chain of `n` hiding levels costs `n` times the sum of its squared edge errors. -/
theorem stateSqNorm_hiding_chain (ψ : H × K → ℂ) (P : ℕ → Matrix H H ℂ) (n : ℕ) :
    stateSqNorm ψ (P 0 - P n) ≤
      (n : ℝ) * ∑ i ∈ Finset.range n, stateSqNorm ψ (P i - P (i + 1)) := by
  have h := stateSqNorm_sum_le ψ (fun i : Fin n => P i.val - P (i.val + 1))
  rw [Fin.sum_univ_eq_sum_range (fun i => P i - P (i + 1)) n,
    Fin.sum_univ_eq_sum_range (fun i => stateSqNorm ψ (P i - P (i + 1))) n,
    operator_chain_telescope, Fintype.card_fin] at h
  exact h

/-- The averaged hiding chain, with one error bound per edge and no dependence on the
number of outcomes or sampled question seeds. -/
theorem hiding_chain_average (ψ : H × K → ℂ) (D : J → ℝ) (hD : ∀ j, 0 ≤ D j)
    (P : ℕ → J → C → Matrix H H ℂ) (n : ℕ) (δ : ℕ → ℝ)
    (hstep : ∀ i < n, (∑ j, D j * ∑ z, stateSqNorm ψ (P i j z - P (i + 1) j z)) ≤ δ i) :
    (∑ j, D j * ∑ z, stateSqNorm ψ (P 0 j z - P n j z)) ≤
      (n : ℝ) * ∑ i ∈ Finset.range n, δ i := by
  calc
    _ ≤ ∑ j, D j * ∑ z, (n : ℝ) * ∑ i ∈ Finset.range n,
        stateSqNorm ψ (P i j z - P (i + 1) j z) := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (hD j)
      exact Finset.sum_le_sum fun z _ => stateSqNorm_hiding_chain ψ (fun i => P i j z) n
    _ = (n : ℝ) * ∑ i ∈ Finset.range n,
        ∑ j, D j * ∑ z, stateSqNorm ψ (P i j z - P (i + 1) j z) := by
      simp_rw [← Finset.mul_sum, mul_left_comm (b := (n : ℝ))]
      rw [← Finset.mul_sum]
      congr 1
      simp_rw [Finset.sum_comm (s := (univ : Finset C)) (t := Finset.range n), Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun i hi => hstep i (Finset.mem_range.mp hi)) (Nat.cast_nonneg n)

/-- With a uniform edge bound, the total hiding-chain error is at most `n² δ`. -/
theorem hiding_chain_uniform (ψ : H × K → ℂ) (D : J → ℝ) (hD : ∀ j, 0 ≤ D j)
    (P : ℕ → J → C → Matrix H H ℂ) (n : ℕ) {δ : ℝ}
    (hstep : ∀ i < n, (∑ j, D j * ∑ z, stateSqNorm ψ (P i j z - P (i + 1) j z)) ≤ δ) :
    (∑ j, D j * ∑ z, stateSqNorm ψ (P 0 j z - P n j z)) ≤ (n : ℝ) ^ 2 * δ := by
  have h := hiding_chain_average ψ D hD P n (fun _ => δ) hstep
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, pow_two, mul_assoc] using h

end MIPRE.Introspection

end
