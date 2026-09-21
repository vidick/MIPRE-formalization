/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.ValueStability

/-! # Replacing the state after Pauli extraction

For fixed projective measurements, changing two normalized state vectors by
squared norm `eta` changes every test, and the whole game value, by at most
`2 sqrt(eta)`. This supplies the actual value estimate used with the state
approximation in introspection, in addition to its scalar error absorption.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder

set_option linter.unusedSectionVars false

variable {N C : Type*} [Fintype N] [DecidableEq N] [Fintype C] [DecidableEq C]

/-- A contraction's quadratic form is Lipschitz on the unit sphere. -/
theorem qform_state_stability (v w : N → ℂ) (hv : ‖evec v‖ = 1) (hw : ‖evec w‖ = 1)
    (R : Matrix N N ℂ) (hR : Bnd R 1) :
    |qform v R - qform w R| ≤ 2 * ‖evec (v - w)‖ := by
  have hcs (x y : N → ℂ) : |(star x ⬝ᵥ y).re| ≤ ‖evec x‖ * ‖evec y‖ := by
    rw [← inner_evec]
    exact (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
  have hvR : ‖evec (R *ᵥ v)‖ ≤ 1 := by simpa only [hv, one_mul] using hR v
  have hdR : ‖evec (R *ᵥ (v - w))‖ ≤ ‖evec (v - w)‖ := by
    simpa only [one_mul] using hR (v - w)
  have h1 : |(star (v - w) ⬝ᵥ (R *ᵥ v)).re| ≤ ‖evec (v - w)‖ :=
    (hcs _ _).trans (by nlinarith [norm_nonneg (evec (v - w))])
  have h2 : |(star w ⬝ᵥ (R *ᵥ (v - w))).re| ≤ ‖evec (v - w)‖ := by
    have h := hcs w (R *ᵥ (v - w))
    rw [hw, one_mul] at h
    exact h.trans hdR
  have heq : qform v R - qform w R =
      (star (v - w) ⬝ᵥ (R *ᵥ v)).re + (star w ⬝ᵥ (R *ᵥ (v - w))).re := by
    simp only [qform, star_sub, sub_dotProduct, Matrix.mulVec_sub,
      dotProduct_sub, Complex.sub_re]
    ring
  rw [heq]
  exact (abs_add_le _ _).trans (by linarith)

/-- The accepted effect of any event in a PVM is a contraction. -/
theorem pvm_event_bound {M : C → Matrix N N ℂ} (hM : IsPVM M) (s : Finset C) :
    Bnd (∑ c ∈ s, M c) 1 := by
  have hc := hM.coarse (fun c => decide (c ∈ s))
  have hs : univ.filter (fun c => decide (c ∈ s) = true) = s := by ext c; simp
  have hsa := hc.isSelfAdjoint true
  have hid := hc.idem true
  rw [hs] at hsa hid
  apply bnd_one_of_conjTranspose_mul_self_le
  rw [hsa, hid]
  exact proj_le_one hsa hid

/-- A change in state changes any PVM event by at most twice the vector distance. -/
theorem pvm_event_state_stability (v w : N → ℂ)
    (hv : ‖evec v‖ = 1) (hw : ‖evec w‖ = 1)
    {M : C → Matrix N N ℂ} (hM : IsPVM M) (s : Finset C) :
    |(∑ c ∈ s, qform v (M c)) - ∑ c ∈ s, qform w (M c)| ≤ 2 * ‖evec (v - w)‖ := by
  rw [← qform_sum, ← qform_sum]
  exact qform_state_stability v w hv hw _ (pvm_event_bound hM s)

section Game

variable {X Y A B H K : Type*} [Fintype X] [Fintype Y]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

/-- State replacement for one concrete decision predicate. -/
theorem testAcceptance_state_stability (ψ φ : H × K → ℂ)
    (hψ : ‖evec ψ‖ = 1) (hφ : ‖evec φ‖ = 1)
    (D : A → B → Bool) (M : A → Matrix H H ℂ) (Q : B → Matrix K K ℂ)
    (hM : IsPVM M) (hQ : IsPVM Q) {η : ℝ} (hd : ‖evec (ψ - φ)‖ ^ 2 ≤ η) :
    |testAcceptance ψ D M Q - testAcceptance φ D M Q| ≤ 2 * Real.sqrt η := by
  have h := pvm_event_state_stability ψ φ hψ hφ (joint_isPVM M Q hM hQ)
    (univ.filter fun ab : A × B => D ab.1 ab.2)
  have hn : ‖evec (ψ - φ)‖ ≤ Real.sqrt η := by
    have ht := Real.sqrt_le_sqrt hd
    rwa [Real.sqrt_sq (norm_nonneg _)] at ht
  have ht := h.trans (mul_le_mul_of_nonneg_left hn (by norm_num : (0 : ℝ) ≤ 2))
  simpa only [sum_filter, Fintype.sum_prod_type, testAcceptance, qform, bornProb,
    ite_mul, one_mul, zero_mul] using ht

/-- The full normalized question distribution preserves the same state-replacement bound. -/
theorem povmValue_state_stability (G : Game X Y A B) (ψ φ : H × K → ℂ)
    (hψ : ‖evec ψ‖ = 1) (hφ : ‖evec φ‖ = 1)
    (MA : X → POVM A H) (MB : Y → POVM B K)
    (hMA : ∀ x, IsPVM (fun a => ((MA x).mats a).val))
    (hMB : ∀ y, IsPVM (fun b => ((MB y).mats b).val))
    {η : ℝ} (hd : ‖evec (ψ - φ)‖ ^ 2 ≤ η) :
    |povmValue G ψ MA MB - povmValue G φ MA MB| ≤ 2 * Real.sqrt η := by
  have hpoint x y := testAcceptance_state_stability ψ φ hψ hφ (G.D x y)
    (fun a => ((MA x).mats a).val) (fun b => ((MB y).mats b).val) (hMA x) (hMB y) hd
  change ∀ x y, |condWin G ψ MA MB x y - condWin G φ MA MB x y| ≤
    2 * Real.sqrt η at hpoint
  have heq : povmValue G ψ MA MB - povmValue G φ MA MB =
      ∑ x, ∑ y, G.μ x y * (condWin G ψ MA MB x y - condWin G φ MA MB x y) := by
    simp only [povmValue, mul_sub, sum_sub_distrib]
  rw [heq]
  calc
    _ ≤ ∑ x, ∑ y, |G.μ x y * (condWin G ψ MA MB x y - condWin G φ MA MB x y)| :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ x, ∑ y, G.μ x y * (2 * Real.sqrt η) := by
      apply sum_le_sum
      intro x _
      apply sum_le_sum
      intro y _
      rw [abs_mul, abs_of_nonneg (G.μ_nonneg x y)]
      exact mul_le_mul_of_nonneg_left (hpoint x y) (G.μ_nonneg x y)
    _ = _ := by
      simp_rw [← sum_mul]
      rw [G.μ_sum_one, one_mul]

/-- Transfer a game's failure bound to the nearby ideal state. -/
theorem povmValue_failure_transfer (G : Game X Y A B) (ψ φ : H × K → ℂ)
    (hψ : ‖evec ψ‖ = 1) (hφ : ‖evec φ‖ = 1)
    (MA : X → POVM A H) (MB : Y → POVM B K)
    (hMA : ∀ x, IsPVM (fun a => ((MA x).mats a).val))
    (hMB : ∀ y, IsPVM (fun b => ((MB y).mats b).val))
    {ε η : ℝ} (hfail : 1 - povmValue G ψ MA MB ≤ ε)
    (hd : ‖evec (ψ - φ)‖ ^ 2 ≤ η) :
    1 - povmValue G φ MA MB ≤ ε + 2 * Real.sqrt η := by
  have h := (abs_le.mp (povmValue_state_stability G ψ φ hψ hφ MA MB hMA hMB hd)).2
  linarith

end Game

end MIPRE.Introspection

end
