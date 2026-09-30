/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.ValueStability
public import MIPRE.Foundations.LocalIsometry

@[expose] public section

/-! # Replacing the state after Pauli extraction

For fixed projective measurements, changing two normalized state vectors by
squared norm `eta` changes every test, and the whole game value, by at most
`2 sqrt(eta)`. This supplies the actual value estimate used with the state
approximation in introspection, in addition to its scalar error absorption.

In a bipartite model the second state is a vector `φ` of the model's Hilbert space, and the model
with its state replaced by it is `Ψ.withState φ` (Phase 4 of `planning/mipco-track.md`).
-/

noncomputable section

namespace MIPRE.Introspection

open Finset
open scoped InnerProductSpace

set_option linter.unusedSectionVars false

section State

variable {𝒞 : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] (Ψ : StateModel 𝒞)
  {C : Type*} [Fintype C] [DecidableEq C]

/-- A contraction's quadratic form is Lipschitz on the unit sphere. -/
theorem qform_state_stability (φ : Ψ.H) (hv : ‖Ψ.ψ‖ = 1) (hw : ‖φ‖ = 1) (R : 𝒞)
    (hR : Ψ.Bnd R 1) :
    |Ψ.qform R - (Ψ.withState φ).qform R| ≤ 2 * ‖Ψ.ψ - φ‖ := by
  have hvR : ‖Ψ.π R Ψ.ψ‖ ≤ 1 := by simpa only [hv, one_mul] using hR Ψ.ψ
  have hdR : ‖Ψ.π R (Ψ.ψ - φ)‖ ≤ ‖Ψ.ψ - φ‖ := by simpa only [one_mul] using hR (Ψ.ψ - φ)
  have h1 : |(⟪Ψ.ψ - φ, Ψ.π R Ψ.ψ⟫_ℂ).re| ≤ ‖Ψ.ψ - φ‖ :=
    (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans
      (by nlinarith [norm_nonneg (Ψ.ψ - φ)]))
  have h2 : |(⟪φ, Ψ.π R (Ψ.ψ - φ)⟫_ℂ).re| ≤ ‖Ψ.ψ - φ‖ := by
    refine (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
    rw [hw, one_mul]
    exact hdR
  have heq : Ψ.qform R - (Ψ.withState φ).qform R =
      (⟪Ψ.ψ - φ, Ψ.π R Ψ.ψ⟫_ℂ).re + (⟪φ, Ψ.π R (Ψ.ψ - φ)⟫_ℂ).re := by
    rw [StateModel.withState_qform]
    show (⟪Ψ.ψ, Ψ.π R Ψ.ψ⟫_ℂ).re - _ = _
    simp only [inner_sub_left, map_sub, inner_sub_right, Complex.sub_re]
    ring
  rw [heq]
  exact (abs_add_le _ _).trans (by linarith)

/-- The accepted effect of any event in a PVM is a contraction. -/
theorem pvm_event_bound {M : C → 𝒞} (hM : IsPVMIn M) (s : Finset C) :
    Ψ.Bnd (∑ c ∈ s, M c) 1 := by
  have hc := hM.coarse (fun c => decide (c ∈ s))
  have hs : univ.filter (fun c => decide (c ∈ s) = true) = s := by ext c; simp
  have hp := hc.isStarProjection true
  rw [hs] at hp
  exact Ψ.bnd_one_of_isStarProjection hp

/-- A change in state changes any PVM event by at most twice the vector distance. -/
theorem pvm_event_state_stability (φ : Ψ.H) (hv : ‖Ψ.ψ‖ = 1) (hw : ‖φ‖ = 1)
    {M : C → 𝒞} (hM : IsPVMIn M) (s : Finset C) :
    |(∑ c ∈ s, Ψ.qform (M c)) - ∑ c ∈ s, (Ψ.withState φ).qform (M c)| ≤ 2 * ‖Ψ.ψ - φ‖ := by
  rw [← Ψ.qform_sum, ← (Ψ.withState φ).qform_sum]
  exact qform_state_stability Ψ φ hv hw _ (pvm_event_bound Ψ hM s)

end State

section Game

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] (Ψ : BipartiteModel 𝒞 𝒜 ℬ)
  {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [DecidableEq A] [Fintype B]
  [DecidableEq B]

/-- State replacement for one concrete decision predicate. -/
theorem testAcceptance_state_stability (φ : Ψ.H) (hΨ : ‖Ψ.ψ‖ = 1) (hφ : ‖φ‖ = 1)
    (D : A → B → Bool) (M : A → 𝒜) (Q : B → ℬ) (hM : IsPVMIn M) (hQ : IsPVMIn Q) {η : ℝ}
    (hd : ‖Ψ.ψ - φ‖ ^ 2 ≤ η) :
    |testAcceptance Ψ D M Q - testAcceptance (Ψ.withState φ) D M Q| ≤ 2 * Real.sqrt η := by
  have h := pvm_event_state_stability Ψ.toStateModel φ hΨ hφ (joint_isPVM Ψ M Q hM hQ)
    (univ.filter fun ab : A × B => D ab.1 ab.2)
  have hn : ‖Ψ.ψ - φ‖ ≤ Real.sqrt η := by
    have ht := Real.sqrt_le_sqrt hd
    rwa [Real.sqrt_sq (norm_nonneg _)] at ht
  have ht := h.trans (mul_le_mul_of_nonneg_left hn (by norm_num : (0 : ℝ) ≤ 2))
  simp only [sum_filter, Fintype.sum_prod_type, ite_mul, one_mul, zero_mul] at ht
  simp only [testAcceptance, BipartiteModel.bornProb, BipartiteModel.withState_πA,
    BipartiteModel.withState_πB, ite_mul, one_mul, zero_mul]
  exact ht

/-- The full normalized question distribution preserves the same state-replacement bound. -/
theorem povmValue_state_stability [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ]
    [StarOrderedRing ℬ] (G : Game X Y A B) (φ : Ψ.H) (hΨ : ‖Ψ.ψ‖ = 1) (hφ : ‖φ‖ = 1)
    (MA : X → POVMIn A 𝒜) (MB : Y → POVMIn B ℬ) (hMA : ∀ x, IsPVMIn (MA x).op)
    (hMB : ∀ y, IsPVMIn (MB y).op) {η : ℝ} (hd : ‖Ψ.ψ - φ‖ ^ 2 ≤ η) :
    |Ψ.povmValue G MA MB - (Ψ.withState φ).povmValue G MA MB| ≤ 2 * Real.sqrt η := by
  have hpoint x y := testAcceptance_state_stability Ψ φ hΨ hφ (G.D x y)
    (fun a => (MA x).op a) (fun b => (MB y).op b) (hMA x) (hMB y) hd
  change ∀ x y, |Ψ.condWin G MA MB x y - (Ψ.withState φ).condWin G MA MB x y| ≤
    2 * Real.sqrt η at hpoint
  have heq : Ψ.povmValue G MA MB - (Ψ.withState φ).povmValue G MA MB =
      ∑ x, ∑ y, G.μ x y * (Ψ.condWin G MA MB x y - (Ψ.withState φ).condWin G MA MB x y) := by
    simp only [BipartiteModel.povmValue, mul_sub, sum_sub_distrib]
  rw [heq]
  calc
    _ ≤ ∑ x, ∑ y, |G.μ x y * (Ψ.condWin G MA MB x y - (Ψ.withState φ).condWin G MA MB x y)| :=
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
theorem povmValue_failure_transfer [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ]
    [StarOrderedRing ℬ] (G : Game X Y A B) (φ : Ψ.H) (hΨ : ‖Ψ.ψ‖ = 1) (hφ : ‖φ‖ = 1)
    (MA : X → POVMIn A 𝒜) (MB : Y → POVMIn B ℬ) (hMA : ∀ x, IsPVMIn (MA x).op)
    (hMB : ∀ y, IsPVMIn (MB y).op) {ε η : ℝ} (hfail : 1 - Ψ.povmValue G MA MB ≤ ε)
    (hd : ‖Ψ.ψ - φ‖ ^ 2 ≤ η) :
    1 - (Ψ.withState φ).povmValue G MA MB ≤ ε + 2 * Real.sqrt η := by
  have h := (abs_le.mp (povmValue_state_stability Ψ G φ hΨ hφ MA MB hMA hMB hd)).2
  linarith

end Game

end MIPRE.Introspection

end

end
