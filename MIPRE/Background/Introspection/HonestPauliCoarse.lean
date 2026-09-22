/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.HonestPauliMeasurements

/-! # Exact coarse-measurement algebra for honest Pauli edges -/

noncomputable section

namespace MIPRE.QLD.Honest

open Matrix Finset Introspection Classical
open scoped Kronecker

section General
variable {I X Y A B : Type*} [Fintype I] [DecidableEq I]
  [Fintype X] [Fintype Y] [DecidableEq A] [DecidableEq B]

omit [DecidableEq I] in
theorem fibre_commute (M : X → Matrix I I ℂ) (N : Y → Matrix I I ℂ)
    (f : X → A) (g : Y → B) (hc : ∀ x y, Commute (M x) (N y)) (a : A) (b : B) :
    Commute (fibSum M f a) (fibSum N g b) := by
  unfold fibSum
  exact Commute.sum_left _ _ _ (fun x _ => Commute.sum_right _ _ _ (fun y _ => hc x y))

omit [DecidableEq I] in
theorem fibre_reject (M : X → Matrix I I ℂ) (N : Y → Matrix I I ℂ)
    (f : X → A) (g : Y → B) (D : A → B → Bool)
    (hz : ∀ x y, D (f x) (g y) = false → M x * N y = 0)
    (a : A) (b : B) (hr : D a b = false) : fibSum M f a * fibSum N g b = 0 := by
  unfold fibSum
  rw [Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro y hy
  exact hz x y (by simpa only [(Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hy).2] using hr)

theorem pvm_fibre_commute (P : X → Matrix I I ℂ) (hP : IsPVM P)
    (f : X → A) (g : X → B) (a : A) (b : B) :
    Commute (fibSum P f a) (fibSum P g b) := by
  apply fibre_commute
  intro x y
  by_cases h : x = y
  · subst y; exact Commute.refl _
  · change P x * P y = P y * P x
    rw [hP.orthogonal h, hP.orthogonal (Ne.symm h)]

theorem pvm_fibre_reject (P : X → Matrix I I ℂ) (hP : IsPVM P)
    (f : X → A) (g : X → B) (D : A → B → Bool)
    (hgood : ∀ x, D (f x) (g x) = true) (a : A) (b : B) (hr : D a b = false) :
    fibSum P f a * fibSum P g b = 0 := by
  apply fibre_reject P P f g D _ a b hr
  intro x y hxy
  by_cases h : x = y
  · subst y; rw [hgood] at hxy; contradiction
  · exact hP.orthogonal h

omit [Fintype I] in
theorem readout_constant (x₀ x : A) :
    readout (fun _ : I => x₀) x = if x₀ = x then (1 : Matrix I I ℂ) else 0 := by
  by_cases h : x₀ = x <;> simp [readout, h]

theorem readout_constant_commute (x₀ x : A) (M : Matrix I I ℂ) :
    Commute (readout (fun _ : I => x₀) x) M := by
  rw [readout_constant]
  split_ifs
  · exact Commute.one_left _
  · exact Commute.zero_left _

omit [Fintype I] [DecidableEq I] in
theorem fibre_comp [Fintype A] (P : X → Matrix I I ℂ) (f : X → A) (g : A → B) (b : B) :
    fibSum (fibSum P f) g b = fibSum P (fun x => g (f x)) b := by
  have hm : ∀ x ∈ univ.filter (fun x => g (f x) = b),
      f x ∈ univ.filter (fun a => g a = b) :=
    fun x hx => Finset.mem_filter.mpr ⟨mem_univ _, (Finset.mem_filter.mp hx).2⟩
  have hf : ∀ a ∈ univ.filter (fun a => g a = b),
      (univ.filter (fun x => g (f x) = b)).filter (fun x => f x = a) =
        univ.filter (fun x => f x = a) := by
    intro a ha
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro x _
    constructor
    · exact And.right
    · intro hx
      exact ⟨by rw [hx]; exact (Finset.mem_filter.mp ha).2, hx⟩
  unfold fibSum
  rw [← Finset.sum_fiberwise_of_maps_to hm P]
  exact Finset.sum_congr rfl fun a ha => by rw [hf a ha]
end General

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m : ℕ}

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] in
theorem liftOp_fibSum {X A : Type*} [Fintype X] [DecidableEq A]
    (P : X → Matrix (Register F m) (Register F m) ℂ) (f : X → A) (a : A) :
    liftOp (fibSum P f a) = fibSum (fun x => liftOp (P x)) f a := by
  simp only [liftOp, fibSum, sum_kronecker_left]

theorem probeLift_eq_fibSum (ω : Omega F m) (W : Bas) :
    probeLift ω W = fibSum (pauliLift W) (probeLabel ω W) := by
  funext b
  exact liftOp_fibSum _ _ b

end MIPRE.QLD.Honest
