/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.LinearMeasurement

/-! # Commutation of the sampling and hiding measurements -/

noncomputable section

namespace MIPRE.Introspection

open Finset Weyl Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ}

theorem synOf_eq_zero_of_not_mem_range
    (w : (Fin n → F) → Matrix (Fin n → F) (Fin n → F) ℂ)
    (L : (Fin n → F) →ₗ[F] (Fin n → F)) (a : Fin n → F) (ha : a ∉ L.range) :
    synOf w L a = 0 := by
  apply Finset.sum_eq_zero
  intro e he
  exact (ha ⟨e, (Finset.mem_filter.mp he).2⟩).elim

theorem commute_matrix_smul {ι : Type*} [Fintype ι]
    {A B : Matrix ι ι ℂ} (h : Commute A B) (c d : ℂ) : Commute (c • A) (d • B) := by
  change (c • A) * (d • B) = (d • B) * (c • A)
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [h.eq, mul_comm c d]

/-- The perpendicular-kernel inclusion makes every sampling projector commute with every
hiding projector, including zero projectors at outcomes outside the ranges. -/
theorem linear_measurements_commute
    (L R : (Fin n → F) →ₗ[F] (Fin n → F)) (hLR : CL.perp R.ker ≤ L.ker)
    (a b : Fin n → F) : Commute (synOf wZ L a) (synOf wX R b) := by
  by_cases ha : a ∈ L.range
  swap
  · rw [synOf_eq_zero_of_not_mem_range _ L a ha]
    exact Commute.zero_left _
  by_cases hb : b ∈ R.range
  swap
  · rw [synOf_eq_zero_of_not_mem_range _ R b hb]
    exact Commute.zero_right _
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  rw [← linear_measurement_fourier_inverse wZ L x, ← linear_measurement_fourier_inverse wX R y]
  apply commute_matrix_smul
  apply Commute.sum_left
  intro v _
  apply Commute.sum_right
  intro u _
  apply commute_matrix_smul
  have hp : trDot u.1 v.1 = 0 := by
    rw [trDot, (CL.mem_perp.mp v.2) u.1 (hLR u.2), map_zero]
  exact (wX_mul_wZ_of_eq u.1 v.1 hp).symm

end MIPRE.Introspection

end
