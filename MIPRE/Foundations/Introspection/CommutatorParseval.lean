/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.Commutation
import MIPRE.Foundations.Parseval

/-! # Parseval for commutators with linear-map readouts

The character transform on the kernel's perpendicular identifies the outcome-summed
commutator error of a linear-map measurement with the uniformly averaged error of its
Pauli observables. This proves the characteristic-two form of the paper's `lem:W`.
The identity holds on every state, with ancillary spaces and empty fibres allowed.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Weyl Matrix Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ} {N : Type*} [Fintype N]

local instance : CharP F 2 := charP_of_injective_algebraMap' (ZMod 2) 2

/-- A chosen preimage maps to its target whenever the target lies in the range. -/
theorem linearPreimage_mem_range (L : (Fin n → F) →ₗ[F] (Fin n → F))
    {y : Fin n → F} (hy : y ∈ L.range) : L (linearPreimage L y) = y := by
  obtain ⟨x, rfl⟩ := hy
  exact linearPreimage_image L x

/-- Distinct nonempty fibres have orthogonal characters on the kernel's perpendicular. -/
theorem sum_linear_fiber_sign (L : (Fin n → F) →ₗ[F] (Fin n → F))
    {a b : Fin n → F} (ha : a ∈ L.range) (hb : b ∈ L.range) :
    (∑ v : CL.perp L.ker, sgn (trDot v.1 (linearPreimage L a + linearPreimage L b))) =
      if a = b then (Fintype.card (CL.perp L.ker) : ℂ) else 0 := by
  rw [sum_subspace_sign, CL.perp_perp]
  have h : linearPreimage L a + linearPreimage L b ∈ L.ker ↔ a = b := by
    rw [LinearMap.mem_ker, map_add, linearPreimage_mem_range L ha,
      linearPreimage_mem_range L hb, Weyl.add_eq_zero_iff_vec]
  simp only [h]

/-- Parseval for vector families supported on the range of a linear map. -/
theorem sum_norm_linearFourier_sq
    (L : (Fin n → F) →ₗ[F] (Fin n → F)) (T : (Fin n → F) → (N → ℂ))
    (hT : ∀ y, y ∉ L.range → T y = 0) :
    (Fintype.card (CL.perp L.ker) : ℝ)⁻¹ *
        (∑ v : CL.perp L.ker, ‖evec (∑ y : Fin n → F,
          sgn (trDot v.1 (linearPreimage L y)) • T y)‖ ^ 2) =
      ∑ y : Fin n → F, ‖evec (T y)‖ ^ 2 := by
  let G (v : CL.perp L.ker) : N → ℂ :=
    ∑ y : Fin n → F, sgn (trDot v.1 (linearPreimage L y)) • T y
  have hexpand (v : CL.perp L.ker) : star (G v) ⬝ᵥ G v =
      ∑ a : Fin n → F, ∑ b : Fin n → F,
        sgn (trDot v.1 (linearPreimage L a + linearPreimage L b)) *
          (star (T a) ⬝ᵥ T b) := by
    dsimp only [G]
    rw [star_sum, sum_dotProduct]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [dotProduct_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [star_smul, star_sgn, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      smul_eq_mul, trDot_add_right, sgn_add, mul_assoc]
  have hdiag (a b : Fin n → F) :
      (∑ v : CL.perp L.ker,
        sgn (trDot v.1 (linearPreimage L a + linearPreimage L b))) *
          (star (T a) ⬝ᵥ T b) =
      if a = b then (Fintype.card (CL.perp L.ker) : ℂ) * (star (T a) ⬝ᵥ T a)
      else 0 := by
    by_cases ha : a ∈ L.range
    · by_cases hb : b ∈ L.range
      · rw [sum_linear_fiber_sign L ha hb]
        split_ifs with hab
        · subst b; rfl
        · exact zero_mul _
      · rw [hT b hb]
        by_cases hab : a = b
        · exact False.elim (hb (hab ▸ ha))
        · simp [hab]
    · rw [hT a ha]
      simp
  have hsum : (∑ v : CL.perp L.ker, star (G v) ⬝ᵥ G v) =
      (Fintype.card (CL.perp L.ker) : ℂ) * ∑ a : Fin n → F, star (T a) ⬝ᵥ T a := by
    simp_rw [hexpand]
    rw [Finset.sum_comm]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hdiag]
    simp
  have hreal : (∑ v : CL.perp L.ker, ‖evec (G v)‖ ^ 2) =
      (Fintype.card (CL.perp L.ker) : ℝ) * ∑ a : Fin n → F, ‖evec (T a)‖ ^ 2 := by
    simp_rw [dotProduct_star_self] at hsum
    exact_mod_cast hsum
  change (Fintype.card (CL.perp L.ker) : ℝ)⁻¹ * (∑ v, ‖evec (G v)‖ ^ 2) = _
  rw [hreal, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact_mod_cast (Fintype.card_pos (α := CL.perp L.ker)).ne'

/-- The readout/observable Parseval identity after any linear action on vectors. -/
theorem linear_measurement_parseval
    (w : (Fin n → F) → Matrix (Fin n → F) (Fin n → F) ℂ)
    (L : (Fin n → F) →ₗ[F] (Fin n → F))
    (f : Matrix (Fin n → F) (Fin n → F) ℂ →ₗ[ℂ] (N → ℂ)) :
    (∑ y : Fin n → F, ‖evec (f (synOf w L y))‖ ^ 2) =
      (Fintype.card (CL.perp L.ker) : ℝ)⁻¹ *
        (∑ v : CL.perp L.ker, ‖evec (f (w v.1))‖ ^ 2) := by
  have h := sum_norm_linearFourier_sq L (fun y => f (synOf w L y))
    (fun y hy => by rw [synOf_eq_zero_of_not_mem_range w L y hy, map_zero])
  have hv (v : CL.perp L.ker) : f (w v.1) =
      ∑ y : Fin n → F, sgn (trDot v.1 (linearPreimage L y)) • f (synOf w L y) := by
    rw [linear_measurement_fourier w L v.1 v.2, map_sum]
    simp only [map_smul]
  simpa only [hv] using h.symm

variable {H B : Type*} [Fintype H] [DecidableEq H] [Fintype B] [DecidableEq B]

/-- Commute a register operator with `M` and apply the result to a bipartite state. -/
def commutatorAction (ψ : ((Fin n → F) × H) × B → ℂ)
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) :
    Matrix (Fin n → F) (Fin n → F) ℂ →ₗ[ℂ] (((Fin n → F) × H) × B → ℂ) where
  toFun P := aOp (M * aOp P - aOp P * M) *ᵥ ψ
  map_add' P Q := by
    simp only [aOp_add, mul_add, add_mul, add_sub_add_comm, Matrix.add_mulVec]
  map_smul' c P := by
    simp only [aOp_smul, Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, Matrix.smul_mulVec,
      RingHom.id_apply]

/-- `lem:W`: the two commutator errors agree exactly, without a dimension factor. -/
theorem linear_measurement_commutator_parseval
    (w : (Fin n → F) → Matrix (Fin n → F) (Fin n → F) ℂ)
    (L : (Fin n → F) →ₗ[F] (Fin n → F))
    (ψ : ((Fin n → F) × H) × B → ℂ)
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) :
    (∑ y : Fin n → F, stateSqNorm ψ
      (M * aOp (synOf w L y) - aOp (synOf w L y) * M)) =
    (Fintype.card (CL.perp L.ker) : ℝ)⁻¹ *
      ∑ v : CL.perp L.ker, stateSqNorm ψ (M * aOp (w v.1) - aOp (w v.1) * M) :=
  linear_measurement_parseval w L (commutatorAction ψ M)

/-- The same identity summed over outcomes and averaged over questions. -/
theorem linear_measurement_commutator_parseval_avg
    {X A : Type*} [Fintype X] [Fintype A]
    (D : X → ℝ)
    (w : (Fin n → F) → Matrix (Fin n → F) (Fin n → F) ℂ)
    (L : X → (Fin n → F) →ₗ[F] (Fin n → F))
    (ψ : ((Fin n → F) × H) × B → ℂ)
    (M : X → A → Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) :
    (∑ x, D x * ∑ a, ∑ y : Fin n → F, stateSqNorm ψ
      (M x a * aOp (synOf w (L x) y) - aOp (synOf w (L x) y) * M x a)) =
    ∑ x, D x * ((Fintype.card (CL.perp (L x).ker) : ℝ)⁻¹ *
      ∑ v : CL.perp (L x).ker, ∑ a,
        stateSqNorm ψ (M x a * aOp (w v.1) - aOp (w v.1) * M x a)) := by
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  simp_rw [linear_measurement_commutator_parseval]
  rw [← Finset.mul_sum, Finset.sum_comm]

end MIPRE.Introspection

end
