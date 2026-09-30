/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.Commutation
public import MIPRE.Foundations.Parseval
public import MIPRE.Foundations.AncillaModel

@[expose] public section

/-! # Parseval for commutators with linear-map readouts

The character transform on the kernel's perpendicular identifies the outcome-summed
commutator error of a linear-map measurement with the uniformly averaged error of its
Pauli observables. This proves the characteristic-two form of the paper's `lem:W`.
The identity holds on every state, with ancillary spaces and empty fibres allowed.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`) whose first player's algebra
carries the register, `Matrix (Fin n → F) (Fin n → F) 𝒜`, with a register operator `P` acting as
`smulKron 1 P`, and Parseval in any complex inner product space.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Weyl Matrix Classical
open scoped InnerProductSpace

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

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

/-- Parseval for vector families supported on the range of a linear map, in any complex inner
product space. -/
theorem sum_norm_linearFourier_sq
    (L : (Fin n → F) →ₗ[F] (Fin n → F)) (T : (Fin n → F) → E)
    (hT : ∀ y, y ∉ L.range → T y = 0) :
    (Fintype.card (CL.perp L.ker) : ℝ)⁻¹ *
        (∑ v : CL.perp L.ker, ‖∑ y : Fin n → F,
          sgn (trDot v.1 (linearPreimage L y)) • T y‖ ^ 2) =
      ∑ y : Fin n → F, ‖T y‖ ^ 2 := by
  let G (v : CL.perp L.ker) : E :=
    ∑ y : Fin n → F, sgn (trDot v.1 (linearPreimage L y)) • T y
  have hexpand (v : CL.perp L.ker) : ⟪G v, G v⟫_ℂ =
      ∑ a : Fin n → F, ∑ b : Fin n → F,
        sgn (trDot v.1 (linearPreimage L a + linearPreimage L b)) * ⟪T a, T b⟫_ℂ := by
    dsimp only [G]
    rw [sum_inner]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [inner_smul_left, inner_smul_right, ← RCLike.star_def, star_sgn, trDot_add_right, sgn_add,
      mul_assoc]
  have hdiag (a b : Fin n → F) :
      (∑ v : CL.perp L.ker,
        sgn (trDot v.1 (linearPreimage L a + linearPreimage L b))) * ⟪T a, T b⟫_ℂ =
      if a = b then (Fintype.card (CL.perp L.ker) : ℂ) * ⟪T a, T a⟫_ℂ else 0 := by
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
  have hsum : (∑ v : CL.perp L.ker, ⟪G v, G v⟫_ℂ) =
      (Fintype.card (CL.perp L.ker) : ℂ) * ∑ a : Fin n → F, ⟪T a, T a⟫_ℂ := by
    simp_rw [hexpand]
    rw [Finset.sum_comm]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hdiag]
    simp
  have hreal : (∑ v : CL.perp L.ker, ‖G v‖ ^ 2) =
      (Fintype.card (CL.perp L.ker) : ℝ) * ∑ a : Fin n → F, ‖T a‖ ^ 2 := by
    have h := congrArg Complex.re hsum
    simp only [Complex.re_sum, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul,
      sub_zero] at h
    simpa only [← RCLike.re_to_complex, inner_self_eq_norm_sq] using h
  change (Fintype.card (CL.perp L.ker) : ℝ)⁻¹ * (∑ v, ‖G v‖ ^ 2) = _
  rw [hreal, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact_mod_cast (Fintype.card_pos (α := CL.perp L.ker)).ne'

/-- The readout/observable Parseval identity after any linear action on vectors. -/
theorem linear_measurement_parseval
    (w : (Fin n → F) → Matrix (Fin n → F) (Fin n → F) ℂ)
    (L : (Fin n → F) →ₗ[F] (Fin n → F))
    (f : Matrix (Fin n → F) (Fin n → F) ℂ →ₗ[ℂ] E) :
    (∑ y : Fin n → F, ‖f (synOf w L y)‖ ^ 2) =
      (Fintype.card (CL.perp L.ker) : ℝ)⁻¹ *
        (∑ v : CL.perp L.ker, ‖f (w v.1)‖ ^ 2) := by
  have h := sum_norm_linearFourier_sq L (fun y => f (synOf w L y))
    (fun y hy => by rw [synOf_eq_zero_of_not_mem_range w L y hy, map_zero])
  have hv (v : CL.perp L.ker) : f (w v.1) =
      ∑ y : Fin n → F, sgn (trDot v.1 (linearPreimage L y)) • f (synOf w L y) := by
    rw [linear_measurement_fourier w L v.1 v.2, map_sum]
    simp only [map_smul]
  simpa only [hv] using h.symm

section Model

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]

theorem smulKron_add_right {R α : Type*} [Ring R] [Algebra ℂ R] (X : R) (P Q : Matrix α α ℂ) :
    smulKron X (P + Q) = smulKron X P + smulKron X Q := by
  ext i j
  simp only [smulKron_apply, Matrix.add_apply, add_smul]

theorem smulKron_smul_right {R α : Type*} [Ring R] [Algebra ℂ R] (X : R) (c : ℂ)
    (P : Matrix α α ℂ) : smulKron X (c • P) = c • smulKron X P := by
  ext i j
  simp only [smulKron_apply, Matrix.smul_apply, smul_eq_mul, mul_smul]

/-- Commute a register operator with `M` and apply the result to the state of a model whose
first player's algebra carries the register, `Matrix (Fin n → F) (Fin n → F) 𝒜`: a register
operator `P` is `smulKron 1 P`. -/
def commutatorAction (Ψ : BipartiteModel 𝒞 (Matrix (Fin n → F) (Fin n → F) 𝒜) ℬ)
    (M : Matrix (Fin n → F) (Fin n → F) 𝒜) :
    Matrix (Fin n → F) (Fin n → F) ℂ →ₗ[ℂ] Ψ.H where
  toFun P := Ψ.π (Ψ.πA (M * smulKron 1 P - smulKron 1 P * M)) Ψ.ψ
  map_add' P Q := by
    simp only [smulKron_add_right, mul_add, add_mul, add_sub_add_comm, map_add,
      _root_.add_apply]
  map_smul' c P := by
    simp only [smulKron_smul_right, mul_smul_comm, smul_mul_assoc, ← smul_sub, map_smul,
      _root_.smul_apply, RingHom.id_apply]

/-- `lem:W`: the two commutator errors agree exactly, without a dimension factor. -/
theorem linear_measurement_commutator_parseval
    (w : (Fin n → F) → Matrix (Fin n → F) (Fin n → F) ℂ)
    (L : (Fin n → F) →ₗ[F] (Fin n → F))
    (Ψ : BipartiteModel 𝒞 (Matrix (Fin n → F) (Fin n → F) 𝒜) ℬ)
    (M : Matrix (Fin n → F) (Fin n → F) 𝒜) :
    (∑ y : Fin n → F, Ψ.stateSqNorm
      (M * smulKron 1 (synOf w L y) - smulKron 1 (synOf w L y) * M)) =
    (Fintype.card (CL.perp L.ker) : ℝ)⁻¹ *
      ∑ v : CL.perp L.ker, Ψ.stateSqNorm (M * smulKron 1 (w v.1) - smulKron 1 (w v.1) * M) :=
  linear_measurement_parseval w L (commutatorAction Ψ M)

/-- The same identity summed over outcomes and averaged over questions. -/
theorem linear_measurement_commutator_parseval_avg
    {X A : Type*} [Fintype X] [Fintype A]
    (D : X → ℝ)
    (w : (Fin n → F) → Matrix (Fin n → F) (Fin n → F) ℂ)
    (L : X → (Fin n → F) →ₗ[F] (Fin n → F))
    (Ψ : BipartiteModel 𝒞 (Matrix (Fin n → F) (Fin n → F) 𝒜) ℬ)
    (M : X → A → Matrix (Fin n → F) (Fin n → F) 𝒜) :
    (∑ x, D x * ∑ a, ∑ y : Fin n → F, Ψ.stateSqNorm
      (M x a * smulKron 1 (synOf w (L x) y) - smulKron 1 (synOf w (L x) y) * M x a)) =
    ∑ x, D x * ((Fintype.card (CL.perp (L x).ker) : ℝ)⁻¹ *
      ∑ v : CL.perp (L x).ker, ∑ a,
        Ψ.stateSqNorm (M x a * smulKron 1 (w v.1) - smulKron 1 (w v.1) * M x a)) := by
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  simp_rw [linear_measurement_commutator_parseval]
  rw [← Finset.mul_sum, Finset.sum_comm]

end Model

end MIPRE.Introspection

end

end
