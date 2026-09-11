/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Tracial/Density/TracialGNS.lean
-/
/-
# Standard tracial algebras from C*-algebras with a tracial state (stage E2)

For a unital C*-algebra `𝒞` with a tracial state `τ`, the GNS space `L²(𝒞, τ)`
(Mathlib's `PositiveLinearMap.GNS`) with the left regular representation
(`gnsStarAlgHom`) and the right regular representation (bounded because `τ` is
tracial) is a `StdTracialAlgebra`. This is the target shape for the density
theorem (PLAN-density.md, §1.2): the interface `TraciallyEmbeddableCorrelation`
does not need a von Neumann algebra, only this. Proof-side infrastructure; no
manuscript statement.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Tracial.Density

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace Density

open scoped InnerProductSpace ComplexOrder
open UniformSpace Completion PositiveLinearMap

variable {𝒞 : Type} [CStarAlgebra 𝒞] [PartialOrder 𝒞] [StarOrderedRing 𝒞]
variable (τ : 𝒞 →ₚ[ℂ] ℂ)

/-! ### The right regular representation on the pre-GNS space -/

/-- The bound `‖x a‖_τ ≤ ‖a‖ ‖x‖_τ` for right multiplication, from traciality. -/
theorem norm_sq_mul_le (hτ : ∀ a b : 𝒞, τ (a * b) = τ (b * a)) (a x : 𝒞) :
    τ (star (x * a) * (x * a)) ≤ ((‖a‖ ^ 2 : ℝ) : ℂ) * τ (star x * x) := by
  have h1 : τ (star (x * a) * (x * a)) = τ (x * (a * star a) * star x) := by
    calc τ (star (x * a) * (x * a)) = τ (star a * (star x * (x * a))) := by
          rw [star_mul, mul_assoc]
      _ = τ ((star x * (x * a)) * star a) := hτ _ _
      _ = τ (star x * ((x * a) * star a)) := by rw [mul_assoc]
      _ = τ (((x * a) * star a) * star x) := hτ _ _
      _ = τ (x * (a * star a) * star x) := by rw [mul_assoc x a]
  have h2 : x * (a * star a) * star x ≤ x * (((‖a‖ ^ 2 : ℝ) : ℂ) • (1 : 𝒞)) * star x := by
    have := star_right_conjugate_le_conjugate (CStarAlgebra.mul_star_le_algebraMap_norm_sq (a := a)) x
    rwa [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul] at this
  have h3 : τ (x * (((‖a‖ ^ 2 : ℝ) : ℂ) • (1 : 𝒞)) * star x) =
      ((‖a‖ ^ 2 : ℝ) : ℂ) * τ (star x * x) := by
    rw [mul_smul_comm, mul_one, smul_mul_assoc, map_smul, smul_eq_mul, hτ]
  rw [h1, ← h3]
  exact OrderHomClass.mono τ h2

/-- Right multiplication by `a` on the pre-GNS space of a tracial state. -/
noncomputable def rightMulMapPreGNS (hτ : ∀ a b : 𝒞, τ (a * b) = τ (b * a)) (a : 𝒞) :
    τ.PreGNS →L[ℂ] τ.PreGNS :=
  (τ.toPreGNS.toLinearMap ∘ₗ LinearMap.mulRight ℂ a ∘ₗ τ.ofPreGNS.toLinearMap).mkContinuous ‖a‖
    fun x => by
      rw [← sq_le_sq₀ (by positivity) (by positivity), mul_pow,
        ← Complex.real_le_real, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_pow,
        Complex.ofReal_pow, preGNS_norm_sq, preGNS_norm_sq]
      have := norm_sq_mul_le τ hτ a (τ.ofPreGNS x)
      simpa only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        LinearMap.mulRight_apply, ofPreGNS_toPreGNS, Complex.ofReal_pow] using this

theorem rightMulMapPreGNS_apply (hτ : ∀ a b : 𝒞, τ (a * b) = τ (b * a)) (a : 𝒞) (x : τ.PreGNS) :
    rightMulMapPreGNS τ hτ a x = τ.toPreGNS (τ.ofPreGNS x * a) := rfl

/-- The right regular representation on the GNS space. -/
noncomputable def rightMul (hτ : ∀ a b : 𝒞, τ (a * b) = τ (b * a)) (a : 𝒞) : τ.GNS →L[ℂ] τ.GNS :=
  (rightMulMapPreGNS τ hτ a).completion

theorem rightMul_apply_coe (hτ : ∀ a b : 𝒞, τ (a * b) = τ (b * a)) (a : 𝒞) (x : τ.PreGNS) :
    rightMul τ hτ a x = ((τ.toPreGNS (τ.ofPreGNS x * a) : τ.PreGNS) : τ.GNS) := by
  rw [rightMul, ContinuousLinearMap.completion_apply_coe, rightMulMapPreGNS_apply]

theorem rightMul_mul (hτ : ∀ a b : 𝒞, τ (a * b) = τ (b * a)) (a b : 𝒞) :
    rightMul τ hτ (a * b) = rightMul τ hτ b * rightMul τ hτ a := by
  ext x
  induction x using induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x =>
    rw [mul_apply_eq_comp, rightMul_apply_coe, rightMul_apply_coe, rightMul_apply_coe]
    simp only [ofPreGNS_toPreGNS, mul_assoc]

theorem rightMul_one (hτ : ∀ a b : 𝒞, τ (a * b) = τ (b * a)) : rightMul τ hτ 1 = 1 := by
  ext x
  induction x using induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x => rw [rightMul_apply_coe, one_apply_eq_self, mul_one, toPreGNS_ofPreGNS]

theorem rightMul_add (hτ : ∀ a b : 𝒞, τ (a * b) = τ (b * a)) (a b : 𝒞) :
    rightMul τ hτ (a + b) = rightMul τ hτ a + rightMul τ hτ b := by
  ext x
  induction x using induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x =>
    rw [_root_.add_apply, rightMul_apply_coe, rightMul_apply_coe, rightMul_apply_coe,
      mul_add, map_add, Completion.coe_add]

theorem rightMul_smul (hτ : ∀ a b : 𝒞, τ (a * b) = τ (b * a)) (c : ℂ) (a : 𝒞) :
    rightMul τ hτ (c • a) = c • rightMul τ hτ a := by
  ext x
  induction x using induction_on with
  | hp => exact isClosed_eq (rightMul τ hτ (c • a)).continuous (c • rightMul τ hτ a).continuous
  | ih x =>
    rw [_root_.smul_apply, rightMul_apply_coe, rightMul_apply_coe, mul_smul_comm,
      LinearEquiv.map_smul, Completion.coe_smul]

/-- `⟪x a, y⟫ = ⟪x, y a*⟫`: the adjoint of right multiplication by `a` is right multiplication
by `a*` (uses traciality). -/
theorem rightMul_star (hτ : ∀ a b : 𝒞, τ (a * b) = τ (b * a)) (a : 𝒞) :
    rightMul τ hτ (star a) = star (rightMul τ hτ a) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  refine (ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun x y => ?_
  induction x, y using induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x y =>
    rw [rightMul_apply_coe, rightMul_apply_coe, inner_coe, inner_coe, preGNS_inner_def,
      preGNS_inner_def]
    simp only [ofPreGNS_toPreGNS, star_mul, star_star]
    rw [hτ, ← mul_assoc, hτ]

/-- The right regular representation as a unital star-algebra homomorphism from the opposite
algebra. -/
noncomputable def rightHom (hτ : ∀ a b : 𝒞, τ (a * b) = τ (b * a)) :
    𝒞ᵐᵒᵖ →⋆ₐ[ℂ] (τ.GNS →L[ℂ] τ.GNS) where
  toFun a := rightMul τ hτ (MulOpposite.unop a)
  map_one' := rightMul_one τ hτ
  map_mul' a b := by
    show rightMul τ hτ (MulOpposite.unop b * MulOpposite.unop a) = _
    rw [rightMul_mul]
  map_zero' := by
    show rightMul τ hτ 0 = 0
    have := rightMul_smul τ hτ 0 0
    rwa [zero_smul, zero_smul] at this
  map_add' a b := by
    show rightMul τ hτ (MulOpposite.unop a + MulOpposite.unop b) = _
    rw [rightMul_add]
  commutes' c := by
    show rightMul τ hτ (MulOpposite.unop (algebraMap ℂ 𝒞ᵐᵒᵖ c)) = algebraMap ℂ _ c
    rw [MulOpposite.algebraMap_apply, MulOpposite.unop_op, Algebra.algebraMap_eq_smul_one,
      rightMul_smul, rightMul_one, Algebra.algebraMap_eq_smul_one]
  map_star' a := by
    show rightMul τ hτ (star (MulOpposite.unop a)) = star (rightMul τ hτ (MulOpposite.unop a))
    rw [rightMul_star]

theorem rightHom_apply (hτ : ∀ a b : 𝒞, τ (a * b) = τ (b * a)) (a : 𝒞) :
    rightHom τ hτ (MulOpposite.op a) = rightMul τ hτ a := rfl

/-! ### The standard tracial algebra of a tracial state -/

/-- The GNS embedding `𝒞 → L²(𝒞, τ)` as a linear map. -/
noncomputable def ιGNS : 𝒞 →ₗ[ℂ] τ.GNS :=
  (toComplL : τ.PreGNS →L[ℂ] τ.GNS).toLinearMap ∘ₗ τ.toPreGNS.toLinearMap

theorem ιGNS_apply (a : 𝒞) : ιGNS τ a = ((τ.toPreGNS a : τ.PreGNS) : τ.GNS) := rfl

theorem denseRange_ιGNS : DenseRange (ιGNS τ) := by
  have h : Set.range (ιGNS τ) = Set.range ((↑) : τ.PreGNS → τ.GNS) := by
    ext v
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨τ.toPreGNS a, rfl⟩
    · rintro ⟨x, rfl⟩; exact ⟨τ.ofPreGNS x, by rw [ιGNS_apply, toPreGNS_ofPreGNS]⟩
  rw [DenseRange, h]
  exact denseRange_coe

theorem inner_ιGNS (a b : 𝒞) : ⟪ιGNS τ a, ιGNS τ b⟫_ℂ = τ (star a * b) := by
  rw [ιGNS_apply, ιGNS_apply, inner_coe, preGNS_inner_def, ofPreGNS_toPreGNS, ofPreGNS_toPreGNS]

theorem gns_apply_ιGNS (a b : 𝒞) : τ.gnsStarAlgHom a (ιGNS τ b) = ιGNS τ (a * b) := by
  rw [ιGNS_apply, ιGNS_apply]
  show τ.gnsNonUnitalStarAlgHom a _ = _
  rw [gnsNonUnitalStarAlgHom_apply_coe, leftMulMapPreGNS_apply, ofPreGNS_toPreGNS]

theorem rightMul_ιGNS (hτ : ∀ a b : 𝒞, τ (a * b) = τ (b * a)) (a b : 𝒞) :
    rightMul τ hτ a (ιGNS τ b) = ιGNS τ (b * a) := by
  rw [ιGNS_apply, ιGNS_apply, rightMul_apply_coe, ofPreGNS_toPreGNS]

/-- **The standard tracial algebra of a tracial state** on a unital C*-algebra: the GNS space
with the left and right regular representations. -/
noncomputable def ofTracialState (hτ1 : τ 1 = 1) (hτ : ∀ a b : 𝒞, τ (a * b) = τ (b * a)) :
    StdTracialAlgebra.{0} where
  A := 𝒞
  τ := τ.toLinearMap
  τ_one := hτ1
  τ_mul_comm := hτ
  τ_star a := by
    show τ (star a) = star (τ a)
    rw [map_star]
  H := τ.GNS
  ι := ιGNS τ
  ι_dense := denseRange_ιGNS τ
  ι_inner := inner_ιGNS τ
  L := τ.gnsStarAlgHom
  R := rightHom τ hτ
  L_apply := gns_apply_ιGNS τ
  R_apply a b := rightMul_ιGNS τ hτ a b
  LR_commute a b := by
    show Commute (τ.gnsStarAlgHom a) (rightMul τ hτ b)
    rw [Commute, SemiconjBy]
    ext x
    induction x using induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x =>
      rw [mul_apply_eq_comp, mul_apply_eq_comp, rightMul_apply_coe]
      show τ.gnsNonUnitalStarAlgHom a _ = rightMul τ hτ b (τ.gnsNonUnitalStarAlgHom a _)
      rw [gnsNonUnitalStarAlgHom_apply_coe, gnsNonUnitalStarAlgHom_apply_coe, rightMul_apply_coe,
        leftMulMapPreGNS_apply, leftMulMapPreGNS_apply, ofPreGNS_toPreGNS, ofPreGNS_toPreGNS,
        mul_assoc]

section Model

variable (hτ1 : τ 1 = 1) (hτ : ∀ a b : 𝒞, τ (a * b) = τ (b * a))

theorem ofTracialState_A : (ofTracialState τ hτ1 hτ).A = 𝒞 := rfl
theorem ofTracialState_H : (ofTracialState τ hτ1 hτ).H = τ.GNS := rfl
theorem ofTracialState_τ (a : 𝒞) : (ofTracialState τ hτ1 hτ).τ a = τ a := rfl
theorem ofTracialState_ι (a : 𝒞) : (ofTracialState τ hτ1 hτ).ι a = ιGNS τ a := rfl
theorem ofTracialState_L (a : 𝒞) : (ofTracialState τ hτ1 hτ).L a = τ.gnsStarAlgHom a := rfl
theorem ofTracialState_Rop (a : 𝒞) : (ofTracialState τ hτ1 hτ).Rop a = rightMul τ hτ a := rfl

/-- Positive elements of a C*-algebra are algebraically positive (single squares). -/
theorem isPosElem_of_nonneg {σ : 𝒞} (hσ : 0 ≤ σ) : IsPosElem σ := by
  refine ⟨1, fun _ => CFC.sqrt σ, ?_⟩
  rw [Fin.sum_univ_one]
  have hsa : IsSelfAdjoint (CFC.sqrt σ) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg σ)
  rw [hsa.star_eq, CFC.sqrt_mul_sqrt_self σ hσ]

/-- The right action of a positive element is a positive operator. -/
theorem rightMul_isPositive {f : 𝒞} (hf : 0 ≤ f) : (rightMul τ hτ f).IsPositive := by
  have hsa : IsSelfAdjoint f := IsSelfAdjoint.of_nonneg hf
  have hsq : rightMul τ hτ f = star (rightMul τ hτ (CFC.sqrt f)) * rightMul τ hτ (CFC.sqrt f) := by
    rw [← rightMul_star, ← rightMul_mul, (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg f)).star_eq,
      CFC.sqrt_mul_sqrt_self f hf]
  rw [hsq, ContinuousLinearMap.star_eq_adjoint]
  exact ContinuousLinearMap.isPositive_adjoint_comp_self _

theorem rightMul_sum {ι : Type*} (s : Finset ι) (f : ι → 𝒞) :
    rightMul τ hτ (∑ i ∈ s, f i) = ∑ i ∈ s, rightMul τ hτ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have := rightMul_smul τ hτ 0 0
    rwa [zero_smul, zero_smul] at this
  | insert j t hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, rightMul_add, ih]

end Model

end Density

end CommutingRepetition
