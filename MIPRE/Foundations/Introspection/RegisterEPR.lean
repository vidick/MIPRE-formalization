/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.RegisterTransport

/-! # Splitting the maximally entangled state along computational registers -/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical
open scoped Kronecker

set_option linter.unusedSectionVars false

variable {I J R H K : Type*}
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype R] [DecidableEq R] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K]

/-- The maximally entangled state, indexed by an arbitrary finite basis. -/
def registerEPR (I : Type*) [Fintype I] [DecidableEq I] : I × I → ℂ :=
  fun p => if p.1 = p.2 then (((Real.sqrt (Fintype.card I))⁻¹ : ℝ) : ℂ) else 0

/-- The finite-basis EPR definition agrees literally with the Weyl-register definition. -/
theorem registerEPR_eq_weyl {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F] {ι : Type*} [Fintype ι] [DecidableEq ι] :
    registerEPR (ι → F) = Weyl.epr (F := F) (n := ι) := rfl

/-- Simultaneous relabelling of both EPR halves leaves the state unchanged. -/
theorem registerEPR_equiv (e : I ≃ J) :
    registerEPR J ∘ e.prodCongr e = registerEPR I := by
  funext p
  simp only [Function.comp_apply, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
    registerEPR, e.injective.eq_iff,
    Fintype.card_congr e]

/-- EPR on a product basis factors exactly into the two EPR states. -/
theorem registerEPR_prod :
    registerEPR (I × J) = expVec (registerEPR I) (registerEPR J) := by
  funext p
  obtain ⟨⟨i, j⟩, ⟨i', j'⟩⟩ := p
  simp only [registerEPR, expVec, Prod.mk.injEq, Fintype.card_prod, Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg _), _root_.mul_inv_rev, Complex.ofReal_mul]
  by_cases hi : i = i' <;> by_cases hj : j = j' <;> simp [hi, hj, mul_comm]

/-- Unit normalization for a nonempty finite EPR basis. -/
theorem registerEPR_norm [Nonempty I] : ‖evec (registerEPR I)‖ = 1 := by
  have hc : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hs : Real.sqrt (Fintype.card I) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hc)
  rw [evec, EuclideanSpace.norm_eq]
  simp only [registerEPR, Fintype.sum_prod_type]
  simp only [apply_ite norm, norm_zero, zero_pow (by decide : 2 ≠ 0),
    ite_pow, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_inv, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt hc.le]
  rw [mul_inv_cancel₀ hc.ne', Real.sqrt_one]

/-- EPR together with the original ancillary state, in the original basis. -/
def registerState (I : Type*) [Fintype I] [DecidableEq I] (ξ : H × K → ℂ) :
    (I × H) × (I × K) → ℂ := expVec (registerEPR I) ξ

theorem registerState_norm [Nonempty I] (ξ : H × K → ℂ) (hξ : ‖evec ξ‖ = 1) :
    ‖evec (registerState I ξ)‖ = 1 := by
  rw [registerState, norm_evec_expVec, registerEPR_norm, hξ, one_mul]

/-- Split a local basis and keep the original ancilla last. -/
def registerParty (e : I ≃ J × R) (H : Type*) : I × H ≃ J × (R × H) :=
  (e.prodCongr (Equiv.refl H)).trans (Equiv.prodAssoc J R H)

/-- The EPR factorization under the actual party-wise register permutation. -/
theorem registerState_split (e : I ≃ J × R) (ξ : H × K → ℂ) :
    registerState I ξ =
      registerState J (registerState R ξ) ∘
        (registerParty e H).prodCongr (registerParty e K) := by
  have h := registerEPR_equiv e
  rw [registerEPR_prod] at h
  funext p
  have hp := congrFun h (p.1.1, p.2.1)
  change registerEPR I (p.1.1, p.2.1) * ξ (p.1.2, p.2.2) =
    registerEPR J ((e p.1.1).1, (e p.2.1).1) *
      (registerEPR R ((e p.1.1).2, (e p.2.1).2) * ξ (p.1.2, p.2.2))
  rw [← hp]
  exact mul_assoc _ _ _

/-- A local operator has exactly the same error in the split register presentation. -/
theorem stateSqNorm_registerState_split (e : I ≃ J × R) (ξ : H × K → ℂ)
    (M : Matrix (J × (R × H)) (J × (R × H)) ℂ) :
    stateSqNorm (registerState I ξ) (registerOp (registerParty e H) M) =
      stateSqNorm (registerState J (registerState R ξ)) M := by
  rw [registerState_split e ξ, stateSqNorm_registerOp]

/-- The complementary register is moved behind the original auxiliary register. -/
def registerOutside (e : I ≃ J × R) (H : Type*) : I × H ≃ (J × H) × R :=
  ((registerParty e H).trans
    ((Equiv.refl J).prodCongr (Equiv.prodComm R H))).trans (Equiv.prodAssoc J H R).symm

/-- Put a local operator on the first register, leaving the complement untouched. -/
def registerExtend (e : I ≃ J × R) (M : Matrix (J × H) (J × H) ℂ) :
    Matrix (I × H) (I × H) ℂ :=
  registerOp (registerOutside e H) (M ⊗ₖ (1 : Matrix R R ℂ))

@[simp] theorem registerExtend_sub (e : I ≃ J × R)
    (M N : Matrix (J × H) (J × H) ℂ) :
    registerExtend e (M - N) = registerExtend e M - registerExtend e N := by
  ext i j
  simp only [registerExtend, registerOp_apply, Matrix.kroneckerMap_apply, Matrix.sub_apply]
  ring

@[simp] theorem registerExtend_mul (e : I ≃ J × R)
    (M N : Matrix (J × H) (J × H) ℂ) :
    registerExtend e (M * N) = registerExtend e M * registerExtend e N := by
  unfold registerExtend
  rw [← registerOp_mul, ← Matrix.mul_kronecker_mul, one_mul]

@[simp] theorem registerExtend_sum {A : Type*} [Fintype A] (e : I ≃ J × R)
    (M : A → Matrix (J × H) (J × H) ℂ) :
    registerExtend e (∑ a, M a) = ∑ a, registerExtend e (M a) := by
  ext i j
  simp only [registerExtend, registerOp_apply, Matrix.kroneckerMap_apply,
    Matrix.sum_apply, Finset.sum_mul]

/-- Extending a local operator by identity on complementary EPR coordinates costs no error. -/
theorem stateSqNorm_registerExtend [Nonempty R] (e : I ≃ J × R)
    (ξ : H × K → ℂ) (M : Matrix (J × H) (J × H) ℂ) :
    stateSqNorm (registerState I ξ) (registerExtend e M) =
      stateSqNorm (registerState J ξ) M := by
  let a := registerOutside e H
  let b := registerOutside e K
  have hstate : registerState I ξ =
      expVec (registerState J ξ) (registerEPR R) ∘ a.prodCongr b := by
    rw [registerState_split e ξ]
    funext p
    change registerEPR J ((e p.1.1).1, (e p.2.1).1) *
        (registerEPR R ((e p.1.1).2, (e p.2.1).2) * ξ (p.1.2, p.2.2)) =
      (registerEPR J ((e p.1.1).1, (e p.2.1).1) * ξ (p.1.2, p.2.2)) *
        registerEPR R ((e p.1.1).2, (e p.2.1).2)
    ring
  change stateSqNorm (registerState I ξ) (registerOp a (M ⊗ₖ (1 : Matrix R R ℂ))) = _
  rw [hstate, stateSqNorm_registerOp a b, stateSqNorm_expVec_kron, stateSqNorm_one_eq,
    registerEPR_norm, one_pow, mul_one]

end MIPRE.Introspection

end
