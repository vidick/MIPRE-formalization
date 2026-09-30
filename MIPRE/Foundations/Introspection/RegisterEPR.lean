/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.RegisterTransport
public import MIPRE.Foundations.Introspection.RegisterModel

@[expose] public section

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

end
