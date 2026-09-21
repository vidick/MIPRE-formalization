/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AdaptiveDilationTransport

/-! # Exact error transport through a registered auxiliary extension

Only an auxiliary register in a fixed pure state is added. The EPR register
and Bob's operators remain unchanged. All identities hold for arbitrary
operators and auxiliary states, without normalization or projectivity.
-/

noncomputable section
namespace MIPRE.Introspection

open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false

section Raw
variable {H K T H' K' : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype T] [DecidableEq T]
  [Fintype H'] [DecidableEq H'] [Fintype K'] [DecidableEq K']

theorem xSqNorm_registerOp (e : H' ≃ H) (f : K' ≃ K) (ψ : H × K → ℂ)
    (M : Matrix H H ℂ) (N : Matrix K K ℂ) :
    xSqNorm (ψ ∘ e.prodCongr f) (registerOp e M) (registerOp f N) =
      xSqNorm ψ M N := by
  simp only [xSqNorm_eq_snorm_sq, snorm]
  have h : (aOp (registerOp e M) : Matrix (H' × K') _ ℂ) - bOp (registerOp f N) =
      registerOp (e.prodCongr f) (aOp M - bOp N) := by
    rw [registerOp_sub]
    simp only [aOp, bOp, registerOp_kronecker, registerOp_one]
  rw [h, registerOp_mulVec, norm_evec_comp_equiv]

/-- The old deviation vector is extended by the same fixed isometry. -/
theorem deviation_extVecA (ψ : H × K → ℂ) (a₀ : T)
    (M : Matrix H H ℂ) (N : Matrix K K ℂ) :
    (aOp (aOp M : Matrix (H × T) _ ℂ) - bOp N) *ᵥ extVecA ψ a₀ =
      extVecA ((aOp M - bOp N) *ᵥ ψ) a₀ := by
  have h : (aOp (aOp M : Matrix (H × T) _ ℂ) - bOp N) *
      (ancillaEmbed H a₀ ⊗ₖ (1 : Matrix K K ℂ)) =
      (ancillaEmbed H a₀ ⊗ₖ (1 : Matrix K K ℂ)) * (aOp M - bOp N) := by
    change ((M ⊗ₖ 1) ⊗ₖ 1 - 1 ⊗ₖ N) * _ = _ * (M ⊗ₖ 1 - 1 ⊗ₖ N)
    rw [Matrix.sub_mul, Matrix.mul_sub]
    simp only [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
      kron_one_mul_ancillaEmbed]
  simp only [extVecA, Matrix.mulVec_mulVec, h]

theorem xSqNorm_extVecA (ψ : H × K → ℂ) (a₀ : T)
    (M : Matrix H H ℂ) (N : Matrix K K ℂ) :
    xSqNorm (extVecA ψ a₀) (aOp M) N = xSqNorm ψ M N := by
  simp only [xSqNorm_eq_snorm_sq, snorm, deviation_extVecA, norm_evec_extVecA]

end Raw

variable {I H K T A B : Type*}
  [Fintype I] [DecidableEq I] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K] [Fintype T] [DecidableEq T]
  [Fintype A] [Fintype B] [DecidableEq B]

/-- Extend an old operator by identity, then absorb the new register into
Alice's auxiliary factor. -/
def registeredExtendOp (M : Matrix (I × H) (I × H) ℂ) :
    Matrix (I × (H × T)) (I × (H × T)) ℂ :=
  registerOp (Equiv.prodAssoc I H T).symm (aOp M)

@[simp] theorem registeredExtendOp_zero :
    registeredExtendOp (I := I) (H := H) (T := T) 0 = 0 := by
  ext i j
  simp [registeredExtendOp, registerOp, aOp_zero]

theorem registeredExtendOp_sub (M N : Matrix (I × H) (I × H) ℂ) :
    registeredExtendOp (T := T) (M - N) = registeredExtendOp M - registeredExtendOp N := by
  simp only [registeredExtendOp, aOp_sub, registerOp_sub]

/-- Every ideal acting on the original register is literally the same
ideal tensored with the enlarged auxiliary identity. -/
theorem registeredExtendOp_aOp (M : Matrix I I ℂ) :
    registeredExtendOp (H := H) (T := T) (aOp M) = aOp M := by
  ext ⟨i, h, t⟩ ⟨j, h', t'⟩
  by_cases hh : h = h'
  · by_cases ht : t = t' <;>
      simp [registeredExtendOp, aOp, Matrix.kroneckerMap_apply,
        Prod.mk.injEq, hh, ht]
  · simp [registeredExtendOp, aOp, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Prod.mk.injEq, hh]

def registeredExtendPOVM (M : POVM A (I × H)) : POVM A (I × (H × T)) :=
  M.aOp.reindex (Equiv.prodAssoc I H T)

@[simp] theorem registeredExtendPOVM_mats (M : POVM A (I × H)) (a : A) :
    ((registeredExtendPOVM (T := T) M).mats a).val = registeredExtendOp (M.mats a).val := rfl

theorem registeredExtendPOVM_map (M : POVM A (I × H)) (f : A → B) :
    registeredExtendPOVM (T := T) (M.map f) = (registeredExtendPOVM M).map f := by
  rw [registeredExtendPOVM, POVM.map_aOp, POVM.map_reindex]
  rfl

theorem registeredExtendPOVM_isPVM (M : POVM A (I × H))
    (hM : IsPVM (fun a => (M.mats a).val)) :
    IsPVM (fun a => ((registeredExtendPOVM (T := T) M).mats a).val) :=
  registerOp_isPVM (Equiv.prodAssoc I H T).symm hM.aOp

theorem stateSqNorm_registeredExtendOp (ξ : H × K → ℂ) (a₀ : T)
    (M : Matrix (I × H) (I × H) ℂ) :
    stateSqNorm (registerState I (extVecA ξ a₀)) (registeredExtendOp M) =
      stateSqNorm (registerState I ξ) M := by
  rw [registeredExtendOp, stateSqNorm_reassociated_extVecA, stateSqNorm_extVecA_aOp]

theorem xSqNorm_registeredExtendOp (ξ : H × K → ℂ) (a₀ : T)
    (M : Matrix (I × H) (I × H) ℂ) (N : Matrix (I × K) (I × K) ℂ) :
    xSqNorm (registerState I (extVecA ξ a₀)) (registeredExtendOp M) N =
      xSqNorm (registerState I ξ) M N := by
  have hs := reindex_extVecA_registerState (I := I) ξ a₀
  change (extVecA (registerState I ξ) a₀) ∘
    ((Equiv.prodAssoc I H T).symm.prodCongr (Equiv.refl (I × K))) = _ at hs
  rw [← hs]
  change xSqNorm _ (registerOp (Equiv.prodAssoc I H T).symm (aOp M))
    (registerOp (Equiv.refl (I × K)) N) = _
  rw [xSqNorm_registerOp, xSqNorm_extVecA]

/-- Bob's same-party error is unaffected by adding an auxiliary register
on Alice's side, including the exact registered state reassociation. -/
theorem snorm_bOp_registered_extVecA (ξ : H × K → ℂ) (a₀ : T)
    (N : Matrix (I × K) (I × K) ℂ) :
    snorm (registerState I (extVecA ξ a₀)) (bOp N) ^ 2 =
      snorm (registerState I ξ) (bOp N) ^ 2 := by
  have h := xSqNorm_registeredExtendOp ξ a₀ (0 : Matrix (I × H) _ ℂ) N
  rw [registeredExtendOp_zero, xSqNorm_eq_snorm_sq, aOp_zero,
    snorm_sub_comm, sub_zero, xSqNorm_eq_snorm_sq, aOp_zero,
    snorm_sub_comm, sub_zero] at h
  exact h

theorem bornProb_registeredExtendOp (ξ : H × K → ℂ) (a₀ : T)
    (M : Matrix (I × H) (I × H) ℂ) (N : Matrix (I × K) (I × K) ℂ) :
    bornProb (registerState I (extVecA ξ a₀)) (registeredExtendOp M) N =
      bornProb (registerState I ξ) M N := by
  have h := bornProb_reindex (Equiv.prodAssoc I H T) (Equiv.refl (I × K))
    (extVecA (registerState I ξ) a₀) (aOp M) N
  change bornProb _ (registeredExtendOp M) N = _ at h
  rw [reindex_extVecA_registerState, bornProb_extVecA, compress_aOp] at h
  exact h

end MIPRE.Introspection
end
