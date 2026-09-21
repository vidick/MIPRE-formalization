/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AdaptivePrefixMeasurement

/-! # Prefix reassembly commutes with adjoining a fixed ancillary register

Both sides use explicit reassociations of the actual computational registers.
The identity identifies the globally extended old measurement with the local
extensions compared by conditional Naimark dilation.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false

theorem registerParty_extend {I J R H A : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype R] [DecidableEq R] [Fintype H] [DecidableEq H]
    [Fintype A] [DecidableEq A]
    (e : I ≃ J × R) (Q : Matrix J J ℂ) (M : Matrix (R × H) (R × H) ℂ) :
    registerOp (registerParty e (H × A))
      (Q ⊗ₖ registerOp (Equiv.prodAssoc R H A).symm
        (aOp M : Matrix ((R × H) × A) _ ℂ)) =
      registerOp (Equiv.prodAssoc I H A).symm
        (aOp (registerOp (registerParty e H) (Q ⊗ₖ M)) : Matrix ((I × H) × A) _ ℂ) := by
  ext ⟨i, h, a⟩ ⟨j, h', a'⟩
  simp only [registerOp_apply, registerParty, Equiv.trans_apply, Equiv.prodCongr_apply,
    Equiv.prodAssoc_apply, Equiv.prodAssoc_symm_apply, aOp, Matrix.kroneckerMap_apply,
    Matrix.one_apply, mul_assoc, Prod.map_fst, Prod.map_snd, Equiv.refl_apply]

variable {F ι H A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι]
  [Fintype H] [DecidableEq H] [Fintype A] [DecidableEq A] {ℓ : ℕ}

/-- Extending the local residual measurement by a fixed ancilla and then
reassembling is identical to extending the reassembled ambient measurement. -/
theorem prefixResidualOp_extend (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F)
    (M : Matrix ((↥((CLChecks.prefixRegister P k y)ᶜ) → F) × H) _ ℂ) :
    prefixResidualOp (H := H × A) P k y
      (registerOp (Equiv.prodAssoc (↥((CLChecks.prefixRegister P k y)ᶜ) → F) H A).symm
        (aOp M : Matrix (((↥((CLChecks.prefixRegister P k y)ᶜ) → F) × H) × A) _ ℂ)) =
      registerOp (Equiv.prodAssoc (ι → F) H A).symm
        (aOp (prefixResidualOp (H := H) P k y M) : Matrix (((ι → F) × H) × A) _ ℂ) :=
  registerParty_extend _ _ _

end MIPRE.Introspection

end
