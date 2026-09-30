/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.AdaptivePrefixMeasurement
public import MIPRE.Foundations.Introspection.RegisteredExtensionErrors

@[expose] public section

/-! # Prefix reassembly commutes with adjoining a fixed ancillary register

Both sides use explicit reassociations of the actual computational registers.
The identity identifies the globally extended old measurement with the local
extensions compared by conditional Naimark dilation.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): adjoining the ancilla to a block
matrix over a register is `registeredExtendOp` (`M ↦ M ⊗ 1`, then the exchange of the layers), and
reassembly behind the prefix projector is `prefixResidualOp` with entries in any algebra.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical
set_option linter.unusedSectionVars false

variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] {T : Type*} [Fintype T] [DecidableEq T]

/-- Splitting a register commutes with adjoining a fixed ancilla to the entries. -/
theorem registerParty_extend {I J R : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype R] [DecidableEq R]
    (e : I ≃ J × R) (Q : Matrix J J ℂ) (M : Matrix R R 𝒜) :
    regSplitHom e (smulKron (registeredExtendOp (T := T) M) Q) =
      registeredExtendOp (T := T) (regSplitHom e (smulKron M Q)) := by
  ext i i' t t'
  simp only [regSplitHom_apply, smulKron_apply, registeredExtendOp_apply, Matrix.smul_apply]
  by_cases h : t = t'
  · subst h
    simp only [diagonal_apply_eq, regSplitHom_apply, smulKron_apply]
  · simp only [diagonal_apply_ne _ h, smul_zero]

variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

/-- Extending the local residual measurement by a fixed ancilla and then
reassembling is identical to extending the reassembled ambient measurement. -/
theorem prefixResidualOp_extend (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F)
    (M : Matrix (↥((CLChecks.prefixRegister P k y)ᶜ) → F) _ 𝒜) :
    prefixResidualOp P k y (registeredExtendOp (T := T) M) =
      registeredExtendOp (T := T) (prefixResidualOp P k y M) :=
  registerParty_extend _ _ _

end MIPRE.Introspection

end

end
