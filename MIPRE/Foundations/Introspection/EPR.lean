/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Expanded
import MIPRE.Foundations.WeylEPR

/-! # Exactly consistent Pauli readouts with arbitrary ancillary states -/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Weyl
open scoped Kronecker

variable {V W H K : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

/-- Exact consistency survives adjoining any bipartite ancillary state. -/
theorem mirror_expVec (ψ : V × W → ℂ) (ξ : H × K → ℂ)
    (P : Matrix V V ℂ) (Q : Matrix W W ℂ) (h : stateVec ψ P = stateVecB ψ Q) :
    stateVec (expVec ψ ξ) (aOp P : Matrix (V × H) _ ℂ) =
      stateVecB (expVec ψ ξ) (aOp Q : Matrix (W × K) _ ℂ) := by
  have hbase := congrArg WithLp.ofLp h
  change (P ⊗ₖ (1 : Matrix W W ℂ)) *ᵥ ψ = ((1 : Matrix V V ℂ) ⊗ₖ Q) *ᵥ ψ at hbase
  unfold stateVec stateVecB aOp
  congr 1
  rw [show (1 : Matrix (W × K) (W × K) ℂ) =
      (1 : Matrix W W ℂ) ⊗ₖ (1 : Matrix K K ℂ) from Matrix.one_kronecker_one.symm,
    show (1 : Matrix (V × H) (V × H) ℂ) =
      (1 : Matrix V V ℂ) ⊗ₖ (1 : Matrix H H ℂ) from Matrix.one_kronecker_one.symm,
    mulVec_kron_kron_expVec, mulVec_kron_kron_expVec, hbase]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {n : ℕ}

/-- EPR on the sampled register, together with an arbitrary auxiliary state. -/
def eprWithAux (ξ : H × K → ℂ) : ((Fin n → F) × H) × ((Fin n → F) × K) → ℂ :=
  expVec (epr (F := F) (n := Fin n)) ξ

/-- The expanded EPR state is normalized whenever its ancillary state is. -/
theorem eprWithAux_norm (ξ : H × K → ℂ) (hξ : ‖evec ξ‖ = 1) :
    ‖evec (eprWithAux (F := F) (n := n) ξ)‖ = 1 := by
  have he : ‖evec (epr (F := F) (n := Fin n))‖ = 1 := by
    have hs := norm_evec_sq (epr (F := F) (n := Fin n))
    rw [epr_unit, Complex.one_re] at hs
    nlinarith [norm_nonneg (evec (epr (F := F) (n := Fin n)))]
  rw [eprWithAux, norm_evec_expVec, he, hξ, one_mul]

/-- The same `X` Pauli on the two EPR halves is an exact mirror, with arbitrary ancillas. -/
theorem eprWithAux_wX_mirror (ξ : H × K → ℂ) (v : Fin n → F) :
    xSqNorm (eprWithAux ξ) (aOp (wX v) : Matrix ((Fin n → F) × H) _ ℂ)
      (aOp (wX v) : Matrix ((Fin n → F) × K) _ ℂ) = 0 := by
  rw [xSqNorm, eprWithAux, mirror_expVec _ ξ _ _ (stateVec_epr_wX v), sub_self, norm_zero,
    zero_pow (by decide : 2 ≠ 0)]

/-- A coarse-grained `Z` readout has the same exact mirror. -/
theorem eprWithAux_readout_mirror (ξ : H × K → ℂ)
    (L : (Fin n → F) →ₗ[F] (Fin n → F)) (y : Fin n → F) :
    aOp (aOp (synOf wZ L y) : Matrix ((Fin n → F) × H) _ ℂ) *ᵥ eprWithAux ξ =
      bOp (aOp (synOf wZ L y) : Matrix ((Fin n → F) × K) _ ℂ) *ᵥ eprWithAux ξ := by
  exact congrArg WithLp.ofLp
    (mirror_expVec (epr (F := F) (n := Fin n)) ξ _ _ (stateVec_epr_synOf wZ_transpose L y))

end MIPRE.Introspection

end
