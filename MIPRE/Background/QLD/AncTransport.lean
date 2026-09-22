/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.Simul

/-!
# The ancilla transports across the padded state (`lem:qld-pauli-selfcons`, the exact steps)

The paper's chain for the self-consistency of the exact Pauli observables --- the step
`eq:qld-pulling-3a`, and again `eq:qld-pulling-4` --- moves a generalized Pauli from one party's
ancilla half to the other's, and calls the move `approx_0`: it is exact, because the two halves are
maximally entangled and the syndrome projectors are symmetric.

`MIPRE/Foundations/WeylEPR.lean` has that for the bare entangled state
(`stateVec_epr_syn`). What the chain needs is the same statement for a
`SimulPair`'s *padded* state `Phi`, which is not literally `hatVec psi` --- the structure only
promises that `Phi` reproduces its expectations (`Phi_reduced`). That is enough: the vector
identity is the vanishing of a squared norm, `xSqNorm Phi A B = 0`, and a squared norm is an
expectation. So `SimulPair.xSqNorm_aOp` carries it from `hatVec psi` to `Phi` with no loss, and the
exact step of the chain is available on the padded state.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}

/-! ## On the expanded state -/

section Expanded

variable {anc anc' : Type*} [Fintype anc] [DecidableEq anc] [Fintype anc'] [DecidableEq anc']

/-- An operator on the first party's ancilla factor, read on the expanded state, is the ancilla
operator applied to the entangled pair. -/
theorem stateVec_expVec_kron_one (φ : dA × dB → ℂ) (e : anc × anc' → ℂ)
    (S : Matrix anc anc ℂ) :
    stateVec (expVec φ e) ((1 : Matrix dA dA ℂ) ⊗ₖ S)
      = WithLp.toLp 2 (expVec φ ((S ⊗ₖ (1 : Matrix anc' anc' ℂ)) *ᵥ e)) := by
  show WithLp.toLp 2 _ = WithLp.toLp 2 _
  congr 1
  rw [show ((1 : Matrix (dB × anc') (dB × anc') ℂ))
      = (1 : Matrix dB dB ℂ) ⊗ₖ (1 : Matrix anc' anc' ℂ) from
    (Matrix.one_kronecker_one).symm, mulVec_kron_kron_expVec, Matrix.one_kronecker_one,
    Matrix.one_mulVec]

/-- The same on the second party. -/
theorem stateVecB_expVec_kron_one (φ : dA × dB → ℂ) (e : anc × anc' → ℂ)
    (S : Matrix anc' anc' ℂ) :
    stateVecB (expVec φ e) ((1 : Matrix dB dB ℂ) ⊗ₖ S)
      = WithLp.toLp 2 (expVec φ (((1 : Matrix anc anc ℂ) ⊗ₖ S) *ᵥ e)) := by
  show WithLp.toLp 2 _ = WithLp.toLp 2 _
  congr 1
  rw [show ((1 : Matrix (dA × anc) (dA × anc) ℂ))
      = (1 : Matrix dA dA ℂ) ⊗ₖ (1 : Matrix anc anc ℂ) from
    (Matrix.one_kronecker_one).symm, mulVec_kron_kron_expVec, Matrix.one_kronecker_one,
    Matrix.one_mulVec]

end Expanded

/-! ## The transport, on the expanded and on the padded state -/

/-- **The ancilla's syndrome projector transports across the expanded state, exactly.** The two
halves of `hatVec`'s entangled pair are maximally entangled and the syndrome projectors are
symmetric, so moving one from Alice's half to Bob's costs nothing. -/
theorem stateVec_hatVec_syn (φ : dA × dB → ℂ) (W : Bas) (v : Anc F m) (a : F) :
    stateVec (hatVec (F := F) (m := m) φ) ((1 : Matrix dA dA ℂ) ⊗ₖ syn (weylOf W) v a)
      = stateVecB (hatVec (F := F) (m := m) φ)
        ((1 : Matrix dB dB ℂ) ⊗ₖ syn (weylOf W) v a) := by
  rw [hatVec, stateVec_expVec_kron_one, stateVecB_expVec_kron_one]
  congr 2
  have h := stateVec_epr_syn (w := weylOf W) (weylOf_transpose W) v a
  rw [stateVec, stateVecB] at h
  exact congrArg (WithLp.ofLp) h

/-- The expanded state's transport, as the vanishing of a cross-party deviation --- the form that
crosses to the padded state. -/
theorem xSqNorm_hatVec_syn (φ : dA × dB → ℂ) (W : Bas) (v : Anc F m) (a : F) :
    xSqNorm (hatVec (F := F) (m := m) φ) ((1 : Matrix dA dA ℂ) ⊗ₖ syn (weylOf W) v a)
        ((1 : Matrix dB dB ℂ) ⊗ₖ syn (weylOf W) v a) = 0 := by
  rw [xSqNorm, stateVec_hatVec_syn, sub_self, norm_zero]
  norm_num

namespace SimulPair

/- The pair space `((dA x Anc) x EA) x ((dB x Anc) x EB)` is a four-fold product whose
`DecidableEq` runs past the default instance-size bound --- each half alone is found, the product
is not. Raised here and nowhere else, as in `MIPRE/Background/QLD/MTilde.lean`. -/
set_option synthInstance.maxSize 1000

variable (P : SimulPair ψ MA MB δ)

/-- **The ancilla's syndrome projector transports across the padded state, exactly.**

This is the `approx_0` step of the paper's pulling chain (`eq:qld-pulling-3a`, and again at
`eq:qld-pulling-4`), on the state the chain is actually run on. `SimulPair` does not say that `Phi`
*is* an expanded state --- only that it reproduces its expectations --- and that is enough, because
the identity to be proved is the vanishing of a squared norm and a squared norm is an
expectation. -/
theorem stateVec_ancSyn (W : Bas) (v : Anc F m) (a : F) :
    stateVec P.Φ (aOp ((1 : Matrix dA dA ℂ) ⊗ₖ syn (weylOf W) v a))
      = stateVecB P.Φ (aOp ((1 : Matrix dB dB ℂ) ⊗ₖ syn (weylOf W) v a)) := by
  have hsa : (((1 : Matrix dA dA ℂ) ⊗ₖ syn (weylOf W) v a))ᴴ
      = (1 : Matrix dA dA ℂ) ⊗ₖ syn (weylOf W) v a := by
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      (isPVM_syn (isWeylFamily_weylOf W) v).isSelfAdjoint]
  have h : xSqNorm P.Φ (aOp ((1 : Matrix dA dA ℂ) ⊗ₖ syn (weylOf W) v a))
      (aOp ((1 : Matrix dB dB ℂ) ⊗ₖ syn (weylOf W) v a)) = 0 := by
    rw [P.xSqNorm_aOp hsa, xSqNorm_hatVec_syn]
  rw [xSqNorm, pow_eq_zero_iff (by norm_num), norm_eq_zero, sub_eq_zero] at h
  exact h

/-- **The two ancilla halves resolve the identity on the padded state** (`eq:qld-pulling-4`).
Summing the matched pairs of syndrome projectors, one on each party, leaves the state unchanged:
by the transport above each matched pair acts as the projector on one side alone, and those sum to
the identity. This is the step that lets the chain insert Bob's ancilla resolution. -/
theorem sum_ancSyn_mulVec (W : Bas) (v : Anc F m) :
    (∑ a : F, (MIPRE.aOp (aOp ((1 : Matrix dA dA ℂ) ⊗ₖ syn (weylOf W) v a))
        * MIPRE.bOp (aOp ((1 : Matrix dB dB ℂ) ⊗ₖ syn (weylOf W) v a)))) *ᵥ P.Φ = P.Φ := by
  have htr : ∀ a : F,
      (MIPRE.bOp (aOp ((1 : Matrix dB dB ℂ) ⊗ₖ syn (weylOf W) v a))) *ᵥ P.Φ
        = (MIPRE.aOp (aOp ((1 : Matrix dA dA ℂ) ⊗ₖ syn (weylOf W) v a))) *ᵥ P.Φ := fun a =>
    congrArg WithLp.ofLp (P.stateVec_ancSyn W v a).symm
  have hidem : ∀ a : F,
      ((1 : Matrix dA dA ℂ) ⊗ₖ syn (weylOf W) v a) * ((1 : Matrix dA dA ℂ) ⊗ₖ syn (weylOf W) v a)
        = (1 : Matrix dA dA ℂ) ⊗ₖ syn (weylOf W) v a := fun a => by
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul,
      (isPVM_syn (isWeylFamily_weylOf W) v).idem]
  have hone : (∑ a : F, ((1 : Matrix dA dA ℂ) ⊗ₖ syn (weylOf W) v a))
      = (1 : Matrix (dA × Anc F m) (dA × Anc F m) ℂ) := by
    rw [← kronecker_sum_right, (isPVM_syn (isWeylFamily_weylOf W) v).sum_eq_one,
      Matrix.one_kronecker_one]
  rw [Matrix.sum_mulVec]
  have hstep : ∀ a : F,
      (MIPRE.aOp (aOp ((1 : Matrix dA dA ℂ) ⊗ₖ syn (weylOf W) v a))
          * MIPRE.bOp (aOp ((1 : Matrix dB dB ℂ) ⊗ₖ syn (weylOf W) v a))) *ᵥ P.Φ
        = (MIPRE.aOp (aOp ((1 : Matrix dA dA ℂ) ⊗ₖ syn (weylOf W) v a))) *ᵥ P.Φ := fun a => by
    rw [← Matrix.mulVec_mulVec, htr a, Matrix.mulVec_mulVec, ← aOp_mul, ← aOp_mul, hidem a]
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => hstep a, ← Matrix.sum_mulVec, ← aOp_sum,
    ← aOp_sum, hone, aOp_one, aOp_one, Matrix.one_mulVec]

end SimulPair

end MIPRE.QLD

end
