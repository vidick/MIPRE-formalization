/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.Win
import MIPRE.Foundations.Pasting
import MIPRE.Background.QLD.Simul

/-!
# The point measurement and the Pauli basis reading, on one party

The repaired proof of `lem:qld-exact-paulis` needs the strategy's `(Point, W)` measurement to be
close to the low-degree reading of its `(Pauli, W)` answer **on the same party**: the Pauli basis
answer does not depend on the sampled point, which is what lets Schwartz--Zippel be applied to a
uniform point independent of the operators.

Both inputs are items of `lem:qld-win-implications`, and both are *cross-party*: the point
measurements of the two players agree (`item_consistency` at the type `(Point, W)`), and Alice's
point answer agrees with the evaluation at the sampled point of the low-degree encoding of Bob's
Pauli basis answer (`item_pauli_consistency`). They share Alice's family, so the triangle
inequality of `normSq_stateVecB_sub_le` leaves a statement about Bob alone, at four times the
error: `688 ε`.

Nothing here is expanded or padded: this is the bare strategy, and the statement is the one the
mass argument of `MIPRE/Background/QLD/NonMultilinear.lean` consumes.
-/

noncomputable section

namespace MIPRE

open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder

/-! ## A common ancilla factor drops out of a same-party deviation -/

section Conv

variable {dA dB anc anc' C : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  [Fintype anc] [DecidableEq anc] [Fintype anc'] [DecidableEq anc'] [Fintype C] [DecidableEq C]
  [AddCommGroup C]

/-- **The convolution of a family on the party's own register with one on its ancilla**: the shape
every hatted measurement has, `X̂_c = ∑_{a + b = c} X_a ⊗ T_b`. -/
def conv (Z : C → Matrix dB dB ℂ) (T : C → Matrix anc' anc' ℂ) (c : C) :
    Matrix (dB × anc') (dB × anc') ℂ :=
  ∑ p ∈ univ.filter fun p : C × C => p.1 + p.2 = c, Z p.1 ⊗ₖ T p.2

/-- Against a projective ancilla family the cross terms of `X̂ᴴ X̂` vanish: the ancilla outcome
determines the other one. -/
theorem conjTranspose_conv_mul_conv (Z : C → Matrix dB dB ℂ) {T : C → Matrix anc' anc' ℂ}
    (hT : IsPVM T) (c : C) :
    (conv (dB := dB) Z T c)ᴴ * conv Z T c = conv (fun a => (Z a)ᴴ * Z a) T c := by
  classical
  simp only [conv, Matrix.conjTranspose_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.sum_eq_single p]
  · rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hT.isSelfAdjoint, hT.idem]
  · intro p' hp' hne
    have hb : p'.2 ≠ p.2 := by
      intro hb
      apply hne
      have h1 := (mem_filter.mp hp).2
      have h2 := (mem_filter.mp hp').2
      refine Prod.ext ?_ hb
      have : p'.1 + p'.2 = p.1 + p.2 := by rw [h1, h2]
      rw [hb] at this
      exact add_right_cancel this
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hT.isSelfAdjoint,
      hT.orthogonal hb, Matrix.kronecker_zero]
  · intro hp'
    exact absurd hp hp'

/-- Summing a convolution over the outcome frees the ancilla factor. -/
theorem sum_conv (Z : C → Matrix dB dB ℂ) {T : C → Matrix anc' anc' ℂ} (hT : IsPVM T) :
    ∑ c, conv (dB := dB) Z T c = (∑ a, Z a) ⊗ₖ (1 : Matrix anc' anc' ℂ) := by
  classical
  simp only [conv]
  have h : ∑ c, ∑ p ∈ univ.filter fun p : C × C => p.1 + p.2 = c, Z p.1 ⊗ₖ T p.2
      = ∑ p : C × C, Z p.1 ⊗ₖ T p.2 :=
    Finset.sum_fiberwise univ (fun p : C × C => p.1 + p.2) fun p => Z p.1 ⊗ₖ T p.2
  have hrow : ∀ a : C, (∑ b : C, Z a ⊗ₖ T b) = Z a ⊗ₖ (1 : Matrix anc' anc' ℂ) := fun a => by
    rw [← kronecker_sum_right, hT.sum_eq_one]
  calc ∑ c, ∑ p ∈ univ.filter fun p : C × C => p.1 + p.2 = c, Z p.1 ⊗ₖ T p.2
      = ∑ p : C × C, Z p.1 ⊗ₖ T p.2 := h
    _ = ∑ a : C, ∑ b : C, Z a ⊗ₖ T b := Fintype.sum_prod_type _
    _ = ∑ a : C, Z a ⊗ₖ (1 : Matrix anc' anc' ℂ) := Finset.sum_congr rfl fun a _ => hrow a
    _ = (∑ a, Z a) ⊗ₖ (1 : Matrix anc' anc' ℂ) :=
        (sum_kronecker_left univ Z (1 : Matrix anc' anc' ℂ)).symm

/-- **The transfer**: on the expanded state, the same-party deviation of two convolutions with a
common projective ancilla family is the deviation of the two families themselves. -/
theorem sum_normSq_stateVecB_conv_eq (ψ : dA × dB → ℂ) {e : anc × anc' → ℂ}
    (he : star e ⬝ᵥ e = 1) (Z : C → Matrix dB dB ℂ) {T : C → Matrix anc' anc' ℂ} (hT : IsPVM T) :
    ∑ c, ‖stateVecB (expVec ψ e) (conv Z T c)‖ ^ 2 = ∑ a, ‖stateVecB ψ (Z a)‖ ^ 2 := by
  classical
  have hterm : ∀ c, ‖stateVecB (expVec ψ e) (conv Z T c)‖ ^ 2
      = bornProb (expVec ψ e) 1 (conv (fun a => (Z a)ᴴ * Z a) T c) := fun c => by
    rw [normSq_stateVecB_eq_one_bornProb, conjTranspose_conv_mul_conv Z hT]
  rw [Finset.sum_congr rfl fun c (_ : c ∈ univ) => hterm c, ← bornProb_sum_right,
    sum_conv _ hT]
  have hone : (1 : Matrix (dA × anc) (dA × anc) ℂ)
      = (1 : Matrix dA dA ℂ) ⊗ₖ (1 : Matrix anc anc ℂ) := (Matrix.one_kronecker_one).symm
  rw [hone, bornProb_expVec_kron ψ e Matrix.PosSemidef.one Matrix.PosSemidef.one]
  have hb : bornProb e (1 : Matrix anc anc ℂ) (1 : Matrix anc' anc' ℂ) = 1 := by
    rw [bornProb, Matrix.one_kronecker_one, Matrix.one_mulVec, he]
    norm_num
  rw [hb, mul_one, bornProb_sum_right]
  exact Finset.sum_congr rfl fun a _ => (normSq_stateVecB_eq_one_bornProb ψ (Z a)).symm

end Conv

end MIPRE

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LowDegree
open scoped Kronecker ComplexOrder MatrixOrder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {hm : m ∣ Fintype.card F}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}

/-- **The point measurement and the Pauli basis reading agree on Bob's side**, on average over the
verifier's content and at `688 ε`: the two cross-party items of `lem:qld-win-implications` share
Alice's point measurement, so the triangle inequality removes it. -/
theorem sum_normSq_point_sub_pauli_le (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) (W : Bas) :
    ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ∑ o : F, ‖stateVecB ψ ((((MB (c.question hm (.point W))).map rdVal).mats o).val
          - (((MB (c.question hm (.pauli W))).map (rdPauli (c.pt W))).mats o).val)‖ ^ 2
      ≤ 688 * ε := by
  have h1 := item_consistency (MB := MB) hψ hfail (.point W) rdVal
  have h2 := item_pauli_consistency (MB := MB) hψ hfail W
  rw [xPovmDist] at h1
  have hterm : ∀ c : Content F m,
      ∑ o : F, ‖stateVecB ψ ((((MB (c.question hm (.point W))).map rdVal).mats o).val
        - (((MB (c.question hm (.pauli W))).map (rdPauli (c.pt W))).mats o).val)‖ ^ 2
      ≤ 2 * ∑ o : F, xSqNorm ψ ((((MA (c.question hm (.point W))).map rdVal).mats o).val)
            ((((MB (c.question hm (.point W))).map rdVal).mats o).val)
        + 2 * ∑ o : F, xSqNorm ψ ((((MA (c.question hm (.point W))).map rdVal).mats o).val)
            ((((MB (c.question hm (.pauli W))).map (rdPauli (c.pt W))).mats o).val) := by
    intro c
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun o _ => normSq_stateVecB_sub_le ψ _ _ _
  have hsum := Finset.sum_le_sum fun c (_ : c ∈ univ) =>
    mul_le_mul_of_nonneg_left (hterm c)
      (by positivity : (0 : ℝ) ≤ (Fintype.card (Content F m) : ℝ)⁻¹)
  have hsplit : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
      (2 * ∑ o : F, xSqNorm ψ ((((MA (c.question hm (.point W))).map rdVal).mats o).val)
          ((((MB (c.question hm (.point W))).map rdVal).mats o).val)
        + 2 * ∑ o : F, xSqNorm ψ ((((MA (c.question hm (.point W))).map rdVal).mats o).val)
          ((((MB (c.question hm (.pauli W))).map (rdPauli (c.pt W))).mats o).val))
      = 2 * (∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
          ∑ o : F, xSqNorm ψ ((((MA (c.question hm (.point W))).map rdVal).mats o).val)
            ((((MB (c.question hm (.point W))).map rdVal).mats o).val))
        + 2 * ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
          ∑ o : F, xSqNorm ψ ((((MA (c.question hm (.point W))).map rdVal).mats o).val)
            ((((MB (c.question hm (.pauli W))).map (rdPauli (c.pt W))).mats o).val) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hsplit] at hsum
  linarith

end MIPRE.QLD

end
