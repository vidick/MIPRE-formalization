/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.Win
import MIPRE.Foundations.Pasting

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
