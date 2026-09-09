/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.LIDT.MIPStarRE.LDT.Test.Defs
import MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.Distribution

/-!
# Bridge, part 5: consistency defects of complete measurements

Generic facts about MIPStarRE's bipartite consistency defect
`qBipartiteConsDefect ψ A B = max 0 (⟨A_tot ⊗ B_tot⟩ − ∑ₐ ⟨A_a ⊗ B_a⟩)` when the
measurements `A`, `B` are complete (`total = 1`) and the state is normalized:

* the defect is `1 − ∑ₐ ⟨A_a ⊗ B_a⟩`, and equals the off-diagonal mass
  `∑_{a ≠ b} ⟨A_a ⊗ B_b⟩` (`qBipartiteConsDefect_eq_offDiagonal`);
* for coarse-grainings `postprocess A f`, `postprocess B g`, the matching mass is
  `∑_{a, b : f a = g b} ⟨A_a ⊗ B_b⟩` (`qBipartiteMatchMass_postprocess`), so the defect is
  bounded by `1 − acc` whenever `acc` is a sum of some of the terms `⟨A_a ⊗ B_b⟩` with
  `f a = g b` (`qBipartiteConsDefect_postprocess_le`).

These are the two facts through which the game's acceptance probability
(`Bridge.Value`) and our `inconsistency` (`Bridge.Consistency`) are compared with the
MIPStarRE quantities.
-/

open MIPStarRE.LDT
open scoped MatrixOrder

namespace MIPRE.LIDT.Bridge

variable {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- Expectation values of tensor products of measurement operators are nonnegative. -/
theorem ev_opTensor_outcome_nonneg (ψ : QuantumState (ιA × ιB)) (A : SubMeas α ιA)
    (B : SubMeas β ιB) (a : α) (b : β) :
    0 ≤ ev ψ (opTensor (A.outcome a) (B.outcome b)) :=
  ev_nonneg_of_psd ψ _ (opTensor_nonneg (A.outcome_pos a) (B.outcome_pos b))

/-- The total mass of two complete measurements on a normalized state is one. -/
theorem sum_ev_opTensor_outcome (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (A : SubMeas α ιA) (B : SubMeas β ιB) (hA : A.total = 1) (hB : B.total = 1) :
    ∑ a, ∑ b, ev ψ (opTensor (A.outcome a) (B.outcome b)) = 1 := by
  have h : ∑ a, ∑ b, opTensor (A.outcome a) (B.outcome b) =
      (1 : MIPStarRE.Quantum.Op (ιA × ιB)) := by
    simp_rw [← opTensor_sum_right_univ, ← opTensor_sum_left_univ, A.sum_eq_total, B.sum_eq_total,
      hA, hB]
    exact Matrix.one_kronecker_one
  rw [← ev_one_of_isNormalized ψ hψ, ← h, ev_sum]
  exact Finset.sum_congr rfl fun a _ => (ev_sum ψ _).symm

/-- The matching mass of two coarse-grained measurements. -/
theorem qBipartiteMatchMass_postprocess [DecidableEq γ] (ψ : QuantumState (ιA × ιB))
    (A : SubMeas α ιA) (B : SubMeas β ιB) (f : α → γ) (g : β → γ) :
    qBipartiteMatchMass ψ (postprocess A f) (postprocess B g) =
      ∑ a, ∑ b, if f a = g b then ev ψ (opTensor (A.outcome a) (B.outcome b)) else 0 := by
  simp only [qBipartiteMatchMass, SubMeas.postprocess_outcome, opTensor_sum_left_finset,
    opTensor_sum_right_finset, ev_finset_sum]
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact Finset.sum_comm

/-- The matching mass of two complete measurements is at most one. -/
theorem qBipartiteMatchMass_le_one (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (A : SubMeas α ιA) (B : SubMeas α ιB) (hA : A.total = 1) (hB : B.total = 1) :
    qBipartiteMatchMass ψ A B ≤ 1 := by
  rw [← sum_ev_opTensor_outcome ψ hψ A B hA hB]
  unfold qBipartiteMatchMass
  refine Finset.sum_le_sum fun a _ => ?_
  exact Finset.single_le_sum (fun b _ => ev_opTensor_outcome_nonneg ψ A B a b) (Finset.mem_univ a)

/-- For complete measurements on a normalized state the defect is `1 − matching mass`. -/
theorem qBipartiteConsDefect_of_complete (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (A : SubMeas α ιA) (B : SubMeas α ιB) (hA : A.total = 1) (hB : B.total = 1) :
    qBipartiteConsDefect ψ A B = 1 - qBipartiteMatchMass ψ A B := by
  have h1 : ev ψ (opTensor A.total B.total) = 1 := by
    rw [hA, hB, show opTensor (1 : MIPStarRE.Quantum.Op ιA) (1 : MIPStarRE.Quantum.Op ιB) = 1 from
      Matrix.one_kronecker_one]
    exact ev_one_of_isNormalized ψ hψ
  simp only [qBipartiteConsDefect, h1]
  exact max_eq_right (sub_nonneg.mpr (qBipartiteMatchMass_le_one ψ hψ A B hA hB))

/-- For complete measurements on a normalized state the defect is the off-diagonal mass. -/
theorem qBipartiteConsDefect_eq_offDiagonal [DecidableEq α] (ψ : QuantumState (ιA × ιB))
    (hψ : ψ.IsNormalized) (A : SubMeas α ιA) (B : SubMeas α ιB) (hA : A.total = 1)
    (hB : B.total = 1) :
    qBipartiteConsDefect ψ A B =
      ∑ a, ∑ b, if a = b then 0 else ev ψ (opTensor (A.outcome a) (B.outcome b)) := by
  rw [qBipartiteConsDefect_of_complete ψ hψ A B hA hB, ← sum_ev_opTensor_outcome ψ hψ A B hA hB]
  unfold qBipartiteMatchMass
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h : ∀ b, (if a = b then (0 : ℝ) else ev ψ (opTensor (A.outcome a) (B.outcome b))) =
      ev ψ (opTensor (A.outcome a) (B.outcome b)) -
        if a = b then ev ψ (opTensor (A.outcome a) (B.outcome b)) else 0 := by
    intro b; split_ifs <;> simp
  simp only [h, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The defect of two coarse-grainings of complete measurements is at most `1 − acc` for
any acceptance mass `acc` made of terms that force equal coarse-grained outcomes. -/
theorem qBipartiteConsDefect_postprocess_le [DecidableEq γ] (ψ : QuantumState (ιA × ιB))
    (hψ : ψ.IsNormalized)
    (A : SubMeas α ιA) (B : SubMeas β ιB) (hA : A.total = 1) (hB : B.total = 1)
    (f : α → γ) (g : β → γ) (D : α → β → Prop) [DecidableRel D] (hD : ∀ a b, D a b → f a = g b) :
    qBipartiteConsDefect ψ (postprocess A f) (postprocess B g) ≤
      1 - ∑ a, ∑ b, if D a b then ev ψ (opTensor (A.outcome a) (B.outcome b)) else 0 := by
  rw [qBipartiteConsDefect_of_complete ψ hψ _ _ (by simpa [postprocess] using hA)
    (by simpa [postprocess] using hB), qBipartiteMatchMass_postprocess]
  refine sub_le_sub_left (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_) 1
  by_cases h : D a b
  · rw [if_pos h, if_pos (hD a b h)]
  · rw [if_neg h]
    by_cases h' : f a = g b
    · rw [if_pos h']
      exact ev_opTensor_outcome_nonneg ψ A B a b
    · rw [if_neg h']

/-! ## Averages over uniform distributions -/

/-- The consistency error under the uniform distribution is the average of the defects. -/
theorem bipartiteConsError_uniform {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {ιA ιB α : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Fintype α]
    (ψ : QuantumState (ιA × ιB)) (A : IdxSubMeas X α ιA) (B : IdxSubMeas X α ιB) :
    bipartiteConsError ψ (uniformDistribution X) A B =
      (1 / (Fintype.card X : ℝ)) * ∑ x, qBipartiteConsDefect ψ (A x) (B x) := by
  classical
  unfold bipartiteConsError avgOver uniformDistribution
  simp only [Distribution.uniformOnFinset_support, Distribution.uniformOnFinset_weight,
    Finset.mem_univ, if_true, Finset.card_univ, Finset.mul_sum]

end MIPRE.LIDT.Bridge
