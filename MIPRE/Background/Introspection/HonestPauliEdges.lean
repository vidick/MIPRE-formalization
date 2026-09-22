/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.HonestPauliCoarse

/-! # The commuting and Magic Square edges of the honest Pauli strategy -/

noncomputable section

namespace MIPRE.QLD.Honest

open Matrix Finset Weyl LCS Introspection Classical
open scoped Kronecker

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {m d : ℕ} [NeZero m]

private theorem pvm_commute {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]
    {P : X → Matrix I I ℂ} (hP : IsPVM P) (x y : X) : Commute (P x) (P y) := by
  by_cases h : x = y
  · subst y; exact Commute.refl _
  · change P x * P y = P y * P x
    rw [hP.orthogonal h, hP.orthogonal (Ne.symm h)]

theorem answerOp_point_pairB_commute (hm : m ∣ Fintype.card F)
    (ω : Omega F m) (W : Bas) (a b : Answer F m d) :
    Commute (answerOp hm (.point W (ω.pt W)) a) (answerOp hm (.pairB W ω) b) := by
  by_cases h : gam ω = 0
  · simp only [answerOp, pairBBranch, if_pos h, probeLift_eq_fibSum, fibre_comp]
    exact pvm_fibre_commute _ (pauliLift_isPVM W) _ _ a b
  · simp only [answerOp, pairBBranch, if_neg h]
    apply fibre_commute
    intro x y
    exact (readout_constant_commute 0 y _).symm

theorem answerOp_point_pairB_reject (hm : m ∣ Fintype.card F)
    (ω : Omega F m) (W : Bas) (a b : Answer F m d)
    (hr : accepts hm (.point W (ω.pt W)) (.pairB W ω) a b = false) :
    answerOp hm (.point W (ω.pt W)) a * answerOp hm (.pairB W ω) b = 0 := by
  by_cases h : gam ω = 0
  · simp only [answerOp, pairBBranch, if_pos h, probeLift_eq_fibSum, fibre_comp]
    apply pvm_fibre_reject _ (pauliLift_isPVM W) _ _
      (accepts hm (.point W (ω.pt W)) (.pairB W ω)) _ a b hr
    intro x
    simp [accepts, subtests, Question.ty, Question.fmtOk, pairTest, h, probeLabel]
  · simp only [answerOp, pairBBranch, if_neg h]
    apply fibre_reject _ _ _ _ (accepts hm (.point W (ω.pt W)) (.pairB W ω)) _ a b hr
    intro x y hxy
    simp [accepts, subtests, Question.ty, Question.fmtOk, pairTest, h] at hxy

/-- The cells used to anchor the two Pauli probes. -/
def distinguished : Bas → Fin LCS.MagicSquare.layout.s
  | .X => LCS.MagicSquare.v 0
  | .Z => LCS.MagicSquare.v 4

omit [NeZero m] in
theorem variableBranch_distinguished (ω : Omega F m) (h : gam ω ≠ 0) (W : Bas) :
    variableBranch ω (distinguished W) = probeLift ω W := by
  funext b
  cases W
  · exact variableBranch_X ω h b
  · exact variableBranch_Z ω h b

theorem answerOp_point_var_commute (hm : m ∣ Fintype.card F)
    (ω : Omega F m) (W : Bas) (a b : Answer F m d) :
    Commute (answerOp hm (.point W (ω.pt W)) a)
      (answerOp hm (.var (distinguished W) ω) b) := by
  by_cases h : gam ω = 0
  · simp only [answerOp, variableBranch, if_pos h]
    apply fibre_commute
    intro x y
    exact (readout_constant_commute 0 y _).symm
  · simp only [answerOp, variableBranch_distinguished ω h, probeLift_eq_fibSum, fibre_comp]
    exact pvm_fibre_commute _ (pauliLift_isPVM W) _ _ a b

theorem answerOp_point_var_reject (hm : m ∣ Fintype.card F)
    (ω : Omega F m) (W : Bas) (a b : Answer F m d)
    (hr : accepts hm (.point W (ω.pt W)) (.var (distinguished W) ω) a b = false) :
    answerOp hm (.point W (ω.pt W)) a * answerOp hm (.var (distinguished W) ω) b = 0 := by
  by_cases h : gam ω = 0
  · simp only [answerOp, variableBranch, if_pos h]
    apply fibre_reject _ _ _ _ (accepts hm (.point W (ω.pt W)) (.var (distinguished W) ω)) _ a b hr
    intro x y hxy
    simp [accepts, subtests, Question.ty, Question.fmtOk, pairTest, h] at hxy
  · simp only [answerOp, variableBranch_distinguished ω h, probeLift_eq_fibSum, fibre_comp]
    apply pvm_fibre_reject _ (pauliLift_isPVM W) _ _
      (accepts hm (.point W (ω.pt W)) (.var (distinguished W) ω)) _ a b hr
    intro x
    cases W <;> simp [accepts, subtests, Question.ty, Question.fmtOk, pairTest,
      h, probeLabel, distinguished, Omega.r]

theorem answerOp_con_var_commute (hm : m ∣ Fintype.card F) (ω : Omega F m)
    (c : Fin LCS.MagicSquare.layout.r) (j : Fin LCS.MagicSquare.layout.s)
    (hj : j ∈ LCS.MagicSquare.layout.V c) (a b : Answer F m d) :
    Commute (answerOp hm (.con c ω) a) (answerOp hm (.var j ω) b) := by
  simp only [answerOp]
  apply fibre_commute
  intro x y
  by_cases h : gam ω = 0
  · simp only [constraintBranch, variableBranch, if_pos h]
    exact readout_constant_commute 0 x _
  · simp only [constraintBranch, variableBranch, if_neg h]
    have hh := (HonestMagicSquare.variable_constraint_commute
      (probe_basis_anticommute ω h) c (LCS.MagicSquare.cellIdx c j) x y).symm
    simpa only [HonestMagicSquare.cellIndex, LCS.MagicSquare.cell_cellIdx hj] using hh

theorem answerOp_con_var_reject (hm : m ∣ Fintype.card F) (ω : Omega F m)
    (c : Fin LCS.MagicSquare.layout.r) (j : Fin LCS.MagicSquare.layout.s)
    (hj : j ∈ LCS.MagicSquare.layout.V c) (a b : Answer F m d)
    (hr : accepts hm (.con c ω) (.var j ω) a b = false) :
    answerOp hm (.con c ω) a * answerOp hm (.var j ω) b = 0 := by
  simp only [answerOp]
  apply fibre_reject _ _ _ _ (accepts hm (.con c ω) (.var j ω)) _ a b hr
  intro x y hxy
  by_cases h : gam ω = 0
  · simp [accepts, subtests, Question.ty, Question.fmtOk, pairTest, h] at hxy
  · simp only [constraintBranch, variableBranch, if_neg h]
    have hb : ¬ (x 0 + x 1 + x 2 = LCS.MagicSquare.game.b c ∧ x (LCS.MagicSquare.cellIdx c j) = y) := by
      intro hh
      have ht : accepts (d := d) hm (.con c ω) (.var j ω) (.bitTriple x) (.bit y) = true := by
        simp [accepts, subtests, Question.ty, Question.fmtOk, pairTest, h, hj,
          Fin.sum_univ_three, hh.1, hh.2]
      rw [ht] at hxy
      contradiction
    have hh := HonestMagicSquare.constraint_reject_zero (probe_basis_isObservable ω .X)
      (probe_basis_isObservable ω .Z) (probe_basis_anticommute ω h)
      c x (LCS.MagicSquare.cellIdx c j) y hb
    simpa only [HonestMagicSquare.cellIndex, LCS.MagicSquare.cell_cellIdx hj] using hh

omit [NeZero m] in
private theorem probe_joint_commute (ω : Omega F m) (h : gam ω = 0)
    (W : Bas) (b : ZMod 2) (p : ZMod 2 × ZMod 2) :
    Commute (probeLift ω W b) (probeLift ω .X p.1 * probeLift ω .Z p.2) := by
  cases W
  · exact (pvm_commute (probeLift_isPVM ω .X) b p.1).mul_right (probeLift_commute ω h b p.2)
  · exact (probeLift_commute ω h p.1 b).symm.mul_right (pvm_commute (probeLift_isPVM ω .Z) b p.2)

omit [NeZero m] in
private theorem probe_joint_reject (ω : Omega F m) (h : gam ω = 0)
    (W : Bas) (b : ZMod 2) (p : ZMod 2 × ZMod 2) (hb : b ≠ pairLabel p W) :
    probeLift ω W b * (probeLift ω .X p.1 * probeLift ω .Z p.2) = 0 := by
  cases W <;> simp only [pairLabel] at hb
  · rw [← mul_assoc, (probeLift_isPVM ω .X).orthogonal hb, zero_mul]
  · rw [← mul_assoc, (probeLift_commute ω h p.1 b).eq.symm, mul_assoc,
      (probeLift_isPVM ω .Z).orthogonal hb, mul_zero]

theorem answerOp_pairB_pair_commute (hm : m ∣ Fintype.card F)
    (ω : Omega F m) (W : Bas) (a b : Answer F m d) :
    Commute (answerOp hm (.pairB W ω) a) (answerOp hm (.pair ω) b) := by
  by_cases h : gam ω = 0
  · simp only [answerOp, pairBBranch, pairBranch, if_pos h, fibre_comp]
    exact fibre_commute _ _ _ _ (probe_joint_commute ω h W) a b
  · simp only [answerOp, pairBBranch, pairBranch, if_neg h]
    apply fibre_commute
    intro x y
    exact readout_constant_commute 0 x _

theorem answerOp_pairB_pair_reject (hm : m ∣ Fintype.card F)
    (ω : Omega F m) (W : Bas) (a b : Answer F m d)
    (hr : accepts hm (.pairB W ω) (.pair ω) a b = false) :
    answerOp hm (.pairB W ω) a * answerOp hm (.pair ω) b = 0 := by
  by_cases h : gam ω = 0
  · simp only [answerOp, pairBBranch, pairBranch, if_pos h, fibre_comp]
    apply fibre_reject _ _ _ _ (accepts hm (.pairB W ω) (.pair ω)) _ a b hr
    intro x y hxy
    apply probe_joint_reject ω h W x y
    intro he
    simp [accepts, subtests, Question.ty, Question.fmtOk, pairTest, h, he] at hxy
  · simp only [answerOp, pairBBranch, pairBranch, if_neg h]
    apply fibre_reject _ _ _ _ (accepts hm (.pairB W ω) (.pair ω)) _ a b hr
    intro x y hxy
    simp [accepts, subtests, Question.ty, Question.fmtOk, pairTest, h] at hxy

end MIPRE.QLD.Honest
