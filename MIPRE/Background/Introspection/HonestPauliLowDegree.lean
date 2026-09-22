/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.HonestPauliMeasurements
import MIPRE.Background.Introspection.HonestPauliCoarse
import MIPRE.Background.LIDT.Adapter.Value

/-! # The honest Pauli strategy passes its actual low-degree edges

The coefficient vectors used by the measurements are restrictions of the
same multilinear encoding. Both seeded line types include their sampled
point, including zero diagonal directions. Coarse measurements of the same
Pauli PVM therefore commute and have zero product on every rejected pair.
-/

noncomputable section
namespace MIPRE.QLD.Honest
open Matrix Finset Weyl LCS Introspection Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}

omit [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] in
theorem eval_lineAnswer {n : ℕ} (u v : LIDT.Point F m) (h : Register F m)
    (hn : (LowDegree.lineRestrict u v (LowDegree.ldEnc h)).natDegree ≤ n) (t : F) :
    (lineAnswer n u v h).eval t = MvPolynomial.eval (u + t • v) (LowDegree.ldEnc h) := by
  rw [← LowDegree.eval_lineRestrict]
  unfold LIDT.LinePoly.eval lineAnswer
  rw [Fin.sum_univ_eq_sum_range
    (fun i => (LowDegree.lineRestrict u v (LowDegree.ldEnc h)).coeff i * t ^ i) (n + 1)]
  exact (Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hn) t).symm

omit [Algebra (ZMod 2) F] in
/-- The seeded representative and parameter recover even a degenerate line. -/
theorem lowDeg_lineAnswer_rep {n : ℕ} (v u : LIDT.Point F m) (h : Register F m)
    (hn : (LowDegree.lineRestrict (LIDT.CL.rep v u) v (LowDegree.ldEnc h)).natDegree ≤ n) :
    lowDeg (LIDT.CL.rep v u) v u (lineAnswer n (LIDT.CL.rep v u) v h)
      (MvPolynomial.eval u (LowDegree.ldEnc h)) = true := by
  unfold lowDeg LIDT.CL.lineVsPoint
  apply decide_eq_true
  refine ⟨⟨LIDT.CL.lineParam (LIDT.CL.rep v u) v u,
    (LIDT.CL.rep_add_lineParam_smul v u).symm⟩, ?_⟩
  intro j
  rw [eval_lineAnswer _ _ _ hn, LIDT.CL.rep_add_lineParam_smul]

omit [Algebra (ZMod 2) F] in
theorem lowDeg_axis_lineAnswer (hd : 1 ≤ d) (i : Fin m) (u : LIDT.Point F m)
    (h : Register F m) :
    lowDeg (LIDT.CL.rep (Pi.single i 1) u) (Pi.single i 1) u
      (lineAnswer d (LIDT.CL.rep (Pi.single i 1) u) (Pi.single i 1) h)
      (MvPolynomial.eval u (LowDegree.ldEnc h)) = true := by
  exact lowDeg_lineAnswer_rep _ _ h
    ((LowDegree.natDegree_lineRestrict_single_le _ _ _).trans
      ((LowDegree.degreeOf_ldEnc_le h i).trans hd))

omit [Algebra (ZMod 2) F] in
theorem lowDeg_diagonal_lineAnswer (hd : 1 ≤ d) (v u : LIDT.Point F m)
    (h : Register F m) :
    lowDeg (LIDT.CL.rep v u) v u (lineAnswer (m * d) (LIDT.CL.rep v u) v h)
      (MvPolynomial.eval u (LowDegree.ldEnc h)) = true := by
  apply lowDeg_lineAnswer_rep
  exact (LowDegree.natDegree_lineRestrict_le _ _ _).trans
    ((LowDegree.totalDegree_ldEnc_le h).trans (by simpa using Nat.mul_le_mul_left m hd))

variable [NeZero m]

theorem answerOp_aline_point_commute (hm : m ∣ Fintype.card F) (c : Content F m)
    (W : Bas) (a b : Answer F m d) :
    Commute (answerOp hm (c.question hm (.aline W)) a)
      (answerOp hm (c.question hm (.point W)) b) :=
  pvm_fibre_commute (pauliLift W) (pauliLift_isPVM W) _ _ a b

theorem answerOp_dline_point_commute (hm : m ∣ Fintype.card F) (c : Content F m)
    (W : Bas) (a b : Answer F m d) :
    Commute (answerOp hm (c.question hm (.dline W)) a)
      (answerOp hm (c.question hm (.point W)) b) :=
  pvm_fibre_commute (pauliLift W) (pauliLift_isPVM W) _ _ a b

theorem answerOp_pauli_point_commute (hm : m ∣ Fintype.card F) (c : Content F m)
    (W : Bas) (a b : Answer F m d) :
    Commute (answerOp hm (c.question hm (.pauli W)) a)
      (answerOp hm (c.question hm (.point W)) b) :=
  pvm_fibre_commute (pauliLift W) (pauliLift_isPVM W) _ _ a b

theorem answerOp_aline_point_reject (hm : m ∣ Fintype.card F) (hd : 1 ≤ d)
    (c : Content F m) (W : Bas) (a b : Answer F m d)
    (hr : accepts hm (c.question hm (.aline W)) (c.question hm (.point W)) a b = false) :
    answerOp hm (c.question hm (.aline W)) a *
      answerOp hm (c.question hm (.point W)) b = 0 := by
  apply pvm_fibre_reject (pauliLift W) (pauliLift_isPVM W) _ _
    (accepts hm (c.question hm (.aline W)) (c.question hm (.point W))) _ a b hr
  intro h
  simpa [accepts, Content.question, Question.fmtOk, subtests, Question.ty, pairTest] using
    lowDeg_axis_lineAnswer hd (LIDT.CL.chi hm c.s) (c.pt W) h

theorem answerOp_dline_point_reject (hm : m ∣ Fintype.card F) (hd : 1 ≤ d)
    (c : Content F m) (W : Bas) (a b : Answer F m d)
    (hr : accepts hm (c.question hm (.dline W)) (c.question hm (.point W)) a b = false) :
    answerOp hm (c.question hm (.dline W)) a *
      answerOp hm (c.question hm (.point W)) b = 0 := by
  apply pvm_fibre_reject (pauliLift W) (pauliLift_isPVM W) _ _
    (accepts hm (c.question hm (.dline W)) (c.question hm (.point W))) _ a b hr
  intro h
  simpa [accepts, Content.question, Question.fmtOk, subtests, Question.ty, pairTest] using
    lowDeg_diagonal_lineAnswer hd (LIDT.CL.zeroBelow (LIDT.CL.chi hm c.s) c.v) (c.pt W) h

theorem answerOp_pauli_point_reject (hm : m ∣ Fintype.card F)
    (c : Content F m) (W : Bas) (a b : Answer F m d)
    (hr : accepts hm (c.question hm (.pauli W)) (c.question hm (.point W)) a b = false) :
    answerOp hm (c.question hm (.pauli W)) a *
      answerOp hm (c.question hm (.point W)) b = 0 := by
  apply pvm_fibre_reject (pauliLift W) (pauliLift_isPVM W) _ _
    (accepts hm (c.question hm (.pauli W)) (c.question hm (.point W))) _ a b hr
  intro h
  simp [accepts, Content.question, Question.fmtOk, subtests, Question.ty, pairTest]

end MIPRE.QLD.Honest
