/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.HonestPauliObservables
import MIPRE.Foundations.LowDegree.LineRestrict
import MIPRE.Foundations.Introspection.Readout

/-! # The honest measurements for all twenty-six Pauli question types

Every measurement uses the same field register tensor one qubit. The low-degree
questions read functions of a Pauli outcome; the commuting and anticommuting
branches use the actual verifier phase. All answer constructors and inactive
branches are explicit.
-/

noncomputable section

namespace MIPRE.QLD.Honest

open Matrix Finset Weyl LCS Introspection Classical
open scoped Kronecker

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}

abbrev Space (F : Type*) (m : ℕ) := Register F m × Fin 2

def liftOp (M : Matrix (Register F m) (Register F m) ℂ) : Matrix (Space F m) (Space F m) ℂ :=
  M ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)

omit [Field F] [Algebra (ZMod 2) F] in
theorem liftOp_isPVM {A : Type*} [Fintype A] [DecidableEq A]
    {P : A → Matrix (Register F m) (Register F m) ℂ} (hP : IsPVM P) :
    IsPVM (fun a => liftOp (P a)) where
  isSelfAdjoint a := by simp only [liftOp, conjTranspose_kronecker, hP.isSelfAdjoint, conjTranspose_one]
  idem a := by rw [liftOp, ← mul_kronecker_mul, hP.idem, one_mul]
  sum_eq_one := by
    simp only [liftOp]
    rw [← sum_kronecker_left, hP.sum_eq_one, one_kronecker_one]

def pauliLift (W : Bas) (h : Register F m) : Matrix (Space F m) (Space F m) ℂ :=
  liftOp (pauliOp W h)

theorem pauliLift_isPVM (W : Bas) : IsPVM (pauliLift (F := F) (m := m) W) :=
  liftOp_isPVM (pauliOp_isPVM W)

def probeLift (ω : Omega F m) (W : Bas) (b : ZMod 2) : Matrix (Space F m) (Space F m) ℂ :=
  liftOp (probeOp ω W b)

theorem probeLift_isPVM (ω : Omega F m) (W : Bas) : IsPVM (probeLift ω W) :=
  liftOp_isPVM (probeOp_isPVM ω W)

theorem probeOp_eq_projector (ω : Omega F m) (W : Bas) (b : ZMod 2) :
    probeOp ω W b = observableToProjector (basis W (probeVector ω W)) b := by
  rw [← probe_observable]
  have h := binary_measurement_eq_projector _ (probeOp_isMeasurementSystem ω W) b
  rcases zmod_two_eq_zero_or_one b with rfl | rfl <;>
    simpa [observableToProjector, observableSign] using h

theorem probeOp_commute (ω : Omega F m) (h : gam ω = 0) (a b : ZMod 2) :
    Commute (probeOp ω .X a) (probeOp ω .Z b) := by
  rw [probeOp_eq_projector, probeOp_eq_projector]
  exact commute_observableToProjector (probe_basis_commute ω h) a b

theorem probeLift_commute (ω : Omega F m) (h : gam ω = 0) (a b : ZMod 2) :
    Commute (probeLift ω .X a) (probeLift ω .Z b) := by
  change liftOp _ * liftOp _ = liftOp _ * liftOp _
  simp only [liftOp, ← mul_kronecker_mul]
  rw [(probeOp_commute ω h a b).eq]

/-- The polynomial coefficient answer to a line query. -/
def lineAnswer (n : ℕ) (u v : LIDT.Point F m) (h : Register F m) : LIDT.LinePoly F n :=
  fun i => (LowDegree.lineRestrict u v (LowDegree.ldEnc h)).coeff i.val

def pairLabel (p : ZMod 2 × ZMod 2) : Bas → ZMod 2
  | .X => p.1
  | .Z => p.2

def pairBranch (ω : Omega F m) : (Bas → ZMod 2) → Matrix (Space F m) (Space F m) ℂ :=
  if gam ω = 0 then
    fibSum (fun p : ZMod 2 × ZMod 2 => probeLift ω .X p.1 * probeLift ω .Z p.2) pairLabel
  else readout (fun _ : Space F m => (0 : Bas → ZMod 2))

theorem pairBranch_isPVM (ω : Omega F m) : IsPVM (pairBranch ω) := by
  unfold pairBranch
  split_ifs with h
  · exact isPVM_fibSum (joint_measurement_isPVM _ _ (probeLift_isPVM ω .X)
      (probeLift_isPVM ω .Z) (probeLift_commute ω h)) _
  · exact readout_isPVM _

def pairBBranch (ω : Omega F m) (W : Bas) : ZMod 2 → Matrix (Space F m) (Space F m) ℂ :=
  if gam ω = 0 then probeLift ω W else readout (fun _ : Space F m => (0 : ZMod 2))

theorem pairBBranch_isPVM (ω : Omega F m) (W : Bas) : IsPVM (pairBBranch ω W) := by
  unfold pairBBranch
  split_ifs
  · exact probeLift_isPVM ω W
  · exact readout_isPVM _

def constraintBranch (ω : Omega F m) (c : Fin LCS.MagicSquare.layout.r) :
    (Fin 3 → ZMod 2) → Matrix (Space F m) (Space F m) ℂ :=
  if gam ω = 0 then readout (fun _ : Space F m => (0 : Fin 3 → ZMod 2))
  else HonestMagicSquare.constraintOp (basis .X (probeVector ω .X)) (basis .Z (probeVector ω .Z)) c

theorem constraintBranch_isPVM (ω : Omega F m) (c : Fin LCS.MagicSquare.layout.r) :
    IsPVM (constraintBranch ω c) := by
  unfold constraintBranch
  split_ifs with h
  · exact readout_isPVM _
  · exact HonestMagicSquare.constraintOp_isPVM (probe_basis_isObservable ω .X)
      (probe_basis_isObservable ω .Z) (probe_basis_anticommute ω h) c

def variableBranch (ω : Omega F m) (j : Fin LCS.MagicSquare.layout.s) :
    ZMod 2 → Matrix (Space F m) (Space F m) ℂ :=
  if gam ω = 0 then readout (fun _ : Space F m => (0 : ZMod 2))
  else HonestMagicSquare.variableOp (basis .X (probeVector ω .X)) (basis .Z (probeVector ω .Z)) j

theorem variableBranch_isPVM (ω : Omega F m) (j : Fin LCS.MagicSquare.layout.s) :
    IsPVM (variableBranch ω j) := by
  unfold variableBranch
  split_ifs with h
  · exact readout_isPVM _
  · exact HonestMagicSquare.variableOp_isPVM (probe_basis_isObservable ω .X)
      (probe_basis_isObservable ω .Z) (probe_basis_anticommute ω h) j

/-- All twenty-six measurements on the actual question and answer alphabets. -/
def answerOp [NeZero m] (hm : m ∣ Fintype.card F) :
    Question F m → Answer F m d → Matrix (Space F m) (Space F m) ℂ
  | .point W u => fibSum (pauliLift W) (fun h => .val (MvPolynomial.eval u (LowDegree.ldEnc h)))
  | .aline W u s => fibSum (pauliLift W)
      (fun h => .apoly (lineAnswer d u (Pi.single (LIDT.CL.chi hm s) 1) h))
  | .dline W u _ v => fibSum (pauliLift W) (fun h => .dpoly (lineAnswer (m * d) u v h))
  | .pauli W => fibSum (pauliLift W) Answer.pauliAns
  | .pairB W ω => fibSum (pairBBranch ω W) Answer.bit
  | .pair ω => fibSum (pairBranch ω) Answer.bitPair
  | .con c ω => fibSum (constraintBranch ω c) Answer.bitTriple
  | .var j ω => fibSum (variableBranch ω j) Answer.bit

theorem answerOp_isPVM [NeZero m] (hm : m ∣ Fintype.card F) (q : Question F m) :
    IsPVM (answerOp (d := d) hm q) := by
  cases q with
  | point W u => exact isPVM_fibSum (pauliLift_isPVM W) _
  | aline W u s => exact isPVM_fibSum (pauliLift_isPVM W) _
  | dline W u s v => exact isPVM_fibSum (pauliLift_isPVM W) _
  | pauli W => exact isPVM_fibSum (pauliLift_isPVM W) _
  | pairB W ω => exact isPVM_fibSum (pairBBranch_isPVM ω W) _
  | pair ω => exact isPVM_fibSum (pairBranch_isPVM ω) _
  | con c ω => exact isPVM_fibSum (constraintBranch_isPVM ω c) _
  | var j ω => exact isPVM_fibSum (variableBranch_isPVM ω j) _

omit [Field F] [Fintype F] [Algebra (ZMod 2) F] in
private theorem fibre_format_zero {X : Type*} [Fintype X]
    (P : X → Matrix (Space F m) (Space F m) ℂ) (f : X → Answer F m d)
    (q : Question F m) (hf : ∀ x, q.fmtOk (f x) = true) (a : Answer F m d)
    (ha : q.fmtOk a = false) : fibSum P f a = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  have hx' : f x = a := (Finset.mem_filter.mp hx).2
  have hh := hf x
  rw [hx', ha] at hh
  contradiction

/-- Every malformed answer has zero effect, for every question. -/
theorem answerOp_format_zero [NeZero m] (hm : m ∣ Fintype.card F) (q : Question F m)
    (a : Answer F m d) (ha : q.fmtOk a = false) : answerOp hm q a = 0 := by
  cases q <;> apply fibre_format_zero <;> try exact ha
  all_goals intro x; rfl

theorem answerOp_pauli [NeZero m] (hm : m ∣ Fintype.card F) (W : Bas) (h : Register F m) :
    answerOp (d := d) hm (.pauli W) (.pauliAns h) = pauliLift W h := by
  simp [answerOp, fibSum, Finset.sum_filter]

theorem variableBranch_X (ω : Omega F m) (h : gam ω ≠ 0) (b : ZMod 2) :
    variableBranch ω (LCS.MagicSquare.v 0) b = probeLift ω .X b := by
  rw [variableBranch, if_neg h]
  change HonestMagicSquare.variableOp _ _ 0 b = _
  rw [HonestMagicSquare.variableOp_zero, probeLift, liftOp,
    probeOp_eq_projector]

theorem variableBranch_Z (ω : Omega F m) (h : gam ω ≠ 0) (b : ZMod 2) :
    variableBranch ω (LCS.MagicSquare.v 4) b = probeLift ω .Z b := by
  rw [variableBranch, if_neg h]
  change HonestMagicSquare.variableOp _ _ 4 b = _
  rw [HonestMagicSquare.variableOp_four, probeLift, liftOp,
    probeOp_eq_projector]

end MIPRE.QLD.Honest
