/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AdaptiveInductionInvariant
import MIPRE.Foundations.Introspection.FinalExtraction

/-! # Terminal adaptive invariants are conditional readouts

An exact CL presentation has no remaining coordinates at its final level.
The terminal residual measurements therefore act on the auxiliary register
alone. Valid answers have exactly the claimed question readout; the
malformed outcome remains an explicit sum of conditional auxiliary effects.
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false

variable {F ι A H : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι]
  [Fintype A] [DecidableEq A] [Fintype H] [DecidableEq H] {ℓ : ℕ}

theorem stageRemaining_terminal {P : CL.CLFun F ι ℓ}
    (hP : P.ExactlyOn univ) (y : ι → F) : stageRemaining P ℓ y = ∅ := by
  simp only [stageRemaining, CLChecks.prefixRegister_full hP, Finset.compl_univ]

/-- Every vector on the empty remaining register is its zero vector. -/
theorem terminalRemaining_eq_zero {P : CL.CLFun F ι ℓ}
    (hP : P.ExactlyOn univ) (y : ι → F) (u : stageRemaining P ℓ y → F) : u = 0 := by
  funext i
  have hi : i.val ∈ (∅ : Finset ι) := by
    simpa only [stageRemaining_terminal hP] using i.property
  simp at hi

/-- The terminal basis reindexing inserts the unique empty-register vector. -/
def terminalResidualEquiv {P : CL.CLFun F ι ℓ}
    (hP : P.ExactlyOn univ) (y : ι → F) :
    H ≃ ((stageRemaining P ℓ y → F) × H) where
  toFun a := (0, a)
  invFun p := p.2
  left_inv _ := rfl
  right_inv p := Prod.ext (terminalRemaining_eq_zero hP y p.1).symm rfl

set_option backward.isDefEq.respectTransparency false in
/-- Reassembling a terminal residual operator is exactly a question readout
tensored with the operator on the auxiliary register. -/
theorem prefixResidualOp_terminal {P : CL.CLFun F ι ℓ}
    (hP : P.ExactlyOn univ) (y : ι → F)
    (M : Matrix ((stageRemaining P ℓ y → F) × H) _ ℂ) :
    prefixResidualOp P ℓ y M = readout P.eval y ⊗ₖ registerOp (terminalResidualEquiv hP y) M := by
  have hfull := CLChecks.prefixRegister_full hP y
  have he (x x' : ι → F) :
      (fun i : CLChecks.prefixRegister P ℓ y => x i) =
        (fun i : CLChecks.prefixRegister P ℓ y => x' i) ↔ x = x' := by
    constructor
    · intro h
      funext i
      exact congrFun h ⟨i, by rw [hfull]; exact mem_univ i⟩
    · intro h
      subst x'
      rfl
  have hins (x : ι → F) :
      Honest.insertRegister (CLChecks.prefixRegister P ℓ y) (fun i => x i) = x := by
    funext i
    have hi : i ∈ CLChecks.prefixRegister P ℓ y := by rw [hfull]; exact mem_univ i
    simp only [Honest.insertRegister, dif_pos hi]
  ext ⟨x, a⟩ ⟨x', a'⟩
  unfold prefixResidualOp Honest.prefixProjector
  simp only [registerOp_apply, registerParty, Equiv.trans_apply,
    Equiv.prodCongr_apply, Equiv.prodAssoc_apply, ambientSplit,
    Matrix.kroneckerMap_apply, readout, Matrix.diagonal_apply]
  change (if (fun i : CLChecks.prefixRegister P ℓ y => x i) =
      (fun i : CLChecks.prefixRegister P ℓ y => x' i) then
      (if (P.truncate ℓ).eval
        (Honest.insertRegister (CLChecks.prefixRegister P ℓ y) (fun i => x i)) = y
        then (1 : ℂ) else 0) else 0) *
      M (fun i => x i, a) (fun i => x' i, a') =
    (if x = x' then (if P.eval x = y then (1 : ℂ) else 0) else 0) *
      M (0, a) (0, a')
  simp only [he, hins, CL.CLFun.truncate_self, terminalRemaining_eq_zero hP y]

/-- Forget only the question component of a valid answer. Malformed answers
remain malformed. -/
def terminalAnswerMap : Option ((ι → F) × A) → Option A := Option.map Prod.snd

variable {P : CL.CLFun F ι ℓ}
  {N : POVM (Option ((ι → F) × A)) ((ι → F) × H)}

theorem IntroPrefixInvariant.terminal_residual_some_zero
    (I : IntroPrefixInvariant P ℓ N) (hP : P.ExactlyOn univ)
    (y x : ι → F) (a : A) (hxy : x ≠ y) :
    ((I.residual y).mats (some (x, a))).val = 0 :=
  I.support y x a (by simpa only [hP.outputPrefix_univ x] using hxy)

/-- Coarsening a terminal branch loses no valid-answer effect: its question
component was already fixed by the structural support invariant. -/
theorem IntroPrefixInvariant.terminal_map_some
    (I : IntroPrefixInvariant P ℓ N) (hP : P.ExactlyOn univ)
    (y : ι → F) (a : A) :
    (((I.residual y).map terminalAnswerMap).mats (some a)).val =
      ((I.residual y).mats (some (y, a))).val := by
  rw [POVM.map_mats]
  apply Finset.sum_eq_single (some (y, a))
  · intro b hb hba
    have he : terminalAnswerMap b = some a := (mem_filter.mp hb).2
    cases b with
    | none => cases he
    | some b =>
      have hsecond : b.2 = a := Option.some.inj he
      have hfirst : b.1 ≠ y := by
        intro h
        exact hba (congrArg some (Prod.ext h hsecond))
      exact I.terminal_residual_some_zero hP y b.1 b.2 hfirst
  · intro h
    exact False.elim (h (by simp [terminalAnswerMap]))

theorem IntroPrefixInvariant.terminal_map_none
    (I : IntroPrefixInvariant P ℓ N) (y : ι → F) :
    (((I.residual y).map terminalAnswerMap).mats none).val =
      ((I.residual y).mats none).val := by
  rw [POVM.map_mats]
  apply Finset.sum_eq_single none
  · intro b hb hbnone
    have he : terminalAnswerMap b = none := (mem_filter.mp hb).2
    cases b with
    | none => exact False.elim (hbnone rfl)
    | some b => cases he
  · intro h
    exact False.elim (h (by simp [terminalAnswerMap]))

/-- The actual auxiliary measurement extracted from the terminal invariant.
It is normalized on `Option A`, including the malformed outcome. -/
def terminalAuxPOVM (hP : P.ExactlyOn univ)
    (I : IntroPrefixInvariant P ℓ N) (y : ι → F) : POVM (Option A) H :=
  registerPOVM (terminalResidualEquiv hP y) ((I.residual y).map terminalAnswerMap)

theorem terminalAuxPOVM_isPVM (hP : P.ExactlyOn univ)
    (I : IntroPrefixInvariant P ℓ N) (y : ι → F) :
    IsPVM (fun a => ((terminalAuxPOVM hP I y).mats a).val) := by
  unfold terminalAuxPOVM
  simpa only [registerPOVM_mats] using
    registerOp_isPVM (terminalResidualEquiv hP y)
      (isPVM_povm_map (I.residual y) (I.projective y) terminalAnswerMap)

theorem terminalAuxPOVM_some (hP : P.ExactlyOn univ)
    (I : IntroPrefixInvariant P ℓ N) (y : ι → F) (a : A) :
    ((terminalAuxPOVM hP I y).mats (some a)).val =
      registerOp (terminalResidualEquiv hP y) ((I.residual y).mats (some (y, a))).val := by
  rw [terminalAuxPOVM, registerPOVM_mats, I.terminal_map_some hP]

theorem terminalAuxPOVM_none (hP : P.ExactlyOn univ)
    (I : IntroPrefixInvariant P ℓ N) (y : ι → F) :
    ((terminalAuxPOVM hP I y).mats none).val =
      registerOp (terminalResidualEquiv hP y) ((I.residual y).mats none).val := by
  rw [terminalAuxPOVM, registerPOVM_mats, I.terminal_map_none]

/-- Every valid terminal answer is an exact conditional readout of the
question, with the concrete auxiliary PVM constructed above. -/
theorem IntroPrefixInvariant.terminal_some
    (I : IntroPrefixInvariant P ℓ N) (hP : P.ExactlyOn univ)
    (y : ι → F) (a : A) :
    (N.mats (some (y, a))).val =
      readout P.eval y ⊗ₖ ((terminalAuxPOVM hP I y).mats (some a)).val := by
  rw [I.form]
  have hs : (∑ x, prefixResidualOp P ℓ x ((I.residual x).mats (some (y, a))).val) =
      prefixResidualOp P ℓ y ((I.residual y).mats (some (y, a))).val := by
    apply Finset.sum_eq_single y
    · intro x _ hxy
      rw [I.terminal_residual_some_zero hP x y a (Ne.symm hxy)]
      ext i j
      simp [prefixResidualOp, registerOp_apply]
    · intro h
      exact False.elim (h (mem_univ y))
  rw [hs, prefixResidualOp_terminal hP, terminalAuxPOVM_some]

/-- Malformed answers are retained as the sum of their conditional
auxiliary effects. No zero-malformed-mass assumption is used. -/
theorem IntroPrefixInvariant.terminal_none
    (I : IntroPrefixInvariant P ℓ N) (hP : P.ExactlyOn univ) :
    (N.mats none).val =
      ∑ y, readout P.eval y ⊗ₖ ((terminalAuxPOVM hP I y).mats none).val := by
  rw [I.form]
  apply Finset.sum_congr rfl
  intro y _
  rw [prefixResidualOp_terminal hP, terminalAuxPOVM_none]

end MIPRE.Introspection
end
