/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.HonestXCoordinates

/-! # The local honest hiding step

This identifies the actual stopping Hide measurement with its local dual-X
measurement and untouched X tail in the coordinate split used by the next
adaptive step.
-/

noncomputable section

namespace MIPRE.Introspection.Honest

open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false

section Coarse
variable {I J A B C D : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype D] [DecidableEq D]

def coarseOp (f : A → B) (P : A → Matrix I I ℂ) (b : B) : Matrix I I ℂ :=
  ∑ a ∈ Finset.univ.filter (fun a => f a = b), P a

theorem coarseOp_comp (f : A → B) (g : B → C) (P : A → Matrix I I ℂ) (c : C) :
    coarseOp g (coarseOp f P) c = coarseOp (g ∘ f) P c := by
  simp only [coarseOp, Finset.sum_filter]
  have hs (b : B) : (if g b = c then ∑ a, if f a = b then P a else 0 else 0) =
      ∑ a, if g b = c then (if f a = b then P a else 0) else 0 := by
    by_cases hb : g b = c <;> simp [hb]
  simp_rw [hs]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single (f a)]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem coarseOp_first (f : A → C) (P : A → Matrix I I ℂ)
    (Q : B → Matrix J J ℂ) (cb : C × B) :
    coarseOp (fun ab : A × B => (f ab.1, ab.2)) (fun ab => P ab.1 ⊗ₖ Q ab.2) cb =
      coarseOp f P cb.1 ⊗ₖ Q cb.2 := by
  rcases cb with ⟨c, b⟩
  simp only [coarseOp, Finset.sum_filter, Fintype.sum_prod_type, Prod.mk.injEq]
  rw [sum_kronecker_left]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : f a = c <;> simp [ha]

end Coarse

variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

def stopLabel (S V : Finset ι)
    (a : (Fin (Fintype.card S) → F) × (↥(V \ S) → F)) : HideLabel F ι :=
  (0, coordinateInsert S a.1, insertRegister (V \ S) a.2)

theorem stopHideAnswer_split (S V : Finset ι) (h : S ⊆ V) (L : CL.RegLinear F S)
    (next : (ι → F) → CL.CLFun F ι ℓ) (x : V → F) :
    stopHideAnswer (.cons S L next) V x =
      stopLabel S V (CL.lperp (coordinateLinear L) (coordinateSplit S V h x).1,
        (coordinateSplit S V h x).2) := by
  simp only [stopHideAnswer, firstHideAnswer, CLChecks.dualReadout,
    CL.CLFun.factorOfPrefix_cons_zero, restrict_insertRegister S V h,
    tail_insertRegister S V h, stopLabel]

/-- Exact factorization of the stopping Hide measurement, with the actual dual map. -/
theorem stopHide_split (S V : Finset ι) (h : S ⊆ V) (L : CL.RegLinear F S)
    (next : (ι → F) → CL.CLFun F ι ℓ) (a : HideLabel F ι) :
    stopHide (.cons S L next) V a =
      registerOp (coordinateSplit S V h)
        (coarseOp (stopLabel S V)
          (fun bt => synOf wX (CL.lperp (coordinateLinear L)) bt.1 ⊗ₖ proj wX bt.2) a) := by
  let f := fun st : (Fin (Fintype.card S) → F) × (↥(V \ S) → F) =>
    (CL.lperp (coordinateLinear L) st.1, st.2)
  have hf (bt : (Fin (Fintype.card S) → F) × (↥(V \ S) → F)) :
      (synOf wX (CL.lperp (coordinateLinear L)) bt.1 ⊗ₖ proj wX bt.2) =
        coarseOp f (fun st => proj wX st.1 ⊗ₖ proj wX st.2) bt :=
    (coarseOp_first _ _ _ bt).symm
  simp_rw [hf]
  rw [coarseOp_comp]
  ext x y
  simp only [stopHide, synOf, coarseOp, registerOp_apply, Matrix.sum_apply,
    Finset.sum_filter]
  apply Fintype.sum_equiv (coordinateSplit S V h)
  intro z
  rw [stopHideAnswer_split S V h L next z]
  by_cases hz : stopLabel S V
      (CL.lperp (coordinateLinear L) (coordinateSplit S V h z).1,
        (coordinateSplit S V h z).2) = a
  · simp only [hz, if_true, Function.comp_apply, f]
    exact congrArg (fun M => M x y) (pauliX_coordinateSplit S V h z)
  · simp [hz, Function.comp_apply, f]

end MIPRE.Introspection.Honest
