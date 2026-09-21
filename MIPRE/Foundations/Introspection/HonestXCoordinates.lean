/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.HonestRead

/-! # Pauli-X projectors under the honest register split

The stopping measurement in Hide uses the X basis of the active register.
These identities expose its tensor factors in the coordinate split used by
the adaptive CL recursion.
-/

noncomputable section

namespace MIPRE.Introspection.Honest

open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false

variable {F I J K : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]

theorem pauliX_entry (e x y : I → F) :
    proj wX e x y = (Fintype.card (I → F) : ℂ)⁻¹ * sgn (trDot (x + y) e) := by
  rw [proj_def, Matrix.smul_apply, Matrix.sum_apply]
  change (Fintype.card (I → F) : ℂ)⁻¹ *
    (∑ a : I → F, sgn (trDot a e) * (if x = y + a then 1 else 0)) = _
  congr 1
  rw [Finset.sum_eq_single (x + y)]
  · have he : y + (x + y) = x := by rw [add_comm x y, ← add_assoc, add_self_vec, zero_add]
    simp [he]
  · intro a _ ha
    have hne : x ≠ y + a := by
      intro he
      apply ha
      rw [he, add_comm y a, add_add_cancel_vec]
    simp [hne]
  · simp

/-- Any additive split preserving the coordinate pairing splits the X spectral projector. -/
theorem pauliX_split
    (e : (I → F) ≃ (J → F) × (K → F))
    (hadd : ∀ a b, e (a + b) = ((e a).1 + (e b).1, (e a).2 + (e b).2))
    (hdot : ∀ a b, trDot a b = trDot (e a).1 (e b).1 + trDot (e a).2 (e b).2)
    (z : I → F) :
    proj wX z = registerOp e (proj wX (e z).1 ⊗ₖ proj wX (e z).2) := by
  have hc : Fintype.card (I → F) = Fintype.card (J → F) * Fintype.card (K → F) := by
    rw [Fintype.card_congr e, Fintype.card_prod]
  ext x y
  simp only [registerOp_apply, Matrix.kroneckerMap_apply, pauliX_entry,
    hdot, hadd, sgn_add, hc, Nat.cast_mul, _root_.mul_inv_rev]
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The coordinate partition underlying `coordinateSplit`, on index types. -/
def coordinateIndexSplit (S V : Finset ι) (h : S ⊆ V) :
    V ≃ Fin (Fintype.card S) ⊕ ↥(V \ S) where
  toFun i := if hi : i.val ∈ S then .inl (Fintype.equivFin S ⟨i, hi⟩)
    else .inr ⟨i, Finset.mem_sdiff.mpr ⟨i.property, hi⟩⟩
  invFun p := match p with
    | .inl j => ⟨(Fintype.equivFin S).symm j, h ((Fintype.equivFin S).symm j).property⟩
    | .inr j => ⟨j, (Finset.mem_sdiff.mp j.property).1⟩
  left_inv i := by
    by_cases hi : i.val ∈ S
    · simp [hi]
    · simp [hi]
  right_inv p := by
    cases p with
    | inl j =>
        simp only [dif_pos ((Fintype.equivFin S).symm j).property]
        exact congrArg Sum.inl ((Fintype.equivFin S).apply_symm_apply j)
    | inr j => simp only [dif_neg (Finset.mem_sdiff.mp j.property).2]

theorem trDot_coordinateSplit (S V : Finset ι) (h : S ⊆ V) (x y : V → F) :
    trDot x y =
      trDot (coordinateSplit S V h x).1 (coordinateSplit S V h y).1 +
      trDot (coordinateSplit S V h x).2 (coordinateSplit S V h y).2 := by
  unfold trDot
  rw [← map_add]
  congr 1
  have he := Equiv.sum_comp (coordinateIndexSplit S V h).symm (fun i : V => x i * y i)
  rw [Fintype.sum_sum_type] at he
  exact he.symm

/-- The concrete active-register X projector is the tensor product of the current
register and untouched-tail X projectors in the honest CL coordinate split. -/
theorem pauliX_coordinateSplit (S V : Finset ι) (h : S ⊆ V) (z : V → F) :
    proj wX z = registerOp (coordinateSplit S V h)
      (proj wX (coordinateSplit S V h z).1 ⊗ₖ proj wX (coordinateSplit S V h z).2) :=
  pauliX_split (coordinateSplit S V h) (fun _ _ => rfl) (trDot_coordinateSplit S V h) z

end MIPRE.Introspection.Honest
