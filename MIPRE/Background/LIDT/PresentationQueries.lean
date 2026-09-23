/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.LIDT.Presentation
import MIPRE.Foundations.CL.ProductSampler

/-!
# The queries of the three-level presentation of the seeded test

What a sampler program must compute for `Regs.pres` (`MIPRE/Background/LIDT/Presentation`), level
by level: its marginals (`eval_truncate_one`, `eval_truncate_two`, `eval_pres`), its stage maps
read off a prefix (`mapOfPrefix_zero`, `mapOfPrefix_one`, `mapOfPrefix_two`) and its factor
spaces (`factorOfPrefix_zero`, `factorOfPrefix_one`, `factorOfPrefix_two`); from the fourth level
on there is nothing (`mapOfPrefix_three_le`, `factorOfPrefix_three_le`).

The seed a stage map reads is the prefix's seed coordinate, and the diagonal line's direction is
the prefix's direction register, already cut down by the selector.
-/

noncomputable section

namespace MIPRE.LIDT.CL.Regs

open Finset MIPRE.CL MIPRE.CL.CLFun

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
  (S : Sel F n hn)

/-- The linear map of the point register applied at the third stage. -/
def ptMap : Ty → F → Point F n → (Point F n →ₗ[F] Point F n)
  | .point, _, _ => LinearMap.id
  | .aline, s, _ => MIPRE.CL.canonLin (Submodule.span F {Pi.single (S.χ s) 1})
  | .dline, _, v => MIPRE.CL.canonLin (Submodule.span F {v})

omit [Fintype ι] [Fintype F] [DecidableEq F] [NeZero n] in
theorem seedLin_apply (t : Ty) (x : ι → F) :
    R.seedLin t x = if t = .point then 0 else proj R.coordSet x := by
  cases t <;> rfl

omit [Fintype ι] in
theorem secondLin_apply (t : Ty) (s : F) (x : ι → F) :
    R.secondLin S t s x = if t = .dline then R.putDir (zeroBelow (S.χ s) (R.dirOf x)) else 0 := by
  cases t
  · rfl
  · rfl
  · exact R.dirLin_apply _ x

theorem finalLin_apply (t : Ty) (s : F) (v : Point F n) (x : ι → F) :
    R.finalLin S t s v x = R.putPt (ptMap S t s v (R.ptOf x)) := by
  cases t <;> exact R.ptLin_apply _ x

omit [Fintype ι] in
theorem coord_seedLin (t : Ty) (x : ι → F) (s : F) (h : t ≠ .point → x R.coord = s) :
    R.secondLin S t ((R.seedLin t x) R.coord) = R.secondLin S t s := by
  cases t with
  | point => rfl
  | aline => rfl
  | dline =>
    change R.secondLin S _ ((proj R.coordSet x) R.coord) = _
    rw [proj_apply_of_mem R.coord_mem_coordSet, h (by simp)]

omit [NeZero n] in
theorem dirSet_subset_compl : R.dirSet ⊆ R.coordSetᶜ := fun c hc => by
  have := R.dirSet_subset hc
  simp only [mem_sdiff, mem_univ, true_and] at this
  exact mem_compl.mpr this

omit [NeZero n] in
theorem finalSet_subset_compl : R.finalSet ⊆ R.dirSetᶜ ∩ R.coordSetᶜ := fun c hc => by
  simp only [finalSet, mem_sdiff, mem_univ, true_and] at hc
  exact mem_inter.mpr ⟨mem_compl.mpr hc.2, mem_compl.mpr hc.1⟩

/-! ## The marginals -/

theorem eval_truncate_one (t : Ty) (x : ι → F) :
    ((R.pres S t).truncate 1).eval x = R.seedLin t x := by
  simp [pres]

theorem eval_truncate_two (t : Ty) (x : ι → F) :
    ((R.pres S t).truncate 2).eval x = R.seedLin t x + R.secondLin S t (x R.coord) x := by
  simp only [pres, truncate_succ_cons, eval_cons, truncate_zero, eval_zero, add_zero]
  rw [R.coord_seedLin S t x (x R.coord) (fun _ => rfl),
    (R.secondLin S t (x R.coord)).apply_proj_of_subset R.dirSet_subset_compl]

omit [Fintype ι] in
theorem dirOf_secondLin (t : Ty) (s : F) (x : ι → F) :
    R.dirOf (R.secondLin S t s x) = if t = .dline then zeroBelow (S.χ s) (R.dirOf x) else 0 := by
  rw [secondLin_apply]
  split_ifs
  · exact R.dirOf_putDir _
  · rfl

theorem eval_pres (t : Ty) (x : ι → F) :
    (R.pres S t).eval x = R.seedLin t x + R.secondLin S t (x R.coord) x +
      R.putPt (ptMap S t (x R.coord)
        (if t = .dline then zeroBelow (S.χ (x R.coord)) (R.dirOf x) else 0) (R.ptOf x)) := by
  simp only [pres, eval_cons, eval_zero, add_zero]
  rw [R.coord_seedLin S t x (x R.coord) (fun _ => rfl),
    (R.secondLin S t (x R.coord)).apply_proj_of_subset R.dirSet_subset_compl, add_assoc]
  congr 2
  have hsd : proj R.dirSetᶜ (proj R.coordSetᶜ x) = proj (R.dirSetᶜ ∩ R.coordSetᶜ) x := by
    rw [proj_proj]
  rw [hsd, (R.finalLin S t _ _).apply_proj_of_subset R.finalSet_subset_compl, finalLin_apply]
  have h1 : (proj R.coordSet x) R.coord = x R.coord := proj_apply_of_mem R.coord_mem_coordSet x
  cases t with
  | point => rfl
  | aline =>
    change R.putPt (ptMap S .aline ((proj R.coordSet x) R.coord) _ _) = _
    rw [h1]
    rfl
  | dline =>
    change R.putPt (ptMap S .dline ((proj R.coordSet x) R.coord) _ _) = _
    rw [h1, dirOf_secondLin]

theorem eval_truncate_three_le (t : Ty) {j : ℕ} (hj : 3 ≤ j) (x : ι → F) :
    ((R.pres S t).truncate j).eval x = (R.pres S t).eval x :=
  eval_truncate_of_le _ hj x

/-! ## The stage maps and factor spaces, read off a prefix -/

theorem mapOfPrefix_zero (t : Ty) (u : ι → F) :
    (R.pres S t).mapOfPrefix 0 u = (R.seedLin t).toLinearMap := rfl

theorem mapOfPrefix_one (t : Ty) (u : ι → F) :
    (R.pres S t).mapOfPrefix 1 u = (R.secondLin S t (u R.coord)).toLinearMap := by
  simp only [pres, mapOfPrefix_cons_succ, mapOfPrefix_cons_zero]
  rw [proj_apply_of_mem R.coord_mem_coordSet]

theorem mapOfPrefix_two (t : Ty) (u : ι → F) :
    (R.pres S t).mapOfPrefix 2 u = (R.finalLin S t (u R.coord) (R.dirOf u)).toLinearMap := by
  simp only [pres, mapOfPrefix_cons_succ, mapOfPrefix_cons_zero]
  rw [proj_apply_of_mem R.coord_mem_coordSet]
  congr 2
  funext j
  simp only [dirOf]
  rw [proj_apply_of_mem (R.dir_mem_dirSet j),
    proj_apply_of_mem (by simpa using R.not_mem_coordSet_dir j)]

theorem mapOfPrefix_three_le (t : Ty) {j : ℕ} (hj : 3 ≤ j) (u : ι → F) :
    (R.pres S t).mapOfPrefix j u = 0 :=
  mapOfPrefix_of_le _ hj u

theorem factorOfPrefix_zero (t : Ty) (u : ι → F) :
    (R.pres S t).factorOfPrefix 0 u = R.coordSet := rfl

theorem factorOfPrefix_one (t : Ty) (u : ι → F) :
    (R.pres S t).factorOfPrefix 1 u = R.dirSet := rfl

theorem factorOfPrefix_two (t : Ty) (u : ι → F) :
    (R.pres S t).factorOfPrefix 2 u = R.finalSet := rfl

theorem factorOfPrefix_three_le (t : Ty) {j : ℕ} (hj : 3 ≤ j) (u : ι → F) :
    (R.pres S t).factorOfPrefix j u = ∅ :=
  factorOfPrefix_of_le _ hj u

end MIPRE.LIDT.CL.Regs

end
