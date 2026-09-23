/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.LIDT.Presentation

/-!
# The presentation's output is a function of its question

Piece AR-5b of `planning/answer-reduction.md` needs the converse of `Regs.questionOf_eval`: the
vector a type's presentation outputs is supported on the copy's own registers, and is a fixed
function (`Regs.embedQ`) of the seeded question it computes (`Regs.pres_eval`). So a strategy
that answers a question vector of the answer-reduced verifier answers, through `embedQ`, the
seeded low-degree test's question, and the two games' questions correspond one to one.
-/

noncomputable section

namespace MIPRE.LIDT.CL.Regs

open Finset MIPRE.CL

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
  (S : Sel F n hn)

/-- **The vector a question is presented as**: the point written in the point register, the
seed decoded by the permutation in the seed register, the direction in the direction register. -/
def embedQ : Question F n → (ι → F)
  | .point u => R.putPt u
  | .aline u₀ s => Pi.single R.coord (S.π.symm s) + R.putPt u₀
  | .dline u₀ s v => Pi.single R.coord (S.π.symm s) + R.putDir v + R.putPt u₀

omit [Fintype ι] [Fintype F] [DecidableEq F] [NeZero n] in
theorem proj_coordSet (x : ι → F) : proj R.coordSet x = Pi.single R.coord (x R.coord) := by
  funext i
  by_cases h : i = R.coord
  · subst h
    simp [proj_apply_of_mem R.coord_mem_coordSet]
  · rw [proj_apply_of_not_mem (by simpa [coordSet] using h), Pi.single_eq_of_ne h]

/-- **The presentation's output is the embedding of the question it computes.** -/
theorem pres_eval (t : Ty) (x : ι → F) :
    (R.pres S t).eval x = R.embedQ S ((R.sampleOf S t x).question hn t) := by
  have hpt : ∀ i, (proj R.dirSetᶜ (proj R.coordSetᶜ x)) (R.pt i) = x (R.pt i) := fun i => by
    rw [proj_apply_of_mem (by simpa using R.not_mem_dirSet_pt i),
      proj_apply_of_mem (by simpa using R.not_mem_coordSet_pt i)]
  have hptOf : R.ptOf (proj R.dirSetᶜ (proj R.coordSetᶜ x)) = R.ptOf x := funext hpt
  have hdirOf : R.dirOf (proj R.coordSetᶜ x) = R.dirOf x := by
    funext j
    simp only [dirOf]
    rw [proj_apply_of_mem (by simpa using R.not_mem_coordSet_dir j)]
  have hcoord : (proj R.coordSet x) R.coord = x R.coord := proj_apply_of_mem R.coord_mem_coordSet x
  cases t with
  | point =>
    simp only [pres, CLFun.eval_cons, CLFun.eval_zero, seedLin, secondLin, finalLin,
      RegLinear.zero_apply, zero_add, add_zero, ptLin_apply, LinearMap.id_apply, hptOf]
    rfl
  | aline =>
    simp only [pres, CLFun.eval_cons, CLFun.eval_zero, seedLin, secondLin, finalLin,
      RegLinear.zero_apply, RegLinear.id_apply, zero_add, add_zero, ptLin_apply, hptOf, hcoord]
    simp only [sampleOf, Sample.question, embedQ, rep, S.chi_π, Equiv.symm_apply_apply,
      proj_coordSet]
  | dline =>
    simp only [pres, CLFun.eval_cons, CLFun.eval_zero, seedLin, secondLin, finalLin,
      RegLinear.id_apply, add_zero, ptLin_apply, dirLin_apply, hptOf, hcoord, hdirOf]
    simp only [dirOf_putDir, sampleOf, Sample.question, embedQ, rep, S.chi_π,
      Equiv.symm_apply_apply, proj_coordSet]
    abel

end MIPRE.LIDT.CL.Regs

end
