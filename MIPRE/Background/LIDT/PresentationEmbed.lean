/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.LIDT.Presentation
import MIPRE.Background.LIDT.CLHonest

/-!
# The presentation's output is a function of its question

Piece AR-5b of `planning/answer-reduction.md` needs the converse of `Regs.questionOf_eval`: the
vector a type's presentation outputs is supported on the copy's own registers, and is a fixed
function (`Regs.embedQ`) of the seeded question it computes (`Regs.pres_eval`). So a strategy
that answers a question vector of the answer-reduced verifier answers, through `embedQ`, the
seeded low-degree test's question, and the two games' questions correspond one to one.
-/

noncomputable section

namespace MIPRE.LIDT.CL

/-- The type of a question. -/
def Question.ty {F : Type*} {n : ℕ} : Question F n → Ty
  | .point _ => .point
  | .aline _ _ => .aline
  | .dline _ _ _ => .dline

@[simp] theorem Sample.question_ty {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
    [NeZero n] (hn : n ∣ Fintype.card F) (sm : Sample F n) (t : Ty) :
    (sm.question hn t).ty = t := by
  cases t <;> rfl

namespace Regs

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

omit [DecidableEq ι] [Fintype ι] [Fintype F] [DecidableEq F] [NeZero n] in
theorem ptOf_add (x y : ι → F) : R.ptOf (x + y) = R.ptOf x + R.ptOf y := rfl

omit [DecidableEq ι] [Fintype ι] [Fintype F] [DecidableEq F] [NeZero n] in
theorem dirOf_add (x y : ι → F) : R.dirOf (x + y) = R.dirOf x + R.dirOf y := rfl

omit [Fintype ι] [Fintype F] [DecidableEq F] [NeZero n] in
theorem ptOf_single_coord (c : F) : R.ptOf (Pi.single R.coord c) = 0 := by
  funext i
  simp [ptOf, R.pt_ne_coord i]

omit [Fintype ι] [Fintype F] [DecidableEq F] [NeZero n] in
theorem dirOf_single_coord (c : F) : R.dirOf (Pi.single R.coord c) = 0 := by
  funext j
  simp [dirOf, R.dir_ne_coord j]

omit [Fintype ι] in
/-- **Reading a presented question back** gives the question. -/
theorem questionOf_embedQ (q : Question F n) : R.questionOf S q.ty (R.embedQ S q) = q := by
  cases q with
  | point u => simp [Question.ty, questionOf, embedQ]
  | aline u₀ s =>
    simp [Question.ty, questionOf, embedQ, ptOf_single_coord, ptOf_add, R.putPt_coord]
  | dline u₀ s v =>
    simp [Question.ty, questionOf, embedQ, ptOf_single_coord, dirOf_single_coord, ptOf_add,
      dirOf_add, R.putPt_coord, R.putDir_coord]

omit [Fintype ι] in
/-- The sample read off a presented sample question gives the question back. -/
theorem sampleOf_embedQ (sm : Sample F n) (t : Ty) :
    (R.sampleOf S t (R.embedQ S (sm.question hn t))).question hn t = sm.question hn t := by
  have h := R.questionOf_embedQ S (sm.question hn t)
  rw [Sample.question_ty] at h
  rw [sampleOf_question, h, recanon_question]

end Regs

/-! ## Two types on one sample -/

/-- A sample with its two types replaced. -/
def Sample.retype {F : Type*} {n : ℕ} (sm : Sample F n) (a b : Ty) : Sample F n :=
  ⟨a, b, sm.u, sm.s, sm.v⟩

/-- A question depends on the sample's point, seed and direction, not on its types. -/
@[simp] theorem Sample.question_retype {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
    [NeZero n] (hn : n ∣ Fintype.card F) (sm : Sample F n) (a b t : Ty) :
    (sm.retype a b).question hn t = sm.question hn t := by
  cases t <;> rfl

/-- A sample is its two types, point, seed and direction. -/
def Sample.equiv (F : Type*) (n : ℕ) : Sample F n ≃ Ty × Ty × Point F n × F × Point F n where
  toFun sm := (sm.tyA, sm.tyB, sm.u, sm.s, sm.v)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

namespace Regs

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
  (S : Sel F n hn)

/-- **Uniform content and a uniform pair of types give a uniform sample**: the sample the
registers carry at the first type, retyped to a pair of types, summed over both types and all
vectors, is every sample `q^{|ι| - (2n+1)}` times. -/
theorem sum_sampleOf_retype {M : Type*} [AddCommMonoid M] (g : Sample F n → M) :
    ∑ a : Ty, ∑ b : Ty, ∑ x : ι → F, g ((R.sampleOf S a x).retype a b)
      = (Fintype.card F ^ (Fintype.card ι - (2 * n + 1))) • ∑ sm : Sample F n, g sm := by
  have h a b : ∑ x : ι → F, g ((R.sampleOf S a x).retype a b) = _ :=
    R.sum_sampleOf S a (fun sm => g (sm.retype a b))
  simp_rw [h, ← Finset.smul_sum]
  congr 1
  rw [← (Sample.equiv F n).symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  rfl

end MIPRE.LIDT.CL.Regs

end
