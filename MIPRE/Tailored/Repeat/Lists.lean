/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.Cost.Iterates
public import MIPRE.Foundations.Cost.Reader
public import MIPRE.Foundations.Repeat.Prims

@[expose] public section

/-!
# List functions in polynomial time for the repeated tailored verifier

The pure stages of the repeated programs (issue #280) cut questions and answers into blocks and
put the coordinates' outputs together. The functions they need, as `PolyTimeFun`s:

* `flattenF`, the concatenation of a list of lists;
* `blocksF`, the `k` blocks of `s` elements of a list (`blocks`), with `s` and `k` in unary;
* `cutF`, a list cut into consecutive pieces of given lengths (`cut`), the lengths in unary.
-/

namespace MIPRE.Tailored.RepProg

open Cost Cost.PolyTimeFun Polynomial

variable {α : Type*} [SizedEncoding α]

theorem esize_drop_le (l : List α) (n : ℕ) : esize (l.drop n) ≤ esize l := by
  have h := esize_list_append (l.take n) (l.drop n)
  rw [List.take_append_drop] at h
  have := esize_pos (l.take n)
  omega

theorem esize_take_le (l : List α) (n : ℕ) : esize (l.take n) ≤ esize l := by
  have h := esize_list_append (l.take n) (l.drop n)
  rw [List.take_append_drop] at h
  have := esize_pos (l.drop n)
  omega

/-! ## Concatenation -/

/-- The concatenation of a list of lists. -/
noncomputable def flattenF : PolyTimeFun (List (List α)) (List α) :=
  congr ((foldlAdd append X (by
    intro l r
    have h := esize_list_append l r
    simp only [append_apply, eval_X]
    omega)).comp ((PolyTimeFun.id _).pair (const []))) List.flatten (by
      intro l
      change l.foldl (fun a b => a ++ b) [] = l.flatten
      simpa using (List.foldl_append_eq_append (l := l) (l' := []) (f := fun b => b)))

@[simp] theorem flattenF_apply (l : List (List α)) : flattenF l = l.flatten := rfl

/-! ## Blocks of equal length -/

/-- The `k` blocks of `s` elements of `l`: its `i`-th block is `chunk s i l`. -/
def blocks (l : List α) (s k : ℕ) : List (List α) := List.ofFn fun i : Fin k => Cost.Data.chunk s i l

@[simp] theorem length_blocks (l : List α) (s k : ℕ) : (blocks l s k).length = k := by
  simp [blocks]

/-- The step of the block cutter: drop a block. -/
noncomputable def dropStepF : PolyTimeFun (List α × Unary) (List α × Unary) := drop.pair snd

@[simp] theorem dropStepF_apply (p : List α × Unary) :
    dropStepF p = (p.1.drop p.2.length, p.2) := rfl

theorem iterate_dropStepF (p : List α × Unary) (i : ℕ) :
    (dropStepF : List α × Unary → List α × Unary)^[i] p = (p.1.drop (i * p.2.length), p.2) := by
  induction i generalizing p with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply, ih]
    simp only [dropStepF_apply, List.drop_drop]
    congr 2
    ring

/-- The `k` blocks of `s` elements, with `s` and `k` in unary. -/
noncomputable def blocksF : PolyTimeFun ((List α × Unary) × Unary) (List (List α)) :=
  congr ((map take).comp ((recordIteratesProg dropStepF X (by
      rintro i ⟨l, u⟩
      rw [iterate_dropStepF]
      simp only [esize_prod, eval_X]
      have := esize_drop_le l (i * u.length)
      omega)).comp (snd.pair fst)))
    (fun p => blocks p.1.1 p.1.2.length p.2.length) (by
      rintro ⟨⟨l, us⟩, uk⟩
      simp only [comp_apply, pair_apply, snd_apply, fst_apply, recordIteratesProg_apply,
        map_apply, recordIterates, blocks, List.map_ofFn]
      congr 1
      funext i
      simp [iterate_dropStepF, Cost.Data.chunk])

@[simp] theorem blocksF_apply (l : List α) (us uk : Unary) :
    blocksF ((l, us), uk) = blocks l us.length uk.length := congr_apply _ _ _ _

/-! ## Consecutive pieces of given lengths -/

/-- `l` cut into consecutive pieces of the lengths `ns`; the pieces past the end of `l` are
short or empty. -/
def cut (l : List α) : List ℕ → List (List α)
  | [] => []
  | n :: ns => l.take n :: cut (l.drop n) ns

end MIPRE.Tailored.RepProg

end
