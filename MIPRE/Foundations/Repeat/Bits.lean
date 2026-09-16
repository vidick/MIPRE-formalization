/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.CL.Repeat
import MIPRE.Foundations.CL.Sampler
import MIPRE.Foundations.Repeat.Prims

/-!
# Blocks of bit strings

The repeated sampler of `thm:parallel-repetition` presents `k` copies of an input CL function
on `𝔽₂^s` as one CL function on `𝔽₂^{k s}` (`CLFun.famSum`, along `finProdFinEquiv`), and its
program handles vectors as bit strings cut into `k` consecutive blocks of `s` bits
(`Data.chunk`). This module relates the two: the bits of a joined vector are the concatenation
of the bits of its blocks (`toBits_join`), the `i`-th block of the vector read off a bit
string is the vector read off the `i`-th chunk (`block_ofBits`), and likewise for indicator
strings of register subspaces (`indicatorBits_blockSet`).
-/

namespace MIPRE.CL

open Cost.Data (chunk)

variable {k s : ℕ}

theorem finProdFinEquiv_val (i : Fin k) (j : Fin s) :
    ((finProdFinEquiv (i, j) : Fin (k * s)) : ℕ) = j + s * i := rfl

/-- A list indexed by `Fin (k s)` is the concatenation of its `k` blocks of `s`. -/
theorem ofFn_eq_flatten_blocks {α : Type*} (f : Fin (k * s) → α) :
    List.ofFn f =
      (List.ofFn fun i : Fin k => List.ofFn fun j : Fin s => f (finProdFinEquiv (i, j))).flatten := by
  rw [List.ofFn_mul]
  refine congrArg List.flatten (congrArg List.ofFn (funext fun i => congrArg List.ofFn
    (funext fun j => congrArg f (Fin.ext ?_))))
  change (i : ℕ) * s + j = _
  rw [finProdFinEquiv_val]
  ring

/-- The bits of a joined vector: the bits of its blocks, concatenated. -/
theorem toBits_join (v : Fin k → Fin s → 𝔽₂) :
    toBits (join finProdFinEquiv v) = (List.ofFn fun i => toBits (v i)).flatten := by
  unfold toBits
  rw [ofFn_eq_flatten_blocks]
  simp [join]

/-- The indicator string of a block set: the indicator strings of the blocks, concatenated. -/
theorem indicatorBits_blockSet (T : Fin k → Finset (Fin s)) :
    indicatorBits (blockSet finProdFinEquiv T) = (List.ofFn fun i => indicatorBits (T i)).flatten := by
  unfold indicatorBits
  rw [ofFn_eq_flatten_blocks]
  simp

theorem length_flatten_ofFn {α : Type*} (g : Fin k → List α) (hg : ∀ i, (g i).length = s) :
    (List.ofFn g).flatten.length = k * s := by
  rw [List.length_flatten, List.map_ofFn]
  simp [Function.comp_def, hg, List.ofFn_const, List.sum_replicate]

/-- The `i`-th chunk of a concatenation of `k` lists of length `s` is the `i`-th list. -/
theorem chunk_flatten_ofFn {α : Type*} : ∀ {k : ℕ} (g : Fin k → List α),
    (∀ i, (g i).length = s) → ∀ i : Fin k, chunk s i (List.ofFn g).flatten = g i
  | 0, _, _, i => i.elim0
  | k + 1, g, hg, i => by
    rw [List.ofFn_succ, List.flatten_cons]
    refine Fin.cases ?_ (fun i' => ?_) i
    · simp only [chunk, Fin.val_zero, zero_mul, List.drop_zero]
      rw [List.take_append_of_le_length (hg 0).ge, List.take_of_length_le (hg 0).le]
    · have ih := chunk_flatten_ofFn (fun i => g i.succ) (fun i => hg i.succ) i'
      simp only [chunk, Fin.val_succ] at ih ⊢
      rw [List.drop_append, List.drop_of_length_le (by rw [hg 0]; nlinarith),
        List.nil_append, hg 0, show (i' + 1) * s - s = i' * s by rw [Nat.add_mul, one_mul]; omega]
      exact ih

/-- The `i`-th block of the vector read off a bit string is the vector read off its `i`-th
chunk. -/
theorem block_ofBits (z : Cost.BitStr) (i : Fin k) :
    block finProdFinEquiv i (ofBits (k * s) z) = ofBits s (chunk s i z) := by
  funext j
  simp only [block, ofBits, finProdFinEquiv_val, chunk, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt j.isLt, List.getElem?_drop]
  rw [show (i : ℕ) * s + j = j + s * i by ring]

theorem chunk_map {α β : Type*} (f : α → β) (i : ℕ) (l : List α) :
    chunk s i (l.map f) = (chunk s i l).map f := by
  simp [chunk, List.map_take, List.map_drop]

theorem length_chunk {α : Type*} {l : List α} (hl : l.length = k * s) (i : Fin k) :
    (chunk s i l).length = s := by
  have hi : (i + 1) * s ≤ k * s := Nat.mul_le_mul_right s i.isLt
  rw [Nat.add_mul, one_mul] at hi
  simp only [chunk, List.length_take, List.length_drop, hl]
  omega

@[simp] theorem chunk_nil {α : Type*} (i : ℕ) : chunk s i ([] : List α) = [] := by
  simp [chunk]

end MIPRE.CL

namespace MIPRE.Cost

namespace Data

/-- The bits denoted by a list of data (`bitOf`), the left inverse of encoding a bit string. -/
def bitsOf (l : List Data) : BitStr := l.map bitOf

@[simp] theorem bitsOf_map_ofBool (x : BitStr) : bitsOf (x.map ofBool) = x := by
  simp [bitsOf, List.map_map, Function.comp_def]

theorem toList_encode_bitStr (x : BitStr) : toList (encode x) = x.map ofBool := by
  rw [encode_bitStr_eq_list, toList_list]

theorem replicate_nil_eq_map (m : ℕ) :
    List.replicate m (nil : Data) = (List.replicate m false).map ofBool := by
  simp [List.map_replicate, ofBool]

end Data

end MIPRE.Cost
