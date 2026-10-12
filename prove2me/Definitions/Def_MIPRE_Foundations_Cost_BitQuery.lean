/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/BitQuery.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric

/-!
# The bit-query program

`bitAtProg` on `(y, m)` — a bit string and a binary index — returns the `m`-th bit of `y`,
or the out-of-range marker `ofNat 2`: this is the answer a succinct description must give
([MNY, Definition 2.4]; `bitQueryAnswer`). It walks `y` while decrementing `m` in binary,
testing for zero at each step, so its cost is `(|y| + 1) · bitAtIter (size y) |m|` with
`bitAtIter` quadratic in `|m|` (each zero test and decrement copies the index). This is
where the `(|m| + 1) ^ 2` factor of the succinctness budget of `IsSuccinctDesc` comes from.
-/

namespace MIPRE.Cost

/-- The answer a succinct description must give to the bit-query `m` about the string
`x`: the `m`-th bit for `m < |x|`, and the out-of-range marker (the unary numeral `2`)
otherwise. -/
def bitQueryAnswer (x : BitStr) (m : ℕ) : Data :=
  if h : m < x.length then encode (x.get ⟨m, h⟩) else Data.ofNat 2

@[simp] theorem bitQueryAnswer_nil (m : ℕ) : bitQueryAnswer [] m = Data.ofNat 2 := by
  simp [bitQueryAnswer]

@[simp] theorem bitQueryAnswer_cons_zero (b : Bool) (x : BitStr) :
    bitQueryAnswer (b :: x) 0 = encode b := by
  simp [bitQueryAnswer]

@[simp] theorem bitQueryAnswer_cons_succ (b : Bool) (x : BitStr) (m : ℕ) :
    bitQueryAnswer (b :: x) (m + 1) = bitQueryAnswer x m := by
  unfold bitQueryAnswer
  by_cases h : m < x.length
  · have h' : m + 1 < (b :: x).length := by simp [h]
    rw [dif_pos h', dif_pos h]
    rfl
  · have h' : ¬ m + 1 < (b :: x).length := by simp [h]
    rw [dif_neg h', dif_neg h]

namespace Prog

/-- Cost of one zero test on a bit string of length `L`. -/
def zeroBound (L : ℕ) : ℕ := (L + 1) * (4 * L + 1 + 8)

/-- Cost of one decrement on a bit string of length `L`. -/
def decBound (L : ℕ) : ℕ := (L + 2) * (10 * (6 * L + 4) + 60)

/-- Cost of one iteration of `bitAtProg` with a string of size at most `sy` and an index of
`L` bits. -/
def bitAtIter (sy L : ℕ) : ℕ := sy + 8 * L + zeroBound L + decBound L + 20

/-- Body of `bitAtProg`: on state `cons y m`, stop with `ofNat 2` if `y` is exhausted; else
test `m` for zero: if zero, stop with the head bit of `y`; otherwise continue with the tail
of `y` and `m - 1`. -/
def bitAtBody : Prog :=
  .elim 0 .nil (.elim 0 (.cons .nil (.const (.ofNat 2)))
    (.let_ (callVar 3 isZeroProg)
      (.elim 0 (.cons .nil (.var 1))
        (.cons (.cons .nil .nil) (.cons (.var 4) (callVar 6 decProg))))))

/-- `bitAtProg` on `cons (encode y) (encode m)` computes `bitQueryAnswer y m`. -/
def bitAtProg : Prog := .loop bitAtBody

end Prog

end MIPRE.Cost
