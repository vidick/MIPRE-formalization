/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/Bits.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Repeat_Prims
import Definitions.Def_MIPRE_Foundations_CL_Repeat

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

@[simp] theorem chunk_zero {α : Type*} (l : List α) : chunk s 0 l = l.take s := by simp [chunk]

@[simp] theorem chunk_nil {α : Type*} (i : ℕ) : chunk s i ([] : List α) = [] := by
  simp [chunk]

end MIPRE.CL

namespace MIPRE.Cost

namespace Data

/-- The bits denoted by a list of data (`bitOf`), the left inverse of encoding a bit string. -/
def bitsOf (l : List Data) : BitStr := l.map bitOf

@[simp] theorem bitsOf_map_ofBool (x : BitStr) : bitsOf (x.map ofBool) = x := by
  simp [bitsOf, List.map_map, Function.comp_def]

end Data

end MIPRE.Cost
