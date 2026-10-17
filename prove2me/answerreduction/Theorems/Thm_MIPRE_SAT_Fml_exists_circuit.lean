/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/Table.lean (statement stub of MIPRE.SAT.Fml.exists_circuit);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_Table

open MIPRE
open MIPRE.SAT
open MIPRE.SAT.Fml

theorem MIPRE.SAT.Fml.exists_circuit (N : ℕ) (f : (Fin N → Bool) → Bool) :
    ∃ C : Circuit, C.WellFormed ∧ C.inputs = N ∧ C.size ≤ 7 * 2 ^ N ∧
      ∀ x : Fin N → Bool, C.evalBits (List.ofFn x) = f x := by sorry
