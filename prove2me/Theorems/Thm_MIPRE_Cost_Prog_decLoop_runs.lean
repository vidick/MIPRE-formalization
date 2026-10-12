/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Numeric.lean (statement stub of MIPRE.Cost.Prog.decLoop_runs);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog

theorem MIPRE.Cost.Prog.decLoop_runs (j : ℕ) (rest : BitStr) (i : ℕ) (env : Env) (S : ℕ)
    (hS : 2 * j + (encode rest).size + 4 + (4 * i + 1) + 2 * j ≤ S) :
    ∃ t ≤ (j + 1) * (S + 15),
      Eval (.cons (encode (List.replicate j false ++ true :: rest))
          (encode (List.replicate i true)) :: env) (.loop decBody)
        (.cons (encode (false :: List.replicate (i + j) true)) (encode rest)) t := by sorry
