/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Basic.lean (statement stub of MIPRE.Cost.Eval.deterministic);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Notation
import Definitions.Def_MIPRE_Foundations_Cost_Basic

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Eval

theorem MIPRE.Cost.Eval.deterministic {env : Env} {p : Prog} {r r' : Data} {t t' : ℕ}
    (h : Eval env p r t) (h' : Eval env p r' t') : r = r' ∧ t = t' := by sorry
