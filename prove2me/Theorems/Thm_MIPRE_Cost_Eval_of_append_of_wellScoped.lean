/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Basic.lean (statement stub of MIPRE.Cost.Eval.of_append_of_wellScoped);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Notation
import Definitions.Def_MIPRE_Foundations_Cost_Basic

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Eval

theorem MIPRE.Cost.Eval.of_append_of_wellScoped {env extra : Env} {p : Prog} {r : Data} {t : ℕ}
    (h : Eval (env ++ extra) p r t) (hp : p.WellScoped env.length) : Eval env p r t := by sorry
