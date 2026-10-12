/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Succinct.lean (statement stub of MIPRE.Cost.isSuccinctDesc_hardcode);
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
import Definitions.Def_MIPRE_Foundations_Cost_BitQuery
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Succinct

open MIPRE
open MIPRE.Cost
open Polynomial

theorem MIPRE.Cost.isSuccinctDesc_hardcode (U : UniversalMachine) {α : Type*} [SizedEncoding α]
    (c' e : Prog) (n' : α) (n : ℕ) (y : BitStr)
    {t : ℕ} (hrun : c'.Runs (encode (e, n')) (encode y) t) (hlen : t ≤ 2 ^ n)
    (hbudget : (bitQueryBound U).eval (esize c' + esize e + esize n' + t) +
      (esize c' + esize e + 1 + esize n' + 1) + 4 ≤ n + 1) :
    IsSuccinctDesc (hardcode (Prog.bitQueryProg U.univ) (encode ((c', e), n'))) n y := by sorry
