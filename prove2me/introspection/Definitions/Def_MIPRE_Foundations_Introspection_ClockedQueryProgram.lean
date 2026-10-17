/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/ClockedQueryProgram.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B

/-! # Polynomial-time source calls with an explicit unary resource

The outer verifier computes its exponential clock once. Passing that clock
as unary data makes each bounded source query a genuine `PolyTimeFun`, so
matrix-column queries and attained-prefix scans can use the existing bounded
map and fold combinators. No polynomial bound in the binary clock is claimed.
-/

noncomputable section
namespace MIPRE.Introspection.ClockedQuery
open Cost Cost.PolyTimeFun

def run (U : ClockedUniversalMachine) : PolyTimeFun (Unary × Prog × Data) Data where
  toFun p := clockedResult p.2.1 p.2.2 p.1.length
  code := U.univT
  closed := U.closed
  timeBound := U.bound
  computes p := by
    rcases p with ⟨budget, source, input⟩
    obtain ⟨t, ht, hr⟩ := U.run source input budget.length
    have hb : encode budget = Data.ofNat budget.length := by
      rw [← unary_length budget, encode_unary]
      simp
    have hs : budget.length + esize source + input.size ≤ esize (budget, source, input) := by
      simp only [esize_prod, esize_data]
      have he : esize budget = 2 * budget.length + 1 := by
        rw [esize, hb, Data.size_ofNat]
      omega
    refine ⟨t, ht.trans (polynomial_eval_mono U.bound hs), ?_⟩
    simpa only [encode_prod, hb, encode_data] using hr

@[simp] theorem run_apply (U : ClockedUniversalMachine) (budget : Unary)
    (source : Prog) (input : Data) :
    run U (budget, source, input) = clockedResult source input budget.length := rfl

end MIPRE.Introspection.ClockedQuery
end
