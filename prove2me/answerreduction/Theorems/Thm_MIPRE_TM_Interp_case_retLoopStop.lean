/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/Interp/Step.lean (statement stub of MIPRE.TM.Interp.case_retLoopStop);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Language
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Sign.Defs
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation
import Mathlib.Tactic
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_Interp_Instr
import Definitions.Def_MIPRE_TM_Interp_Machine
import Definitions.Def_MIPRE_TM_Interp_Tape
import Definitions.Def_MIPRE_TM_Interp_Reach
import Definitions.Def_MIPRE_TM_Interp_Routines
import Definitions.Def_MIPRE_TM_Interp_Repr
import Definitions.Def_MIPRE_TM_Interp_CopyTree
import Definitions.Def_MIPRE_TM_Interp_GetEnv
import Definitions.Def_MIPRE_TM_Interp_Desc
import Definitions.Def_MIPRE_TM_Interp_Step

open MIPRE
open MIPRE.TM
open MIPRE.TM.Interp
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}

theorem MIPRE.TM.Interp.case_retLoopStop {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .retLoop1 0) ds)
    {r' : Data} {b : Prog} {env env' : Env} {k : List Frame} {r : ℕ}
    (hr : RepOf ds ⟨.ret (.cons .nil r'), env, .loop1 b env' :: k⟩ r 1 ((kontRepr k).length + 1)) :
    PreTo c (caseBound ⟨.ret (.cons .nil r'), env, .loop1 b env' :: k⟩ (ds X).l.length)
      (at_ .retLoopStop 15) ⟨.ret r', env', k⟩ r (ctrlRepr (.ret r')).length (kontRepr k).length
      ((ds X).l.length + sz ⟨.ret (.cons .nil r'), env, .loop1 b env' :: k⟩) := by sorry
