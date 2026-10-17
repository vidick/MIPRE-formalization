/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/Interp/GetEnv.lean (statement stub of MIPRE.TM.Interp.exec_getEnv);
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

open MIPRE
open MIPRE.TM
open MIPRE.TM.Interp
open Turing MultiInputTM Phase MIPRE.Cost
variable {input : Fin 7 → List Sym}

theorem MIPRE.TM.Interp.exec_getEnv {k : ProgId} {pc : Fin maxPc} (hins : instrAt k pc = .getEnv)
    (hpc : pc.val + 1 < maxPc) (env : Env) (i : ℕ) (c : Cfg input) (hq : c.state = at_ k pc)
    (hE : EnvTape (c.workTapes E) env) (hpos : c.workTapePos E = (envRepr env).length)
    (hC : Holds (c.workTapes C) (c.workTapePos C) (S (Data.ofNat i))) :
    ∃ n ≤ 3 * i + 3 * (envRepr env).length + 9,
    ∃ c', Reach c n c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [] [C, E, X] ∧
      c'.workTapes C = c.workTapes C ∧ c'.workTapePos C = c.workTapePos C + (2 * i + 1 : ℕ) ∧
      c'.workTapes E = c.workTapes E ∧ c'.workTapePos E = (envRepr env).length ∧
      DstEff X c c' (S (Env.get env i)) := by sorry
