/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/Interp/Step.lean (statement stub of MIPRE.TM.Interp.evDispatch_round);
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

theorem MIPRE.TM.Interp.evDispatch_round {pc : Fin maxPc} {tgt : ProgId} (h1 : instrAt .evDispatch pc = .move C true)
    (h2 : pc.val + 1 < maxPc) (h2' : instrAt .evDispatch ⟨pc.val + 1, h2⟩ = .move C true)
    (h3 : pc.val + 2 < maxPc) (h3' : instrAt .evDispatch ⟨pc.val + 2, h3⟩ = .branch C (some .zero) tgt)
    {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .evDispatch pc) ds) :
    ((ds C).l[(ds C).p + 2]? = some .zero →
      ∃ c', Reach c 3 c' [] ∧ Desc c' (at_ tgt 0) (Function.update ds C ⟨(ds C).l, (ds C).p + 2⟩)) ∧
    ((ds C).l[(ds C).p + 2]? ≠ some .zero → (h4 : pc.val + 2 + 1 < maxPc) →
      ∃ c', Reach c 3 c' [] ∧
        Desc c' (next_ .evDispatch ⟨pc.val + 2, h3⟩ h4)
          (Function.update ds C ⟨(ds C).l, (ds C).p + 2⟩)) := by sorry
