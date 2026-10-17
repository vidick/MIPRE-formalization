/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/Interp/Repr.lean (statement stub of MIPRE.TM.Interp.mem_frameBody);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Sign.Defs
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
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
import Definitions.Def_MIPRE_TM_Interp_Instr
import Definitions.Def_MIPRE_TM_Interp_Tape
import Definitions.Def_MIPRE_TM_Interp_Repr

open MIPRE
open MIPRE.TM
open MIPRE.TM.Interp
open MIPRE.Cost MIPRE.Cost.Machine

theorem MIPRE.TM.Interp.mem_frameBody (f : Frame) : ∀ s ∈ frameBody f, s ≠ .fr := by sorry
