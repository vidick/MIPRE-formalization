/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Sound.lean (statement stub of MIPRE.TM.CookLevin.window_of_sat);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Computability.Language
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sign.Defs
import Mathlib.Logic.Relation
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_CookLevin_Local
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_TM_CookLevin_Tableau
import Definitions.Def_MIPRE_TM_CookLevin_Semantics
import Definitions.Def_MIPRE_TM_CookLevin_Correct
import Definitions.Def_MIPRE_TM_CookLevin_Sound

open MIPRE
open MIPRE.TM
open MIPRE.TM.CookLevin
open Turing MIPRE.SAT MultiInputTM
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S G : ℕ}
  (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
omit [Fintype Symbol] [Fintype State]

theorem MIPRE.TM.CookLevin.window_of_sat (a : TabVar i w Symbol State S G → Bool) (t : Fin S)
    (c : Cfg i w Symbol State input) (hrow : RowOk a t.castSucc c) (js : Tape i w → Center S)
    (hwin : checkPred M acc (fun v => a (winVarOf (G := G) t js v))) :
    ∃ L : LocalCfg i w Symbol State, LocallyConsistent M acc L ∧
      (∀ v, L.encode v = a (winVarOf (G := G) t js v)) ∧
      L.cellPre = (localCfgOf M acc c js).cellPre ∧ L.headPre = (localCfgOf M acc c js).headPre ∧
      L.statePre = (localCfgOf M acc c js).statePre := by sorry
