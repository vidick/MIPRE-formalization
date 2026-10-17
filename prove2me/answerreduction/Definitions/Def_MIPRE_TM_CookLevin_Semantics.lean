/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Semantics.lean (definition bundle: declarations the uploaded statements rest on);
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

/-!
# The windows of a run are locally consistent

`localCfgOf M acc c js` is the local configuration read off a configuration `c` and its
successor at the window `js`; its encoding is the assignment of the run on the window's
variables (`encode_localCfgOf`), and it is locally consistent
(`locallyConsistent_localCfgOf`): the completeness half of the tableau's correctness
(`planning/succinct-cook-levin.md`, S1). The proof is the case analysis of the paper's
`lem:correct-tableau` on where the heads are, with the clamping of the input heads
(`Turing.moveInputPos`) matched against the tableau's rule (`newOffset`).
-/

namespace MIPRE.TM.CookLevin

open Turing SAT MultiInputTM
open MultiTapeTM (moveInputPos moveInputPos_zero)

section

variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}

/-! ## Positions -/

@[simp] theorem cellIdx_val (c : Center S) (δ : Fin 5) : ((cellIdx c δ : Pos S) : ℕ) = c + δ := rfl

@[simp] theorem center_val (c : Center S) : ((center c : Pos S) : ℕ) = c + 2 := rfl

/-! ## The local configuration of a run -/

variable (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}

/-- The local configuration of a configuration and its successor at the window `js`. -/
def localCfgOf (c : Cfg i w Symbol State input) (js : Tape i w → Center S) :
    LocalCfg i w Symbol State where
  cellPre d δ := cellValAt (S := S) c d (cellIdx (js d) δ)
  headPre d δ := decide (headCell (S := S) c d = cellIdx (js d) δ)
  cellPost d := cellValAt (S := S) (M.step c) d (center (js d))
  headPost d := decide (headCell (S := S) (M.step c) d = center (js d))
  statePre := c.state
  statePost := (M.step c).state
  emitOne := decide (M.outputSymbol c = some acc)
  emitBad := decide (M.outputSymbol c ≠ none ∧ M.outputSymbol c ≠ some acc)

/-! ## Heads -/

/-! ## The step, componentwise -/

/-! ## The cells under the heads -/

/-! ## Head positions -/

/-- The bounds under which every head is on an interior cell; they hold at every time
`t ≤ S` of a run (`headsIn_cfgAt`), since a head moves at most one position per step. -/
structure HeadsIn (c : Cfg i w Symbol State input) (S : ℕ) : Prop where
  input_pos : ∀ j, (c.inputPos j : ℕ) ≤ 2 * S + 2
  work_pos : ∀ j, -(S : ℤ) ≤ c.workTapePos j ∧ c.workTapePos j ≤ S

/-! ## The full step -/

end

end MIPRE.TM.CookLevin
