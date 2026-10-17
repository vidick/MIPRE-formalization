/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/Interp/Routines.lean (statement stub of MIPRE.TM.Interp.scan_leftToMarker);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Computability.Language
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Sign.Defs
import Mathlib.Logic.Relation
import Mathlib.Tactic
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_Interp_Instr
import Definitions.Def_MIPRE_TM_Interp_Machine
import Definitions.Def_MIPRE_TM_Interp_Tape
import Definitions.Def_MIPRE_TM_Interp_Reach
import Definitions.Def_MIPRE_TM_Interp_Routines

open MIPRE
open MIPRE.TM
open MIPRE.TM.Interp
open Turing MultiInputTM Phase
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}

theorem MIPRE.TM.Interp.scan_leftToMarker {k : ProgId} {pc : Fin maxPc} {m : Sym} {t : WT}
    (hins : instrAt k pc = .leftToMarker m t) (hpc : pc.val + 1 < maxPc) (l : List Sym) :
    ∀ (c : Cfg input), c.state = some ⟨k, pc, p1⟩ →
      Holds (c.workTapes t) (c.workTapePos t + 1 - l.length) l → (∀ s ∈ l, s ≠ m) →
      (c.workTapes t (c.workTapePos t - l.length) = some m ∨
        c.workTapes t (c.workTapePos t - l.length) = none) →
    ∃ c', Reach c (l.length + 1) c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [] [t] ∧
      c'.workTapes t = c.workTapes t ∧ c'.workTapePos t = c.workTapePos t - l.length + 1 := by sorry
