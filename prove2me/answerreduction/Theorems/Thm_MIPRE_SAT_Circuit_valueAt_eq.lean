/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/Circuit.lean (statement stub of MIPRE.SAT.Circuit.valueAt_eq);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit

open MIPRE
open MIPRE.SAT
open MIPRE.SAT.Circuit
open MIPRE.Cost

theorem MIPRE.SAT.Circuit.valueAt_eq (C : Circuit) (x : ℕ → Bool) (g : ℕ) :
    C.valueAt x g = (C.gates.getD g (.const false)).eval x (List.ofFn fun k : Fin g => C.valueAt x k) := by sorry
