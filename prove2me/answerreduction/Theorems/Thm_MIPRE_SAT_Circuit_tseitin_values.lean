/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/Tseitin.lean (statement stub of MIPRE.SAT.Circuit.tseitin_values);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin

open MIPRE
open MIPRE.SAT
open MIPRE.SAT.Circuit
variable {V : Type*}

theorem MIPRE.SAT.Circuit.tseitin_values (C : Circuit) (hC : C.RefsLt) (inp gv : ℕ → V) (w : V → Bool)
    (hSat : ∀ c ∈ C.tseitin inp gv, c.eval w = true) :
    ∀ g < C.gates.length, w (gv g) = C.valueAt (fun i => w (inp i)) g := by sorry
