/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Parameters.lean (statement stub of MIPRE.LIDT.prefactor_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Parameters

open MIPRE
open MIPRE.LIDT

theorem MIPRE.LIDT.prefactor_le (m d : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) :
    100000 * (clK m d : ℝ) ^ 2 * (m : ℝ) ^ 4 * (3 * (m : ℝ) * d)
      ≤ clA * ((d * m : ℕ) : ℝ) ^ clA := by sorry
