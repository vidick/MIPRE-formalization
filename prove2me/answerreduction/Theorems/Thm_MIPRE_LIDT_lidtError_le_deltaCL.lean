/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Parameters.lean (statement stub of MIPRE.LIDT.lidtError_le_deltaCL);
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

theorem MIPRE.LIDT.lidtError_le_deltaCL (m d q : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (ε : ℝ) (hε : 0 ≤ ε) :
    lidtError m d q (clK m d) (3 * m * ε) ≤ deltaCL q m d ε := by sorry
