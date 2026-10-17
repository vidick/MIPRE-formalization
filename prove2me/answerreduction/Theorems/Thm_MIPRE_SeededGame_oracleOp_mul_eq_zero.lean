/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/OracularComplete.lean (statement stub of MIPRE.SeededGame.oracleOp_mul_eq_zero);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_OracularGame
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_OracularComplete

open MIPRE
open MIPRE.SeededGame
open Finset Matrix
variable {V A : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype A] [DecidableEq A]
variable (S : SeededGame V A)
variable {S}
variable (S)
variable {S}
variable (S)
variable {S}

theorem MIPRE.SeededGame.oracleOp_mul_eq_zero (T : SyncStrategy S.toGame.doubled) (hT : T.IsPCC)
    (hval : T.value = 1) {p q : Role × V} (hμ : 0 < S.oDist p q) {u v : OAns A}
    (hrej : S.oaccepts p q u v = false) :
    S.oracleOp T p u * S.oracleOp T q v = 0 := by sorry
