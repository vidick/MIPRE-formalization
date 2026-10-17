/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/Anticomm.lean (statement stub of MIPRE.QLD.MS.pvBit_rep);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Definitions.Def_MIPRE_LCS_Strategy_ObservableToProjector
import Definitions.Def_MIPRE_LCS_NonlocalGame
import Definitions.Def_MIPRE_LCS_Pauli
import Definitions.Def_MIPRE_LCS_MagicSquare_Strategy
import Definitions.Def_MIPRE_LCS_MagicSquare_Game
import Definitions.Def_MIPRE_Foundations_Swap
import Definitions.Def_MIPRE_Background_QLD_Anticomm

open MIPRE
open MIPRE.QLD
open MIPRE.QLD.MS
open Finset Matrix Kronecker MIPRE MIPRE.LCS MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

theorem MIPRE.QLD.MS.pvBit_rep (c : Fin layout.r) {a : Fin layout.s → ZMod 2}
    (ha : (∑ k ∈ layout.V c, a k) = game.b c) (j : Fin 3) :
    pvBit c (rep c (Sum.inl a)) j = a (cell c j) := by sorry
