/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Swap.lean (statement stub of MIPRE.povmValue_swapVec_of_symm);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Swap

open MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
variable {X A dA dB : Type*} [Fintype X] [Fintype A] [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB]

theorem MIPRE.povmValue_swapVec_of_symm {G : Game X X A A} (ψ : dA × dB → ℂ)
    (MA : X → POVM A dA) (MB : X → POVM A dB)
    (hμ : ∀ x y, G.μ x y = G.μ y x) (hD : ∀ x y a b, G.D x y a b = G.D y x b a) :
    povmValue G (swapVec ψ) MB MA = povmValue G ψ MA MB := by sorry
