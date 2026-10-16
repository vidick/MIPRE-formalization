/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Dilation.lean (statement stub of MIPRE.exists_isometry_of_povm);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_MIPRE_Foundations_Dilation

open MIPRE
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

theorem MIPRE.exists_isometry_of_povm {d A : Type*} [Fintype d] [DecidableEq d]
    [Fintype A] [DecidableEq A] {E : A → Matrix d d ℂ}
    (hpos : ∀ a, (E a).PosSemidef) (hsum : ∑ a, E a = 1) :
    ∃ V : Matrix (d × A) d ℂ, Vᴴ * V = 1 ∧
      ∀ a : A, Vᴴ * (ancillaProj d a * V) = E a := by sorry
