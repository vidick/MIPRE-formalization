/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Parseval.lean (statement stub of MIPRE.sum_avg_norm_fibre_sq);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval

open MIPRE
open Finset Matrix MIPRE.Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {N : Type*} [Fintype N] [DecidableEq N]
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]

theorem MIPRE.sum_avg_norm_fibre_sq (U : F × F → (N → ℂ)) (hU : ∑ p : F × F, U p = 0) :
    ∑ ab : F × F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) *
        ∑ c : F, ‖evec (∑ p ∈ univ.filter fun p : F × F =>
          ab.1 * p.1 + ab.2 * p.2 = c, U p)‖ ^ 2
      = (1 - (Fintype.card F : ℝ)⁻¹) * ∑ p : F × F, ‖evec (U p)‖ ^ 2 := by sorry
