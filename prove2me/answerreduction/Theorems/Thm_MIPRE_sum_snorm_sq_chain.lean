/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/OracularTensor.lean (statement stub of MIPRE.sum_snorm_sq_chain);
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
import Definitions.Def_MIPRE_Foundations_OracularGame
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_OracularSound
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_POVMMix
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_OracularTensor

open MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]

theorem MIPRE.sum_snorm_sq_chain (ψ : HA × HB → ℂ) {K : Type*} [Fintype K] [DecidableEq K]
    (C OA OB : K → Matrix HA HA ℂ) (P Q : K → Matrix HB HB ℂ) (hQ : IsPVM Q) (hOA : IsPVM OA) :
    ∑ o : K × K,
        snorm ψ ((aOp (C o.1) : Matrix (HA × HB) (HA × HB) ℂ) * bOp (Q o.2)
          - aOp (OA o.1 * OB o.2)) ^ 2
      ≤ 3 * ∑ u, snorm ψ ((aOp (C u) : Matrix (HA × HB) (HA × HB) ℂ) - bOp (P u)) ^ 2
        + 3 * ∑ u, snorm ψ ((aOp (OA u) : Matrix (HA × HB) (HA × HB) ℂ) - bOp (P u)) ^ 2
        + 3 * ∑ v, snorm ψ ((aOp (OB v) : Matrix (HA × HB) (HA × HB) ℂ) - bOp (Q v)) ^ 2 := by sorry
