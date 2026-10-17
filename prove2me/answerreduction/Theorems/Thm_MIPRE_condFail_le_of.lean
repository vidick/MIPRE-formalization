/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Disagreement.lean (statement stub of MIPRE.condFail_le_of);
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
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_POVMMix
import Definitions.Def_MIPRE_Foundations_Disagreement

open MIPRE
open Finset Matrix
open scoped Kronecker
variable {Λ : Type*} [Fintype Λ] {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB]
  [DecidableEq dB]
variable {X Y A B C : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq C] {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}

theorem MIPRE.condFail_le_of (hψ : star ψ ⬝ᵥ ψ = 1) {x : X} {y : Y} (EA : A → Prop) (EB : B → Prop)
    [DecidablePred EA] [DecidablePred EB] (f : A → C) (g : B → C)
    (hD : ∀ a b, ¬ EA a → ¬ EB b → f a = g b → G.D x y a b = true) :
    condFail G ψ MA MB x y
      ≤ ∑ a, (if EA a then bornProb ψ (((MA x).mats a).val) (1 : Matrix dB dB ℂ) else 0)
        + ∑ b, (if EB b then bornProb ψ (1 : Matrix dA dA ℂ) (((MB y).mats b).val) else 0)
        + dis ψ ((MA x).map f) ((MB y).map g) := by sorry
