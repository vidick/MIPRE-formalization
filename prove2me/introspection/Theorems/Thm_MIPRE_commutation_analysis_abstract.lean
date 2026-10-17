/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Commutation.lean (statement stub of MIPRE.commutation_analysis_abstract);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation

open MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N] [DecidableEq N] {B C : Type*} [Fintype B] [Fintype C]
  {v : N → ℂ} {δ : ℝ}

theorem MIPRE.commutation_analysis_abstract (v : N → ℂ)
    (alpha : B → Matrix N N ℂ) (gamma : C → Matrix N N ℂ)
    (betaB : B → Matrix N N ℂ) (betaC : C → Matrix N N ℂ)
    (betaBC : B × C → Matrix N N ℂ)
    (halpha : ∑ b, (alpha b)ᴴ * alpha b ≤ (1 : Matrix N N ℂ))
    (hgamma : ∑ c, (gamma c)ᴴ * gamma c ≤ (1 : Matrix N N ℂ))
    (hbetaB : ∑ b, (betaB b)ᴴ * betaB b ≤ (1 : Matrix N N ℂ))
    (hbetaC : ∑ c, (betaC c)ᴴ * betaC c ≤ (1 : Matrix N N ℂ))
    (hcomm : ∀ b c, alpha b * betaC c = betaC c * alpha b)
    (hcomm' : ∀ b c, gamma c * betaB b = betaB b * gamma c)
    (hmul : ∀ b c, betaC c * betaB b = betaBC (b, c))
    (hmul' : ∀ b c, betaB b * betaC c = betaBC (b, c))
    (hA : ∑ b, snorm v (alpha b - betaB b) ^ 2 ≤ δ)
    (hC : ∑ c, snorm v (gamma c - betaC c) ^ 2 ≤ δ) :
    ∑ p : B × C, snorm v (alpha p.1 * gamma p.2 - gamma p.2 * alpha p.1) ^ 2 ≤ 16 * δ := by sorry
