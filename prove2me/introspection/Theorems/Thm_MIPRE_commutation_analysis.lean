/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Commutation.lean (statement stub of MIPRE.commutation_analysis);
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
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {B C : Type*} [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

theorem MIPRE.commutation_analysis {ψ : dA × dB → ℂ} {A : POVM B dA} {Cm : POVM C dA}
    {P : B × C → Matrix dB dB ℂ} (hP : IsPVM P) {δ : ℝ}
    (hA : ∑ b, snorm ψ ((aOp ((A.mats b).val) : Matrix (dA × dB) (dA × dB) ℂ)
        - bOp (∑ c, P (b, c))) ^ 2 ≤ δ)
    (hC : ∑ c, snorm ψ ((aOp ((Cm.mats c).val) : Matrix (dA × dB) (dA × dB) ℂ)
        - bOp (∑ b, P (b, c))) ^ 2 ≤ δ) :
    ∑ p : B × C, snorm ψ ((aOp ((A.mats p.1).val) : Matrix (dA × dB) (dA × dB) ℂ)
          * aOp ((Cm.mats p.2).val)
        - (aOp ((Cm.mats p.2).val) : Matrix (dA × dB) (dA × dB) ℂ)
          * aOp ((A.mats p.1).val)) ^ 2 ≤ 16 * δ := by sorry
