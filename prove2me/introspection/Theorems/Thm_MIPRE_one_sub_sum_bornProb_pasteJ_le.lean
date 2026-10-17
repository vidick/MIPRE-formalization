/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Pasting.lean (statement stub of MIPRE.one_sub_sum_bornProb_pasteJ_le);
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
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_Pasting

open MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {ι R1 R2 K : Type*} [Fintype ι] [Fintype R1] [DecidableEq R1] [Fintype R2]
  [DecidableEq R2] [Fintype K] [DecidableEq K]

theorem MIPRE.one_sub_sum_bornProb_pasteJ_le {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1)
    {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    {A : ι → R1 × R2 → Matrix dA dA ℂ} {R : ι → R1 → Matrix dB dB ℂ}
    {G : ι → K → Matrix dB dB ℂ} {Ga : ι → K → Matrix dA dA ℂ} (e : ι → K → R2)
    (hA : ∀ i, IsPVM (A i)) (hR : ∀ i, IsPVM (R i)) (hG : ∀ i, IsPVM (G i))
    (hGa : ∀ i, IsPVM (Ga i)) {δ η ε : ℝ}
    (hP1 : ∑ i, w i * ∑ a : R1, xSqNorm ψ (∑ b : R2, A i (a, b)) (R i a) ≤ δ)
    (hP2 : ∑ i, w i * ∑ b : R2,
      xSqNorm ψ (∑ a : R1, A i (a, b)) (fibSum (G i) (e i) b) ≤ δ)
    (hP4 : ∑ i, w i * ∑ g : K, xSqNorm ψ (Ga i g) (G i g) ≤ η)
    (hcoll : ∑ i, w i * collisionTerm ψ (R i) (G i) (Ga i) (e i) ≤ ε) :
    1 - ∑ i, w i * ∑ p : R1 × R2, bornProb ψ (A i p) (pasteJ (R i) (G i) (e i) p)
      ≤ δ / 2 + Real.sqrt (δ / 2) + Real.sqrt (32 * δ + 4 * Real.sqrt η + 2 * ε) := by sorry
