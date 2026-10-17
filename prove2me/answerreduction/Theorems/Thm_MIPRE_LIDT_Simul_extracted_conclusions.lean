/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Extraction.lean (statement stub of MIPRE.LIDT.Simul.extracted_conclusions);
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
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
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
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Background_LIDT_Coefficients
import Definitions.Def_MIPRE_Background_LIDT_Extraction

open MIPRE
open MIPRE.LIDT
open MIPRE.LIDT.Simul
open Finset MIPRE MIPRE.LIDT
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ}
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

theorem MIPRE.LIDT.Simul.extracted_conclusions (hd : 1 ≤ d) (hr : r ≤ K) {ψ : dA × dB → ℂ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (A : Point F m → POVM (Fin r → F) dA)
    (B : Point F m → POVM (Fin r → F) dB)
    (RA : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := K + m) (d := d))
      (Matrix dA dA ℂ))
    (RB : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := K + m) (d := d))
      (Matrix dB dB ℂ)) {δ : ℝ}
    (h1 : inconsistency (uniform (Point F (K + m))) ψ (combPOVM hd A) (evalPOVM RB) ≤ δ)
    (h2 : inconsistency (uniform (Point F (K + m))) ψ (evalPOVM RA) (combPOVM hd B) ≤ δ)
    (h3 : inconsistency (uniform Unit) ψ (fun _ => RA.toPOVM ()) (fun _ => RB.toPOVM ()) ≤ δ) :
    inconsistency (uniform (Point F m)) ψ A (evalTuplePOVM (extractPM hd hr RB))
        ≤ δ + (K + m) * d / Fintype.card F ∧
      inconsistency (uniform (Point F m)) ψ (evalTuplePOVM (extractPM hd hr RA)) B
        ≤ δ + (K + m) * d / Fintype.card F ∧
      inconsistency (uniform Unit) ψ (fun _ => (extractPM hd hr RA).toPOVM ())
        (fun _ => (extractPM hd hr RB).toPOVM ()) ≤ δ := by sorry
