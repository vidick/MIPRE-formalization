/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/PcpBlocks.lean (statement stub of MIPRE.SAT.PcpAlgebra.exists_proof_of_satisfying_assignment);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
import Definitions.Def_MIPRE_Foundations_SAT_Decoupled
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_SAT_Pcp
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_ZeroBasis
import Definitions.Def_MIPRE_Foundations_SAT_PcpAlgebra
import Definitions.Def_MIPRE_Foundations_SAT_PcpBlocks

open MIPRE
open MIPRE.SAT
open MIPRE.SAT.PcpAlgebra
open Finset MvPolynomial MIPRE.LowDegree
variable {P : PcpParams} {F : Type*} [Field F]

theorem MIPRE.SAT.PcpAlgebra.exists_proof_of_satisfying_assignment
    (φ : MvPolynomial (Fin P.m') F) (hφdeg : ∀ j, φ.degreeOf j ≤ 6)
    (hφbool : ∀ y : Fin P.m' → Bool, eval (pt y) φ = 0 ∨ eval (pt y) φ = 1)
    (a : Fin 5 → (Fin P.m → Bool) → Bool)
    (hsat : ∀ y : Fin P.m' → Bool, eval (pt y) φ = 1 →
      ∃ i : Fin 5, a i (P.block i y) = y (P.signIndex i)) :
    ∃ pf : PcpProof P F,
      (∀ i, pf.g i = ldEnc (fun x => ofBool (a i x))) ∧
      ∀ z, TypedAccepts φ z (pf.ev z) := by sorry
