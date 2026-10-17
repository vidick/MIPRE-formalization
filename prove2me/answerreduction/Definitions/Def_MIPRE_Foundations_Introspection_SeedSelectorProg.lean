/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/SeedSelectorProg.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Linarith
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
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Theorems.Thm_MIPRE_SAT_bitsVal_injective
import Theorems.Thm_MIPRE_SAT_bitsVal_lt

/-! # The executable seed enumeration for Pauli sampling

Field elements are numbered by their canonical little-endian bit strings.
For `m = 2^j` and a field of size `2^k`, the selector keeps the highest `j`
bits. This is the paper's equal-block selector for this explicit enumeration;
it does not identify the enumeration with `Fintype.equivFin`.
-/

noncomputable section
namespace MIPRE.Introspection.SeedProgram
open Cost Cost.PolyTimeFun SAT

def fieldIndex {k : ℕ} (E : BinField k) (a : E.carrier) : Fin (2 ^ k) :=
  ⟨bitsVal (E.toBits a), by simpa only [E.length_toBits] using SAT.bitsVal_lt (E.toBits a)⟩

theorem fieldIndex_injective {k : ℕ} (E : BinField k) : Function.Injective (fieldIndex E) := by
  intro a b h
  have he : E.toBits a = E.toBits b :=
    SAT.bitsVal_injective (by rw [E.length_toBits, E.length_toBits]) (congrArg Fin.val h)
  have hd := congrArg E.ofBits he
  simpa only [E.ofBits_toBits] using hd

/-- A genuine field enumeration, with forward direction given by canonical
binary rank. Only its inverse uses finite choice. -/
def fieldEnumeration {k : ℕ} (E : BinField k) : E.carrier ≃ Fin (2 ^ k) :=
  Equiv.ofBijective (fieldIndex E)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fieldIndex_injective E, by simp only [Fintype.card_fin, E.card_carrier]⟩)

def selector {k : ℕ} (E : BinField k) (j : ℕ) (hj : j ≤ k) (a : E.carrier) : Fin (2 ^ j) :=
  ⟨(fieldIndex E a).val / 2 ^ (k - j), Nat.div_lt_of_lt_mul (by
    rw [← pow_add, Nat.sub_add_cancel hj]
    exact (fieldIndex E a).isLt)⟩

def seedCoordinates {k : ℕ} (E : BinField k) (j : ℕ) (hj : j ≤ k) :
    E.carrier ≃ Fin (2 ^ j) × Fin (2 ^ (k - j)) :=
  ((fieldEnumeration E).trans (finCongr (by rw [← pow_add, Nat.add_sub_of_le hj]))).trans
    finProdFinEquiv.symm

/-- `k`, `j`, and the raw seed are supplied explicitly. The computation never
constructs a unary representation of the field size. -/
def selectorProg : PolyTimeFun (Unary × Unary × BitStr) ℕ :=
  bitsValue.comp (drop.comp ((snd.comp snd).pair
    (drop.comp (fst.pair (fst.comp snd)))))

end MIPRE.Introspection.SeedProgram
end
