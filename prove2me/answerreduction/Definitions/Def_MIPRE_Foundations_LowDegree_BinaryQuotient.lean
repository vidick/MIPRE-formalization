/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryQuotient.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.AdjoinRoot
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_eval2_polyOfBits

/-!
# Coordinates for arbitrary monic binary polynomial quotients

The basis and coefficient representation require only monicity. In particular,
the modulus need not be irreducible or squarefree. The abstract coordinate maps
are used in proofs; the executable addition and multiplication are the existing
uniform coefficient-list programs.
-/

noncomputable section

namespace MIPRE.LowDegree.BinaryQuotient

open Cost BinaryPolynomial

def coeffBit (z : ZMod 2) : Bool := decide (z = 1)

theorem ofBool_coeffBit (z : ZMod 2) : ofBool (coeffBit z) = z := by
  revert z
  decide

theorem coeffBit_ofBool (b : Bool) : coeffBit (ofBool b) = b := by
  cases b <;> decide

variable (f : Polynomial (ZMod 2)) (hf : f.Monic)

/-- The monic quotient's specified power-basis coordinate equivalence. -/
def coordinateEquiv : AdjoinRoot f ≃ₗ[ZMod 2] (Fin f.natDegree → ZMod 2) :=
  (AdjoinRoot.powerBasisAux' hf).equivFun

/-- Canonical bits of a quotient element in the monic power basis. -/
def toBits (x : AdjoinRoot f) : BitStr :=
  List.ofFn fun i => coeffBit ((AdjoinRoot.powerBasisAux' hf).repr x i)

/-- Decode the first `natDegree f` coefficients; omitted coefficients are zero. -/
def ofBits (l : BitStr) : AdjoinRoot f :=
  ∑ i : Fin f.natDegree,
    (ofBool (l.getD i false) : ZMod 2) • (AdjoinRoot.powerBasisAux' hf) i

/-- The canonical encoding has precisely the quotient dimension. -/
@[simp] theorem length_toBits (x : AdjoinRoot f) :
    (toBits f hf x).length = f.natDegree := List.length_ofFn

/-- Decoding a quotient element's canonical bits recovers the element. -/
@[simp] theorem ofBits_toBits (x : AdjoinRoot f) :
    ofBits f hf (toBits f hf x) = x := by
  let b := AdjoinRoot.powerBasisAux' hf
  refine (Finset.sum_congr rfl fun i _ => ?_).trans (b.sum_repr x)
  congr 1
  rw [show (toBits f hf x).getD (i : ℕ) false = coeffBit (b.repr x i) from by
    simp [toBits, b], ofBool_coeffBit]

/-- Correct-width decoding equals evaluation at the quotient's canonical root. -/
theorem ofBits_eq_evalBits (l : BitStr) (hlen : l.length = f.natDegree) :
    ofBits f hf l = evalBits (AdjoinRoot.root f) l := by
  change (∑ i : Fin f.natDegree,
    (ofBool (l.getD i false) : ZMod 2) • (AdjoinRoot.powerBasisAux' hf) i) = _
  have hb (i : Fin f.natDegree) : (AdjoinRoot.powerBasisAux' hf) i =
      AdjoinRoot.root f ^ (i : ℕ) :=
    (AdjoinRoot.powerBasis' hf).basis_eq_pow i
  simp_rw [hb, Algebra.smul_def]
  rw [← eval2_polyOfBits (algebraMap (ZMod 2) (AdjoinRoot f))]
  simp only [polyOfBits, Polynomial.eval₂_finsetSum, Polynomial.eval₂_monomial]
  rw [hlen, ← Fin.sum_univ_eq_sum_range]
  rfl

/-- Canonical coefficient bits evaluate to the quotient element they encode. -/
@[simp] theorem evalBits_toBits (x : AdjoinRoot f) :
    evalBits (AdjoinRoot.root f) (toBits f hf x) = x := by
  rw [← ofBits_eq_evalBits f hf _ (length_toBits f hf x), ofBits_toBits]

end MIPRE.LowDegree.BinaryQuotient

end
