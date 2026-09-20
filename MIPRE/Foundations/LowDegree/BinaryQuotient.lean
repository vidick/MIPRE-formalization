/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryPolynomial
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.CharP.Algebra
import Mathlib.RingTheory.AdjoinRoot

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

private def coeffBit (z : ZMod 2) : Bool := decide (z = 1)

private theorem ofBool_coeffBit (z : ZMod 2) : ofBool (coeffBit z) = z := by
  revert z
  decide

private theorem coeffBit_ofBool (b : Bool) : coeffBit (ofBool b) = b := by
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

/-- Every correctly sized list is already the canonical quotient encoding. -/
theorem toBits_ofBits (l : BitStr) (hlen : l.length = f.natDegree) :
    toBits f hf (ofBits f hf l) = l := by
  let b := AdjoinRoot.powerBasisAux' hf
  change (List.ofFn fun i : Fin f.natDegree =>
    coeffBit (b.repr (∑ j : Fin f.natDegree, (ofBool (l.getD j false) : ZMod 2) • b j) i)) = l
  have hc (i : Fin f.natDegree) :
      b.repr (∑ j : Fin f.natDegree, (ofBool (l.getD j false) : ZMod 2) • b j) i =
        ofBool (l.getD i false) := by
    simp [Finsupp.single_apply]
  simp only [hc, coeffBit_ofBool]
  apply List.ext_getElem
  · simp [hlen]
  · intro i hi hj
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

/-- Correct-width decoding equals evaluation at the quotient's canonical root. -/
theorem ofBits_eq_evalBits (l : BitStr) (hlen : l.length = f.natDegree) :
    ofBits f hf l = evalBits (AdjoinRoot.root f) l := by
  change (∑ i : Fin f.natDegree,
    (ofBool (l.getD i false) : ZMod 2) • (AdjoinRoot.powerBasisAux' hf) i) = _
  have hb (i : Fin f.natDegree) : (AdjoinRoot.powerBasisAux' hf) i =
      AdjoinRoot.root f ^ (i : ℕ) :=
    (AdjoinRoot.powerBasis' hf).basis_eq_pow i
  simp_rw [hb, Algebra.smul_def]
  rw [← eval₂_polyOfBits (algebraMap (ZMod 2) (AdjoinRoot f))]
  simp only [polyOfBits, Polynomial.eval₂_finsetSum, Polynomial.eval₂_monomial]
  rw [hlen, ← Fin.sum_univ_eq_sum_range]
  rfl

/-- Canonical coefficient bits evaluate to the quotient element they encode. -/
@[simp] theorem evalBits_toBits (x : AdjoinRoot f) :
    evalBits (AdjoinRoot.root f) (toBits f hf x) = x := by
  rw [← ofBits_eq_evalBits f hf _ (length_toBits f hf x), ofBits_toBits]

include hf in
/-- Equality in any monic quotient is faithful on fixed-width coefficient lists. -/
theorem evalBits_eq_iff (a b : BitStr)
    (ha : a.length = f.natDegree) (hb : b.length = f.natDegree) :
    evalBits (AdjoinRoot.root f) a = evalBits (AdjoinRoot.root f) b ↔ a = b := by
  rw [← ofBits_eq_evalBits f hf a ha, ← ofBits_eq_evalBits f hf b hb]
  constructor
  · intro h
    have he := congrArg (toBits f hf) h
    simpa only [toBits_ofBits f hf a ha, toBits_ofBits f hf b hb] using he
  · rintro rfl
    rfl

/-- The quotient root satisfies the lower-coefficient reduction equation. -/
theorem root_eq (p : BitStr) (hpoly : f = polyOfBits (p ++ [true])) :
    AdjoinRoot.root f ^ p.length = evalBits (AdjoinRoot.root f) p := by
  nontriviality (AdjoinRoot f)
  let : CharP (AdjoinRoot f) 2 :=
    charP_of_injective_ringHom (AdjoinRoot.of f).injective 2
  have h : (polyOfBits (p ++ [true])).eval₂ (AdjoinRoot.of f) (AdjoinRoot.root f) = 0 := by
    rw [← hpoly]
    exact AdjoinRoot.eval₂_root f
  rw [eval₂_polyOfBits, evalBits_append] at h
  simp only [evalBits_cons, evalBits_nil, ofBool, if_true, mul_zero, add_zero, mul_one] at h
  exact (CharTwo.add_eq_zero.mp h).symm

/-- The fixed XOR program implements addition for any monic quotient. -/
theorem ofBits_xor (a b : BitStr)
    (ha : a.length = f.natDegree) (hb : b.length = f.natDegree) :
    ofBits f hf (xorBitsProg (a, b)) = ofBits f hf a + ofBits f hf b := by
  nontriviality (AdjoinRoot f)
  let : CharP (AdjoinRoot f) 2 :=
    charP_of_injective_ringHom (AdjoinRoot.of f).injective 2
  rw [xorBitsProg_apply, ofBits_eq_evalBits f hf _ (by simp [ha, hb]),
    ofBits_eq_evalBits f hf a ha, ofBits_eq_evalBits f hf b hb]
  exact evalBits_xor (AdjoinRoot.root f) a b (ha.trans hb.symm)

/-- Uniform modular multiplication works before irreducibility is known. -/
theorem ofBits_mulReduce (p a b : BitStr)
    (hp : p.length = f.natDegree) (hpoly : f = polyOfBits (p ++ [true]))
    (ha : a.length = f.natDegree) (hb : b.length = f.natDegree) :
    ofBits f hf (mulReduceProg (p, a, b)) = ofBits f hf a * ofBits f hf b := by
  nontriviality (AdjoinRoot f)
  let : CharP (AdjoinRoot f) 2 :=
    charP_of_injective_ringHom (AdjoinRoot.of f).injective 2
  rw [mulReduceProg_apply, ofBits_eq_evalBits f hf _
      ((length_mulReduce p a b (ha.trans hp.symm)).trans hp),
    ofBits_eq_evalBits f hf a ha, ofBits_eq_evalBits f hf b hb]
  exact evalBits_mulReduce _ p a b (ha.trans hp.symm) (root_eq f p hpoly)

end MIPRE.LowDegree.BinaryQuotient

end
