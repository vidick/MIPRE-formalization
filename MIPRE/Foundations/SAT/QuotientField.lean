/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.SAT.Pcp
import MIPRE.Foundations.LowDegree.BinaryPolynomial
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.CharP.Algebra
import Mathlib.RingTheory.AdjoinRoot

/-!
# Binary fields represented in the polynomial power basis

Unlike an arbitrary basis of a Galois field, the power basis of `F₂[X]/(f)`
connects directly to the uniform coefficient-list programs. This is the field
representation needed for the classical PCP's arithmetic. A self-dual normal
representation and its change-of-basis algorithm remain separate constructions.
-/

noncomputable section

namespace MIPRE.SAT

open Finset LowDegree LowDegree.BinaryPolynomial Cost

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private def bitOfCoeff (z : ZMod 2) : Bool := decide (z = 1)

private theorem ofBool_bitOfCoeff (z : ZMod 2) : ofBool (bitOfCoeff z) = z := by
  revert z
  decide

private theorem bitOfCoeff_ofBool (b : Bool) : bitOfCoeff (ofBool b) = b := by
  cases b <;> decide

section Quotient

variable (f : Polynomial (ZMod 2)) (hf : f.Monic) [Fact (Irreducible f)]

local instance : CharP (AdjoinRoot f) 2 :=
  charP_of_injective_ringHom (AdjoinRoot.of f).injective 2

/-- A binary field with coefficient bits in the power basis of a monic irreducible
polynomial. The basis is specified, rather than chosen by abstract finite-field existence. -/
def quotientBinField : BinField f.natDegree :=
  let b : Module.Basis (Fin f.natDegree) (ZMod 2) (AdjoinRoot f) :=
    AdjoinRoot.powerBasisAux' hf
  letI : Fintype (AdjoinRoot f) :=
    Fintype.ofEquiv (Fin f.natDegree → ZMod 2) b.equivFun.symm.toEquiv
  { carrier := AdjoinRoot f
    instField := inferInstance
    instFintype := inferInstance
    instDecidableEq := inferInstance
    card_carrier := by
      rw [Fintype.card_congr b.equivFun.toEquiv]
      simp
    toBits := fun x => List.ofFn fun i => bitOfCoeff (b.repr x i)
    ofBits := fun l => ∑ i : Fin f.natDegree, (ofBool (l.getD i false) : ZMod 2) • b i
    length_toBits := fun _ => List.length_ofFn
    ofBits_toBits := fun x => by
      refine (Finset.sum_congr rfl fun i _ => ?_).trans (b.sum_repr x)
      congr 1
      rw [show (List.ofFn fun i => bitOfCoeff (b.repr x i)).getD (i : ℕ) false =
          bitOfCoeff (b.repr x i) from by simp, ofBool_bitOfCoeff] }

/-- Every correctly sized bit string is the canonical representation of its
decoded field element. In particular, raw equality tests are faithful. -/
theorem quotientBinField_toBits_ofBits (l : BitStr) (hlen : l.length = f.natDegree) :
    (quotientBinField f hf).toBits ((quotientBinField f hf).ofBits l) = l := by
  let b := AdjoinRoot.powerBasisAux' hf
  change (List.ofFn fun i : Fin f.natDegree =>
    bitOfCoeff (b.repr (∑ j : Fin f.natDegree, (ofBool (l.getD j false) : ZMod 2) • b j) i)) = l
  have hc (i : Fin f.natDegree) :
      b.repr (∑ j : Fin f.natDegree, (ofBool (l.getD j false) : ZMod 2) • b j) i =
        ofBool (l.getD i false) := by
    simp [Finsupp.single_apply]
  simp only [hc, bitOfCoeff_ofBool]
  apply List.ext_getElem
  · simp [hlen]
  · intro i hi hj
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

/-- Correct-width coefficient decoding is evaluation at the quotient's root. -/
theorem quotientBinField_ofBits (l : BitStr) (hlen : l.length = f.natDegree) :
    (quotientBinField f hf).ofBits l = evalBits (AdjoinRoot.root f) l := by
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

include hf in
/-- Equality of correctly sized coefficient vectors is equivalent to equality
of their evaluations at the irreducible quotient's root. -/
theorem quotient_evalBits_eq_iff (a b : BitStr)
    (ha : a.length = f.natDegree) (hb : b.length = f.natDegree) :
    evalBits (AdjoinRoot.root f) a = evalBits (AdjoinRoot.root f) b ↔ a = b := by
  rw [← quotientBinField_ofBits f hf a ha, ← quotientBinField_ofBits f hf b hb]
  constructor
  · intro h
    have he := congrArg (quotientBinField f hf).toBits h
    simpa only [quotientBinField_toBits_ofBits f hf a ha,
      quotientBinField_toBits_ofBits f hf b hb] using he
  · intro h
    rw [h]

/-- A coefficient vector defining the lower part of the modulus satisfies the
root equation consumed by the arithmetic programs. -/
theorem quotient_root_eq (p : BitStr) (hpoly : f = polyOfBits (p ++ [true])) :
    AdjoinRoot.root f ^ p.length = evalBits (AdjoinRoot.root f) p := by
  have h : (polyOfBits (p ++ [true])).eval₂ (AdjoinRoot.of f) (AdjoinRoot.root f) = 0 := by
    rw [← hpoly]
    exact AdjoinRoot.eval₂_root f
  rw [eval₂_polyOfBits, evalBits_append] at h
  simp only [evalBits_cons, evalBits_nil, ofBool, if_true, mul_zero, add_zero, mul_one] at h
  exact (CharTwo.add_eq_zero.mp h).symm

/-- The uniform XOR program implements field addition on correctly sized inputs. -/
theorem quotientBinField_add (a b : BitStr)
    (ha : a.length = f.natDegree) (hb : b.length = f.natDegree) :
    (quotientBinField f hf).ofBits (xorBitsProg (a, b)) =
      (quotientBinField f hf).ofBits a + (quotientBinField f hf).ofBits b := by
  rw [xorBitsProg_apply, quotientBinField_ofBits f hf _ (by simp [ha, hb]),
    quotientBinField_ofBits f hf a ha, quotientBinField_ofBits f hf b hb]
  exact evalBits_xor (R := AdjoinRoot f) (AdjoinRoot.root f) a b (ha.trans hb.symm)

/-- The uniform modular-multiplication program implements field multiplication. -/
theorem quotientBinField_mul (p a b : BitStr)
    (hp : p.length = f.natDegree) (hpoly : f = polyOfBits (p ++ [true]))
    (ha : a.length = f.natDegree) (hb : b.length = f.natDegree) :
    (quotientBinField f hf).ofBits (mulReduceProg (p, a, b)) =
      (quotientBinField f hf).ofBits a * (quotientBinField f hf).ofBits b := by
  rw [mulReduceProg_apply, quotientBinField_ofBits f hf _
      ((length_mulReduce p a b (ha.trans hp.symm)).trans hp),
    quotientBinField_ofBits f hf a ha, quotientBinField_ofBits f hf b hb]
  exact evalBits_mulReduce (R := AdjoinRoot f) _ p a b (ha.trans hp.symm)
    (quotient_root_eq f p hpoly)

end Quotient

/-- Shoup's concrete quotient model, before transporting the degree equality. -/
def shoupFieldModel (k : ℕ) (hk : 1 ≤ k) :
    BinField (polyOfBits (shoupIrreducible (unary k))).natDegree :=
  letI : Fact (Irreducible (polyOfBits (shoupIrreducible (unary k)))) :=
    ⟨shoupIrreducible_irreducible k hk⟩
  quotientBinField _ (shoupIrreducible_monic k hk)

/-- A field of size `2^k` in the polynomial basis supplied by Shoup's algorithm. -/
def shoupBinField (k : ℕ) (hk : 1 ≤ k) : BinField k :=
  let E := shoupFieldModel k hk
  { carrier := E.carrier
    instField := E.instField
    instFintype := E.instFintype
    instDecidableEq := E.instDecidableEq
    card_carrier := by rw [E.card_carrier, shoupIrreducible_natDegree k hk]
    toBits := E.toBits
    ofBits := E.ofBits
    length_toBits := fun a => (E.length_toBits a).trans (shoupIrreducible_natDegree k hk)
    ofBits_toBits := E.ofBits_toBits }

/-- The degree metadata does not change the quotient carrier or its arithmetic. -/
instance shoupBinField_charP (k : ℕ) (hk : 1 ≤ k) : CharP (shoupBinField k hk).carrier 2 := by
  letI : Fact (Irreducible (polyOfBits (shoupIrreducible (unary k)))) :=
    ⟨shoupIrreducible_irreducible k hk⟩
  exact charP_of_injective_ringHom
    (AdjoinRoot.of (polyOfBits (shoupIrreducible (unary k)))).injective 2

/-- Canonical decoding is unchanged by the explicit degree bookkeeping. -/
theorem shoupBinField_toBits_ofBits (k : ℕ) (hk : 1 ≤ k) (l : BitStr) (hl : l.length = k) :
    (shoupBinField k hk).toBits ((shoupBinField k hk).ofBits l) = l := by
  letI : Fact (Irreducible (polyOfBits (shoupIrreducible (unary k)))) :=
    ⟨shoupIrreducible_irreducible k hk⟩
  exact quotientBinField_toBits_ofBits _ (shoupIrreducible_monic k hk) l
    (hl.trans (shoupIrreducible_natDegree k hk).symm)

/-- The admissible field family with exactly the domain required by `PcpDecider.fld`. -/
def shoupAdmissibleField (k : ℕ) (hk : Odd k) : BinField k :=
  shoupBinField k (by obtain ⟨r, hr⟩ := hk; omega)

/-- The distinguished root in the explicit Shoup field carrier. -/
def shoupRoot (k : ℕ) (hk : 1 ≤ k) : (shoupBinField k hk).carrier :=
  AdjoinRoot.root (polyOfBits (shoupIrreducible (unary k)))

theorem shoupRoot_equation (k : ℕ) (hk : 1 ≤ k) :
    shoupRoot k hk ^ (shoupLowerCoeffs (unary k)).length =
      evalBits (shoupRoot k hk) (shoupLowerCoeffs (unary k)) := by
  let : Fact (Irreducible (polyOfBits (shoupIrreducible (unary k)))) :=
    ⟨shoupIrreducible_irreducible k hk⟩
  exact quotient_root_eq _ _ (shoupLowerCoeffs_poly k hk).symm

/-- A canonical Shoup coefficient vector evaluates to its original field element. -/
theorem shoupRoot_eval_toBits (k : ℕ) (hk : 1 ≤ k) (a : (shoupBinField k hk).carrier) :
    evalBits (shoupRoot k hk) ((shoupBinField k hk).toBits a) = a := by
  let : Fact (Irreducible (polyOfBits (shoupIrreducible (unary k)))) :=
    ⟨shoupIrreducible_irreducible k hk⟩
  have h := quotientBinField_ofBits _ (shoupIrreducible_monic k hk)
    ((shoupBinField k hk).toBits a)
    (((shoupBinField k hk).length_toBits a).trans (shoupIrreducible_natDegree k hk).symm)
  exact h.symm.trans ((shoupBinField k hk).ofBits_toBits a)

/-- Equality at the Shoup root is faithful on the verifier's fixed-width vectors. -/
theorem shoupRoot_eval_eq_iff (k : ℕ) (hk : 1 ≤ k) (a b : BitStr)
    (ha : a.length = k) (hb : b.length = k) :
    evalBits (shoupRoot k hk) a = evalBits (shoupRoot k hk) b ↔ a = b := by
  let : Fact (Irreducible (polyOfBits (shoupIrreducible (unary k)))) :=
    ⟨shoupIrreducible_irreducible k hk⟩
  exact quotient_evalBits_eq_iff _ (shoupIrreducible_monic k hk) a b
    (ha.trans (shoupIrreducible_natDegree k hk).symm)
    (hb.trans (shoupIrreducible_natDegree k hk).symm)

/-- Compute the modulus from unary `k`, then multiply the two coefficient vectors.
This is one uniform ambient program, with a polynomial bound in its input size. -/
def shoupMulProg : PolyTimeFun (Unary × BitStr × BitStr) BitStr :=
  mulReduceProg.comp ((shoupLowerCoeffs.comp PolyTimeFun.fst).pair PolyTimeFun.snd)

/-- The uniform multiplication program runs in time polynomial in `k` on `k`-bit
operands, including construction of the modulus. -/
theorem shoupMulProg_time_le : ∃ R : Polynomial ℕ, ∀ k : ℕ, ∀ a b : BitStr,
    a.length = k → b.length = k →
      ∃ t ≤ R.eval k,
        shoupMulProg.code.Runs (encode (unary k, a, b))
          (encode (shoupMulProg (unary k, a, b))) t := by
  refine ⟨shoupMulProg.timeBound.comp (10 * Polynomial.X + 5), fun k a b ha hb => ?_⟩
  obtain ⟨t, ht, hr⟩ := shoupMulProg.computes (unary k, a, b)
  refine ⟨t, ht.trans ?_, hr⟩
  have hsize : esize (unary k, a, b) ≤ 10 * k + 5 := by
    have h₁ := esize_bitStr_le a
    have h₂ := esize_bitStr_le b
    simp only [esize_prod, esize_unary]
    rw [ha] at h₁
    rw [hb] at h₂
    omega
  simpa using polynomial_eval_mono shoupMulProg.timeBound hsize

/-- Correctness of the uniform field multiplication program on `k`-bit operands. -/
theorem shoupMulProg_correct (k : ℕ) (hk : 1 ≤ k) (a b : BitStr)
    (ha : a.length = k) (hb : b.length = k) :
    (shoupFieldModel k hk).ofBits (shoupMulProg (unary k, a, b)) =
      (shoupFieldModel k hk).ofBits a * (shoupFieldModel k hk).ofBits b := by
  let : Fact (Irreducible (polyOfBits (shoupIrreducible (unary k)))) :=
    ⟨shoupIrreducible_irreducible k hk⟩
  exact quotientBinField_mul _ (shoupIrreducible_monic k hk) (shoupLowerCoeffs (unary k)) a b
    ((shoupLowerCoeffs_length k hk).trans (shoupIrreducible_natDegree k hk).symm)
    (shoupLowerCoeffs_poly k hk).symm (ha.trans (shoupIrreducible_natDegree k hk).symm)
    (hb.trans (shoupIrreducible_natDegree k hk).symm)

end MIPRE.SAT

end
