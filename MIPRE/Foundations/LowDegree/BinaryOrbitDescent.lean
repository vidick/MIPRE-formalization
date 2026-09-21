/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryOrbitPolynomial

/-! # Descending a closed orbit product to binary coefficient bits -/

noncomputable section

namespace MIPRE.LowDegree.BinaryQuotient

open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial

variable {R : Type*} [CommRing R]

/-- Coefficients of the interpreted nested list are the decoded list entries. -/
theorem coeff_coeffPolynomial (z : R) (cs : List BitStr) (i : ℕ) :
    (coeffPolynomial z cs).coeff i = evalBits z (cs.getD i []) := by
  induction cs generalizing i with
  | nil => simp
  | cons c cs ih =>
    cases i with
    | zero => simp
    | succ i => simp [coeff_X_mul, ih]

/-- Select the constant coordinate of each quotient coefficient. -/
def descendBits (cs : List BitStr) : BitStr := cs.map (fun c => c.headD false)

/-- Coefficient descent has a fixed linear-time list program. -/
def descendBitsProg : PolyTimeFun (List BitStr) BitStr := map (headD false)

@[simp] theorem descendBitsProg_apply (cs : List BitStr) :
    descendBitsProg cs = descendBits cs := rfl

/-- If every coefficient is its constant coordinate, descent recovers the same polynomial. -/
theorem map_polyOfBits_descendBits [Algebra (ZMod 2) R] (z : R) (cs : List BitStr)
    (hc : ∀ c ∈ cs, evalBits z c = ofBool (c.headD false)) :
    (polyOfBits (descendBits cs)).map (algebraMap (ZMod 2) R) = coeffPolynomial z cs := by
  induction cs with
  | nil => simp [descendBits, polyOfBits]
  | cons c cs ih =>
    have h := hc c (by simp)
    have ht := ih (fun d hd => hc d (by simp [hd]))
    change (polyOfBits (c.headD false :: descendBits cs)).map _ = _
    rw [polyOfBits_cons, Polynomial.map_add, Polynomial.map_C, Polynomial.map_mul,
      Polynomial.map_X, ht, coeffPolynomial_cons, h]
    cases c.headD false <;> simp [ofBool]

variable (f : Polynomial (ZMod 2)) (hf : f.Monic)

include hf in
/-- In faithful fixed-width quotient coordinates, a zero or one has only its constant bit. -/
theorem evalBits_eq_head_of_zero_or_one (p c : BitStr)
    (hp : p.length = f.natDegree) (hc : c.length = f.natDegree) (hp0 : p ≠ [])
    (h : evalBits (AdjoinRoot.root f) c = 0 ∨ evalBits (AdjoinRoot.root f) c = 1) :
    evalBits (AdjoinRoot.root f) c = ofBool (c.headD false) := by
  rcases h with h | h
  · have he : c = zeroBits p := (evalBits_eq_iff f hf c (zeroBits p) hc
        ((length_zeroBits p).trans hp)).mp (by simpa using h)
    rw [he, evalBits_zeroBits]
    cases p <;> rfl
  · have he : c = oneBits p := (evalBits_eq_iff f hf c (oneBits p) hc
        ((length_oneBits p).trans hp)).mp (by rw [evalBits_oneBits _ p hp0]; exact h)
    rw [he, evalBits_oneBits _ p hp0]
    cases p with
    | nil => exact (hp0 rfl).elim
    | cons b bs => rfl

/-- Print binary coefficients of the supplied Frobenius orbit. -/
def orbitPolynomialBits (u : Unary) (p a : BitStr) : BitStr :=
  descendBits (orbitProductBits u p a)

/-- A uniform polynomial-time program for a binary orbit polynomial. -/
def orbitPolynomialBitsProg : PolyTimeFun (Unary × BitStr × BitStr) BitStr :=
  descendBitsProg.comp orbitProductBitsProg

@[simp] theorem orbitPolynomialBitsProg_apply (u : Unary) (p a : BitStr) :
    orbitPolynomialBitsProg (u, p, a) = orbitPolynomialBits u p a := by
  change descendBits (orbitProductBitsProg (u, p, a)) = _
  rw [orbitProductBitsProg_apply]
  rfl

include hf in
/-- Closing an orbit in an irreducible quotient justifies executable coefficient descent. -/
theorem map_orbitPolynomialBits [Fact (Irreducible f)] (u : Unary) (p a : BitStr)
    (hp : p.length = f.natDegree) (hpoly : f = polyOfBits (p ++ [true]))
    (hp0 : p ≠ []) (ha : a.length = p.length)
    (hclosed : evalBits (AdjoinRoot.root f) a ^ (2 ^ u.length) =
      evalBits (AdjoinRoot.root f) a) :
    (polyOfBits (orbitPolynomialBits u p a)).map (algebraMap (ZMod 2) (AdjoinRoot f)) =
      orbitPolynomial (evalBits (AdjoinRoot.root f) a) u.length := by
  let : CharP (AdjoinRoot f) 2 := charP_of_injective_ringHom (AdjoinRoot.of f).injective 2
  have hprod : coeffPolynomial (AdjoinRoot.root f) (orbitProductBits u p a) =
      orbitPolynomial (evalBits (AdjoinRoot.root f) a) u.length :=
    coeffPolynomial_orbitProductBits _ u p a hp0 (root_eq f p hpoly) ha
  rw [orbitPolynomialBits, map_polyOfBits_descendBits _ _ ?_, hprod]
  intro c hc
  apply evalBits_eq_head_of_zero_or_one f hf p c hp
    ((orbitProductBits_width u p a ha c hc).trans hp) hp0
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hc
  have hcoeff : (coeffPolynomial (AdjoinRoot.root f) (orbitProductBits u p a)).coeff i =
      evalBits (AdjoinRoot.root f) c := by
    simp only [coeff_coeffPolynomial, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, he]
  rw [← hcoeff, hprod]
  exact orbitPolynomial_coeff_zero_or_one _ _ hclosed i

include hf in
/-- The descended orbit product is monic and has the requested orbit degree. -/
theorem orbitPolynomialBits_monic_natDegree [Fact (Irreducible f)]
    (u : Unary) (p a : BitStr) (hp : p.length = f.natDegree)
    (hpoly : f = polyOfBits (p ++ [true])) (hp0 : p ≠ []) (ha : a.length = p.length)
    (hclosed : evalBits (AdjoinRoot.root f) a ^ (2 ^ u.length) =
      evalBits (AdjoinRoot.root f) a) :
    (polyOfBits (orbitPolynomialBits u p a)).Monic ∧
      (polyOfBits (orbitPolynomialBits u p a)).natDegree = u.length := by
  have h := map_orbitPolynomialBits f hf u p a hp hpoly hp0 ha hclosed
  constructor
  · have hm := orbitPolynomial_monic (evalBits (AdjoinRoot.root f) a) u.length
    rw [← h] at hm
    exact Polynomial.monic_map_iff.mp hm
  · rw [← natDegree_map_eq_of_injective (algebraMap (ZMod 2) (AdjoinRoot f)).injective, h,
      natDegree_orbitPolynomial]


include hf in
/-- When the orbit length is the element's exact degree, the program prints its minimal polynomial. -/
theorem orbitPolynomialBits_eq_minpoly [Fact (Irreducible f)]
    (u : Unary) (p a : BitStr) (hp : p.length = f.natDegree)
    (hpoly : f = polyOfBits (p ++ [true])) (hp0 : p ≠ []) (ha : a.length = p.length)
    (hclosed : evalBits (AdjoinRoot.root f) a ^ (2 ^ u.length) =
      evalBits (AdjoinRoot.root f) a) (hu : 0 < u.length)
    (hdegree : (minpoly (ZMod 2) (evalBits (AdjoinRoot.root f) a)).natDegree = u.length) :
    polyOfBits (orbitPolynomialBits u p a) = minpoly (ZMod 2) (evalBits (AdjoinRoot.root f) a) := by
  let : CharP (AdjoinRoot f) 2 := charP_of_injective_ringHom (AdjoinRoot.of f).injective 2
  have hm := map_orbitPolynomialBits f hf u p a hp hpoly hp0 ha hclosed
  have hz : aeval (evalBits (AdjoinRoot.root f) a) (polyOfBits (orbitPolynomialBits u p a)) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, hm]
    exact eval_orbitPolynomial _ _ hu
  have hc := orbitPolynomialBits_monic_natDegree f hf u p a hp hpoly hp0 ha hclosed
  have hi : IsIntegral (ZMod 2) (evalBits (AdjoinRoot.root f) a) :=
    ⟨_, hc.1, hz⟩
  exact eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hi) hc.1 (minpoly.dvd _ _ hz)
    (by rw [hc.2, hdegree])

include hf in
/-- The exact-degree orbit constructor produces an irreducible binary polynomial. -/
theorem orbitPolynomialBits_irreducible [Fact (Irreducible f)]
    (u : Unary) (p a : BitStr) (hp : p.length = f.natDegree)
    (hpoly : f = polyOfBits (p ++ [true])) (hp0 : p ≠ []) (ha : a.length = p.length)
    (hclosed : evalBits (AdjoinRoot.root f) a ^ (2 ^ u.length) =
      evalBits (AdjoinRoot.root f) a) (hu : 0 < u.length)
    (hdegree : (minpoly (ZMod 2) (evalBits (AdjoinRoot.root f) a)).natDegree = u.length) :
    Irreducible (polyOfBits (orbitPolynomialBits u p a)) := by
  rw [orbitPolynomialBits_eq_minpoly f hf u p a hp hpoly hp0 ha hclosed hu hdegree]
  let : Module.Finite (ZMod 2) (AdjoinRoot f) := hf.finite_adjoinRoot
  apply minpoly.irreducible
  exact IsIntegral.of_finite (ZMod 2) _

end MIPRE.LowDegree.BinaryQuotient

end
