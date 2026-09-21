/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryQuotientComponents
import MIPRE.Foundations.LowDegree.BinaryQuotientFactors
import MIPRE.Foundations.LowDegree.BinaryQuotientReduced
import MIPRE.Foundations.LowDegree.BinaryGCD

/-!
# Deterministic squarefree factorization over the binary field

Frobenius fixed-space separation computes primitive idempotents of the monic
quotient. The factor supported by an idempotent represented by `E` is
`gcd(f, E - 1)`. All executing operations are uniform ambient programs; the
finite-ring arguments justify correctness without enumerating the quotient.
-/

noncomputable section

namespace MIPRE.LowDegree.BinaryQuotient

open Cost Cost.PolyTimeFun Polynomial BinaryPolynomial

/-- XOR is binary polynomial addition on equal-width lists. -/
theorem polyOfBits_xorBits (a b : BitStr) (h : a.length = b.length) :
    polyOfBits (xorBits a b) = polyOfBits a + polyOfBits b := by
  simpa only [polyOfBits_eq_evalBits] using evalBits_xor (X : Polynomial (ZMod 2)) a b h

/-- Fixed-width one represents the constant polynomial one at every positive width. -/
theorem polyOfBits_oneBits (p : BitStr) (hp : p ≠ []) : polyOfBits (oneBits p) = 1 := by
  simpa only [polyOfBits_eq_evalBits] using evalBits_oneBits (X : Polynomial (ZMod 2)) p hp

/-- The factor list extracted from the computed primitive components. -/
def factorBits (p : BitStr) : List BitStr :=
  (quotientComponentsProg p).map (fun e => gcdBits (p ++ [true]) (xorBits e (oneBits p)))

private def componentFactorBitsProg : PolyTimeFun (BitStr × BitStr) BitStr :=
  gcdBitsProg.comp ((append.comp (snd.pair (const [true]))).pair
    (xorBitsProg.comp (fst.pair (oneBitsProg.comp snd))))

/-- A fixed deterministic polynomial-time squarefree binary factorization program.
Its input consists of the lower coefficients of the monic polynomial. -/
def factorBitsProg : PolyTimeFun BitStr (List BitStr) :=
  (mapWith componentFactorBitsProg).comp (quotientComponentsProg.pair (PolyTimeFun.id _))

@[simp] theorem factorBitsProg_apply (p : BitStr) : factorBitsProg p = factorBits p := rfl

variable (f : Polynomial (ZMod 2)) (hf : f.Monic)

/-- The extracted coefficient lists represent precisely the primitive-component factors. -/
theorem factorBitsProg_polynomials (p : BitStr) (hp : p.length = f.natDegree)
    (hpoly : f = polyOfBits (p ++ [true])) (hp0 : p ≠ []) :
    (factorBitsProg p).map polyOfBits =
      (components f hf).map (fun e => componentFactor f (polyOfBits (toBits f hf e))) := by
  change ((quotientComponentsProg p).map
    (fun e => gcdBits (p ++ [true]) (xorBits e (oneBits p)))).map polyOfBits = _
  rw [quotientComponentsProg_correct f hf p hp hpoly hp0, List.map_map, List.map_map]
  apply List.map_congr_left
  intro e _
  change polyOfBits (gcdBits (p ++ [true]) (xorBits (toBits f hf e) (oneBits p))) = _
  rw [polyOfBits_gcdBits, polyOfBits_xorBits _ _ (by simp [hp]), polyOfBits_oneBits p hp0]
  rw [← hpoly, componentFactor, CharTwo.sub_eq_add]

include hf in
/-- Every output of squarefree binary factorization is monic and irreducible. -/
theorem factorBitsProg_factors (p : BitStr) (hp : p.length = f.natDegree)
    (hpoly : f = polyOfBits (p ++ [true])) (hp0 : p ≠ []) (hs : Squarefree f) :
    ∀ a ∈ factorBitsProg p, (polyOfBits a).Monic ∧ Irreducible (polyOfBits a) := by
  have hdegree : f.degree ≠ 0 := by
    rw [degree_eq_natDegree hf.ne_zero]
    have hlen : 0 < p.length := List.length_pos_iff.mpr hp0
    exact_mod_cast (show f.natDegree ≠ 0 by omega)
  let : Nontrivial (AdjoinRoot f) := AdjoinRoot.nontrivial f hdegree
  let : Fintype (AdjoinRoot f) :=
    Fintype.ofEquiv (Fin f.natDegree → ZMod 2) (coordinateEquiv f hf).symm.toEquiv
  intro a ha
  have hm : polyOfBits a ∈ (factorBitsProg p).map polyOfBits := List.mem_map.mpr ⟨a, ha, rfl⟩
  rw [factorBitsProg_polynomials f hf p hp hpoly hp0] at hm
  obtain ⟨e, he, hE⟩ := List.mem_map.mp hm
  rw [← hE]
  refine ⟨componentFactor_monic f _ hf.ne_zero, ?_⟩
  apply componentFactor_irreducible f _ hf.ne_zero (square_bijective f hf hs)
  rw [mk_polyOfBits_toBits]
  exact components_primitive f hf e he

include hf in
/-- The output factors reconstruct the entire input polynomial. -/
theorem factorBitsProg_prod (p : BitStr) (hp : p.length = f.natDegree)
    (hpoly : f = polyOfBits (p ++ [true])) (hp0 : p ≠ []) (hs : Squarefree f) :
    ((factorBitsProg p).map polyOfBits).prod = f := by
  have hdegree : f.degree ≠ 0 := by
    rw [degree_eq_natDegree hf.ne_zero]
    have hlen : 0 < p.length := List.length_pos_iff.mpr hp0
    exact_mod_cast (show f.natDegree ≠ 0 by omega)
  let : Nontrivial (AdjoinRoot f) := AdjoinRoot.nontrivial f hdegree
  let : Fintype (AdjoinRoot f) :=
    Fintype.ofEquiv (Fin f.natDegree → ZMod 2) (coordinateEquiv f hf).symm.toEquiv
  rw [factorBitsProg_polynomials f hf p hp hpoly hp0]
  exact componentFactors_toBits_prod f hf (square_bijective f hf hs) (components f hf)
    (components_family f hf) (components_primitive f hf)

end MIPRE.LowDegree.BinaryQuotient

end
