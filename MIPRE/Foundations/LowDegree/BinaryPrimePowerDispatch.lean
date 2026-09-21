/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryOddPrimeConstructor
import MIPRE.Foundations.LowDegree.BinaryArtinSchreierLoop
import MIPRE.Foundations.LowDegree.BinaryDegreeDecomposition

/-! # Uniform dispatch and prime-power polynomial decomposition -/

noncomputable section

namespace MIPRE.LowDegree.BinaryPolynomial

open Cost Cost.PolyTimeFun Polynomial DegreeArithmetic

/-- Degree one has the fixed irreducible polynomial `X`. -/
theorem polyOfBits_X : polyOfBits [false, true] = (X : (ZMod 2)[X]) := by
  simp only [polyOfBits_cons, show polyOfBits [] = 0 from rfl, ofBool,
    Bool.false_eq_true, ↓reduceIte, C_0, C_1, mul_zero, add_zero, mul_one, zero_add]

/-- Dispatch degree one, powers of two, and odd-prime powers by raw unary inputs. -/
def primePowerBits (q r : Unary) : BitStr :=
  if r.length = 1 then [false, true]
  else if q.length = 2 then BinaryArtinSchreier.powerTwoBits r
  else oddPrimePowerBits q r

/-- The dispatch is one fixed total polynomial-time program. -/
def primePowerBitsProg : PolyTimeFun (Unary × Unary) BitStr :=
  congr (ite (eqUnaryProg.comp (snd.pair (const (unary 1)))) (const [false, true])
    (ite (eqUnaryProg.comp (fst.pair (const (unary 2))))
      (BinaryArtinSchreier.powerTwoBitsProg.comp snd) oddPrimePowerBitsProg))
    (fun s => primePowerBits s.1 s.2) (by
      rintro ⟨q, r⟩
      change (if decide (r.length = (unary 1).length) then [false, true]
        else if decide (q.length = (unary 2).length) then BinaryArtinSchreier.powerTwoBitsProg r
        else oddPrimePowerBitsProg (q, r)) = _
      simp only [length_unary, decide_eq_true_eq,
        BinaryArtinSchreier.powerTwoBitsProg_apply, oddPrimePowerBitsProg_apply, primePowerBits])

@[simp] theorem primePowerBitsProg_apply (q r : Unary) :
    primePowerBitsProg (q, r) = primePowerBits q r := rfl

/-- Every prime-power contribution is printed as a canonical monic irreducible polynomial. -/
theorem primePowerBits_correct (q e : ℕ) (he : e = 0 ∨ q.Prime) :
    let a := primePowerBits (unary q) (unary (q ^ e))
    a.getLastD false = true ∧ (polyOfBits a).Monic ∧ Irreducible (polyOfBits a) ∧
      (polyOfBits a).natDegree = q ^ e := by
  cases e with
  | zero =>
    simp only [primePowerBits, length_unary, pow_zero, ↓reduceIte, polyOfBits_X,
      List.getLastD_cons]
    exact ⟨rfl, monic_X, irreducible_X, natDegree_X⟩
  | succ e =>
    have hq : q.Prime := he.resolve_left (by omega)
    have hr : q ^ (e + 1) ≠ 1 := ne_of_gt (one_lt_pow₀ hq.one_lt (by omega))
    by_cases hq2 : q = 2
    · subst q
      simp only [primePowerBits, length_unary, hr, ↓reduceIte]
      exact ⟨BinaryArtinSchreier.powerTwoBits_getLast _,
        BinaryArtinSchreier.powerTwoBits_correct (e + 1)⟩
    · simpa only [primePowerBits, length_unary, hr, hq2, ↓reduceIte] using
        oddPrimePowerBits_correct q e hq hq2

/-- Dispatch correctness includes neutral entries outside the prime factorization support. -/
theorem primePowerBits_factorization_correct (n q : ℕ) :
    let a := primePowerBits (unary q) (unary (q ^ n.factorization q))
    a.getLastD false = true ∧ (polyOfBits a).Monic ∧ Irreducible (polyOfBits a) ∧
      (polyOfBits a).natDegree = q ^ n.factorization q := by
  apply primePowerBits_correct
  by_cases hq : q.Prime
  · exact Or.inr hq
  · exact Or.inl (Nat.factorization_eq_zero_of_not_prime n hq)

/-- The supplied degree is decomposed into a fixed ordered list of irreducible polynomials. -/
def degreePolynomials (u : Unary) : List BitStr :=
  (primePowerPairs u).map (fun s => primePowerBits s.1 s.2)

/-- One polynomial-time program prints the entire prime-power polynomial list. -/
def degreePolynomialsProg : PolyTimeFun Unary (List BitStr) :=
  (map primePowerBitsProg).comp primePowerPairsProg

@[simp] theorem degreePolynomialsProg_apply (u : Unary) :
    degreePolynomialsProg u = degreePolynomials u := rfl

/-- Every printed component polynomial is monic and irreducible. -/
theorem degreePolynomials_correct (n : ℕ) :
    ∀ a ∈ degreePolynomials (unary n), (polyOfBits a).Monic ∧ Irreducible (polyOfBits a) := by
  intro a ha
  simp only [degreePolynomials, primePowerPairs_eq, List.map_ofFn] at ha
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  exact (primePowerBits_factorization_correct n i).2.1 |> fun hm =>
    ⟨hm, (primePowerBits_factorization_correct n i).2.2.1⟩

/-- The polynomial degrees are exactly the mathematical prime-power contribution list. -/
theorem degreePolynomials_degrees (n : ℕ) :
    (degreePolynomials (unary n)).map (fun a => (polyOfBits a).natDegree) =
      BinaryDegreeFactors.degreeFactors n := by
  simp only [degreePolynomials, primePowerPairs_eq, List.map_ofFn, BinaryDegreeFactors.degreeFactors]
  congr 1
  funext i
  exact (primePowerBits_factorization_correct n i).2.2.2

end MIPRE.LowDegree.BinaryPolynomial

end
