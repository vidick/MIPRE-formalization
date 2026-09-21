/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryIrreducibleAssembly

/-! # A specified polynomial-time irreducible polynomial of every positive binary degree -/

noncomputable section

namespace MIPRE.LowDegree.BinaryPolynomial

open Cost Cost.PolyTimeFun Polynomial DegreeArithmetic

/-- The complete constructor, with a fixed constant output at degree zero. -/
def irreducibleBits (u : Unary) : BitStr :=
  if u.isEmpty then [true]
  else ((degreePolynomials u).foldl assemblyStep (u, [false])).2 ++ [true]

/-- One globally polynomial-time program constructs every positive binary degree. -/
def irreducibleBitsProg : PolyTimeFun Unary BitStr :=
  congr (ite isEmptyProg (const [true])
    (append.comp ((assembleBitsProg.comp
      (degreePolynomialsProg.pair ((PolyTimeFun.id _).pair (const [false])))).pair (const [true]))))
    irreducibleBits (by
      intro u
      change (if u.isEmpty then [true]
        else assembleBitsProg (degreePolynomialsProg u, u, [false]) ++ [true]) = _
      rw [degreePolynomialsProg_apply, assembleBitsProg_apply]
      rfl)

@[simp] theorem irreducibleBitsProg_apply (u : Unary) : irreducibleBitsProg u = irreducibleBits u := rfl

/-- Degree zero is handled directly without invoking the construction loops. -/
@[simp] theorem irreducibleBits_zero : irreducibleBits (unary 0) = [true] := rfl

/-- Every output is in nonzero canonical coefficient form. -/
theorem irreducibleBits_getLast (u : Unary) : (irreducibleBits u).getLastD false = true := by
  unfold irreducibleBits
  split <;> simp

/-- The complete deterministic constructor is monic, irreducible, and has exactly
its requested degree for every positive unary input. -/
theorem irreducibleBits_correct (n : ℕ) (hn : 1 ≤ n) :
    (polyOfBits (irreducibleBits (unary n))).Monic ∧
      Irreducible (polyOfBits (irreducibleBits (unary n))) ∧
      (polyOfBits (irreducibleBits (unary n))).natDegree = n := by
  have hpos : 0 < n := hn
  let l := degreePolynomials (unary n)
  have hl : ∀ a ∈ l, (polyOfBits a).Monic ∧ Irreducible (polyOfBits a) := degreePolynomials_correct n
  have hprod : (l.map (fun a => (polyOfBits a).natDegree)).prod = n := by
    rw [degreePolynomials_degrees]
    exact BinaryDegreeFactors.degreeFactors_prod n hpos
  have hpair : l.Pairwise (fun a b => (polyOfBits a).natDegree.Coprime (polyOfBits b).natDegree) := by
    have hp := BinaryDegreeFactors.degreeFactors_pairwise n
    rw [← degreePolynomials_degrees n] at hp
    simpa only [List.pairwise_map] using hp
  have hfold := fold_assemblyStep_correct l (unary n) [false]
    (by simpa only [List.cons_append, List.nil_append, polyOfBits_X] using irreducible_X (R := ZMod 2))
    hl hpair (by intro a _; simp) (by simp only [List.length_singleton, one_mul, hprod, length_unary, le_refl])
  have hempty : (unary n).isEmpty = false := by
    apply Bool.eq_false_iff.mpr
    intro he
    have hz := List.isEmpty_iff_length_eq_zero.mp he
    rw [length_unary] at hz
    omega
  simp only [irreducibleBits, hempty, Bool.false_eq_true, if_false]
  refine ⟨monic_polyOfBits_append_true _, hfold.1, ?_⟩
  rw [natDegree_polyOfBits_append_true, hfold.2, List.length_singleton, one_mul, hprod]

/-- The program prints the leading coefficient as well as all lower coefficients. -/
theorem irreducibleBits_length (n : ℕ) (hn : 1 ≤ n) :
    (irreducibleBits (unary n)).length = n + 1 := by
  rw [← natDegree_add_one_of_getLast _ (irreducibleBits_getLast _), (irreducibleBits_correct n hn).2.2]

/-- A concrete polynomial bounds the actual ambient run time as a function of degree,
including degree zero and output printing. -/
theorem irreducibleBitsProg_time_le :
    ∃ R : Polynomial ℕ, ∀ n : ℕ, ∃ t : ℕ,
      t ≤ R.eval n ∧ irreducibleBitsProg.code.Runs (encode (unary n))
        (encode (irreducibleBits (unary n))) t := by
  refine ⟨irreducibleBitsProg.timeBound.comp (2 * X + 1), ?_⟩
  intro n
  obtain ⟨t, ht, hr⟩ := irreducibleBitsProg.computes (unary n)
  refine ⟨t, ?_, hr⟩
  simpa only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_one, esize_unary] using ht

end MIPRE.LowDegree.BinaryPolynomial

end
