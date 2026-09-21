/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryOddPrimeProgram
import MIPRE.Foundations.LowDegree.BinaryPrimePowerTrace

/-! # Certified polynomial-time irreducibles of every odd-prime-power degree -/

noncomputable section

namespace MIPRE.LowDegree.BinaryPolynomial

open Cost Polynomial BinaryQuotient

/-- The output width is bounded by the requested degree even on malformed inputs. -/
theorem oddPrimePowerBits_width_le (q r : Unary) :
    (oddPrimePowerBits q r).length ≤ r.length + 1 := by
  apply (length_normalizeBits_le _).trans
  simp only [orbitPolynomialBits, descendBits, List.length_map, length_orbitProductBits, le_refl]

/-- The trace generator in the explicit extension has exactly the requested odd-prime-power degree. -/
theorem oddTraceBits_natDegree (q e : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) :
    let f := polyOfBits (nonresidueLiftBitsProg (unary q))
    let F := f.comp (X ^ (q ^ (e + 1)))
    (minpoly (ZMod 2) (evalBits (AdjoinRoot.root F)
      (oddTraceBits (unary q) (unary (q ^ (e + 1)))))).natDegree = q ^ (e + 1) := by
  let f := polyOfBits (nonresidueLiftBitsProg (unary q))
  let F := f.comp (X ^ (q ^ (e + 1)))
  have ha := nonresidueLiftBitsProg_correct q hq hq2
  have hf : f.Monic := ha.2.1
  have hi : Irreducible f := ha.2.2.1
  let : Fact (Irreducible F) :=
    ⟨irreducible_comp_prime_pow_of_nonresidue f hf hi q (e + 1) hq hq2 ha.2.2.2.2⟩
  let : CharP (AdjoinRoot F) 2 := charP_of_injective_ringHom (AdjoinRoot.of F).injective 2
  let p := oddExtensionLowerBits (unary q) (unary (q ^ (e + 1)))
  have hp := oddExtensionLowerBits_spec q (e + 1) hq hq2
  have he := polyOfBits_oddExtensionBits q (q ^ (e + 1)) (pow_pos hq.pos _)
  have hpoly : F = polyOfBits (p ++ [true]) := he.symm.trans hp.2.1
  have htrace := evalBits_oddTraceBits_of_root (AdjoinRoot.root F) q (e + 1) hq hq2
    (root_eq F p hpoly)
  have hdegree := BinaryPrimePowerTrace.flat_trace_natDegree f hf hi q e hq hq2
    ha.2.2.2.2 (nonresidueLiftBits_order q hq hq2) (nonresidueLiftBits_degree_coprime q hq hq2)
  have htrace' : evalBits (AdjoinRoot.root F)
      (oddTraceBits (unary q) (unary (q ^ (e + 1)))) =
      BinaryPrimePowerTrace.traceElement (AdjoinRoot.root F) f.natDegree (q ^ (e + 1)) := by
    rw [htrace, BinaryPrimePowerTrace.traceElement,
      Fin.sum_univ_eq_sum_range (fun i => AdjoinRoot.root F ^ (2 ^ (q ^ (e + 1) * i)))]
    rw [ha.2.2.2.1]
  change (minpoly (ZMod 2) (evalBits (AdjoinRoot.root F)
    (oddTraceBits (unary q) (unary (q ^ (e + 1)))))).natDegree = _
  rw [htrace']
  exact hdegree

/-- The requested odd-prime-power constructor is correct, including canonical coefficient output. -/
theorem oddPrimePowerBits_correct (q e : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) :
    let a := oddPrimePowerBits (unary q) (unary (q ^ (e + 1)))
    a.getLastD false = true ∧ (polyOfBits a).Monic ∧ Irreducible (polyOfBits a) ∧
      (polyOfBits a).natDegree = q ^ (e + 1) := by
  let f := polyOfBits (nonresidueLiftBitsProg (unary q))
  let F := f.comp (X ^ (q ^ (e + 1)))
  let p := oddExtensionLowerBits (unary q) (unary (q ^ (e + 1)))
  let gamma := oddTraceBits (unary q) (unary (q ^ (e + 1)))
  have ha := nonresidueLiftBitsProg_correct q hq hq2
  have hf : F.Monic := ha.2.1.comp (monic_X.pow _) (by simp [hq.ne_zero])
  let : Fact (Irreducible F) :=
    ⟨irreducible_comp_prime_pow_of_nonresidue f ha.2.1 ha.2.2.1 q (e + 1) hq hq2 ha.2.2.2.2⟩
  let : Module.Finite (ZMod 2) (AdjoinRoot F) := hf.finite_adjoinRoot
  have hs := oddExtensionLowerBits_spec q (e + 1) hq hq2
  have he := polyOfBits_oddExtensionBits q (q ^ (e + 1)) (pow_pos hq.pos _)
  have hpoly : F = polyOfBits (p ++ [true]) := he.symm.trans hs.2.1
  have hp : p.length = F.natDegree := hs.1.trans (congrArg Polynomial.natDegree he)
  have hwidth : gamma.length = p.length := oddTraceBits_width _ _
  have hdegree : (minpoly (ZMod 2) (evalBits (AdjoinRoot.root F) gamma)).natDegree = q ^ (e + 1) :=
    oddTraceBits_natDegree q e hq hq2
  have hclosed : evalBits (AdjoinRoot.root F) gamma ^ (2 ^ (q ^ (e + 1))) =
      evalBits (AdjoinRoot.root F) gamma :=
    (BinaryFiniteField.minpoly_natDegree_dvd_iff_frobenius _
      (IsIntegral.of_finite (ZMod 2) _) _).mp (by rw [hdegree])
  have hm := orbitPolynomialBits_monic_natDegree F hf (unary (q ^ (e + 1))) p gamma hp hpoly
    hs.2.2 hwidth (by simpa only [length_unary] using hclosed)
  have hi := orbitPolynomialBits_irreducible F hf (unary (q ^ (e + 1))) p gamma hp hpoly
    hs.2.2 hwidth (by simpa only [length_unary] using hclosed)
    (by simpa only [length_unary] using pow_pos hq.pos (e + 1))
    (by simpa only [length_unary] using hdegree)
  let b := orbitPolynomialBits (unary (q ^ (e + 1))) p gamma
  change (normalizeBits b).getLastD false = true ∧ (polyOfBits (normalizeBits b)).Monic ∧
    Irreducible (polyOfBits (normalizeBits b)) ∧
    (polyOfBits (normalizeBits b)).natDegree = q ^ (e + 1)
  rw [polyOfBits_normalizeBits]
  refine ⟨?_, hm.1, hi, by simpa only [length_unary] using hm.2⟩
  rcases normalizeBits_getLast b with hn | hn
  · exact (hm.1.ne_zero ((normalizeBits_eq_nil_iff b).mp hn)).elim
  · exact hn

/-- The printed coefficient list has exactly degree plus one entries. -/
theorem oddPrimePowerBits_length (q e : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) :
    (oddPrimePowerBits (unary q) (unary (q ^ (e + 1)))).length = q ^ (e + 1) + 1 := by
  have h := oddPrimePowerBits_correct q e hq hq2
  rw [← natDegree_add_one_of_getLast _ h.1, h.2.2.2]

end MIPRE.LowDegree.BinaryPolynomial

end
