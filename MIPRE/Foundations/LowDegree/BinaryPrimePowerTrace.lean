/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryCoprimeDegree
import MIPRE.Foundations.LowDegree.BinaryOddPrimeExtension
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! # Exact degree of the odd-prime Shoup trace -/

noncomputable section

namespace MIPRE.LowDegree.BinaryPrimePowerTrace

open Polynomial IntermediateField

/-- The Frobenius trace used by Shoup's prime-power construction. -/
def traceElement {E : Type*} [CommRing E] (β : E) (m r : ℕ) : E :=
  ∑ i : Fin m, β ^ (2 ^ (r * (i : ℕ)))

/-- Reducing the trace exponents modulo `q` yields a nonzero polynomial of degree
less than `q`; hence the trace cannot belong to the `q`-th-power root field. -/
theorem traceElement_not_mem_range {L E : Type*} [Field L] [Field E] [Algebra L E]
    (β : E) (w : L) (m r q : ℕ) (hm : 0 < m) (hq : 1 < q)
    (hw : algebraMap L E w = β ^ q)
    (hinj : Function.Injective (fun i : Fin m => 2 ^ (r * (i : ℕ)) % q))
    (hdeg : q ≤ (minpoly L β).natDegree) :
    traceElement β m r ∉ (algebraMap L E).range := by
  classical
  rintro ⟨c, hc⟩
  let A : (Fin m) → L[X] := fun i =>
    C (w ^ (2 ^ (r * (i : ℕ)) / q)) * X ^ (2 ^ (r * (i : ℕ)) % q)
  let P : L[X] := (∑ i : Fin m, A i) - C c
  let i₀ : Fin m := ⟨0, hm⟩
  have hres₀ : 2 ^ (r * (i₀ : ℕ)) % q = 1 := by
    simp only [i₀, Nat.mul_zero, pow_zero, Nat.mod_eq_of_lt hq]
  have hcoeff : P.coeff 1 = 1 := by
    change ((∑ i : Fin m, A i) - C c).coeff 1 = 1
    rw [coeff_sub, finsetSum_coeff, coeff_C]
    simp only [one_ne_zero, ↓reduceIte, sub_zero]
    rw [Finset.sum_eq_single i₀]
    · simp [A, i₀, Nat.mod_eq_of_lt hq, Nat.div_eq_of_lt hq]
    · intro j _ hj
      have hr : 2 ^ (r * (j : ℕ)) % q ≠ 1 := by
        intro he
        exact hj (hinj (he.trans hres₀.symm))
      change (C (w ^ (2 ^ (r * (j : ℕ)) / q)) * X ^ (2 ^ (r * (j : ℕ)) % q)).coeff 1 = 0
      simp only [coeff_C_mul_X_pow, Ne.symm hr, if_false]
    · simp
  have hP : P ≠ 0 := by intro he; simp [he] at hcoeff
  have hPdeg : P.degree < (q : WithBot ℕ) := by
    change ((∑ i : Fin m, A i) - C c).degree < _
    apply (degree_sub_le _ _).trans_lt
    apply max_lt
    · apply (degree_sum_le _ _).trans_lt
      apply (Finset.sup_lt_iff (WithBot.bot_lt_coe q)).2
      intro i _
      exact (degree_C_mul_X_pow_le _ _).trans_lt
        (WithBot.coe_lt_coe.mpr (Nat.mod_lt _ (by omega)))
    · exact degree_C_le.trans_lt (WithBot.coe_lt_coe.mpr (show 0 < q by omega))
  have heval (i : Fin m) : aeval β (A i) = β ^ (2 ^ (r * (i : ℕ))) := by
    simp only [A, map_mul, aeval_C, map_pow, aeval_X, hw, ← pow_mul, ← pow_add]
    congr 1
    exact Nat.div_add_mod _ _
  have hz : aeval β P = 0 := by
    change aeval β ((∑ i : Fin m, A i) - C c) = 0
    rw [map_sub, map_sum]
    simp only [heval, aeval_C, hc, traceElement, sub_self]
  have hle := natDegree_le_of_dvd (minpoly.dvd L β hz) hP
  have hlt : P.natDegree < q := (natDegree_lt_iff_degree_lt (by omega)).mpr hPdeg
  omega

/-- The trace's Frobenius orbit closes after `r` when the original orbit closes after `m*r`. -/
theorem traceElement_closed {E : Type*} [CommRing E] [CharP E 2]
    (β : E) (m r : ℕ) (hβ : β ^ (2 ^ (r * m)) = β) :
    traceElement β m r ^ (2 ^ r) = traceElement β m r := by
  have hshift (i : ℕ) : (β ^ (2 ^ (r * i))) ^ (2 ^ r) = β ^ (2 ^ (r * (i + 1))) := by
    rw [← pow_mul, ← pow_add, Nat.mul_add, Nat.mul_one]
  rw [traceElement, sum_pow_char_pow]
  simp only [hshift]
  rw [Fin.sum_univ_eq_sum_range (fun i => β ^ (2 ^ (r * (i + 1)))),
    Fin.sum_univ_eq_sum_range (fun i => β ^ (2 ^ (r * i)))]
  have h := Finset.sum_range_succ' (fun i => β ^ (2 ^ (r * i))) m
  have h' := Finset.sum_range_succ (fun i => β ^ (2 ^ (r * i))) m
  have hh := h.symm.trans h'
  simp only [Nat.mul_zero, pow_zero, pow_one, hβ] at hh
  exact add_right_cancel hh

/-- The seed's multiplicative-order specification makes the reduced trace exponents distinct. -/
theorem exponent_residues_injective (m r q : ℕ) (horder : orderOf (2 : ZMod q) = m)
    (hcop : r.Coprime m) :
    Function.Injective (fun i : Fin m => 2 ^ (r * (i : ℕ)) % q) := by
  have hp : IsPrimitiveRoot (2 : ZMod q) m := IsPrimitiveRoot.iff_orderOf.mpr horder
  have hr := hp.pow_of_coprime r hcop
  intro i j hij
  apply Fin.ext
  apply hr.pow_inj i.isLt j.isLt
  rw [← pow_mul, ← pow_mul]
  have he := (ZMod.natCast_eq_natCast_iff' (2 ^ (r * (i : ℕ)))
    (2 ^ (r * (j : ℕ))) q).2 hij
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using he

/-- The closed Shoup trace has the full requested prime-power degree. The smaller
root field is used only in this proof, never as an executable representation. -/
theorem traceElement_natDegree {L E : Type*} [Field L] [Field E] [Finite L]
    [Algebra L E] [Algebra (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
    (β : E) (w : L) (m q e : ℕ) (hm : 0 < m) (hq : q.Prime)
    (hw : algebraMap L E w = β ^ q)
    (horder : orderOf (2 : ZMod q) = m) (hcop : q.Coprime m)
    (hcard : Nat.card L = 2 ^ (m * q ^ e))
    (hdeg : q ≤ (minpoly L β).natDegree)
    (hβ : β ^ (2 ^ (q ^ (e + 1) * m)) = β) :
    (minpoly (ZMod 2) (traceElement β m (q ^ (e + 1)))).natDegree = q ^ (e + 1) := by
  let : CharP E 2 := charP_of_injective_ringHom (algebraMap (ZMod 2) E).injective 2
  let γ := traceElement β m (q ^ (e + 1))
  have hi : IsIntegral (ZMod 2) γ := IsIntegral.of_finite (ZMod 2) γ
  have hclosed : γ ^ (2 ^ (q ^ (e + 1))) = γ := traceElement_closed β m _ hβ
  have hdiv := (BinaryFiniteField.minpoly_natDegree_dvd_iff_frobenius γ hi _).2 hclosed
  obtain ⟨j, hj, hd⟩ := (Nat.dvd_prime_pow hq).1 hdiv
  by_cases heq : j = e + 1
  · simpa [heq] using hd
  have hje : j ≤ e := by omega
  have hd' : (minpoly (ZMod 2) γ).natDegree ∣ q ^ e := by
    rw [hd]
    exact pow_dvd_pow q hje
  have hfix : iterateFrobenius E 2 (q ^ e) γ = γ :=
    (BinaryFiniteField.minpoly_natDegree_dvd_iff_frobenius γ hi _).1 hd'
  have hlarge : iterateFrobenius E 2 (q ^ e * m) γ = γ := by
    rw [iterateFrobenius_mul_apply]
    exact Function.IsFixedPt.iterate hfix m
  have hmem : γ ∈ (algebraMap L E).range := by
    apply (BinaryFiniteField.mem_range_iff_pow_card γ).2
    rw [hcard, Nat.mul_comm m]
    exact hlarge
  exact False.elim ((traceElement_not_mem_range β w m (q ^ (e + 1)) q hm hq.one_lt hw
    (exponent_residues_injective m _ q horder (hcop.pow_left _)) hdeg) hmem)

/-- The intermediate-field premises follow from the two exact root degrees.
This form applies directly to the flat Kummer quotient. -/
theorem traceElement_natDegree_of_root_degrees {E : Type*} [Field E] [Finite E]
    [Algebra (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
    (β : E) (m q e : ℕ) (hm : 0 < m) (hq : q.Prime)
    (horder : orderOf (2 : ZMod q) = m) (hcop : q.Coprime m)
    (hprim : IntermediateField.adjoin (ZMod 2) ({β} : Set E) = ⊤)
    (hβ : (minpoly (ZMod 2) β).natDegree = m * q ^ (e + 1))
    (hβq : (minpoly (ZMod 2) (β ^ q)).natDegree = m * q ^ e) :
    (minpoly (ZMod 2) (traceElement β m (q ^ (e + 1)))).natDegree = q ^ (e + 1) := by
  let L := IntermediateField.adjoin (ZMod 2) ({β ^ q} : Set E)
  let w : L := ⟨β ^ q, IntermediateField.subset_adjoin (ZMod 2) _ (by simp)⟩
  have hi : IsIntegral (ZMod 2) β := IsIntegral.of_finite (ZMod 2) β
  have hdim : Module.finrank (ZMod 2) E = m * q ^ (e + 1) := by
    rw [← hβ, ← IntermediateField.adjoin.finrank hi, hprim, finrank_top']
  have hL : Module.finrank (ZMod 2) L = m * q ^ e := by
    rw [IntermediateField.adjoin.finrank (hi.pow q), hβq]
  have hprimL : IntermediateField.adjoin L ({β} : Set E) = ⊤ :=
    IntermediateField.adjoin_eq_top_of_adjoin_eq_top (ZMod 2) hprim
  have hrdeg : (minpoly L β).natDegree = Module.finrank L E := by
    rw [← IntermediateField.adjoin.finrank (IsIntegral.of_finite L β), hprimL, finrank_top']
  have hmul : (m * q ^ e) * Module.finrank L E = (m * q ^ e) * q := by
    have h := Module.finrank_mul_finrank (ZMod 2) L E
    rw [hL, hdim] at h
    simpa only [pow_succ, Nat.mul_assoc] using h
  have hrank : Module.finrank L E = q :=
    Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hm (pow_pos hq.pos e)) hmul
  have hcard : Nat.card L = 2 ^ (m * q ^ e) := by
    let : Fintype L := Fintype.ofFinite L
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, hL]
  have hclosed : β ^ (2 ^ (q ^ (e + 1) * m)) = β :=
    (BinaryFiniteField.minpoly_natDegree_dvd_iff_frobenius β hi _).1
      (by rw [hβ, Nat.mul_comm])
  exact traceElement_natDegree β w m q e hm hq rfl horder hcop hcard
    (by rw [hrdeg, hrank]) hclosed

/-- The trace in the explicitly specified flat odd-prime-power quotient has exactly
the requested prime-power degree over the binary field. -/
theorem flat_trace_natDegree (f : (ZMod 2)[X]) (hf : f.Monic) (hi : Irreducible f)
    (q e : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (hn : ∀ b : AdjoinRoot f, b ^ q ≠ AdjoinRoot.root f)
    (horder : orderOf (2 : ZMod q) = f.natDegree) (hcop : q.Coprime f.natDegree) :
    (minpoly (ZMod 2) (traceElement (AdjoinRoot.root (f.comp (X ^ (q ^ (e + 1)))))
      f.natDegree (q ^ (e + 1)))).natDegree = q ^ (e + 1) := by
  let F := f.comp (X ^ (q ^ (e + 1)))
  have hm : F.Monic := hf.comp (monic_X.pow _) (by simp [hq.ne_zero])
  let : Fact (Irreducible F) :=
    ⟨BinaryPolynomial.irreducible_comp_prime_pow_of_nonresidue f hf hi q (e + 1) hq hq2 hn⟩
  let : Fintype (AdjoinRoot F) := Fintype.ofEquiv (Fin F.natDegree → ZMod 2)
    (BinaryQuotient.coordinateEquiv F hm).symm.toEquiv
  let : Module.Finite (ZMod 2) (AdjoinRoot F) := hm.finite_adjoinRoot
  apply traceElement_natDegree_of_root_degrees (AdjoinRoot.root F) f.natDegree q e
    hi.natDegree_pos hq horder hcop (IntermediateField.adjoin_root_eq_top F)
  · rw [BinaryPolynomial.flat_prime_power_minpoly f hf hi q (e + 1) hq hq2 hn,
      natDegree_comp, natDegree_X_pow]
  · rw [BinaryPolynomial.flat_prime_power_root_pow_minpoly f hf hi q e hq hq2 hn,
      natDegree_comp, natDegree_X_pow]

end MIPRE.LowDegree.BinaryPrimePowerTrace

end