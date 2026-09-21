/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryFactorization
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization

/-!
# The deterministic cyclotomic seed for odd prime-power construction

For an odd prime `q`, factor `1+X+...+X^(q-1)` and choose the first factor in the
specified factorization order. This gives a concrete irreducible polynomial of
degree equal to the order of two modulo `q`; it does not enumerate fields.
-/

noncomputable section

namespace MIPRE.LowDegree.BinaryPolynomial

open Cost Cost.PolyTimeFun Polynomial

/-- The all-one coefficient vector is the geometric-sum polynomial. -/
theorem polyOfBits_replicate_true (n : ℕ) :
    polyOfBits (List.replicate n true) = ∑ i ∈ Finset.range n, (X : Polynomial (ZMod 2)) ^ i := by
  unfold polyOfBits
  simp only [List.length_replicate]
  apply Finset.sum_congr rfl
  intro i hi
  have hl : i < n := Finset.mem_range.mp hi
  simp [List.getD_eq_getElem?_getD, hl, monomial_one_right_eq_X_pow]

/-- Lower coefficients of the prime cyclotomic polynomial; the leading one is implicit. -/
def cyclotomicLowerBits (u : Unary) : BitStr := List.replicate (u.length - 1) true

/-- Uniform unary printing of the binary prime-cyclotomic coefficient vector. -/
def cyclotomicLowerBitsProg : PolyTimeFun Unary BitStr :=
  congr (replicate.comp (PolyTimeFun.tail.pair (const true))) cyclotomicLowerBits (by
    intro u
    simp [cyclotomicLowerBits])

@[simp] theorem cyclotomicLowerBitsProg_apply (u : Unary) :
    cyclotomicLowerBitsProg u = cyclotomicLowerBits u := rfl

/-- The printed monic polynomial is exactly the cyclotomic polynomial at every prime. -/
theorem polyOfBits_cyclotomicLowerBits (q : ℕ) (hq : q.Prime) :
    polyOfBits (cyclotomicLowerBits (unary q) ++ [true]) = cyclotomic q (ZMod 2) := by
  let : Fact q.Prime := ⟨hq⟩
  have hq1 : q - 1 + 1 = q := Nat.sub_add_cancel hq.one_le
  rw [cyclotomicLowerBits, length_unary, ← List.replicate_one, ← List.replicate_add, hq1,
    polyOfBits_replicate_true, cyclotomic_prime]

/-- Choose the first factor in the fixed deterministic factorization order. -/
def cyclotomicSeedBits (u : Unary) : BitStr :=
  (BinaryQuotient.factorBitsProg (cyclotomicLowerBits u)).headD []

/-- One fixed ambient program producing the auxiliary irreducible seed. -/
def cyclotomicSeedBitsProg : PolyTimeFun Unary BitStr :=
  (PolyTimeFun.headD []).comp (BinaryQuotient.factorBitsProg.comp cyclotomicLowerBitsProg)

@[simp] theorem cyclotomicSeedBitsProg_apply (u : Unary) :
    cyclotomicSeedBitsProg u = cyclotomicSeedBits u := rfl

/-- An odd prime remains nonzero in the binary field. -/
theorem oddPrime_cast_ne_zero (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) : (q : ZMod 2) ≠ 0 := by
  intro hz
  have hcop : Nat.Coprime 2 q := (Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2)
  exact (Nat.prime_two.coprime_iff_not_dvd.mp hcop) ((CharP.cast_eq_zero_iff (ZMod 2) 2 q).mp hz)

/-- The chosen seed is a specified monic irreducible divisor of the prime cyclotomic polynomial. -/
theorem cyclotomicSeedBits_correct (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) :
    (polyOfBits (cyclotomicSeedBits (unary q))).Monic ∧
    Irreducible (polyOfBits (cyclotomicSeedBits (unary q))) ∧
    polyOfBits (cyclotomicSeedBits (unary q)) ∣ cyclotomic q (ZMod 2) := by
  let p := cyclotomicLowerBits (unary q)
  have hp : p.length = (cyclotomic q (ZMod 2)).natDegree := by
    rw [← polyOfBits_cyclotomicLowerBits q hq, natDegree_polyOfBits_append_true]
  have hp0 : p ≠ [] := by
    intro h
    have he := congrArg List.length h
    simp only [p, cyclotomicLowerBits, length_unary, List.length_replicate, List.length_nil] at he
    have := hq.two_le
    omega
  let : NeZero (q : ZMod 2) := ⟨oddPrime_cast_ne_zero q hq hq2⟩
  have hs := squarefree_cyclotomic q (ZMod 2)
  have hprod := BinaryQuotient.factorBitsProg_prod (cyclotomic q (ZMod 2))
    (cyclotomic.monic q (ZMod 2)) p hp (polyOfBits_cyclotomicLowerBits q hq).symm hp0 hs
  have hnonempty : BinaryQuotient.factorBitsProg p ≠ [] := by
    intro hz
    rw [hz, List.map_nil, List.prod_nil] at hprod
    have hd := congrArg Polynomial.natDegree hprod
    rw [← hp] at hd
    simp only [natDegree_one] at hd
    exact hp0 (List.length_eq_zero_iff.mp hd.symm)
  have hmem : cyclotomicSeedBits (unary q) ∈ BinaryQuotient.factorBitsProg p := by
    change (BinaryQuotient.factorBitsProg p).headD [] ∈ _
    cases hl : BinaryQuotient.factorBitsProg p with
    | nil => exact (hnonempty hl).elim
    | cons a l => simp
  have hfac := BinaryQuotient.factorBitsProg_factors (cyclotomic q (ZMod 2))
    (cyclotomic.monic q (ZMod 2)) p hp (polyOfBits_cyclotomicLowerBits q hq).symm hp0 hs _ hmem
  refine ⟨hfac.1, hfac.2, ?_⟩
  rw [← hprod]
  exact List.dvd_prod (List.mem_map.mpr ⟨_, hmem, rfl⟩)

/-- The seed degree is the multiplicative order of two modulo the odd prime. -/
theorem cyclotomicSeedBits_natDegree (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (hcop : Nat.Coprime 2 q) :
    (polyOfBits (cyclotomicSeedBits (unary q))).natDegree =
      orderOf (ZMod.unitOfCoprime (2 ^ 1) (hcop.pow_left 1)) := by
  have h := cyclotomicSeedBits_correct q hq hq2
  exact natDegree_of_dvd_cyclotomic_of_irreducible
    (show Fintype.card (ZMod 2) = 2 ^ 1 by simp) hcop h.2.2 h.2.1

/-- The seed has positive degree dividing `q-1`, so its size is polynomial in unary `q`. -/
theorem cyclotomicSeedBits_degree_dvd (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) :
    0 < (polyOfBits (cyclotomicSeedBits (unary q))).natDegree ∧
      (polyOfBits (cyclotomicSeedBits (unary q))).natDegree ∣ q - 1 := by
  have h := cyclotomicSeedBits_correct q hq hq2
  refine ⟨h.2.1.natDegree_pos, ?_⟩
  have hcop : Nat.Coprime 2 q := (Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2)
  let : NeZero q := ⟨hq.ne_zero⟩
  rw [cyclotomicSeedBits_natDegree q hq hq2 hcop]
  have hd := orderOf_dvd_card (x := ZMod.unitOfCoprime (2 ^ 1) (hcop.pow_left 1))
  simpa only [ZMod.card_units_eq_totient, Nat.totient_prime hq] using hd

/-- The seed degree is coprime to the requested odd prime. -/
theorem cyclotomicSeedBits_degree_coprime (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) :
    Nat.Coprime (polyOfBits (cyclotomicSeedBits (unary q))).natDegree q := by
  have h := (cyclotomicSeedBits_degree_dvd q hq hq2).2
  have hc : Nat.Coprime (q - 1) q := by
    have hc : Nat.Coprime (q - 1) ((q - 1) + 1) := by simp
    simpa only [Nat.sub_add_cancel hq.one_le] using hc
  exact hc.of_dvd_left h

/-- The seed's specified root is a primitive `q`-th root of unity. -/
theorem cyclotomicSeedBits_root_primitive (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) :
    IsPrimitiveRoot (AdjoinRoot.root (polyOfBits (cyclotomicSeedBits (unary q)))) q := by
  let f := polyOfBits (cyclotomicSeedBits (unary q))
  have h := cyclotomicSeedBits_correct q hq hq2
  let : Fact (Irreducible f) := ⟨h.2.1⟩
  let : NeZero (q : ZMod 2) := ⟨oddPrime_cast_ne_zero q hq hq2⟩
  let : NeZero (q : AdjoinRoot f) := NeZero.of_injective (algebraMap (ZMod 2) (AdjoinRoot f)).injective
  have hd : f.map (algebraMap (ZMod 2) (AdjoinRoot f)) ∣ cyclotomic q (AdjoinRoot f) := by
    simpa using Polynomial.map_dvd (algebraMap (ZMod 2) (AdjoinRoot f)) h.2.2
  exact isRoot_cyclotomic_iff.mp ((AdjoinRoot.isRoot_root f).dvd hd)

end MIPRE.LowDegree.BinaryPolynomial

end
