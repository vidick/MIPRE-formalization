/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryNonresidueAlgebra
import Mathlib.FieldTheory.Finite.Extension

/-! # Equal-degree factors in a successful auxiliary root lift -/

namespace MIPRE.LowDegree.BinaryPolynomial

open Polynomial

/-- A residue root forces the substituted polynomial to divide the multiplicative
field polynomial. This exponentially large polynomial is only a proof device. -/
theorem comp_dvd_card_sub_one_of_residue {F K : Type*} [Field F] [Field K]
    [Algebra F K] [Fintype K] (f : Polynomial F) (hi : Irreducible f)
    (a b : K) (ha : aeval a f = 0) (ha0 : a ≠ 0) (q : ℕ)
    (hq : q ∣ Fintype.card K - 1) (hb : b ^ q = a) :
    f.comp (X ^ q) ∣ X ^ (Fintype.card K - 1) - 1 := by
  have hb0 : b ≠ 0 := by
    intro h
    subst b
    by_cases hq0 : q = 0
    · subst q
      have hc : Fintype.card K - 1 = 0 := by simpa using hq
      have hc2 := Fintype.one_lt_card (α := K)
      omega
    · exact ha0 (by simpa [zero_pow hq0] using hb.symm)
  have hp : a ^ ((Fintype.card K - 1) / q) = 1 := by
    rw [← hb, ← pow_mul, Nat.mul_div_cancel' hq]
    exact FiniteField.pow_card_sub_one_eq_one b hb0
  have hf : f ∣ X ^ ((Fintype.card K - 1) / q) - 1 :=
    (hi.dvd_iff_aeval_eq_zero ha).mp (by simp [hp])
  have hc := map_dvd (compRingHom (X ^ q)) hf
  simpa only [coe_compRingHom_apply, sub_comp, pow_comp, X_comp, one_comp,
    ← pow_mul, Nat.mul_div_cancel' hq] using hc

/-- A factor of a power substitution has at least the original irreducible degree. -/
theorem natDegree_le_of_dvd_comp_power {F : Type*} [Field F]
    (f g : Polynomial F) (hf : f.Monic) (hi : Irreducible f) (hg : Irreducible g)
    (q : ℕ) (hd : g ∣ f.comp (X ^ q)) : f.natDegree ≤ g.natDegree := by
  let : Fact (Irreducible g) := ⟨hg⟩
  let : Module.Finite F (AdjoinRoot g) := (AdjoinRoot.powerBasis hg.ne_zero).finite
  have hz : aeval (AdjoinRoot.root g ^ q) f = 0 := by
    have hroot : aeval (AdjoinRoot.root g) (f.comp (X ^ q)) = 0 :=
      by simpa only [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero] using hd
    simpa only [aeval_def, eval₂_comp, eval₂_pow, eval₂_X] using hroot
  have hm := minpoly.eq_of_irreducible_of_monic hi hz hf
  rw [hm]
  have hdim : Module.finrank F (AdjoinRoot g) = g.natDegree :=
    (AdjoinRoot.powerBasis hg.ne_zero).finrank
  simpa only [hdim] using (minpoly.natDegree_le (A := F) (AdjoinRoot.root g ^ q))

/-- Every irreducible factor in a residue lift has exactly the old degree. -/
theorem residue_factor_natDegree {F K : Type*} [Field F] [Finite F] [Field K]
    [Algebra F K] [Fintype K] (f g : Polynomial F) (hf : f.Monic)
    (hi : Irreducible f) (hg : Irreducible g)
    (hcard : Fintype.card K = Nat.card F ^ f.natDegree)
    (a b : K) (ha : aeval a f = 0) (ha0 : a ≠ 0) (q : ℕ)
    (hq : q ∣ Fintype.card K - 1) (hb : b ^ q = a)
    (hd : g ∣ f.comp (X ^ q)) : g.natDegree = f.natDegree := by
  have hdiv := hd.trans (comp_dvd_card_sub_one_of_residue f hi a b ha ha0 q hq hb)
  have hfield : g ∣ X ^ Nat.card F ^ f.natDegree - X := by
    have hc : 1 ≤ Fintype.card K := Fintype.card_pos
    have hx : (X : Polynomial F) ^ Fintype.card K - X =
        X * (X ^ (Fintype.card K - 1) - 1) := by
      rw [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel hc]
    rw [← hcard, hx]
    exact dvd_mul_of_dvd_right hdiv X
  have hdeg := hg.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hfield
  exact Nat.le_antisymm (Nat.le_of_dvd hi.natDegree_pos hdeg)
    (natDegree_le_of_dvd_comp_power f g hf hi hg q hd)

end MIPRE.LowDegree.BinaryPolynomial
