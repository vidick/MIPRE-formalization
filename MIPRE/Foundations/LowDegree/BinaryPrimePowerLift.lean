/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryResidueFactors

/-! # Primitive-root progress and squarefreeness in auxiliary lifting -/

namespace MIPRE.LowDegree.BinaryPolynomial

open Polynomial

/-- Odd prime powers remain nonzero over the binary field. -/
theorem oddPrimePower_cast_ne_zero (q s : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) :
    ((q ^ s : ℕ) : ZMod 2) ≠ 0 := by
  rw [Nat.cast_pow]
  exact pow_ne_zero _ (oddPrime_cast_ne_zero q hq hq2)

/-- Any root of a cyclotomic divisor has the prescribed primitive order. -/
theorem primitiveRoot_of_aeval_dvd_cyclotomic {F K : Type*} [Field F] [Field K]
    [Algebra F K] (f : Polynomial F) (n : ℕ) [NeZero (n : K)]
    (hd : f ∣ cyclotomic n F) (z : K) (hz : aeval z f = 0) : IsPrimitiveRoot z n := by
  have hroot : IsRoot (f.map (algebraMap F K)) z := by
    simpa only [IsRoot, eval_map, ← aeval_def] using hz
  have hdiv : f.map (algebraMap F K) ∣ cyclotomic n K := by
    simpa using Polynomial.map_dvd (algebraMap F K) hd
  exact isRoot_cyclotomic_iff.mp (hroot.dvd hdiv)

/-- Each factor chosen in a lift advances primitive prime-power order. -/
theorem lifted_root_primitive (f g : Polynomial (ZMod 2)) (q s : ℕ)
    (hq : q.Prime) (hq2 : q ≠ 2) (hs : 0 < s) (hg : Irreducible g)
    (hf : f ∣ cyclotomic (q ^ s) (ZMod 2)) (hd : g ∣ f.comp (X ^ q)) :
    IsPrimitiveRoot (AdjoinRoot.root g) (q ^ (s + 1)) := by
  let : Fact (Irreducible g) := ⟨hg⟩
  let : NeZero ((q ^ s : ℕ) : ZMod 2) := ⟨oddPrimePower_cast_ne_zero q s hq hq2⟩
  let : NeZero ((q ^ s : ℕ) : AdjoinRoot g) :=
    NeZero.of_injective (algebraMap (ZMod 2) (AdjoinRoot g)).injective
  have hz : aeval (AdjoinRoot.root g ^ q) f = 0 := by
    have hroot : aeval (AdjoinRoot.root g) (f.comp (X ^ q)) = 0 := by
      simpa only [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero] using hd
    simpa only [aeval_def, eval₂_comp, eval₂_pow, eval₂_X] using hroot
  exact primitiveRoot_of_prime_power_root _ q s hq hs
    (primitiveRoot_of_aeval_dvd_cyclotomic f (q ^ s) hf _ hz)

/-- The cyclotomic divisibility invariant passes to every chosen factor. -/
theorem lifted_factor_dvd_cyclotomic (f g : Polynomial (ZMod 2)) (q s : ℕ)
    (hq : q.Prime) (hq2 : q ≠ 2) (hs : 0 < s) (hg : Irreducible g)
    (hf : f ∣ cyclotomic (q ^ s) (ZMod 2)) (hd : g ∣ f.comp (X ^ q)) :
    g ∣ cyclotomic (q ^ (s + 1)) (ZMod 2) := by
  let : Fact (Irreducible g) := ⟨hg⟩
  let : NeZero ((q ^ (s + 1) : ℕ) : ZMod 2) :=
    ⟨oddPrimePower_cast_ne_zero q (s + 1) hq hq2⟩
  let : NeZero ((q ^ (s + 1) : ℕ) : AdjoinRoot g) :=
    NeZero.of_injective (algebraMap (ZMod 2) (AdjoinRoot g)).injective
  have hp := lifted_root_primitive f g q s hq hq2 hs hg hf hd
  have hr := isRoot_cyclotomic_iff.mpr hp
  have hz : aeval (AdjoinRoot.root g) (cyclotomic (q ^ (s + 1)) (ZMod 2)) = 0 := by
    rw [aeval_def, ← eval_map, Polynomial.map_cyclotomic]
    exact hr
  simpa only [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero] using hz

/-- Every substitution queried by the auxiliary loop is squarefree. -/
theorem squarefree_comp_power_of_dvd_cyclotomic (f : Polynomial (ZMod 2)) (q s : ℕ)
    (hq : q.Prime) (hq2 : q ≠ 2) (hf : f ∣ cyclotomic (q ^ s) (ZMod 2)) :
    Squarefree (f.comp (X ^ q)) := by
  have hd := hf.trans (cyclotomic.dvd_X_pow_sub_one (q ^ s) (ZMod 2))
  have hc := map_dvd (compRingHom (X ^ q)) hd
  have hdiv : f.comp (X ^ q) ∣ X ^ (q ^ (s + 1)) - 1 := by
    simpa only [coe_compRingHom_apply, sub_comp, pow_comp, X_comp, one_comp,
      ← pow_mul, pow_succ'] using hc
  exact ((X_pow_sub_one_separable_iff.mpr
    (oddPrimePower_cast_ne_zero q (s + 1) hq hq2)).of_dvd hdiv).squarefree

end MIPRE.LowDegree.BinaryPolynomial
