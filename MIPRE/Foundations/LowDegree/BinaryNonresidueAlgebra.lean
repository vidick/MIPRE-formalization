/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryCyclotomicSeed
import Mathlib.FieldTheory.Minpoly.Finite

/-! # Algebraic progress and stopping criteria for auxiliary root lifting -/

namespace MIPRE.LowDegree.BinaryPolynomial

open Polynomial

/-- Extracting one more prime root increases its prime-power order by exactly one power. -/
theorem primitiveRoot_of_prime_power_root {M : Type*} [CommMonoid M]
    (x : M) (q s : ℕ) (hq : q.Prime) (hs : 0 < s)
    (hx : IsPrimitiveRoot (x ^ q) (q ^ s)) : IsPrimitiveRoot x (q ^ (s + 1)) := by
  have hd : q ^ s ∣ orderOf x := by
    rw [hx.eq_orderOf]
    exact orderOf_pow_dvd q
  have hqdiv : q ∣ orderOf x := (dvd_pow_self q hs.ne').trans hd
  have horder : orderOf x / q = q ^ s := by
    rw [← orderOf_pow_of_dvd hq.ne_zero hqdiv]
    exact hx.eq_orderOf.symm
  apply IsPrimitiveRoot.iff_orderOf.mpr
  rw [pow_succ, ← horder, Nat.div_mul_cancel hqdiv]

/-- An irreducible monic polynomial cannot have a root in a smaller-dimensional extension. -/
theorem aeval_ne_zero_of_finrank_lt {F K : Type*} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] (g : Polynomial F) (hg : g.Monic) (hi : Irreducible g)
    (hd : Module.finrank F K < g.natDegree) (x : K) : aeval x g ≠ 0 := by
  intro hx
  have he := minpoly.eq_of_irreducible_of_monic hi hx hg
  rw [he] at hd
  exact (not_lt_of_ge (minpoly.natDegree_le (A := F) x)) hd

/-- Irreducibility of the substituted polynomial certifies a nonresidue at the old root.
This is the soundness of the executable singleton-factor stopping test. -/
theorem nonresidue_of_irreducible_comp {F K : Type*} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] (f : Polynomial F) (hf : f.Monic)
    (hd : Module.finrank F K = f.natDegree) (hp : 0 < f.natDegree)
    (q : ℕ) (hq : 1 < q) (a : K) (ha : aeval a f = 0)
    (hi : Irreducible (f.comp (X ^ q))) : ∀ b : K, b ^ q ≠ a := by
  intro b hb
  have hq0 : q ≠ 0 := by omega
  have hm : (f.comp (X ^ q)).Monic := hf.comp (monic_X.pow q) (by simpa using hq0)
  have hdeg : Module.finrank F K < (f.comp (X ^ q)).natDegree := by
    rw [hd, natDegree_comp, natDegree_X_pow]
    nlinarith
  apply aeval_ne_zero_of_finrank_lt (f.comp (X ^ q)) hm hi hdeg b
  rw [aeval_def, eval₂_comp]
  simpa only [eval₂_pow, eval₂_X, hb, ← aeval_def] using ha

end MIPRE.LowDegree.BinaryPolynomial
