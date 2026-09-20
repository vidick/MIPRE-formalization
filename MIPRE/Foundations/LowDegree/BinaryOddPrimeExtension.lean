/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryNonresidueCorrectness

/-! # Exact root degrees in the flat odd-prime-power extension -/

namespace MIPRE.LowDegree.BinaryPolynomial

open Polynomial

/-- The flat extension root has the full specified minimal polynomial. -/
theorem flat_prime_power_minpoly {F : Type*} [Field F]
    (f : Polynomial F) (hf : f.Monic) (hi : Irreducible f)
    (q e : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (hn : ∀ b : AdjoinRoot f, b ^ q ≠ AdjoinRoot.root f) :
    minpoly F (AdjoinRoot.root (f.comp (X ^ (q ^ e)))) = f.comp (X ^ (q ^ e)) := by
  have hm : (f.comp (X ^ (q ^ e))).Monic :=
    hf.comp (monic_X.pow _) (by simp [hq.ne_zero])
  let : Fact (Irreducible (f.comp (X ^ (q ^ e)))) :=
    ⟨irreducible_comp_prime_pow_of_nonresidue f hf hi q e hq hq2 hn⟩
  rw [AdjoinRoot.minpoly_root hm.ne_zero, hm.leadingCoeff, inv_one, C_1, mul_one]

/-- Raising the flat extension generator to the base prime removes exactly one
prime-power level from its minimal polynomial. -/
theorem flat_prime_power_root_pow_minpoly {F : Type*} [Field F]
    (f : Polynomial F) (hf : f.Monic) (hi : Irreducible f)
    (q e : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (hn : ∀ b : AdjoinRoot f, b ^ q ≠ AdjoinRoot.root f) :
    minpoly F (AdjoinRoot.root (f.comp (X ^ (q ^ (e + 1)))) ^ q) =
      f.comp (X ^ (q ^ e)) := by
  let h := f.comp (X ^ (q ^ (e + 1)))
  let g := f.comp (X ^ (q ^ e))
  have hh : Irreducible h := irreducible_comp_prime_pow_of_nonresidue f hf hi q (e + 1) hq hq2 hn
  have hg : Irreducible g := irreducible_comp_prime_pow_of_nonresidue f hf hi q e hq hq2 hn
  let : Fact (Irreducible h) := ⟨hh⟩
  have hgm : g.Monic := hf.comp (monic_X.pow _) (by simp [hq.ne_zero])
  have hcomp : g.comp (X ^ q) = h := by
    simp only [g, h, comp_assoc, pow_comp, X_comp, ← pow_mul, pow_succ']
  have hz : aeval (AdjoinRoot.root h ^ q) g = 0 := by
    have hz' : aeval (AdjoinRoot.root h) (g.comp (X ^ q)) = 0 := by rw [hcomp]; simp
    simpa only [aeval_def, eval₂_comp, eval₂_pow, eval₂_X] using hz'
  exact (minpoly.eq_of_irreducible_of_monic hg hz hgm).symm

/-- The top root raised to the requested extension degree has the original minimal polynomial. -/
theorem flat_prime_power_root_pow_all_minpoly {F : Type*} [Field F]
    (f : Polynomial F) (hf : f.Monic) (hi : Irreducible f)
    (q e : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (hn : ∀ b : AdjoinRoot f, b ^ q ≠ AdjoinRoot.root f) :
    minpoly F (AdjoinRoot.root (f.comp (X ^ (q ^ e))) ^ (q ^ e)) = f := by
  let h := f.comp (X ^ (q ^ e))
  let : Fact (Irreducible h) :=
    ⟨irreducible_comp_prime_pow_of_nonresidue f hf hi q e hq hq2 hn⟩
  have hz : aeval (AdjoinRoot.root h ^ (q ^ e)) f = 0 := by
    have hz' : aeval (AdjoinRoot.root h) h = 0 := by simp
    simpa only [h, aeval_def, eval₂_comp, eval₂_pow, eval₂_X] using hz'
  exact (minpoly.eq_of_irreducible_of_monic hi hz hf).symm

end MIPRE.LowDegree.BinaryPolynomial
