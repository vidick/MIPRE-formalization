/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryNonresidueAlgebra
import Mathlib.FieldTheory.KummerExtension

/-! # Irreducibility of the flat odd-prime-power extension -/

namespace MIPRE.LowDegree.BinaryPolynomial

open Polynomial IntermediateField

/-- A nonresidue at the specified quotient root suffices for every odd-prime-power
composition, through the canonical isomorphism with any other simple root field. -/
theorem irreducible_comp_prime_pow_of_nonresidue {F : Type*} [Field F]
    (f : Polynomial F) (hf : f.Monic) (hi : Irreducible f)
    (q s : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (hn : ∀ b : AdjoinRoot f, b ^ q ≠ AdjoinRoot.root f) :
    Irreducible (f.comp (X ^ (q ^ s))) := by
  apply irreducible_comp hf (monic_X.pow (q ^ s)) hi
  intro E _ _ x hx
  subst f
  have hxi : IsIntegral F x := minpoly.ne_zero_iff.mp hi.ne_zero
  let e := adjoinRootEquivAdjoin F hxi
  have hgen : ∀ b : F⟮x⟯, b ^ q ≠ AdjoinSimple.gen F x := by
    intro b hb
    apply hn (e.symm b)
    rw [← map_pow, hb]
    exact adjoinRootEquivAdjoin_symm_apply_gen F hxi
  simpa only [Polynomial.map_pow, map_X] using
    X_pow_sub_C_irreducible_of_prime_pow hq hq2 s hgen

/-- The next substitution is reducible only if the current root is a residue. -/
theorem residue_of_not_irreducible_comp {F : Type*} [Field F]
    (f : Polynomial F) (hf : f.Monic) (hi : Irreducible f)
    (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (hred : ¬ Irreducible (f.comp (X ^ q))) :
    ∃ b : AdjoinRoot f, b ^ q = AdjoinRoot.root f := by
  by_contra h
  have hn : ∀ b : AdjoinRoot f, b ^ q ≠ AdjoinRoot.root f := by simpa using h
  apply hred
  simpa only [pow_one] using irreducible_comp_prime_pow_of_nonresidue f hf hi q 1 hq hq2 hn

end MIPRE.LowDegree.BinaryPolynomial
