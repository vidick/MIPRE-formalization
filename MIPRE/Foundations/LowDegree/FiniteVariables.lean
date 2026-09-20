/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.Encoding
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Restricting polynomials to an embedded set of variables

Setting all other variables to zero preserves every individual-degree bound.
This lets circuit polynomials be written with natural-number input and gate
indices, then restricted to the exact finite variable count used by the PCP.
-/

noncomputable section

namespace MIPRE.LowDegree

open MvPolynomial
open scoped Classical

variable {σ τ F : Type*} [CommRing F] {f : σ → τ} (hf : Function.Injective f)

/-- Extend values by zero outside an embedded set of coordinates. -/
def extendZero (x : σ → F) (j : τ) : F :=
  if h : j ∈ Set.range f then x ((Equiv.ofInjective f hf).symm ⟨j, h⟩) else 0

@[simp] theorem extendZero_apply (x : σ → F) (i : σ) : extendZero hf x (f i) = x i := by
  simp [extendZero, Equiv.ofInjective_symm_apply]

/-- Evaluation after restriction equals evaluation at the zero extension. -/
theorem eval_killCompl (p : MvPolynomial τ F) (x : σ → F) :
    eval x (killCompl hf p) = eval (extendZero hf x) p := by
  have he : (eval x).comp (killCompl hf).toRingHom = eval (extendZero hf x) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro j
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        killCompl, aeval_X, eval_X, extendZero]
      split <;> simp
  exact RingHom.congr_fun he p

/-- A useful form of restriction correctness: any zero extension agrees. -/
theorem eval_killCompl_eq (p : MvPolynomial τ F) (x : σ → F) (y : τ → F)
    (hxy : ∀ i, y (f i) = x i) (hy : ∀ j, j ∉ Set.range f → y j = 0) :
    eval x (killCompl hf p) = eval y p := by
  rw [eval_killCompl]
  have he : extendZero hf x = y := by
    funext j
    by_cases hj : j ∈ Set.range f
    · obtain ⟨i, rfl⟩ := hj
      rw [extendZero_apply, hxy]
    · simp [extendZero, hj, hy j hj]
  rw [he]

/-- Restriction cannot increase the degree of any retained coordinate. -/
theorem degreeOf_killCompl_le (p : MvPolynomial τ F) (i : σ) :
    (killCompl hf p).degreeOf i ≤ p.degreeOf (f i) := by
  rw [← degreeOf_rename_of_injective hf i]
  simp only [degreeOf_eq_sup]
  exact Finset.sup_mono (support_rename_killCompl_subset hf)

/-- In particular, uniform individual-degree bounds survive restriction. -/
theorem degreeOf_killCompl_le_of_bound (p : MvPolynomial τ F) {d : ℕ}
    (h : ∀ j, p.degreeOf j ≤ d) : ∀ i, (killCompl hf p).degreeOf i ≤ d :=
  fun i => (degreeOf_killCompl_le hf p i).trans (h (f i))

end MIPRE.LowDegree

end
