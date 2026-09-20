/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.Encoding
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Tactic.Ring

/-!
# Certificates for polynomials vanishing on the Boolean cube

The paper's `prop:zero-basis`, used in classical PCP completeness. Reduction by
`X i * (1 - X i)` preserves every individual-degree bound. This is stronger than
the total-degree bound in the general combinatorial Nullstellensatz.
-/

noncomputable section

namespace MIPRE.LowDegree

open Finset MvPolynomial

variable {F : Type*} [Field F] {m : ℕ}

/-- The univariate Boolean-cube constraint at coordinate `i`. -/
def cubeZero (i : Fin m) : MvPolynomial (Fin m) F := X i * (1 - X i)

@[simp] theorem eval_cubeZero (i : Fin m) (y : Fin m → Bool) :
    eval (pt y) (cubeZero i : MvPolynomial (Fin m) F) = 0 := by
  cases h : y i <;> simp [cubeZero, pt, ofBool, h]

private theorem degreeOf_divMonomial_le (f : MvPolynomial (Fin m) F)
    (s : Fin m →₀ ℕ) (j : Fin m) :
    (f.divMonomial s).degreeOf j ≤ f.degreeOf j - s j := by
  apply degreeOf_le_iff.mpr
  intro e he
  have he' : s + e ∈ f.support := by
    simpa only [mem_support_iff, coeff_divMonomial] using he
  have h := degreeOf_le_iff.mp (le_refl (f.degreeOf j)) _ he'
  simp only [Finsupp.add_apply] at h
  omega

private theorem degreeOf_modMonomial_le (f : MvPolynomial (Fin m) F)
    (s : Fin m →₀ ℕ) (j : Fin m) :
    (f.modMonomial s).degreeOf j ≤ f.degreeOf j := by
  apply degreeOf_le_iff.mpr
  intro e he
  have hn : ¬ s ≤ e := by
    intro h
    have := coeff_modMonomial_of_le f h
    exact (mem_support_iff.mp he) this
  have he' : e ∈ f.support := by
    simpa only [mem_support_iff, coeff_modMonomial_of_not_le f hn] using he
  exact degreeOf_le_iff.mp (le_refl (f.degreeOf j)) e he'

private theorem degreeOf_mod_square_le_one (f : MvPolynomial (Fin m) F) (i : Fin m) :
    (f.modMonomial (Finsupp.single i 2)).degreeOf i ≤ 1 := by
  apply degreeOf_le_iff.mpr
  intro e he
  by_contra! hn
  have hs : Finsupp.single i 2 ≤ e := Finsupp.single_le_iff.mpr (by omega)
  exact (mem_support_iff.mp he) (coeff_modMonomial_of_le f hs)

/-- Eliminate powers of one variable, without increasing any individual degree. -/
theorem exists_cubeZero_division (f : MvPolynomial (Fin m) F) (i : Fin m) :
    ∃ c r : MvPolynomial (Fin m) F,
      f = c * cubeZero i + r ∧
      (∀ j, c.degreeOf j ≤ f.degreeOf j) ∧
      (∀ j, r.degreeOf j ≤ f.degreeOf j) ∧ r.degreeOf i ≤ 1 := by
  generalize hn : f.degreeOf i = n
  induction n using Nat.strong_induction_on generalizing f with
  | h n ih =>
    by_cases hsmall : f.degreeOf i ≤ 1
    · exact ⟨0, f, by simp, by simp, fun _ => le_rfl, hsmall⟩
    let s : Fin m →₀ ℕ := Finsupp.single i 2
    let q := f.divMonomial s
    let t := f.modMonomial s
    let r₀ := t + q * X i
    have hq (j : Fin m) : q.degreeOf j ≤ f.degreeOf j - s j :=
      degreeOf_divMonomial_le f s j
    have hq' (j : Fin m) : q.degreeOf j ≤ f.degreeOf j := (hq j).trans (Nat.sub_le ..)
    have ht (j : Fin m) : t.degreeOf j ≤ f.degreeOf j := degreeOf_modMonomial_le f s j
    have hti : t.degreeOf i ≤ 1 := degreeOf_mod_square_le_one f i
    have hqi : q.degreeOf i ≤ f.degreeOf i - 2 := by simpa [s] using hq i
    have hr₀i : r₀.degreeOf i < f.degreeOf i := by
      have h := (degreeOf_add_le i t (q * X i)).trans
        (max_le_max hti (degreeOf_mul_X_self i q))
      change r₀.degreeOf i ≤ _ at h
      omega
    have hr₀ (j : Fin m) : r₀.degreeOf j ≤ f.degreeOf j := by
      by_cases hji : j = i
      · subst j; exact hr₀i.le
      · exact (degreeOf_add_le j t (q * X i)).trans
          (max_le (ht j) (by rw [degreeOf_mul_X_of_ne q hji]; exact hq' j))
    have hf : f = -q * cubeZero i + r₀ := by
      have he := divMonomial_add_modMonomial f s
      have hs : (monomial s (1 : F)) = (X i : MvPolynomial (Fin m) F) ^ 2 := by
        simp [s, X_pow_eq_monomial]
      rw [hs] at he
      change X i ^ 2 * q + t = f at he
      rw [← he]
      dsimp [cubeZero, r₀]
      ring
    obtain ⟨c, r, hcr, hc, hr, hri⟩ := ih (r₀.degreeOf i) (by omega) r₀ rfl
    refine ⟨-q + c, r, ?_, ?_, fun j => (hr j).trans (hr₀ j), hri⟩
    · rw [hf, hcr]; ring
    · intro j
      exact (degreeOf_add_le j (-q) c).trans
        (max_le (by simpa using hq' j) ((hc j).trans (hr₀ j)))

/-- Simultaneous reduction in a finite set of coordinates. -/
private theorem exists_cube_remainder (f : MvPolynomial (Fin m) F) (S : Finset (Fin m)) :
    ∃ (c : Fin m → MvPolynomial (Fin m) F) (r : MvPolynomial (Fin m) F),
      f = (∑ i, c i * cubeZero i) + r ∧
      (∀ i j, (c i).degreeOf j ≤ f.degreeOf j) ∧
      (∀ j, r.degreeOf j ≤ f.degreeOf j) ∧ (∀ i ∈ S, r.degreeOf i ≤ 1) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, f, by simp, by simp, fun _ => le_rfl, by simp⟩
  | @insert i S hi ih =>
    obtain ⟨c, r, hf, hc, hr, hS⟩ := ih
    obtain ⟨a, r', ha, had, hrd, hri⟩ := exists_cubeZero_division r i
    let c' := fun j => c j + if j = i then a else 0
    have hsum : (∑ j, c' j * cubeZero j) = (∑ j, c j * cubeZero j) + a * cubeZero i := by
      simp [c', add_mul, Finset.sum_add_distrib, ite_mul]
    refine ⟨c', r', ?_, ?_, fun j => (hrd j).trans (hr j), ?_⟩
    · rw [hsum, hf, ha]; ring
    · intro j l
      apply (degreeOf_add_le l (c j) _).trans
      apply max_le (hc j l)
      split_ifs
      · exact (had l).trans (hr l)
      · simp
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hri
      · exact (hrd j).trans (hS j hj)

/-- **Boolean-cube zero basis**, with individual-degree bounds on every certificate.
The equality is an identity of polynomials, not only an equality of functions. -/
theorem exists_zero_basis (f : MvPolynomial (Fin m) F) {d : ℕ}
    (hd : ∀ i, f.degreeOf i ≤ d) (hf : ∀ y : Fin m → Bool, eval (pt y) f = 0) :
    ∃ c : Fin m → MvPolynomial (Fin m) F,
      f = ∑ i, c i * cubeZero i ∧ ∀ i j, (c i).degreeOf j ≤ d := by
  classical
  obtain ⟨c, r, hfr, hc, _, hr⟩ := exists_cube_remainder f univ
  have heval (y : Fin m → Bool) : eval (pt y) r = 0 := by
    have h := hf y
    rw [hfr, map_add, map_sum] at h
    simpa using h
  have hz : r = 0 := by
    apply eq_zero_of_eval_zero_at_prod_finset r (fun _ => {0, 1})
    · intro i
      have := hr i (mem_univ i)
      simpa using Nat.lt_succ_of_le this
    · intro x hx
      let y : Fin m → Bool := fun i => decide (x i = 1)
      have hxy : pt y = x := by
        funext i
        have h := hx i
        simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with h | h <;> simp [pt, y, ofBool, h]
      simpa [hxy] using heval y
  exact ⟨c, by simpa [hz] using hfr, fun i j => (hc i j).trans (hd j)⟩

end MIPRE.LowDegree

end
