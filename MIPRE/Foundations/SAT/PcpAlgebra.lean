/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.ZeroBasis
import MIPRE.Foundations.LowDegree.SchwartzZippel

/-!
# The algebraic tests of the classical PCP

The formula test and Boolean-cube zero test from `thm:pcp-decider`. These lemmas
concern polynomials and their evaluations. Circuit padding, the embedding of the
five answer blocks, and the verifier's ambient program are separate obligations.
-/

noncomputable section

namespace MIPRE.SAT.PcpAlgebra

open Finset MvPolynomial LowDegree

variable {F : Type*} [Field F] {m : ℕ}

/-- The constraint polynomial: a clause is violated exactly when all five factors
are nonzero on the Boolean cube and its describing formula accepts. -/
def constraint (φ : MvPolynomial (Fin m) F) (g : Fin 5 → MvPolynomial (Fin m) F)
    (sign : Fin 5 → Fin m) : MvPolynomial (Fin m) F :=
  φ * ∏ i, (g i - X (sign i))

/-- The polynomial reconstructed from the claimed zero-basis certificates. -/
def zeroCombination (c : Fin m → MvPolynomial (Fin m) F) : MvPolynomial (Fin m) F :=
  ∑ i, c i * cubeZero i

@[simp] theorem eval_zeroCombination_cube (c : Fin m → MvPolynomial (Fin m) F)
    (y : Fin m → Bool) : eval (pt y) (zeroCombination c) = 0 := by
  simp [zeroCombination]

/-- The two equalities tested by the algebraic verifier at one point. -/
def Accepts (φ : MvPolynomial (Fin m) F) (g : Fin 5 → MvPolynomial (Fin m) F)
    (sign : Fin 5 → Fin m) (c₀ : MvPolynomial (Fin m) F)
    (c : Fin m → MvPolynomial (Fin m) F) (z : Fin m → F) : Prop :=
  eval z c₀ = eval z (constraint φ g sign) ∧ eval z c₀ = eval z (zeroCombination c)

/-- Completeness of both algebraic tests, including the certificate degree bound. -/
theorem completeness (φ : MvPolynomial (Fin m) F) (g : Fin 5 → MvPolynomial (Fin m) F)
    (sign : Fin 5 → Fin m) {d : ℕ}
    (hdeg : ∀ j, (constraint φ g sign).degreeOf j ≤ d)
    (hzero : ∀ y : Fin m → Bool, eval (pt y) (constraint φ g sign) = 0) :
    ∃ c : Fin m → MvPolynomial (Fin m) F,
      (∀ i j, (c i).degreeOf j ≤ d) ∧
      ∀ z, Accepts φ g sign (constraint φ g sign) c z := by
  obtain ⟨c, hc, hd⟩ := exists_zero_basis _ hdeg hzero
  refine ⟨c, hd, fun z => ⟨rfl, ?_⟩⟩
  exact congrArg (eval z) hc

/-- The conservative individual-degree bound used in the source's soundness proof.
It does not rely on disjointness of the five blocks. -/
theorem degreeOf_constraint_le (φ : MvPolynomial (Fin m) F)
    (g : Fin 5 → MvPolynomial (Fin m) F) (sign : Fin 5 → Fin m) {d : ℕ}
    (hφ : ∀ j, φ.degreeOf j ≤ 6) (hg : ∀ i j, (g i).degreeOf j ≤ d) (j : Fin m) :
    (constraint φ g sign).degreeOf j ≤ 6 + 5 * max d 1 := by
  apply (degreeOf_mul_le j _ _).trans
  apply Nat.add_le_add (hφ j)
  apply (degreeOf_prod_le j univ _).trans
  calc
    (∑ i : Fin 5, (g i - X (sign i)).degreeOf j) ≤ ∑ _i : Fin 5, max d 1 := by
      apply Finset.sum_le_sum
      intro i _
      apply (degreeOf_sub_le j _ _).trans
      apply max_le_max (hg i j)
      by_cases h : j = sign i
      · simp [h]
      · simp [degreeOf_X_of_ne h]
    _ = 5 * max d 1 := by simp

theorem degreeOf_zeroCombination_le (c : Fin m → MvPolynomial (Fin m) F) {d : ℕ}
    (hc : ∀ i j, (c i).degreeOf j ≤ d) (j : Fin m) :
    (zeroCombination c).degreeOf j ≤ d + 2 := by
  apply (degreeOf_sum_le j univ _).trans
  apply Finset.sup_le
  intro i _
  apply (degreeOf_mul_le j _ _).trans
  apply Nat.add_le_add (hc i j)
  have hx : (X i : MvPolynomial (Fin m) F).degreeOf j ≤ 1 := by
    by_cases h : j = i
    · simp [h]
    · simp [degreeOf_X_of_ne h]
  exact (degreeOf_mul_le j _ _).trans
    (Nat.add_le_add hx ((degreeOf_sub_le j 1 (X i)).trans (by simpa using hx)))

/-- Soundness first forces both tested polynomial identities. -/
theorem identities_of_majority [Fintype F] [DecidableEq F]
    (φ : MvPolynomial (Fin m) F) (g : Fin 5 → MvPolynomial (Fin m) F)
    (sign : Fin 5 → Fin m) (c₀ : MvPolynomial (Fin m) F)
    (c : Fin m → MvPolynomial (Fin m) F) {d : ℕ}
    (hφ : ∀ j, φ.degreeOf j ≤ 6) (hg : ∀ i j, (g i).degreeOf j ≤ d)
    (hc₀ : ∀ j, c₀.degreeOf j ≤ d) (hc : ∀ i j, (c i).degreeOf j ≤ d)
    (hq : 2 * (m * (6 + 5 * max d 1)) ≤ Fintype.card F)
    (S : Finset (Fin m → F)) (hS : ∀ z ∈ S, Accepts φ g sign c₀ c z)
    (hmajority : Fintype.card F ^ m < 2 * S.card) :
    c₀ = constraint φ g sign ∧ c₀ = zeroCombination c := by
  have hd : d ≤ 6 + 5 * max d 1 := by have := le_max_left d 1; omega
  have hd' : d + 2 ≤ 6 + 5 * max d 1 := by have := le_max_left d 1; omega
  constructor
  · exact eq_of_majority_subset (fun j => (hc₀ j).trans hd)
      (degreeOf_constraint_le φ g sign hφ hg) hq S (fun z hz => (hS z hz).1) hmajority
  · exact eq_of_majority_subset (fun j => (hc₀ j).trans hd)
      (fun j => (degreeOf_zeroCombination_le c hc j).trans hd') hq S
      (fun z hz => (hS z hz).2) hmajority

/-- On every described Boolean clause, an identity certificate forces one answer
polynomial to match its sign. This is the clause-satisfaction step of decoding. -/
theorem clause_satisfied_of_identities
    (φ : MvPolynomial (Fin m) F) (g : Fin 5 → MvPolynomial (Fin m) F)
    (sign : Fin 5 → Fin m) (c : Fin m → MvPolynomial (Fin m) F)
    (h : constraint φ g sign = zeroCombination c) (y : Fin m → Bool)
    (hφ : eval (pt y) φ = 1) :
    ∃ i : Fin 5, eval (pt y) (g i) = ofBool (y (sign i)) := by
  have hz : eval (pt y) (constraint φ g sign) = 0 := by rw [h]; simp
  simp only [constraint, map_mul, map_prod, map_sub, eval_X, hφ, one_mul] at hz
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hz
  exact ⟨i, sub_eq_zero.mp hi⟩

/-- The satisfying literal survives Boolean decoding, including when other answer
evaluations at the same point are not Boolean. -/
theorem clause_decoded_of_identities [DecidableEq F]
    (φ : MvPolynomial (Fin m) F) (g : Fin 5 → MvPolynomial (Fin m) F)
    (sign : Fin 5 → Fin m) (c : Fin m → MvPolynomial (Fin m) F)
    (h : constraint φ g sign = zeroCombination c) (y : Fin m → Bool)
    (hφ : eval (pt y) φ = 1) :
    ∃ i : Fin 5, coded (g i) y = ofBool (y (sign i)) := by
  obtain ⟨i, hi⟩ := clause_satisfied_of_identities φ g sign c h y hφ
  exact ⟨i, coded_eq_of_eval_eq_ofBool (g i) y _ hi⟩

end MIPRE.SAT.PcpAlgebra

end
