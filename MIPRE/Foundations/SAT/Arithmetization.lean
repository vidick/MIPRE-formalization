/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.SAT.Formula
import MIPRE.Foundations.LowDegree.Encoding

/-!
# Arithmetization of Boolean formulas

The mathematical part of the paper's `lem:formula-arithmetization`: replace
conjunction by multiplication, disjunction by `1 - (1 - f) * (1 - g)`, and
negation by `1 - f`. Each variable's degree is bounded by its occurrence count.
The evaluator and its cost in an effective finite-field representation are separate.
-/

noncomputable section

namespace MIPRE.SAT.Fml

open MvPolynomial LowDegree

variable {F σ : Type*} [CommRing F] [DecidableEq σ]

/-- Arithmetize after assigning a polynomial variable to every input index. -/
def arith (ρ : ℕ → σ) : Fml → MvPolynomial σ F
  | .inp i => X (ρ i)
  | .const b => C (ofBool b)
  | .and f g => arith ρ f * arith ρ g
  | .or f g => 1 - (1 - arith ρ f) * (1 - arith ρ g)
  | .not f => 1 - arith ρ f

/-- The occurrence count, including collisions in the variable assignment `ρ`. -/
def occurrences (ρ : ℕ → σ) (j : σ) : Fml → ℕ
  | .inp i => if j = ρ i then 1 else 0
  | .const _ => 0
  | .and f g => occurrences ρ j f + occurrences ρ j g
  | .or f g => occurrences ρ j f + occurrences ρ j g
  | .not f => occurrences ρ j f

omit [DecidableEq σ] in
/-- On Boolean inputs, arithmetization agrees with the original formula. -/
theorem eval_arith (ρ : ℕ → σ) (f : Fml) (x : σ → Bool) :
    MvPolynomial.eval (fun j => (ofBool (x j) : F)) (arith ρ f) =
      ofBool (f.eval (fun i => x (ρ i))) := by
  induction f with
  | inp i => simp [arith, Fml.eval]
  | const b => simp [arith, Fml.eval]
  | and f g hf hg =>
    simp only [arith, map_mul, hf, hg, Fml.eval]
    cases f.eval (fun i => x (ρ i)) <;> cases g.eval (fun i => x (ρ i)) <;> simp [ofBool]
  | or f g hf hg =>
    simp only [arith, map_sub, map_one, map_mul, hf, hg, Fml.eval]
    cases f.eval (fun i => x (ρ i)) <;> cases g.eval (fun i => x (ρ i)) <;> simp [ofBool]
  | not f hf =>
    simp only [arith, map_sub, map_one, hf, Fml.eval]
    cases f.eval (fun i => x (ρ i)) <;> simp [ofBool]

/-- The degree in each variable is at most its number of syntactic occurrences. -/
theorem degreeOf_arith_le [Nontrivial F] (ρ : ℕ → σ) (f : Fml) (j : σ) :
    (arith (F := F) ρ f).degreeOf j ≤ occurrences ρ j f := by
  have hnot (p : MvPolynomial σ F) : (1 - p).degreeOf j ≤ p.degreeOf j := by
    simpa using degreeOf_sub_le j 1 p
  induction f with
  | inp i =>
    by_cases h : j = ρ i
    · simp [arith, occurrences, h]
    · simp [arith, occurrences, h, degreeOf_X_of_ne h]
  | const b => simp [arith, occurrences]
  | and f g hf hg => exact (degreeOf_mul_le j _ _).trans (Nat.add_le_add hf hg)
  | or f g hf hg =>
    exact (hnot _).trans ((degreeOf_mul_le j _ _).trans
      (Nat.add_le_add ((hnot _).trans hf) ((hnot _).trans hg)))
  | not f hf => exact (hnot _).trans hf

/-- A syntactic occurrence bound supplies the individual-degree bound. -/
theorem degreeOf_arith_le_of_occurrences [Nontrivial F] (ρ : ℕ → σ) (f : Fml) {d : ℕ}
    (h : ∀ j, occurrences ρ j f ≤ d) :
    ∀ j, (arith (F := F) ρ f).degreeOf j ≤ d :=
  fun j => (degreeOf_arith_le ρ f j).trans (h j)

end MIPRE.SAT.Fml

end
