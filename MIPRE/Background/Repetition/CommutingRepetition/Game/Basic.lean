/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Game/Basic.lean
-/
/-
# Games with [0,1] payoffs and direct repetition

Encoding decision D1 of the formalization plan.
Anchors: 02_preliminaries.tex (definition of a finite two-player one-round
game; direct repetition G^{⊗n} with product acceptance); audit definition
`game`, `direct_repetition`.

The `Game.repeat` construction pattern follows QuantumParallelRepetition.lean
(github.com/openai/ten-proofs, Apache-2.0; see lean/NOTICE), with the Bool
predicate replaced by a [0,1]-valued payoff as the manuscript requires.
-/
import Mathlib

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped BigOperators

/-- A finite two-player one-round game `G = (X, Y, A, B, μ, V)`:
finite nonempty question sets `X, Y` and answer sets `A, B` (nonemptiness is
assumed at the theorems that need it), a probability distribution `μ` on
`X × Y` given by `questionWeight`, and an acceptance function
`payoff = V(a, b | x, y) ∈ [0,1]`.
[02_preliminaries.tex, "Games and direct repetition"; audit def `game`] -/
structure Game (X Y A B : Type*)
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] where
  questionWeight : X → Y → ℝ
  weight_nonneg : ∀ x y, 0 ≤ questionWeight x y
  weight_normalized : (∑ x : X, ∑ y : Y, questionWeight x y) = 1
  payoff : X → Y → A → B → ℝ
  payoff_nonneg : ∀ x y a b, 0 ≤ payoff x y a b
  payoff_le_one : ∀ x y a b, payoff x y a b ≤ 1

namespace Game

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The predicate case: every payoff value is 0 or 1. The manuscript proves
the predicate case first (05_prerounding.tex lines 10–18 standing
assumption; 07_main_theorem.tex sec 7.4 removes it). -/
def IsPredicate (G : Game X Y A B) : Prop :=
  ∀ x y a b, G.payoff x y a b = 0 ∨ G.payoff x y a b = 1

/-- Marginal law of Alice's question. -/
def marginalX (G : Game X Y A B) (x : X) : ℝ :=
  ∑ y : Y, G.questionWeight x y

/-- Marginal law of Bob's question. -/
def marginalY (G : Game X Y A B) (y : Y) : ℝ :=
  ∑ x : X, G.questionWeight x y

theorem marginalX_nonneg (G : Game X Y A B) (x : X) : 0 ≤ G.marginalX x :=
  Finset.sum_nonneg fun y _ => G.weight_nonneg x y

theorem marginalY_nonneg (G : Game X Y A B) (y : Y) : 0 ≤ G.marginalY y :=
  Finset.sum_nonneg fun x _ => G.weight_nonneg x y

theorem marginalX_normalized (G : Game X Y A B) :
    (∑ x : X, G.marginalX x) = 1 := by
  simpa [marginalX] using G.weight_normalized

theorem marginalY_normalized (G : Game X Y A B) :
    (∑ y : Y, G.marginalY y) = 1 := by
  unfold marginalY
  rw [Finset.sum_comm]
  exact G.weight_normalized

/-- Each question weight is at most one (a single term of a normalized
nonnegative sum). -/
theorem questionWeight_le_one (G : Game X Y A B) (x : X) (y : Y) :
    G.questionWeight x y ≤ 1 := by
  calc G.questionWeight x y
      ≤ ∑ y' : Y, G.questionWeight x y' :=
        Finset.single_le_sum (fun y' _ => G.weight_nonneg x y')
          (Finset.mem_univ y)
    _ ≤ ∑ x' : X, ∑ y' : Y, G.questionWeight x' y' :=
        Finset.single_le_sum
          (fun x' _ => Finset.sum_nonneg fun y' _ => G.weight_nonneg x' y')
          (Finset.mem_univ x)
    _ = 1 := G.weight_normalized

/-- Direct `n`-fold repetition `G^{⊗n}`: product question law on
`(Fin n → X) × (Fin n → Y)` and product acceptance
`V^{⊗n}(a^n, b^n | x^n, y^n) = ∏ᵢ V(aᵢ, bᵢ | xᵢ, yᵢ)`.
`n = 0` is a total-function extension outside the paper's `n ≥ 1` scope
(empty products; the main theorem hypothesizes `1 ≤ n`).
[02_preliminaries.tex, eq for V^{⊗n}; audit def `direct_repetition`] -/
def «repeat» (G : Game X Y A B) (n : ℕ) :
    Game (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B) where
  questionWeight xs ys := ∏ i : Fin n, G.questionWeight (xs i) (ys i)
  weight_nonneg xs ys :=
    Finset.prod_nonneg fun i _ => G.weight_nonneg (xs i) (ys i)
  weight_normalized := by
    classical
    calc
      (∑ xs : Fin n → X, ∑ ys : Fin n → Y,
        ∏ i : Fin n, G.questionWeight (xs i) (ys i)) =
          ∑ xs : Fin n → X, ∏ i : Fin n, ∑ y : Y,
            G.questionWeight (xs i) y := by
              apply Finset.sum_congr rfl
              intro xs _
              exact (Fintype.prod_sum
                (fun i : Fin n => fun y : Y => G.questionWeight (xs i) y)).symm
      _ = ∏ _i : Fin n, ∑ x : X, ∑ y : Y,
            G.questionWeight x y := by
              exact (Fintype.prod_sum
                (fun _i : Fin n => fun x : X => ∑ y : Y,
                  G.questionWeight x y)).symm
      _ = 1 := by simp [G.weight_normalized]
  payoff xs ys as bs := ∏ i : Fin n, G.payoff (xs i) (ys i) (as i) (bs i)
  payoff_nonneg xs ys as bs :=
    Finset.prod_nonneg fun i _ => G.payoff_nonneg (xs i) (ys i) (as i) (bs i)
  payoff_le_one xs ys as bs :=
    Finset.prod_le_one
      (fun i _ => G.payoff_nonneg (xs i) (ys i) (as i) (bs i))
      (fun i _ => G.payoff_le_one (xs i) (ys i) (as i) (bs i))

theorem repeat_isPredicate {G : Game X Y A B} (hG : G.IsPredicate) (n : ℕ) :
    (G.«repeat» n).IsPredicate := by
  intro xs ys as bs
  classical
  show (∏ i : Fin n, G.payoff (xs i) (ys i) (as i) (bs i)) = 0 ∨
    (∏ i : Fin n, G.payoff (xs i) (ys i) (as i) (bs i)) = 1
  by_cases h : ∀ i : Fin n, G.payoff (xs i) (ys i) (as i) (bs i) = 1
  · right
    exact Finset.prod_eq_one fun i _ => h i
  · left
    push_neg at h
    obtain ⟨i, hi⟩ := h
    rcases hG (xs i) (ys i) (as i) (bs i) with h0 | h1
    · exact Finset.prod_eq_zero (Finset.mem_univ i) h0
    · exact absurd h1 hi

end Game

end CommutingRepetition
