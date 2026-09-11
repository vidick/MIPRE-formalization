/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import Mathlib
import MIPRE.Foundations.Games

/-!
# Direct parallel repetition of a game

The `n`-fold direct repetition `G^{⊗n}` of a game (blueprint `def:direct-repetition`):
the referee samples `n` independent question pairs, sends the tuples to the players, and
accepts if and only if every coordinate is accepted. The construction is that of the two
vendored developments (`MIPRE/Background/Repetition/`), so that their theorems transfer
without bookkeeping; the repetition of a synchronous game is synchronous.
-/

namespace MIPRE

open scoped BigOperators

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The `n`-fold direct repetition of a game (blueprint `def:direct-repetition`):
product question distribution on `(Fin n → X) × (Fin n → Y)` and the conjunction of the
coordinate predicates. -/
def Game.repeat (G : Game X Y A B) (n : ℕ) :
    Game (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B) where
  μ xs ys := ∏ i : Fin n, G.μ (xs i) (ys i)
  μ_nonneg xs ys := Finset.prod_nonneg fun i _ => G.μ_nonneg (xs i) (ys i)
  μ_sum_one := by
    classical
    calc
      (∑ xs : Fin n → X, ∑ ys : Fin n → Y, ∏ i : Fin n, G.μ (xs i) (ys i)) =
          ∑ xs : Fin n → X, ∏ i : Fin n, ∑ y : Y, G.μ (xs i) y := by
            apply Finset.sum_congr rfl
            intro xs _
            exact (Fintype.prod_sum (fun i : Fin n => fun y : Y => G.μ (xs i) y)).symm
      _ = ∏ _i : Fin n, ∑ x : X, ∑ y : Y, G.μ x y := by
            exact (Fintype.prod_sum
              (fun _i : Fin n => fun x : X => ∑ y : Y, G.μ x y)).symm
      _ = 1 := by simp [G.μ_sum_one]
  D xs ys as bs := decide (∀ i : Fin n, G.D (xs i) (ys i) (as i) (bs i) = true)

/-- The `n`-fold direct repetition of a synchronous game is synchronous: unequal answer
tuples to equal question tuples differ in some coordinate, which is then rejected. -/
def SynchronousGame.repeat [DecidableEq A] (G : SynchronousGame X A) (n : ℕ) :
    SynchronousGame (Fin n → X) (Fin n → A) where
  μ xs ys := ∏ i : Fin n, G.μ (xs i) (ys i)
  μ_nonneg xs ys := Finset.prod_nonneg fun i _ => G.μ_nonneg (xs i) (ys i)
  μ_sum_one := by
    classical
    calc
      (∑ xs : Fin n → X, ∑ ys : Fin n → X, ∏ i : Fin n, G.μ (xs i) (ys i)) =
          ∑ xs : Fin n → X, ∏ i : Fin n, ∑ y : X, G.μ (xs i) y := by
            apply Finset.sum_congr rfl
            intro xs _
            exact (Fintype.prod_sum (fun i : Fin n => fun y : X => G.μ (xs i) y)).symm
      _ = ∏ _i : Fin n, ∑ x : X, ∑ y : X, G.μ x y := by
            exact (Fintype.prod_sum
              (fun _i : Fin n => fun x : X => ∑ y : X, G.μ x y)).symm
      _ = 1 := by simp [G.μ_sum_one]
  D xs ys as bs := decide (∀ i : Fin n, G.D (xs i) (ys i) (as i) (bs i) = true)
  synchronous := by
    intro xs as bs hne
    rw [decide_eq_false_iff_not]
    intro h
    apply hne
    funext i
    by_contra hi
    have hfalse := G.synchronous (xs i) (as i) (bs i) hi
    rw [h i] at hfalse
    exact absurd hfalse (by simp)

/-- The repetition of a synchronous game, viewed as a game, is the repetition of the
underlying game. -/
theorem SynchronousGame.repeat_toGame [DecidableEq A] (G : SynchronousGame X A) (n : ℕ) :
    (G.repeat n).toGame = G.toGame.repeat n :=
  rfl

end MIPRE
