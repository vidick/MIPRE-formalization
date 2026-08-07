/-
Copyright (c) 2026 Sean Perazzolo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Perazzolo
-/
import MIPRE.LCS.Basic
import MIPRE.LCS.Observable
import Mathlib.Algebra.Star.Module

/-!
# Observable-based Strategy for LCS Games

This module defines the data structure for a strategy in a Linear Constraint System (LCS)
game using the observable formalism. In this formalism, players choose observables
(self-adjoint involutive operators) instead of projectors.

## Key Definitions
- `ObservableStrategy`: The data representing an observable strategy, including:
  - `alice_obs`, `bob_obs`: The observables for Alice and Bob.
  - `sameEquation_comm`: The local commutativity of Alice's observables within an equation.
  - `alice_bob_commute`: The global commutativity between Alice's and Bob's observables.
-/

namespace MIPRE.LCS

open scoped BigOperators


structure ObservableStrategy
  (R : Type*) [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  (G : LCSLayout) where
  alice_obs : Fin G.s → R
  bob_obs : Fin G.s -> R
  alice_observable : ∀ j, IsObservable (alice_obs j)
  bob_observable : ∀ j, IsObservable (bob_obs j)
  sameEquation_comm :
    ∀ i, Pairwise (fun j k : G.V i => Commute (alice_obs j.1) (alice_obs k.1))
  alice_bob_commute :
    ∀ j k, Commute (alice_obs j) (bob_obs k)

open Matrix
open Kronecker

def bipartiteAliceLift {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ :=
  M ⊗ₖ (1 : Matrix n n ℂ)

def bipartiteBobLift {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ :=
  (1 : Matrix n n ℂ) ⊗ₖ M

lemma bipartiteAliceLift_observable {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (h : IsObservable M) : IsObservable (bipartiteAliceLift M) where
  involutive := by
    change (M ⊗ₖ (1 : Matrix n n ℂ)) * (M ⊗ₖ (1 : Matrix n n ℂ)) = 1
    rw [← mul_kronecker_mul, h.involutive, mul_one, one_kronecker_one]
  self_adjoint := by
    change (M ⊗ₖ (1 : Matrix n n ℂ))ᴴ = M ⊗ₖ 1
    have h1 : (1 : Matrix n n ℂ)ᴴ = 1 := by exact Matrix.conjTranspose_one
    have hM_ct : Mᴴ = M := by simpa [star_eq_conjTranspose] using h.self_adjoint
    rw [conjTranspose_kronecker, hM_ct, h1]

lemma bipartiteBobLift_observable {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (h : IsObservable M) : IsObservable (bipartiteBobLift M) where
  involutive := by
    change ((1 : Matrix n n ℂ) ⊗ₖ M) * ((1 : Matrix n n ℂ) ⊗ₖ M) = 1
    rw [← mul_kronecker_mul, h.involutive, mul_one, one_kronecker_one]
  self_adjoint := by
    change ((1 : Matrix n n ℂ) ⊗ₖ M)ᴴ = 1 ⊗ₖ M
    have h1 : (1 : Matrix n n ℂ)ᴴ = 1 := by exact Matrix.conjTranspose_one
    have hM_ct : Mᴴ = M := by simpa [star_eq_conjTranspose] using h.self_adjoint
    rw [conjTranspose_kronecker, hM_ct, h1]

lemma bipartite_alice_bob_commute {n : Type*} [Fintype n] [DecidableEq n]
    (M N : Matrix n n ℂ) : Commute (bipartiteAliceLift M) (bipartiteBobLift N) := by
  change
    (M ⊗ₖ (1 : Matrix n n ℂ)) * ((1 : Matrix n n ℂ) ⊗ₖ N) =
      ((1 : Matrix n n ℂ) ⊗ₖ N) * (M ⊗ₖ (1 : Matrix n n ℂ))
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, mul_one, one_mul, mul_one, one_mul]

lemma bipartiteAliceLift_commute {n : Type*} [Fintype n] [DecidableEq n]
    {M N : Matrix n n ℂ} (h : Commute M N) :
    Commute (bipartiteAliceLift M) (bipartiteAliceLift N) := by
  change
    (M ⊗ₖ (1 : Matrix n n ℂ)) * (N ⊗ₖ (1 : Matrix n n ℂ)) =
      (N ⊗ₖ (1 : Matrix n n ℂ)) * (M ⊗ₖ (1 : Matrix n n ℂ))
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, h]

structure BipartiteObservableStrategy
    (n : Type*) [Fintype n] [DecidableEq n]
    (G : LCSLayout) where
  obs : Fin G.s → Matrix n n ℂ
  is_observable : ∀ j, IsObservable (obs j)
  sameEquation_comm :
    ∀ i, Pairwise (fun j k : G.V i => Commute (obs j.1) (obs k.1))

namespace BipartiteObservableStrategy

noncomputable def toObservableStrategy
    {n : Type*} [Fintype n] [DecidableEq n] {G : LCSLayout}
    (strat : BipartiteObservableStrategy n G) :
    ObservableStrategy (Matrix (n × n) (n × n) ℂ) G where
  alice_obs := fun j => bipartiteAliceLift (strat.obs j)
  bob_obs := fun j => bipartiteBobLift (strat.obs j)
  alice_observable := fun j => bipartiteAliceLift_observable (strat.is_observable j)
  bob_observable := fun j => bipartiteBobLift_observable (strat.is_observable j)
  sameEquation_comm := fun i => by
    intro a b hab
    exact bipartiteAliceLift_commute (strat.sameEquation_comm i hab)
  alice_bob_commute := fun j k => bipartite_alice_bob_commute (strat.obs j) (strat.obs k)

@[simp] lemma alice_obs_eq
    {n : Type*} [Fintype n] [DecidableEq n] {G : LCSLayout}
    (strat : BipartiteObservableStrategy n G) (j : Fin G.s) :
    strat.toObservableStrategy.alice_obs j = bipartiteAliceLift (strat.obs j) :=
  rfl

@[simp] lemma bob_obs_eq
    {n : Type*} [Fintype n] [DecidableEq n] {G : LCSLayout}
    (strat : BipartiteObservableStrategy n G) (j : Fin G.s) :
    strat.toObservableStrategy.bob_obs j = bipartiteBobLift (strat.obs j) :=
  rfl

@[simp] lemma alice_observable_eq
    {n : Type*} [Fintype n] [DecidableEq n] {G : LCSLayout}
    (strat : BipartiteObservableStrategy n G) (j : Fin G.s) :
    strat.toObservableStrategy.alice_observable j =
      bipartiteAliceLift_observable (strat.is_observable j) :=
  rfl

@[simp] lemma bob_observable_eq
    {n : Type*} [Fintype n] [DecidableEq n] {G : LCSLayout}
    (strat : BipartiteObservableStrategy n G) (j : Fin G.s) :
    strat.toObservableStrategy.bob_observable j =
      bipartiteBobLift_observable (strat.is_observable j) :=
  rfl

@[simp] lemma sameEquation_comm_eq
    {n : Type*} [Fintype n] [DecidableEq n] {G : LCSLayout}
    (strat : BipartiteObservableStrategy n G) (i : Fin G.r)
    (j k : G.V i) (hjk : j ≠ k) :
    strat.toObservableStrategy.sameEquation_comm i hjk =
      bipartiteAliceLift_commute (strat.sameEquation_comm i hjk) :=
  rfl

end BipartiteObservableStrategy

end MIPRE.LCS
