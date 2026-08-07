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
  - `aliceObs`, `bobObs`: The observables for Alice and Bob.
  - `sameEquation_comm`: The local commutativity of Alice's observables within an equation.
  - `alice_bob_commute`: The global commutativity between Alice's and Bob's observables.
-/

namespace MIPRE.LCS



/-- An observable-based strategy for the LCS layout `G`: Alice and Bob each assign a
binary observable to every variable, Alice's observables commute within each equation,
and every observable of Alice commutes with every observable of Bob. -/
structure ObservableStrategy
  (R : Type*) [Ring R] [StarRing R]
  (G : Layout) where
  /-- Alice's observable for each variable. -/
  aliceObs : Fin G.s → R
  /-- Bob's observable for each variable. -/
  bobObs : Fin G.s → R
  /-- Alice's operators are observables. -/
  alice_isObservable : ∀ j, IsObservable (aliceObs j)
  /-- Bob's operators are observables. -/
  bob_isObservable : ∀ j, IsObservable (bobObs j)
  /-- Alice's observables commute within each equation. -/
  sameEquation_comm :
    ∀ i, Pairwise (fun j k : G.V i ↦ Commute (aliceObs j.1) (aliceObs k.1))
  /-- Every observable of Alice commutes with every observable of Bob. -/
  alice_bob_commute :
    ∀ j k, Commute (aliceObs j) (bobObs k)

open Matrix
open scoped Kronecker

/-- Alice's side of the bipartite lift, `M ↦ M ⊗ 1`. -/
def bipartiteAliceLift {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ :=
  M ⊗ₖ (1 : Matrix n n ℂ)

/-- Bob's side of the bipartite lift, `M ↦ 1 ⊗ M`. -/
def bipartiteBobLift {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ :=
  (1 : Matrix n n ℂ) ⊗ₖ M

lemma isObservable_bipartiteAliceLift {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (h : IsObservable M) : IsObservable (bipartiteAliceLift M) where
  involutive := by
    change (M ⊗ₖ (1 : Matrix n n ℂ)) * (M ⊗ₖ (1 : Matrix n n ℂ)) = 1
    rw [← mul_kronecker_mul, h.involutive, mul_one, one_kronecker_one]
  self_adjoint := by
    change (M ⊗ₖ (1 : Matrix n n ℂ))ᴴ = M ⊗ₖ 1
    have h1 : (1 : Matrix n n ℂ)ᴴ = 1 := by exact Matrix.conjTranspose_one
    have hM_ct : Mᴴ = M := by simpa [star_eq_conjTranspose] using h.self_adjoint
    rw [conjTranspose_kronecker, hM_ct, h1]

lemma isObservable_bipartiteBobLift {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (h : IsObservable M) : IsObservable (bipartiteBobLift M) where
  involutive := by
    change ((1 : Matrix n n ℂ) ⊗ₖ M) * ((1 : Matrix n n ℂ) ⊗ₖ M) = 1
    rw [← mul_kronecker_mul, h.involutive, mul_one, one_kronecker_one]
  self_adjoint := by
    change ((1 : Matrix n n ℂ) ⊗ₖ M)ᴴ = 1 ⊗ₖ M
    have h1 : (1 : Matrix n n ℂ)ᴴ = 1 := by exact Matrix.conjTranspose_one
    have hM_ct : Mᴴ = M := by simpa [star_eq_conjTranspose] using h.self_adjoint
    rw [conjTranspose_kronecker, hM_ct, h1]

lemma bipartiteAliceLift_commute_bipartiteBobLift {n : Type*} [Fintype n] [DecidableEq n]
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

/-- A bipartite observable strategy: a single grid of observables on `ℂ^n`, commuting
within each equation, which both players use through the Kronecker lifts `M ⊗ 1` and
`1 ⊗ M` (see `toObservableStrategy`). -/
structure BipartiteObservableStrategy
    (n : Type*) [Fintype n] [DecidableEq n]
    (G : Layout) where
  /-- The grid of observables, one per variable. -/
  obs : Fin G.s → Matrix n n ℂ
  /-- Each grid entry is an observable. -/
  isObservable : ∀ j, IsObservable (obs j)
  /-- Grid observables commute within each equation. -/
  sameEquation_comm :
    ∀ i, Pairwise (fun j k : G.V i ↦ Commute (obs j.1) (obs k.1))

namespace BipartiteObservableStrategy

/-- The observable strategy on `ℂ^n ⊗ ℂ^n` induced by a bipartite strategy: Alice plays
`M ⊗ 1` and Bob plays `1 ⊗ M`. -/
noncomputable def toObservableStrategy
    {n : Type*} [Fintype n] [DecidableEq n] {G : Layout}
    (strat : BipartiteObservableStrategy n G) :
    ObservableStrategy (Matrix (n × n) (n × n) ℂ) G where
  aliceObs := fun j ↦ bipartiteAliceLift (strat.obs j)
  bobObs := fun j ↦ bipartiteBobLift (strat.obs j)
  alice_isObservable := fun j ↦ isObservable_bipartiteAliceLift (strat.isObservable j)
  bob_isObservable := fun j ↦ isObservable_bipartiteBobLift (strat.isObservable j)
  sameEquation_comm := fun i ↦ by
    intro a b hab
    exact bipartiteAliceLift_commute (strat.sameEquation_comm i hab)
  alice_bob_commute := fun j k ↦
    bipartiteAliceLift_commute_bipartiteBobLift (strat.obs j) (strat.obs k)

@[simp] lemma toObservableStrategy_aliceObs
    {n : Type*} [Fintype n] [DecidableEq n] {G : Layout}
    (strat : BipartiteObservableStrategy n G) (j : Fin G.s) :
    strat.toObservableStrategy.aliceObs j = bipartiteAliceLift (strat.obs j) :=
  rfl

@[simp] lemma toObservableStrategy_bobObs
    {n : Type*} [Fintype n] [DecidableEq n] {G : Layout}
    (strat : BipartiteObservableStrategy n G) (j : Fin G.s) :
    strat.toObservableStrategy.bobObs j = bipartiteBobLift (strat.obs j) :=
  rfl

end BipartiteObservableStrategy

end MIPRE.LCS
