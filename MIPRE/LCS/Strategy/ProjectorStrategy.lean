/-
Copyright (c) 2026 Sean Perazzolo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Perazzolo
-/
import MIPRE.LCS.Basic
import MIPRE.LCS.Common
import MIPRE.LCS.Measurement
import MIPRE.LCS.Observable
import MIPRE.LCS.Strategy.ObservableToProjector

/-!
# Projector-based Strategy for LCS Games

This module defines the standard formalism for LCS game strategies using
projector measurement systems. In this formalism, players' strategies are
represented by families of projectors $\{E_{i,x}\}$ and $\{F_{j,y}\}$.

## Key Definitions
- `ProjectorStrategy`: The core structure representing a projector-based strategy.
- `ProjectorStrategy.aliceObs`, `ProjectorStrategy.bobObs`: Derived observables extracted
  from the projector measurements.

## Key Lemmas
- `ProjectorStrategy.isObservable_aliceObs`, `ProjectorStrategy.isObservable_bobObs`:
  Proves that the derived operators are observables.
- `ProjectorStrategy.aliceObs_commute`, `alice_bob_commute`: Verification of commutation relations.
-/

namespace MIPRE.LCS


variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
variable {G : Layout}

/-- A projector-based strategy for the LCS layout `G`: Alice has one measurement per
equation, with outcomes the local assignments; Bob has one binary measurement per
variable; and every projector of Alice commutes with every projector of Bob. -/
structure ProjectorStrategy
  (R : Type*) [Ring R] [StarRing R]
  (G : Layout) where
  /-- Alice's measurement for equation `i`, indexed by local assignments. -/
  E : ∀ i, (Layout.Assignment G i → R)
  /-- Bob's binary measurement for each variable. -/
  F : Fin G.s → (ZMod 2 → R)
  /-- Alice's families are measurement systems. -/
  alice_ms : ∀ i, IsMeasurementSystem (E i)
  /-- Bob's families are measurement systems. -/
  bob_ms   : ∀ j, IsMeasurementSystem (F j)
  /-- Every projector of Alice commutes with every projector of Bob. -/
  alice_bob_commute : ∀ i j α β, E i α * F j β = F j β * E i α

/-- Alice's derived observable for variable `j` in equation `i`: the `±1`-observable of
the marginal of her equation-`i` measurement on the `j`-th coordinate. -/
noncomputable def ProjectorStrategy.aliceObs
  (strat : ProjectorStrategy R G) (i : Fin G.r) (j : G.V i) : R :=
  observableOfMeasurementSystem (inducedMeasurementSystem (strat.E i) (fun x ↦ x j))

/-- Bob's derived observable `F j 0 - F j 1` for variable `j`. -/
def ProjectorStrategy.bobObs (strat : ProjectorStrategy R G) (j : Fin G.s) : R :=
  observableOfMeasurementSystem (strat.F j)

section WithStrategy

variable (strat : ProjectorStrategy R G)

local notation "A[" i ", " j "]" => ProjectorStrategy.aliceObs strat i j
local notation "B[" j "]" => ProjectorStrategy.bobObs strat j
local notation "E[" i ", " x "]" => strat.E i x
local notation "F[" j ", " y "]" => strat.F j y


omit [Algebra ℂ R] [StarModule ℂ R] in
lemma ProjectorStrategy.isObservable_bobObs (j : Fin G.s) :
  IsObservable B[j] :=
  isObservable_observableOfMeasurementSystem (strat.F j) (strat.bob_ms j)

omit [Algebra ℂ R] [StarModule ℂ R] in
lemma ProjectorStrategy.isObservable_aliceObs (i : Fin G.r) (j : G.V i) :
  IsObservable A[i, j] :=
  isObservable_observableOfMeasurementSystem _
    (IsMeasurementSystem.induced _ (strat.alice_ms i) _)


omit [Algebra ℂ R] [StarModule ℂ R] in
lemma ProjectorStrategy.aliceObs_commute (i : Fin G.r) (j j' : G.V i) :
  Commute A[i, j] A[i, j'] := by
  let comm := IsMeasurementSystem.commute_sum (strat.alice_ms i)
  exact Commute.sub_left (Commute.sub_right (comm _ _) (comm _ _))
    (Commute.sub_right (comm _ _) (comm _ _))

omit [Algebra ℂ R] [StarModule ℂ R] in
lemma ProjectorStrategy.aliceObs_commute_bobObs (i : Fin G.r) (k : G.V i)
    (j_var : Fin G.s) :
    Commute A[i, k] B[j_var] := by
  unfold ProjectorStrategy.aliceObs ProjectorStrategy.bobObs observableOfMeasurementSystem
    inducedMeasurementSystem
  apply Commute.sub_left <;> apply Commute.sub_right
  all_goals {
    apply Commute.sum_left; intro x _; apply strat.alice_bob_commute }

omit [StarModule ℂ R] in
lemma ProjectorStrategy.aliceObs_mul_E (i : Fin G.r)
  (j : G.V i) (x : Layout.Assignment G i) :
  A[i, j] * E[i, x] = ((-1 : ℂ) ^ (x j).val) • E[i, x] := by
  classical
  unfold ProjectorStrategy.aliceObs observableOfMeasurementSystem inducedMeasurementSystem
  rw [sub_mul, IsMeasurementSystem.sum_mul_single (strat.alice_ms i),
    IsMeasurementSystem.sum_mul_single (strat.alice_ms i)]
  rcases zmod_two_eq_zero_or_one (x j) with h | h <;> simp [h]

omit [StarModule ℂ R] in
lemma ProjectorStrategy.aliceObs_noncommProd_mul_E (i : Fin G.r)
  (s : Finset (G.V i)) (x : Layout.Assignment G i)
  (comm :
    (s : Set (G.V i)).Pairwise (fun j j' ↦ Commute A[i, j] A[i, j'])) :
  s.noncommProd (fun j ↦ A[i, j]) comm * E[i, x] =
    (s.prod fun j ↦ (-1 : ℂ) ^ (x j).val) • E[i, x] := by
  classical
  induction s using Finset.cons_induction_on with
  | empty =>
      simp
  | cons a s ha ih =>
      rw [Finset.noncommProd_cons, Finset.prod_cons, mul_assoc, ih]
      · rw [Algebra.mul_smul_comm, ProjectorStrategy.aliceObs_mul_E]
        simp [smul_smul, mul_comm]

/-- The product of Alice's observables for all variables in equation `i`. -/
noncomputable def ProjectorStrategy.aliceRowProd (i : Fin G.r) : R :=
  (G.V i).attach.noncommProd (fun j ↦ A[i, j])
    (fun j _ j' _ _ ↦ ProjectorStrategy.aliceObs_commute strat i j j')

/-- Paper-style notation for `ProjectorStrategy.aliceRowProd strat i`. -/
local notation "∏ₐ[" i "]" => ProjectorStrategy.aliceRowProd strat i

omit [Algebra ℂ R] [StarModule ℂ R] in
lemma ProjectorStrategy.bobObs_commute_aliceRowProd (i : Fin G.r) (j : G.V i) :
    Commute B[↑j] ∏ₐ[i] := by
  unfold ProjectorStrategy.aliceRowProd
  apply Finset.noncommProd_commute
  intro k _
  exact (ProjectorStrategy.aliceObs_commute_bobObs strat i k ↑j).symm

omit [Algebra ℂ R] [StarModule ℂ R] in
lemma ProjectorStrategy.aliceObs_commute_aliceRowProd (i : Fin G.r)
    (j : G.V i) :
    Commute A[i, j] ∏ₐ[i] := by
  unfold ProjectorStrategy.aliceRowProd
  apply Finset.noncommProd_commute
  intro k _
  exact ProjectorStrategy.aliceObs_commute strat i j k

omit [Algebra ℂ R] [StarModule ℂ R] in
lemma ProjectorStrategy.bob_measurement_recover (j : Fin G.s) :
    F[j, 0] - F[j, 1] = B[j] ∧ F[j, 0] + F[j, 1] = 1 := by
  constructor
  · change _ = observableOfMeasurementSystem (strat.F j)
    simp [observableOfMeasurementSystem]
  · have h := (strat.bob_ms j).sum_one
    rw [sum_univ_zmod_two] at h
    exact h

omit [StarModule ℂ R] in
lemma ProjectorStrategy.F_eq_observableToProjector (j : Fin G.s) (y : ZMod 2) :
  F[j, y] = observableToProjector B[j] y := by
  classical
  unfold ProjectorStrategy.bobObs observableOfMeasurementSystem observableToProjector observableSign
  have hsum := (strat.bob_ms j).sum_one
  rw [sum_univ_zmod_two] at hsum
  rcases zmod_two_eq_zero_or_one y with rfl | rfl
  · simp only [← hsum]
    symm
    calc
      (1 / 2 : ℂ) • (strat.F j 0 + strat.F j 1 + (1 : ℂ) • (strat.F j 0 - strat.F j 1))
      _ = (1 / 2 : ℂ) • (strat.F j 0 + strat.F j 0) := by
        congr 1; simp only [one_smul]; abel
      _ = (1 / 2 : ℂ) • strat.F j 0 + (1 / 2 : ℂ) • strat.F j 0 := by
        rw [smul_add]
      _ = (1 / 2 + 1 / 2 : ℂ) • strat.F j 0 := by
        rw [add_smul]
      _ = strat.F j 0 := by
        norm_num
  · simp only [← hsum]
    symm
    calc
      (1 / 2 : ℂ) • (strat.F j 0 + strat.F j 1 + (-1 : ℂ) • (strat.F j 0 - strat.F j 1))
      _ = (1 / 2 : ℂ) • (strat.F j 1 + strat.F j 1) := by
        congr 1; simp only [neg_smul, one_smul]; abel
      _ = (1 / 2 : ℂ) • strat.F j 1 + (1 / 2 : ℂ) • strat.F j 1 := by
        rw [smul_add]
      _ = (1 / 2 + 1 / 2 : ℂ) • strat.F j 1 := by
        rw [add_smul]
      _ = strat.F j 1 := by
        norm_num

end WithStrategy

end MIPRE.LCS
