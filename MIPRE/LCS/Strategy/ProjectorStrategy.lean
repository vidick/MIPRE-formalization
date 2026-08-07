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
- `Alice_A`, `Bob_B`: Derived observables extracted from the projector measurements.

## Key Lemmas
- `alice_is_observable`, `bob_is_observable`: Proves that the derived operators are observables.
- `alice_observables_commute`, `alice_bob_commute`: Verification of commutation relations.
-/

namespace MIPRE.LCS

open scoped BigOperators

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
variable {G : LCSLayout}
set_option linter.unusedSectionVars false

structure ProjectorStrategy
  (R : Type*) [Ring R] [StarRing R] [Algebra ℂ R]
  (G : LCSLayout) where
  E : ∀ i, (Assignment G i → R)
  F : Fin G.s → (ZMod 2 → R)
  alice_ms : ∀ i, IsMeasurementSystem (E i)
  bob_ms   : ∀ j, IsMeasurementSystem (F j)
  commute  : ∀ i j α β, E i α * F j β = F j β * E i α

noncomputable def Alice_A
  (strat : ProjectorStrategy R G) (i : Fin G.r) (j : G.V i) : R :=
  ObservableOfMeasurementSystem (InducedMeasurementSystem (strat.E i) (fun x => x j))

def Bob_B (strat : ProjectorStrategy R G) (j : Fin G.s) : R :=
  ObservableOfMeasurementSystem (strat.F j)

section WithStrategy

variable (strat : ProjectorStrategy R G)

local notation "A[" i ", " j "]" => Alice_A strat i j
local notation "B[" j "]" => Bob_B strat j
local notation "E[" i ", " x "]" => strat.E i x
local notation "F[" j ", " y "]" => strat.F j y


lemma bob_is_observable (j : Fin G.s) :
  IsObservable B[j] :=
  is_observable_of_measurement_system (strat.F j) (strat.bob_ms j)

lemma alice_is_observable (i : Fin G.r) (j : G.V i) :
  IsObservable A[i, j] :=
  is_observable_of_measurement_system _
    (induced_measurement_system_is_measurement_system _ (strat.alice_ms i) _)


lemma alice_observables_commute (i : Fin G.r) (j j' : G.V i) :
  Commute A[i, j] A[i, j'] := by
  let comm := measurement_commute_sum (strat.alice_ms i)
  exact Commute.sub_left (Commute.sub_right (comm _ _) (comm _ _))
    (Commute.sub_right (comm _ _) (comm _ _))

lemma alice_bob_commute_gen (i : Fin G.r) (k : G.V i)
    (j_var : Fin G.s) :
    Commute A[i, k] B[j_var] := by
  unfold Alice_A Bob_B ObservableOfMeasurementSystem InducedMeasurementSystem
  apply Commute.sub_left <;> apply Commute.sub_right
  all_goals {
    apply Commute.sum_left; intro x _; apply strat.commute }

lemma alice_A_mul_projector (i : Fin G.r)
  (j : G.V i) (x : Assignment G i) :
  A[i, j] * E[i, x] = ((-1 : ℂ) ^ (x j).val) • E[i, x] := by
  classical
  unfold Alice_A ObservableOfMeasurementSystem InducedMeasurementSystem
  rw [sub_mul, measurement_sum_mul_projector (strat.alice_ms i),
    measurement_sum_mul_projector (strat.alice_ms i)]
  rcases zmod_two_eq_zero_or_one (x j) with h | h <;> simp [h]

lemma alice_partial_prod_mul_projector (i : Fin G.r)
  (s : Finset (G.V i)) (x : Assignment G i)
  (comm :
    (s : Set (G.V i)).Pairwise (fun j j' => Commute A[i, j] A[i, j'])) :
  s.noncommProd (fun j => A[i, j]) comm * E[i, x] =
    (s.prod fun j => (-1 : ℂ) ^ (x j).val) • E[i, x] := by
  classical
  induction s using Finset.cons_induction_on with
  | empty =>
      simp
  | cons a s ha ih =>
      rw [Finset.noncommProd_cons, Finset.prod_cons, mul_assoc, ih]
      · rw [Algebra.mul_smul_comm, alice_A_mul_projector]
        simp [smul_smul, mul_comm]

/-- The product of Alice's observables for all variables in equation `i`. -/
noncomputable def Alice_Row_Prod (i : Fin G.r) : R :=
  (G.V i).attach.noncommProd (fun j => A[i, j])
    (fun j _ j' _ _ => alice_observables_commute strat i j j')

/-- Paper-style notation for `Alice_Row_Prod strat i`. -/
local notation "∏ₐ[" i "]" => Alice_Row_Prod strat i

lemma bob_commute_row_prod (i : Fin G.r) (j : G.V i) :
    Commute B[↑j] ∏ₐ[i] := by
  unfold Alice_Row_Prod
  apply Finset.noncommProd_commute
  intro k _
  exact (alice_bob_commute_gen strat i k ↑j).symm

lemma alice_commute_row_prod (i : Fin G.r)
    (j : G.V i) :
    Commute A[i, j] ∏ₐ[i] := by
  unfold Alice_Row_Prod
  apply Finset.noncommProd_commute
  intro k _
  exact alice_observables_commute strat i j k

lemma bob_measurement_recover (j : Fin G.s) :
    F[j, 0] - F[j, 1] = B[j] ∧ F[j, 0] + F[j, 1] = 1 := by
  constructor
  · change _ = ObservableOfMeasurementSystem (strat.F j)
    simp [ObservableOfMeasurementSystem]
  · have h := (strat.bob_ms j).sum_one
    rw [sum_univ_zmod_two] at h
    exact h

lemma bob_measurement_eq_projector (j : Fin G.s) (y : ZMod 2) :
  F[j, y] = ObservableToProjector B[j] y := by
  classical
  unfold Bob_B ObservableOfMeasurementSystem ObservableToProjector observableSign
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
