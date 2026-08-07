/-
Copyright (c) 2026 Sean Perazzolo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Perazzolo
-/
import MIPRE.LCS.Basic
import MIPRE.LCS.Measurement
import Mathlib.Algebra.Star.Module
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Observables in LCS Games

This module defines the algebraic properties of quantum observables
in the context of Linear Constraint System (LCS) games. An observable
is represented as a self-adjoint, involutive operator.

## Key Definitions
- `IsObservable`: A property of an element $O$ in a star-ring if $O^2=1$ and $O^\dagger=O$.
- `ObservableOfMeasurementSystem`: Constructs an observable from a binary projector measurement $P$
  as $O = P_0 - P_1$.

## Key Lemmas
- `is_observable_of_measurement_system`: Verifies that the difference of projectors
  in a binary measurement forms a valid observable.
-/

namespace MIPRE.LCS

set_option linter.unusedSectionVars false

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
variable {G : LCSLayout}

structure IsObservable (O : R) : Prop where
  involutive   : O * O = 1
  self_adjoint : star O = O

def ObservableOfMeasurementSystem (f : Fin 2 → R) : R :=
  f 0 - f 1


lemma is_observable_of_measurement_system
  (f : Fin 2 → R) (h : IsMeasurementSystem f) :
  IsObservable (ObservableOfMeasurementSystem f) where
  involutive := by
    dsimp [ObservableOfMeasurementSystem]
    rw [sub_mul, mul_sub, mul_sub, h.idempotent 0, h.idempotent 1]
    rw [h.orthogonal 0 1 (by decide), h.orthogonal 1 0 (by decide)]
    rw [sub_zero, zero_sub, sub_neg_eq_add]
    exact (Fin.sum_univ_two f).symm.trans h.sum_one
  self_adjoint := by
    dsimp [ObservableOfMeasurementSystem]
    rw [star_sub, h.self_adjoint 0, h.self_adjoint 1]

lemma binary_measurement_eq_projector (f : Fin 2 → R) (h : IsMeasurementSystem f) (y : Fin 2) :
    f y = (1 / 2 : ℂ) • (1 + (-1 : ℂ) ^ y.val • ObservableOfMeasurementSystem f) := by
  have hsum := h.sum_one
  rw [Fin.sum_univ_two] at hsum
  unfold ObservableOfMeasurementSystem
  have hy : y = 0 ∨ y = 1 := by omega
  rcases hy with rfl | rfl
  · simp only [Fin.val_zero, pow_zero, one_smul, ← hsum]
    have h1 : f 0 + f 1 + (f 0 - f 1) = f 0 + f 0 := by abel
    rw [h1, ← one_smul ℂ (f 0), ← add_smul]
    have h2 : (1 / 2 : ℂ) * (1 + 1 : ℂ) = 1 := by norm_num
    rw [smul_smul, h2, one_smul]
  · simp only [Fin.val_one, pow_one]
    have h1 : (1 : R) + (-1 : ℂ) • (f 0 - f 1) = f 1 + f 1 := by
      rw [← hsum, neg_smul, one_smul]; abel
    rw [h1, ← one_smul ℂ (f 1), ← add_smul]
    have h2 : (1 / 2 : ℂ) * (1 + 1 : ℂ) = 1 := by norm_num
    rw [smul_smul, h2, one_smul]

end MIPRE.LCS
