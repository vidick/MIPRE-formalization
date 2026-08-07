/-
Copyright (c) 2026 Sean Perazzolo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Perazzolo
-/
import MIPRE.LCS.Basic
import MIPRE.LCS.Common
import MIPRE.LCS.Observable
import MIPRE.LCS.Measurement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Conversion from Observables to Projectors

This module defines the mapping from observables (self-adjoint involutive operators)
to projector measurement systems and proves their fundamental algebraic properties.

Given an observable $O$, we define two projectors $P_0, P_1$ corresponding to
the outcomes $\{0, 1\} \subseteq \mathbb{F}_2$:
- $P_0 = \frac{1}{2}(I + O)$
- $P_1 = \frac{1}{2}(I - O)$

These projectors form a complete binary measurement system.
-/

namespace MIPRE.LCS


variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]


/-- Converts an observable $O$ and an outcome $a \in \{0, 1\}$ to a projector
$P = (1/2)(I + (-1)^a O)$. -/
noncomputable def observableToProjector
  (O : R) (a : ZMod 2) : R :=
  (1 / 2 : ℂ) • (1 + observableSign a • O)

/-- If $O$ is an observable, then the projector
$P_a = (1/2)(1 + (-1)^a O)$ is self-adjoint. -/
lemma star_observableToProjector (O : R) (hO : IsObservable O) (a : ZMod 2) :
    star (observableToProjector O a) = observableToProjector O a := by
  rcases zmod_two_eq_zero_or_one a with rfl | rfl
  all_goals (
    simp [observableToProjector]
    simp [observableSign]
    simp [hO.self_adjoint]
  )

omit [StarModule ℂ R] in
/-- If $O$ is an observable, then each $\mathrm{observableToProjector}(O,a)$ is idempotent,
so it is a projector. -/
lemma idempotent_observableToProjector (O : R) (hO : IsObservable O) (a : ZMod 2) :
    observableToProjector O a * observableToProjector O a = observableToProjector O a := by
  rcases zmod_two_eq_zero_or_one a with rfl | rfl
  · calc
      observableToProjector O 0 * observableToProjector O 0
          = ((1 / 2 : ℂ) * (1 / 2 : ℂ)) • ((1 + O) * (1 + O)) := by
              simpa [observableToProjector, observableSign] using
                (smul_mul_smul (1 / 2 : ℂ) (1 + O) (1 / 2 : ℂ) (1 + O))
      _ = ((1 / 2 : ℂ) * (1 / 2 : ℂ)) • ((2 : ℂ) • (1 + O)) := by
            congr 1
            rw [add_mul, one_mul, mul_add, mul_one, hO.involutive]
            rw [two_smul]
            abel
      _ = (1 / 2 : ℂ) • (1 + O) := by
            rw [smul_smul]
            norm_num
      _ = observableToProjector O 0 := by
            simp [observableToProjector, observableSign]
  · calc
      observableToProjector O 1 * observableToProjector O 1
          = ((1 / 2 : ℂ) * (1 / 2 : ℂ)) • ((1 + (-1 : ℂ) • O) * (1 + (-1 : ℂ) • O)) := by
              simpa [observableToProjector, observableSign] using
                (smul_mul_smul (1 / 2 : ℂ) (1 + (-1 : ℂ) • O) (1 / 2 : ℂ) (1 + (-1 : ℂ) • O))
      _ = ((1 / 2 : ℂ) * (1 / 2 : ℂ)) • ((2 : ℂ) • (1 + (-1 : ℂ) • O)) := by
            congr 1
            rw [add_mul, one_mul, mul_add, mul_one, smul_mul_smul, hO.involutive]
            norm_num
            simp [two_smul, add_assoc, add_left_comm, add_comm]
      _ = (1 / 2 : ℂ) • (1 + (-1 : ℂ) • O) := by
            rw [smul_smul]
            norm_num
      _ = observableToProjector O 1 := by
            simp [observableToProjector, observableSign]

omit [StarModule ℂ R] in
/-- The two projectors associated to the two outcomes of a single observable are orthogonal:
$P_0 P_1 = 0$. -/
lemma orthogonal_observableToProjector (O : R) (hO : IsObservable O) :
    observableToProjector O 0 * observableToProjector O 1 = 0 := by
  calc
    observableToProjector O 0 * observableToProjector O 1
        = ((1 / 2 : ℂ) * (1 / 2 : ℂ)) • ((1 + O) * (1 + (-1 : ℂ) • O)) := by
            simpa [observableToProjector, observableSign] using
              (smul_mul_smul (1 / 2 : ℂ) (1 + O) (1 / 2 : ℂ) (1 + (-1 : ℂ) • O))
      _ = ((1 / 2 : ℂ) * (1 / 2 : ℂ)) • (0 : R) := by
          congr 1
          rw [add_mul, one_mul, mul_add, mul_one, mul_smul_comm, hO.involutive]
          norm_num
      _ = 0 := by simp

omit [StarRing R] [StarModule ℂ R] in
/-- The two projectors associated to a single observable form a complete binary measurement:
$P_0 + P_1 = 1$. -/
lemma sum_one_observableToProjector (O : R) :
    observableToProjector O 0 + observableToProjector O 1 = 1 := by
  calc
    observableToProjector O 0 + observableToProjector O 1
    = ((1 / 2 : ℂ) + (1 / 2 : ℂ)) • (1 : R) := by
      rw [observableToProjector, observableToProjector, observableSign, observableSign, if_pos rfl,
        if_neg (by decide)]
      simp [smul_add, add_assoc, ← add_smul]
    _ = 1 := by
      norm_num

omit [StarModule ℂ R] in
lemma observable_mul_observableToProjector
    (O : R) (hO : IsObservable O) (a : ZMod 2) :
    O * observableToProjector O a =
      ((-1 : ℂ) ^ a.val) • observableToProjector O a := by
  rcases zmod_two_eq_zero_or_one a with rfl | rfl
  · simp [observableToProjector, observableSign, hO.involutive, mul_add,
      smul_add, add_comm]
  · simp [observableToProjector, observableSign, hO.involutive, mul_add,
      smul_add, add_comm]

omit [StarRing R] [StarModule ℂ R] in
/-- If observables $O₁$ and $O₂$ commute, then all corresponding projectors
$P_a(O₁)$ and $P_b(O₂)$ commute as well. -/
lemma commute_observableToProjector {O1 O2 : R} (h : Commute O1 O2) (a b : ZMod 2) :
    Commute (observableToProjector O1 a) (observableToProjector O2 b) := by
  rw [observableToProjector, observableToProjector]
  apply Commute.smul_right
  apply Commute.smul_left
  apply Commute.add_left (.one_left _)
  apply Commute.add_right (.one_right _)
  exact (h.smul_left _).smul_right _

/-- Given an observable $O$, the mapping `observableToProjector O` is a measurement system. -/
lemma isMeasurementSystem_observableToProjector (O : R) (hO : IsObservable O) :
    IsMeasurementSystem (observableToProjector O) where
  sum_one := by
    rw [sum_univ_zmod_two, sum_one_observableToProjector]
  idempotent a := idempotent_observableToProjector O hO a
  orthogonal a b hab := by
    rcases zmod_two_eq_zero_or_one a with rfl | rfl <;>
      rcases zmod_two_eq_zero_or_one b with rfl | rfl <;>
        try exact absurd rfl hab
    · exact orthogonal_observableToProjector O hO
    · rw [commute_observableToProjector (Commute.refl O) 1 0]
      exact orthogonal_observableToProjector O hO
  self_adjoint a := star_observableToProjector O hO a

end MIPRE.LCS
