/-
Copyright (c) 2026 Sean Perazzolo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Perazzolo
-/
import MIPRE.LCS.Basic

/-!
# Projector Measurement Systems

This module defines the concept of a projector-valued measurement (PVM) in a general star-ring.
A measurement system is a family of self-adjoint, idempotent, and mutually orthogonal elements
that sum to the identity.

## Key Definitions
- `IsMeasurementSystem`: A property of a family of elements $\{E_i\}_{i \in I}$ indicating
  they form a valid measurement system.
- `inducedMeasurementSystem`: A construction to build a measurement over a smaller outcome space
  given a function $g : I \to J$.

## Key Lemmas
- `IsMeasurementSystem.commute`: Projectors in a measurement system always commute with each other.
- `IsMeasurementSystem.sum_mul_sum`: The product of two sums of projectors corresponds to the sum
  over the intersection of the outcome sets.
-/

namespace MIPRE.LCS


variable {R : Type*} [Ring R] [StarRing R]

/-- A projector-valued measurement in a star-ring: a family of self-adjoint, idempotent,
mutually orthogonal elements that sum to the identity. -/
structure IsMeasurementSystem
  {I : Type*} [Fintype I]
  (f : I → R) : Prop where
  /-- The measurement operators sum to one. -/
  sum_one      : ∑ x, f x = 1
  /-- Each measurement operator is idempotent. -/
  idempotent   : ∀ x, f x * f x = f x
  /-- Distinct measurement operators are orthogonal. -/
  orthogonal   : ∀ x y, x ≠ y → f x * f y = 0
  /-- Each measurement operator is self-adjoint. -/
  self_adjoint : ∀ x, star (f x) = f x

/-- The measurement on outcome space `J` induced by pushing a measurement on `I` forward
along `g : I → J`, summing the operators over each fiber. -/
noncomputable def inducedMeasurementSystem {I J : Type*} [Fintype I] [Fintype J]
  [DecidableEq J] (f : I → R) (g : I → J) : J → R :=
  fun j ↦ ∑ i ∈ Finset.univ.filter (fun i ↦ g i = j), f i

lemma IsMeasurementSystem.induced
  {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
  (f : I → R) (h : IsMeasurementSystem f) (g : I → J) :
  IsMeasurementSystem (inducedMeasurementSystem f g) where
  sum_one := by
    dsimp [inducedMeasurementSystem]
    rw [Finset.sum_fiberwise Finset.univ g f, h.sum_one]
  idempotent j := by
    dsimp [inducedMeasurementSystem]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl (fun x hx ↦ ?_)
    rw [Finset.mul_sum]
    have : ∑ i ∈ Finset.univ.filter (fun i ↦ g i = j), f x * f i = f x * f x := by
      apply Finset.sum_eq_single x
      · intro y _ hxy; exact h.orthogonal x y hxy.symm
      · intro hnx; exact (hnx hx).elim
    rw [this, h.idempotent x]
  orthogonal j1 j2 hj := by
    dsimp [inducedMeasurementSystem]
    rw [Finset.sum_mul]
    apply Finset.sum_eq_zero (fun x hx ↦ ?_)
    rw [Finset.mul_sum]
    apply Finset.sum_eq_zero (fun y hy ↦ ?_)
    apply h.orthogonal
    rintro rfl
    exact hj ((Finset.mem_filter.1 hx).2.symm.trans (Finset.mem_filter.1 hy).2)
  self_adjoint j := by
    dsimp [inducedMeasurementSystem]
    rw [star_sum]
    exact Finset.sum_congr rfl (fun x _ ↦ h.self_adjoint x)


lemma IsMeasurementSystem.commute {I} [Fintype I] {f : I → R}
  (h : IsMeasurementSystem f) (x y : I) : Commute (f x) (f y) := by
  by_cases hxy : x = y
  · rw [hxy]
  · rw [Commute, SemiconjBy, h.orthogonal x y hxy, h.orthogonal y x (Ne.symm hxy)]

lemma IsMeasurementSystem.commute_sum {I} [Fintype I] {f : I → R}
  (h : IsMeasurementSystem f) (A B : Finset I) : Commute (∑ x ∈ A, f x) (∑ y ∈ B, f y) :=
  Commute.sum_left _ _ _ (fun x _ ↦
    Commute.sum_right _ _ _ (fun y _ ↦ IsMeasurementSystem.commute h x y))


lemma IsMeasurementSystem.sum_mul_sum {I} [Fintype I] [DecidableEq I] {f : I → R}
    (h : IsMeasurementSystem f) (S T : Finset I) :
    (∑ x ∈ S, f x) * (∑ y ∈ T, f y) = ∑ x ∈ (S ∩ T), f x := by
  classical
  rw [Finset.sum_mul]
  have h_mul (x : I) : f x * ∑ y ∈ T, f y = if x ∈ T then f x else 0 := by
    rw [Finset.mul_sum]
    by_cases hxT : x ∈ T
    · rw [if_pos hxT]
      have : ∑ y ∈ T, f x * f y = f x * f x := by
        apply Finset.sum_eq_single x
        · intro b _ hb; exact h.orthogonal x b (Ne.symm hb)
        · intro hnx; exact (hnx hxT).elim
      rw [this, h.idempotent x]
    · rw [if_neg hxT]
      apply Finset.sum_eq_zero
      intro y hy
      apply h.orthogonal
      intro h_eq; subst h_eq; contradiction
  rw [Finset.sum_congr rfl (fun x _ ↦ h_mul x)]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.filter_mem_eq_inter]

lemma IsMeasurementSystem.eq_of_forall_mul_eq {I} [Fintype I] {f : I → R}
    (h : IsMeasurementSystem f)
    {T U : R} (heq : ∀ x, T * f x = U * f x) : T = U := by
  calc T = T * 1 := (mul_one T).symm
       _ = T * ∑ x, f x := by rw [h.sum_one]
       _ = ∑ x, T * f x := by rw [Finset.mul_sum]
       _ = ∑ x, U * f x := Finset.sum_congr rfl (fun x _ ↦ heq x)
       _ = U * ∑ x, f x := by rw [← Finset.mul_sum]
       _ = U * 1 := by rw [h.sum_one]
       _ = U := mul_one U

lemma IsMeasurementSystem.sum_mul_single {I} [Fintype I] [DecidableEq I] {f : I → R}
    (h : IsMeasurementSystem f) (S : Finset I) (x : I) :
    (∑ y ∈ S, f y) * f x = if x ∈ S then f x else 0 := by
  classical
  split_ifs with hx
  · rw [Finset.sum_mul, Finset.sum_eq_single_of_mem x hx]
    · exact h.idempotent x
    · intro y _ hyx; exact h.orthogonal y x hyx
  · rw [Finset.sum_mul, Finset.sum_eq_zero]
    intro y hy
    exact h.orthogonal y x (by rintro rfl; exact hx hy)

end MIPRE.LCS
