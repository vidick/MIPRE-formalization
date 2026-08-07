/-
Copyright (c) 2026 Sean Perazzolo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Perazzolo
-/
import MIPRE.LCS.Observable
import Mathlib.LinearAlgebra.Matrix.Kronecker

namespace MIPRE.LCS

open Matrix
open Kronecker
open scoped BigOperators

namespace Pauli

-- Base Pauli Matrices
def I : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]
def X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def Y : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

lemma I_eq_one : I = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i
  · fin_cases j <;> simp [I]
  · fin_cases j <;> simp [I]

lemma I_comm_left (P : Matrix (Fin 2) (Fin 2) ℂ) : Commute I P := by
  rw [I_eq_one]; exact Commute.one_left P

lemma I_comm_right (P : Matrix (Fin 2) (Fin 2) ℂ) : Commute P I := by
  rw [I_eq_one]; exact Commute.one_right P

lemma I_mul_self : I * I = 1 := by
  ext i j
  fin_cases i
  · fin_cases j <;> simp [I]
  · fin_cases j <;> simp [I]

lemma X_mul_self : X * X = 1 := by
  ext i j
  fin_cases i
  · fin_cases j <;> simp [X]
  · fin_cases j <;> simp [X]

lemma Y_mul_self : Y * Y = 1 := by
  ext i j
  fin_cases i
  · fin_cases j <;> simp [Y]
  · fin_cases j <;> simp [Y]

lemma Z_mul_self : Z * Z = 1 := by
  ext i j
  fin_cases i
  · fin_cases j <;> simp [Z]
  · fin_cases j <;> simp [Z]

lemma star_I : star I = I := by
  ext i j
  fin_cases i
  · fin_cases j <;> simp [I, Matrix.star_apply]
  · fin_cases j <;> simp [I, Matrix.star_apply]

lemma star_X : star X = X := by
  ext i j
  fin_cases i
  · fin_cases j <;> simp [X, Matrix.star_apply]
  · fin_cases j <;> simp [X, Matrix.star_apply]

lemma star_Y : star Y = Y := by
  ext i j
  fin_cases i
  · fin_cases j <;> simp [Y, Matrix.star_apply]
  · fin_cases j <;> simp [Y, Matrix.star_apply]

lemma star_Z : star Z = Z := by
  ext i j
  fin_cases i
  · fin_cases j <;> simp [Z, Matrix.star_apply]
  · fin_cases j <;> simp [Z, Matrix.star_apply]

lemma X_mul_Y : X * Y = Complex.I • Z := by
  ext i j
  fin_cases i
  · fin_cases j <;> simp [X, Y, Z]
  · fin_cases j <;> simp [X, Y, Z]

lemma Y_mul_X : Y * X = (-Complex.I) • Z := by
  ext i j
  fin_cases i
  · fin_cases j <;> simp [X, Y, Z]
  · fin_cases j <;> simp [X, Y, Z]

lemma X_mul_Z : X * Z = (-Complex.I) • Y := by
  ext i j
  fin_cases i
  · fin_cases j <;> simp [X, Y, Z]
  · fin_cases j <;> simp [X, Y, Z]

lemma Z_mul_X : Z * X = Complex.I • Y := by
  ext i j
  fin_cases i
  · fin_cases j <;> simp [X, Y, Z]
  · fin_cases j <;> simp [X, Y, Z]

lemma Y_mul_Z : Y * Z = Complex.I • X := by
  ext i j
  fin_cases i
  · fin_cases j <;> simp [X, Y, Z]
  · fin_cases j <;> simp [X, Y, Z]

lemma Z_mul_Y : Z * Y = (-Complex.I) • X := by
  ext i j
  fin_cases i
  · fin_cases j <;> simp [X, Y, Z]
  · fin_cases j <;> simp [X, Y, Z]

lemma X_anticomm_Y : X * Y = -(Y * X) := by
  rw [Y_mul_X, X_mul_Y]
  simp

lemma X_anticomm_Z : X * Z = -(Z * X) := by
  rw [Z_mul_X, X_mul_Z]
  simp

lemma Y_anticomm_Z : Y * Z = -(Z * Y) := by
  rw [Z_mul_Y, Y_mul_Z]
  simp

lemma isObservable_I : IsObservable I where
  involutive := I_mul_self
  self_adjoint := star_I

lemma isObservable_X : IsObservable X where
  involutive := X_mul_self
  self_adjoint := star_X

lemma isObservable_Y : IsObservable Y where
  involutive := Y_mul_self
  self_adjoint := star_Y

lemma isObservable_Z : IsObservable Z where
  involutive := Z_mul_self
  self_adjoint := star_Z

end Pauli

lemma commute_kronecker_of_commute {A B C D : Matrix (Fin 2) (Fin 2) ℂ}
    (hAC : Commute A C) (hBD : Commute B D) :
    Commute (A ⊗ₖ B) (C ⊗ₖ D) := by
  unfold Commute SemiconjBy at hAC hBD ⊢
  calc
    (A ⊗ₖ B) * (C ⊗ₖ D) = (A * C) ⊗ₖ (B * D) := by rw [mul_kronecker_mul]
    _ = (C * A) ⊗ₖ (D * B) := by rw [hAC, hBD]
    _ = (C ⊗ₖ D) * (A ⊗ₖ B) := by rw [mul_kronecker_mul]

lemma commute_kronecker_of_anticomm {A B C D : Matrix (Fin 2) (Fin 2) ℂ}
    (hAC : A * C = -(C * A)) (hBD : B * D = -(D * B)) :
    Commute (A ⊗ₖ B) (C ⊗ₖ D) := by
  unfold Commute SemiconjBy
  calc
    (A ⊗ₖ B) * (C ⊗ₖ D) = (A * C) ⊗ₖ (B * D) := by rw [mul_kronecker_mul]
    _ = (-(C * A)) ⊗ₖ (-(D * B)) := by rw [hAC, hBD]
    _ = (((-1 : ℂ) • (C * A)) ⊗ₖ ((-1 : ℂ) • (D * B))) := by simp
    _ = (C * A) ⊗ₖ (D * B) := by
      rw [smul_kronecker, kronecker_smul]
      simp
    _ = (C ⊗ₖ D) * (A ⊗ₖ B) := by rw [mul_kronecker_mul]

lemma IsObservable.kronecker {A B : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : IsObservable A) (hB : IsObservable B) :
    IsObservable (A ⊗ₖ B) where
  involutive := by
    change (A ⊗ₖ B) * (A ⊗ₖ B) = 1
    rw [← mul_kronecker_mul, hA.involutive, hB.involutive, one_kronecker_one]
  self_adjoint := by
    have hA_ct : Aᴴ = A := by
      simpa [star_eq_conjTranspose] using hA.self_adjoint
    have hB_ct : Bᴴ = B := by
      simpa [star_eq_conjTranspose] using hB.self_adjoint
    simp [conjTranspose_kronecker, hA_ct, hB_ct, star_eq_conjTranspose]

end MIPRE.LCS
