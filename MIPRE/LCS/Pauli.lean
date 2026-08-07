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

-- Base Pauli Matrices
def I2 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]
def X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def Y : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

lemma I2_eq_one : I2 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i
  · fin_cases j <;> simp [I2]
  · fin_cases j <;> simp [I2]

lemma I2_comm_left (P : Matrix (Fin 2) (Fin 2) ℂ) : Commute I2 P := by
  rw [I2_eq_one]; exact Commute.one_left P

lemma I2_comm_right (P : Matrix (Fin 2) (Fin 2) ℂ) : Commute P I2 := by
  rw [I2_eq_one]; exact Commute.one_right P

lemma I2_sq : I2 * I2 = 1 := by
  ext i j
  fin_cases i
  · fin_cases j <;> simp [I2]
  · fin_cases j <;> simp [I2]

lemma X_sq : X * X = 1 := by
  ext i j
  fin_cases i
  · fin_cases j <;> simp [X]
  · fin_cases j <;> simp [X]

lemma Y_sq : Y * Y = 1 := by
  ext i j
  fin_cases i
  · fin_cases j <;> simp [Y]
  · fin_cases j <;> simp [Y]

lemma Z_sq : Z * Z = 1 := by
  ext i j
  fin_cases i
  · fin_cases j <;> simp [Z]
  · fin_cases j <;> simp [Z]

lemma I2_selfAdjoint : star I2 = I2 := by
  ext i j
  fin_cases i
  · fin_cases j <;> simp [I2, Matrix.star_apply]
  · fin_cases j <;> simp [I2, Matrix.star_apply]

lemma X_selfAdjoint : star X = X := by
  ext i j
  fin_cases i
  · fin_cases j <;> simp [X, Matrix.star_apply]
  · fin_cases j <;> simp [X, Matrix.star_apply]

lemma Y_selfAdjoint : star Y = Y := by
  ext i j
  fin_cases i
  · fin_cases j <;> simp [Y, Matrix.star_apply]
  · fin_cases j <;> simp [Y, Matrix.star_apply]

lemma Z_selfAdjoint : star Z = Z := by
  ext i j
  fin_cases i
  · fin_cases j <;> simp [Z, Matrix.star_apply]
  · fin_cases j <;> simp [Z, Matrix.star_apply]

lemma XY_mul : X * Y = Complex.I • Z := by
  ext i j
  fin_cases i
  · fin_cases j <;> simp [X, Y, Z]
  · fin_cases j <;> simp [X, Y, Z]

lemma YX_mul : Y * X = (-Complex.I) • Z := by
  ext i j
  fin_cases i
  · fin_cases j <;> simp [X, Y, Z]
  · fin_cases j <;> simp [X, Y, Z]

lemma XZ_mul : X * Z = (-Complex.I) • Y := by
  ext i j
  fin_cases i
  · fin_cases j <;> simp [X, Y, Z]
  · fin_cases j <;> simp [X, Y, Z]

lemma ZX_mul : Z * X = Complex.I • Y := by
  ext i j
  fin_cases i
  · fin_cases j <;> simp [X, Y, Z]
  · fin_cases j <;> simp [X, Y, Z]

lemma YZ_mul : Y * Z = Complex.I • X := by
  ext i j
  fin_cases i
  · fin_cases j <;> simp [X, Y, Z]
  · fin_cases j <;> simp [X, Y, Z]

lemma ZY_mul : Z * Y = (-Complex.I) • X := by
  ext i j
  fin_cases i
  · fin_cases j <;> simp [X, Y, Z]
  · fin_cases j <;> simp [X, Y, Z]

lemma XY_anticomm : X * Y = -(Y * X) := by
  rw [YX_mul, XY_mul]
  simp

lemma XZ_anticomm : X * Z = -(Z * X) := by
  rw [ZX_mul, XZ_mul]
  simp

lemma YZ_anticomm : Y * Z = -(Z * Y) := by
  rw [ZY_mul, YZ_mul]
  simp

lemma I2_observable : IsObservable I2 where
  involutive := I2_sq
  self_adjoint := I2_selfAdjoint

lemma X_observable : IsObservable X where
  involutive := X_sq
  self_adjoint := X_selfAdjoint

lemma Y_observable : IsObservable Y where
  involutive := Y_sq
  self_adjoint := Y_selfAdjoint

lemma Z_observable : IsObservable Z where
  involutive := Z_sq
  self_adjoint := Z_selfAdjoint



lemma kronecker_comm_of_comm {A B C D : Matrix (Fin 2) (Fin 2) ℂ}
    (hAC : Commute A C) (hBD : Commute B D) :
    Commute (A ⊗ₖ B) (C ⊗ₖ D) := by
  unfold Commute SemiconjBy at hAC hBD ⊢
  calc
    (A ⊗ₖ B) * (C ⊗ₖ D) = (A * C) ⊗ₖ (B * D) := by rw [mul_kronecker_mul]
    _ = (C * A) ⊗ₖ (D * B) := by rw [hAC, hBD]
    _ = (C ⊗ₖ D) * (A ⊗ₖ B) := by rw [mul_kronecker_mul]

lemma kronecker_comm_of_anticomm {A B C D : Matrix (Fin 2) (Fin 2) ℂ}
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

lemma kronecker_observable {A B : Matrix (Fin 2) (Fin 2) ℂ}
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
