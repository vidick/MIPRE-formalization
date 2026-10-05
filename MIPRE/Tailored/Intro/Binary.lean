/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Intro.Closure
public import MIPRE.Foundations.Introspection.HonestMagicSquare

@[expose] public section

/-!
# Binary measurements and the Magic Square grid as permutation observables

The Pauli basis test's honest strategy answers its probe and Magic Square questions with the
two-outcome measurements `½(1 ± O)` of observables `O` (`MIPRE.LCS.observableToProjector`),
the observables being Weyl operators on the register and, for the Magic Square, the nine
entries of `HonestMagicSquare.grid` on the register and one ancilla qubit. This file shows:

* `encObs_observableToProjector`: an answer bit that reads the outcome, possibly flipped, has
  observable `±O`; one that ignores it has observable `±1`;
* `isSignedPerm_pauliX`, `isSignedPerm_pauliZ`: the qubit Paulis `X` and `Z` are signed
  permutations (unlike `Y`, which is why the Mermin–Peres grid is not a ZPC strategy);
* `isSignedPerm_grid`: so are the nine entries of the grid, when `A` and `B` are.
-/

namespace MIPRE.Tailored

open Finset Matrix
open scoped Kronecker

/-! ## Binary measurements -/

section Binary

variable {R : Type*} [Ring R] [Algebra ℂ R] {k : ℕ}

theorem univ_zmod_two : (univ : Finset (ZMod 2)) = {0, 1} := by decide

theorem observableSign_eq_bitSign (b : ZMod 2) :
    LCS.observableSign b = bitSign (decide (b = 1)) := by
  fin_cases b <;> rfl

/-- **A bit reading the outcome of `½(1 ± O)`, flipped by `c`, has observable `(-1)^c O`.** -/
theorem encObs_observableToProjector (O : R) (enc : ZMod 2 → Fin k → Bool) (i : Fin k)
    (c : Bool) (h : ∀ b, enc b i = xor c (decide (b = 1))) :
    encObs (LCS.observableToProjector O) enc i = bitSign c • O := by
  rw [encObs, pvmObs, univ_zmod_two, Finset.sum_pair (by decide)]
  simp only [h, LCS.observableToProjector, LCS.observableSign]
  cases c <;> simp [bitSign] <;> module

/-- **A bit ignoring the outcome of `½(1 ± O)` has observable `±1`.** -/
theorem encObs_observableToProjector_const (O : R) (enc : ZMod 2 → Fin k → Bool) (i : Fin k)
    (c : Bool) (h : ∀ b, enc b i = c) :
    encObs (LCS.observableToProjector O) enc i = bitSign c • 1 := by
  rw [encObs, pvmObs, univ_zmod_two, Finset.sum_pair (by decide)]
  simp only [h, LCS.observableToProjector, LCS.observableSign]
  simp only [↓reduceIte, one_ne_zero]
  module

end Binary

/-! ## The qubit Paulis and the grid -/

theorem pauliX_eq : LCS.Pauli.X = signedPermMatrix (Equiv.swap 0 1) fun _ => false := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LCS.Pauli.X, signedPermMatrix, bitSign]

theorem pauliZ_eq : LCS.Pauli.Z = signedPermMatrix 1 fun j => decide (j = 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LCS.Pauli.Z, signedPermMatrix, bitSign]

theorem isSignedPerm_pauliX : IsSignedPerm LCS.Pauli.X := ⟨_, _, pauliX_eq⟩

theorem isSignedPerm_pauliZ : IsSignedPerm LCS.Pauli.Z := ⟨_, _, pauliZ_eq⟩

theorem isDiag_pauliZ : LCS.Pauli.Z.IsDiag := by
  rw [pauliZ_eq, isDiag_signedPermMatrix_iff]

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- **The nine observables of the Magic Square grid are signed permutations** when `A` and `B`
are. -/
theorem isSignedPerm_grid {A B : Matrix I I ℂ} (hA : IsSignedPerm A) (hB : IsSignedPerm B)
    (j : Fin 9) : IsSignedPerm (Introspection.HonestMagicSquare.grid A B j) := by
  fin_cases j <;> simp only [Introspection.HonestMagicSquare.grid]
  · exact hA.kronecker IsSignedPerm.one
  · exact IsSignedPerm.one.kronecker isSignedPerm_pauliX
  · exact hA.kronecker isSignedPerm_pauliX
  · exact IsSignedPerm.one.kronecker isSignedPerm_pauliZ
  · exact hB.kronecker IsSignedPerm.one
  · exact hB.kronecker isSignedPerm_pauliZ
  · exact hA.kronecker isSignedPerm_pauliZ
  · exact hB.kronecker isSignedPerm_pauliX
  · exact (hA.mul hB).kronecker (isSignedPerm_pauliZ.mul isSignedPerm_pauliX)

end MIPRE.Tailored

end
