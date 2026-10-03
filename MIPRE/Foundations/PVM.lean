/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef
public import MIPRE.Foundations.Measurement
public import MIPRE.Tactics

@[expose] public section

/-!
# Observables of a projective measurement

A projective measurement `P : Λ → Matrix n n ℂ` and a weighting `ε : Λ → ℂ` give the operator
`pvmObs P ε = ∑_a ε a • P a`. The one fact worth isolating is that this is a **ring
homomorphism** in `ε`:

`pvmObs P ε * pvmObs P δ = pvmObs P (ε * δ)`,  `pvmObs P 1 = 1`,

because the projections are mutually orthogonal (`IsPVM.orthogonal`). Everything the rigidity
arguments want about signed sums of a projective measurement follows: with `ε` valued in
`{±1}`, `pvmObs P ε` is a self-adjoint reflection; two weightings of the *same* measurement
commute, whatever they are; and if `ε δ η` is constantly `s` then `pvmObs P ε * pvmObs P δ *
pvmObs P η = s • 1` exactly.

That last one is what a linear-constraint-system game's Alice-side dilation buys: the three
reflections of one constraint commute and multiply to the constraint's sign, with no error
term. Blueprint `lem:ms-direct-anticomm` is the consumer.

The rules are those of a projective measurement in any `⋆`-algebra
(`MIPRE/Foundations/Measurement.lean`, `IsPVMIn`), of which a matrix projective measurement is one
(`IsPVM.toIn`): this file proves only what is about matrices, that the elements of a matrix
projective measurement are mutually orthogonal (`IsPVM.orthogonal`), and derives the rest.
-/

noncomputable section

namespace MIPRE

open Finset Matrix
open scoped ComplexOrder MatrixOrder

variable {n Λ : Type*} [Fintype n] [DecidableEq n] [Fintype Λ] [DecidableEq Λ]

/-- A **projective measurement** on `Matrix n n ℂ`: self-adjoint idempotents summing to one.
Stated as a predicate on a bare family rather than a bundled structure, because the families
this is applied to arrive from `exists_projective_dilation` in exactly this shape. -/
structure IsPVM (P : Λ → Matrix n n ℂ) : Prop where
  /-- Each element is self-adjoint. -/
  isSelfAdjoint : ∀ a, (P a)ᴴ = P a
  /-- Each element is idempotent. -/
  idem : ∀ a, P a * P a = P a
  /-- The elements sum to one. -/
  sum_eq_one : ∑ a, P a = 1

namespace IsPVM

variable {P : Λ → Matrix n n ℂ}

omit [DecidableEq Λ] in
theorem posSemidef (h : IsPVM P) (a : Λ) : (P a).PosSemidef := by
  have : P a = (P a)ᴴ * P a := by rw [h.isSelfAdjoint, h.idem]
  rw [this]
  exact Matrix.posSemidef_conjTranspose_mul_self _

omit [DecidableEq Λ] in
theorem nonneg (h : IsPVM P) (a : Λ) : (0 : Matrix n n ℂ) ≤ P a :=
  Matrix.nonneg_iff_posSemidef.mpr (h.posSemidef a)

/-- **The elements of a projective measurement are mutually orthogonal.** Conjugating
`∑_c P c = 1` by `P a` makes the off-diagonal compressions a family of positive matrices
summing to zero, so each is zero, and `P a P b P a = 0` forces `P b P a = 0`. -/
theorem orthogonal (h : IsPVM P) {a b : Λ} (hab : a ≠ b) : P a * P b = 0 := by
  classical
  -- the compressions `P a P c P a` for `c ≠ a` sum to zero
  have hsum : ∑ c ∈ univ.erase a, P a * P c * P a = 0 := by
    have hall : ∑ c : Λ, P a * P c * P a = P a := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, h.sum_eq_one, Matrix.mul_one, h.idem]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)] at hall
    have hdiag : P a * P a * P a = P a := by rw [h.idem, h.idem]
    rw [hdiag] at hall
    have := hall
    linear_combination (norm := module) this
  -- each compression is positive
  have hpos : ∀ c : Λ, (0 : Matrix n n ℂ) ≤ P a * P c * P a := by
    intro c
    have hc : P a * P c * P a = (P a)ᴴ * P c * P a := by rw [h.isSelfAdjoint]
    rw [hc]
    exact Matrix.nonneg_iff_posSemidef.mpr ((h.posSemidef c).conjTranspose_mul_mul_same _)
  have hb : P a * P b * P a = 0 := by
    refine le_antisymm ?_ (hpos b)
    calc P a * P b * P a ≤ ∑ c ∈ univ.erase a, P a * P c * P a :=
          Finset.single_le_sum (fun c _ => hpos c) (Finset.mem_erase.mpr ⟨hab.symm, mem_univ b⟩)
      _ = 0 := hsum
  -- hence `P b P a = 0`, and its adjoint
  have hstar : (P b * P a)ᴴ * (P b * P a) = 0 := by
    rw [Matrix.conjTranspose_mul, h.isSelfAdjoint, h.isSelfAdjoint]
    calc P a * P b * (P b * P a) = P a * (P b * P b) * P a := by
          simp only [Matrix.mul_assoc]
      _ = P a * P b * P a := by rw [h.idem]
      _ = 0 := hb
  have hba : P b * P a = 0 := Matrix.conjTranspose_mul_self_eq_zero.mp hstar
  have := congrArg Matrix.conjTranspose hba
  rwa [Matrix.conjTranspose_mul, h.isSelfAdjoint, h.isSelfAdjoint,
    Matrix.conjTranspose_zero] at this

/-- **A matrix projective measurement is a projective measurement in the matrix algebra**
(`MIPRE/Foundations/Measurement.lean`), orthogonality included. -/
theorem toIn (h : IsPVM P) : IsPVMIn P :=
  ⟨h.isSelfAdjoint, h.idem, h.sum_eq_one, h.orthogonal⟩

omit [DecidableEq Λ] in
/-- Conversely, a projective measurement in the matrix algebra is a matrix projective
measurement. -/
theorem _root_.MIPRE.IsPVMIn.toIsPVM {P : Λ → Matrix n n ℂ} (h : IsPVMIn P) : IsPVM P :=
  ⟨h.star_eq, h.idem, h.sum_eq_one⟩

/-- **Coarse-graining a projective measurement gives a projective measurement.** Summing the
elements over a level set of `f` preserves self-adjointness, and mutual orthogonality
(`IsPVM.orthogonal`) makes the sum idempotent; the level sets partition the outcomes, so the sums
still add to one. This is what makes the expansion stage's convolutions projective. -/
theorem coarse {Λ' : Type*} [Fintype Λ'] [DecidableEq Λ'] (h : IsPVM P) (f : Λ → Λ') :
    IsPVM (fun c => ∑ a ∈ univ.filter fun a => f a = c, P a) :=
  (h.toIn.coarse f).toIsPVM

/-- `P a * P b` is `P a` on the diagonal and zero off it. -/
theorem mul_eq_ite (h : IsPVM P) (a b : Λ) :
    P a * P b = if a = b then P a else 0 :=
  h.toIn.mul_eq_ite a b

end IsPVM

/-! ## The observable of a weighting

`pvmObs P ε = ∑_a ε a • P a` is defined for any measurement in any `ℂ`-module
(`MIPRE/Foundations/Measurement.lean`); these are its rules for a matrix projective measurement,
the instances of `IsPVMIn.pvmObs_mul` and its companions. -/

variable {P : Λ → Matrix n n ℂ}

end MIPRE

end

end
