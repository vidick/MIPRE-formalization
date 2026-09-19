/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef

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

/-- `P a * P b` is `P a` on the diagonal and zero off it. -/
theorem mul_eq_ite (h : IsPVM P) (a b : Λ) :
    P a * P b = if a = b then P a else 0 := by
  by_cases hab : a = b
  · subst hab; rw [if_pos rfl, h.idem]
  · rw [if_neg hab, h.orthogonal hab]

end IsPVM

/-! ## The observable of a weighting -/

/-- `∑_a ε a • P a`, the operator a weighting of a projective measurement's outcomes
defines. -/
def pvmObs (P : Λ → Matrix n n ℂ) (ε : Λ → ℂ) : Matrix n n ℂ := ∑ a, ε a • P a

variable {P : Λ → Matrix n n ℂ}

/-- **`pvmObs P` is multiplicative.** This is the whole content of the file. -/
theorem pvmObs_mul (h : IsPVM P) (ε δ : Λ → ℂ) :
    pvmObs P ε * pvmObs P δ = pvmObs P (ε * δ) := by
  classical
  have step : ∀ a : Λ, (ε a • P a) * pvmObs P δ = ((ε * δ) a) • P a := by
    intro a
    rw [pvmObs, Finset.mul_sum, Finset.sum_eq_single a]
    · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h.idem]
      rfl
    · intro b _ hb
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h.orthogonal (Ne.symm hb), smul_zero]
    · intro hna
      exact absurd (Finset.mem_univ a) hna
  rw [pvmObs, Finset.sum_mul, Finset.sum_congr rfl fun a (_ : a ∈ univ) => step a, pvmObs]

omit [DecidableEq Λ] in
theorem pvmObs_const (h : IsPVM P) (c : ℂ) :
    pvmObs P (fun _ => c) = c • (1 : Matrix n n ℂ) := by
  rw [pvmObs, ← Finset.smul_sum, h.sum_eq_one]

omit [DecidableEq Λ] in
theorem pvmObs_one (h : IsPVM P) : pvmObs P 1 = (1 : Matrix n n ℂ) := by
  rw [show (1 : Λ → ℂ) = fun _ => (1 : ℂ) from rfl, pvmObs_const h, one_smul]

omit [DecidableEq Λ] in
theorem pvmObs_conjTranspose (h : IsPVM P) (ε : Λ → ℂ) :
    (pvmObs P ε)ᴴ = pvmObs P (star ε) := by
  rw [pvmObs, pvmObs, Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl fun a _ => by
    rw [Matrix.conjTranspose_smul, h.isSelfAdjoint]
    rfl

omit [DecidableEq Λ] in
/-- A real weighting gives a self-adjoint operator. -/
theorem pvmObs_isSelfAdjoint (h : IsPVM P) {ε : Λ → ℂ} (hε : ∀ a, star (ε a) = ε a) :
    (pvmObs P ε)ᴴ = pvmObs P ε := by
  rw [pvmObs_conjTranspose h]
  congr 1
  funext a
  exact hε a

/-- A weighting squaring to one pointwise gives an operator squaring to one. -/
theorem pvmObs_mul_self (h : IsPVM P) {ε : Λ → ℂ} (hε : ∀ a, ε a * ε a = 1) :
    pvmObs P ε * pvmObs P ε = 1 := by
  rw [pvmObs_mul h]
  rw [show ε * ε = 1 from funext fun a => hε a]
  exact pvmObs_one h

/-- Two weightings of the *same* measurement commute. -/
theorem pvmObs_comm (h : IsPVM P) (ε δ : Λ → ℂ) :
    pvmObs P ε * pvmObs P δ = pvmObs P δ * pvmObs P ε := by
  rw [pvmObs_mul h, pvmObs_mul h, mul_comm]

/-- Three weightings whose pointwise product is the constant `s` multiply to `s • 1`
**exactly**. -/
theorem pvmObs_mul_mul (h : IsPVM P) {ε δ η : Λ → ℂ} {s : ℂ}
    (hs : ∀ a, ε a * δ a * η a = s) :
    pvmObs P ε * pvmObs P δ * pvmObs P η = s • (1 : Matrix n n ℂ) := by
  rw [pvmObs_mul h, pvmObs_mul h]
  rw [show ε * δ * η = fun _ => s from funext fun a => hs a]
  exact pvmObs_const h s

end MIPRE

end
