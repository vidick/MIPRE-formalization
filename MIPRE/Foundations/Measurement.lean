/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import MIPRE.Tactics

@[expose] public section

/-!
# Measurements in a `⋆`-algebra

The measurements of the analyses, stated in any `⋆`-algebra rather than in a matrix algebra, so
that the same statements hold in the players' algebras of a bipartite model
(`MIPRE/Foundations/BipartiteModel.lean`).

* `IsPVMIn P`: a projective measurement, self-adjoint idempotents summing to one and mutually
  orthogonal. In a matrix algebra, or any C*-algebra, orthogonality follows from the other three
  (`MIPRE.IsPVM.orthogonal` for matrices); in a general ring it does not, so it is a field.
* `POVMIn X R`: a positive operator valued measure in an ordered `⋆`-algebra, with the fields of
  the matrix `MIPRE.POVM` verbatim, so that a matrix POVM is one (`MIPRE.POVM.toIn`).
* `pvmObs P ε = ∑_a ε a • P a`, the observable of a weighting of the outcomes, a ring
  homomorphism in `ε` for a projective measurement (`IsPVMIn.pvmObs_mul`).

The matrix versions (`MIPRE/Foundations/PVM.lean`, `MIPRE/Foundations/POVMValue.lean`) are these
in `Matrix n n ℂ`.
-/

namespace MIPRE

open Finset

variable {R : Type*} {Λ : Type*}

/-! ## Projective measurements -/

/-- **A projective measurement** in a `⋆`-ring: self-adjoint idempotents, summing to one and
mutually orthogonal. -/
structure IsPVMIn [Ring R] [StarRing R] [Fintype Λ] (P : Λ → R) : Prop where
  /-- Each element is self-adjoint. -/
  star_eq : ∀ a, star (P a) = P a
  /-- Each element is idempotent. -/
  idem : ∀ a, P a * P a = P a
  /-- The elements sum to one. -/
  sum_eq_one : ∑ a, P a = 1
  /-- Distinct elements are orthogonal. -/
  orthogonal : ∀ {a b : Λ}, a ≠ b → P a * P b = 0

namespace IsPVMIn

variable [Ring R] [StarRing R] [Fintype Λ] {P : Λ → R}

theorem isStarProjection (h : IsPVMIn P) (a : Λ) : IsStarProjection (P a) :=
  ⟨h.idem a, h.star_eq a⟩

/-- In a star-ordered ring, the elements of a projective measurement are nonnegative. -/
theorem nonneg [PartialOrder R] [StarOrderedRing R] (h : IsPVMIn P) (a : Λ) : 0 ≤ P a := by
  have : P a = star (P a) * P a := by rw [h.star_eq, h.idem]
  rw [this]
  exact star_mul_self_nonneg _

/-- `P a * P b` is `P a` on the diagonal and zero off it. -/
theorem mul_eq_ite [DecidableEq Λ] (h : IsPVMIn P) (a b : Λ) :
    P a * P b = if a = b then P a else 0 := by
  by_cases hab : a = b
  · subst hab; rw [ite_eq_left rfl, h.idem]
  · rw [ite_eq_right hab, h.orthogonal hab]

/-- **Coarse-graining a projective measurement gives a projective measurement.** -/
theorem coarse {Λ' : Type*} [Fintype Λ'] [DecidableEq Λ'] (h : IsPVMIn P) (f : Λ → Λ') :
    IsPVMIn (fun c => ∑ a ∈ univ.filter fun a => f a = c, P a) where
  star_eq c := by
    rw [star_sum]
    exact Finset.sum_congr rfl fun a _ => h.star_eq a
  idem c := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mul_sum, Finset.sum_eq_single_of_mem a ha
      (fun a' _ ha' => h.orthogonal ha'.symm)]
    exact h.idem a
  sum_eq_one := by
    rw [Finset.sum_fiberwise (univ : Finset Λ) f P]
    exact h.sum_eq_one
  orthogonal {c c'} hcc' := by
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun a ha => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_eq_zero fun a' ha' => h.orthogonal fun haa' => hcc' ?_
    rw [Finset.mem_filter] at ha ha'
    rw [← ha.2, ← ha'.2, haa']

end IsPVMIn

/-! ## The observable of a weighting -/

/-- `∑_a ε a • P a`, the operator a weighting of a measurement's outcomes defines. -/
def pvmObs [Fintype Λ] [AddCommMonoid R] [Module ℂ R] (P : Λ → R) (ε : Λ → ℂ) : R :=
  ∑ a, ε a • P a

section Obs

variable [Ring R] [StarRing R] [Algebra ℂ R] [Fintype Λ] {P : Λ → R}

/-- **`pvmObs P` is multiplicative** for a projective measurement. -/
theorem IsPVMIn.pvmObs_mul (h : IsPVMIn P) (ε δ : Λ → ℂ) :
    pvmObs P ε * pvmObs P δ = pvmObs P (ε * δ) := by
  classical
  have step : ∀ a : Λ, (ε a • P a) * pvmObs P δ = ((ε * δ) a) • P a := by
    intro a
    rw [pvmObs, Finset.mul_sum, Finset.sum_eq_single a]
    · rw [smul_mul_smul_comm, h.idem]
      rfl
    · intro b _ hb
      rw [smul_mul_smul_comm, h.orthogonal (Ne.symm hb), smul_zero]
    · intro hna
      exact absurd (Finset.mem_univ a) hna
  rw [pvmObs, Finset.sum_mul, Finset.sum_congr rfl fun a (_ : a ∈ univ) => step a, pvmObs]

theorem IsPVMIn.pvmObs_const (h : IsPVMIn P) (c : ℂ) : pvmObs P (fun _ => c) = c • (1 : R) := by
  rw [pvmObs, ← Finset.smul_sum, h.sum_eq_one]

theorem IsPVMIn.pvmObs_one (h : IsPVMIn P) : pvmObs P 1 = (1 : R) := by
  rw [show (1 : Λ → ℂ) = fun _ => (1 : ℂ) from rfl, h.pvmObs_const, one_smul]

theorem IsPVMIn.star_pvmObs [StarModule ℂ R] (h : IsPVMIn P) (ε : Λ → ℂ) :
    star (pvmObs P ε) = pvmObs P (star ε) := by
  rw [pvmObs, pvmObs, star_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [star_smul, h.star_eq]; rfl

/-- A real weighting gives a self-adjoint operator. -/
theorem IsPVMIn.pvmObs_star_eq [StarModule ℂ R] (h : IsPVMIn P) {ε : Λ → ℂ}
    (hε : ∀ a, star (ε a) = ε a) :
    star (pvmObs P ε) = pvmObs P ε := by
  rw [h.star_pvmObs]
  congr 1
  funext a
  exact hε a

/-- A weighting squaring to one pointwise gives an operator squaring to one. -/
theorem IsPVMIn.pvmObs_mul_self (h : IsPVMIn P) {ε : Λ → ℂ} (hε : ∀ a, ε a * ε a = 1) :
    pvmObs P ε * pvmObs P ε = 1 := by
  rw [h.pvmObs_mul, show ε * ε = 1 from funext fun a => hε a]
  exact h.pvmObs_one

/-- Two weightings of the *same* measurement commute. -/
theorem IsPVMIn.pvmObs_comm (h : IsPVMIn P) (ε δ : Λ → ℂ) :
    pvmObs P ε * pvmObs P δ = pvmObs P δ * pvmObs P ε := by
  rw [h.pvmObs_mul, h.pvmObs_mul, mul_comm]

/-- Three weightings whose pointwise product is the constant `s` multiply to `s • 1`
**exactly**. -/
theorem IsPVMIn.pvmObs_mul_mul (h : IsPVMIn P) {ε δ η : Λ → ℂ} {s : ℂ}
    (hs : ∀ a, ε a * δ a * η a = s) :
    pvmObs P ε * pvmObs P δ * pvmObs P η = s • (1 : R) := by
  rw [h.pvmObs_mul, h.pvmObs_mul, show ε * δ * η = fun _ => s from funext fun a => hs a]
  exact h.pvmObs_const s

end Obs

/-! ## Positive operator valued measures -/

/-- **A positive operator valued measure** in an ordered `⋆`-ring, with outcomes `X`: the fields
of the matrix `MIPRE.POVM`. -/
structure POVMIn (X : Type*) (R : Type*) [Fintype X] [Ring R] [StarRing R] [PartialOrder R] where
  /-- The measurement operators, one for each outcome. -/
  mats : X → selfAdjoint R
  /-- Each measurement operator is nonnegative. -/
  nonneg : ∀ x, 0 ≤ mats x
  /-- The measurement operators sum to one. -/
  normalized : ∑ x, mats x = 1

namespace POVMIn

variable {X : Type*} [Fintype X] [Ring R] [StarRing R] [PartialOrder R]

/-- The measurement operator of an outcome, as an element of `R`. -/
def op (M : POVMIn X R) (x : X) : R := (M.mats x : R)

theorem op_eq (M : POVMIn X R) (x : X) : M.op x = (M.mats x : R) := rfl

theorem star_op (M : POVMIn X R) (x : X) : star (M.op x) = M.op x := (M.mats x).2

theorem sum_op (M : POVMIn X R) : ∑ x, M.op x = 1 := by
  rw [show (∑ x, M.op x) = ((∑ x, M.mats x : selfAdjoint R) : R) from
    (AddSubmonoidClass.coe_finsetSum _ _).symm, M.normalized]
  rfl

theorem op_nonneg (M : POVMIn X R) (x : X) : 0 ≤ M.op x := Subtype.coe_le_coe.mpr (M.nonneg x)

/-- Each measurement operator is at most one. -/
theorem op_le_one [StarOrderedRing R] (M : POVMIn X R) (x : X) : M.op x ≤ 1 := by
  rw [← M.sum_op]
  exact Finset.single_le_sum (fun y _ => M.op_nonneg y) (Finset.mem_univ x)

/-- **The coarse-graining of a POVM along a map of outcomes**: each new outcome gets the sum of
the operators of its fibre. -/
def map [StarOrderedRing R] {Y : Type*} [Fintype Y] [DecidableEq Y] (f : X → Y)
    (M : POVMIn X R) : POVMIn Y R where
  mats y := ∑ x ∈ Finset.univ.filter (fun x => f x = y), M.mats x
  nonneg y := by
    have h : (0 : R) ≤ ∑ x ∈ Finset.univ.filter (fun x => f x = y), (M.mats x : R) :=
      Finset.sum_nonneg fun x _ => M.op_nonneg x
    rw [← AddSubmonoidClass.coe_finsetSum] at h
    exact Subtype.coe_le_coe.mp h
  normalized := (Finset.sum_fiberwise Finset.univ f M.mats).trans M.normalized

theorem map_op [StarOrderedRing R] {Y : Type*} [Fintype Y] [DecidableEq Y] (f : X → Y)
    (M : POVMIn X R) (y : Y) :
    (M.map f).op y = ∑ x ∈ Finset.univ.filter (fun x => f x = y), M.op x :=
  AddSubmonoidClass.coe_finsetSum _ _

end POVMIn

end MIPRE

end
