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

/-- **The image of a projective measurement under a unital `⋆`-ring homomorphism** is one. -/
theorem map {S F : Type*} [Ring S] [StarRing S] [FunLike F R S] [RingHomClass F R S]
    [StarHomClass F R S] (f : F) (h : IsPVMIn P) : IsPVMIn fun a => f (P a) where
  star_eq a := by rw [← map_star, h.star_eq]
  idem a := by rw [← map_mul, h.idem]
  sum_eq_one := by rw [← map_sum, h.sum_eq_one, map_one]
  orthogonal hab := by rw [← map_mul, h.orthogonal hab, map_zero]

/-! ### The marginals of a projective measurement with a product outcome set -/

section Marginals

variable {B C : Type*} [Fintype B] [Fintype C] {Q : B × C → R}

/-- **The two marginals of a projective measurement multiply to the joint element**: the
off-diagonal terms of the product vanish by orthogonality, and the surviving one is
idempotent. -/
theorem marg_mul_marg (h : IsPVMIn Q) (b : B) (c : C) :
    (∑ b', Q (b', c)) * (∑ c', Q (b, c')) = Q (b, c) := by
  classical
  rw [Finset.sum_mul]
  rw [Finset.sum_eq_single b (fun b' _ hb' => ?_) fun hmem => absurd (Finset.mem_univ b) hmem]
  · rw [Finset.mul_sum,
      Finset.sum_eq_single c (fun c' _ hc' => ?_) fun hmem => absurd (Finset.mem_univ c) hmem]
    · exact h.idem (b, c)
    · exact h.orthogonal fun he => hc' (Prod.mk.injEq .. ▸ he).2.symm
  · rw [Finset.mul_sum]
    refine Finset.sum_eq_zero fun c' _ => ?_
    exact h.orthogonal fun he => hb' (Prod.mk.injEq .. ▸ he).1

/-- The other order. -/
theorem marg_mul_marg' (h : IsPVMIn Q) (b : B) (c : C) :
    (∑ c', Q (b, c')) * (∑ b', Q (b', c)) = Q (b, c) := by
  classical
  rw [Finset.sum_mul]
  rw [Finset.sum_eq_single c (fun c' _ hc' => ?_) fun hmem => absurd (Finset.mem_univ c) hmem]
  · rw [Finset.mul_sum,
      Finset.sum_eq_single b (fun b' _ hb' => ?_) fun hmem => absurd (Finset.mem_univ b) hmem]
    · exact h.idem (b, c)
    · exact h.orthogonal fun he => hb' (Prod.mk.injEq .. ▸ he).1.symm
  · rw [Finset.mul_sum]
    refine Finset.sum_eq_zero fun b' _ => ?_
    exact h.orthogonal fun he => hc' (Prod.mk.injEq .. ▸ he).2

theorem sum_marg_left (h : IsPVMIn Q) : ∑ b, (∑ c, Q (b, c)) = 1 := by
  rw [← Fintype.sum_prod_type]
  exact h.sum_eq_one

theorem sum_marg_right (h : IsPVMIn Q) : ∑ c, (∑ b, Q (b, c)) = 1 := by
  rw [Finset.sum_comm, ← Fintype.sum_prod_type]
  exact h.sum_eq_one

/-- The marginal forgetting the second outcome is projective. -/
theorem marg_left (h : IsPVMIn Q) : IsPVMIn fun b => ∑ c, Q (b, c) where
  star_eq b := by
    rw [star_sum]
    exact Finset.sum_congr rfl fun c _ => h.star_eq (b, c)
  idem b := by
    classical
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum, Finset.sum_eq_single c (fun c' _ hc' => ?_)
      fun hmem => absurd (Finset.mem_univ c) hmem]
    · exact h.idem (b, c)
    · exact h.orthogonal fun he => hc' (Prod.mk.injEq .. ▸ he).2.symm
  sum_eq_one := h.sum_marg_left
  orthogonal {b b'} hbb' := by
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun c' _ => h.orthogonal fun he => hbb' (Prod.mk.injEq .. ▸ he).1

/-- The marginal forgetting the first outcome is projective. -/
theorem marg_right (h : IsPVMIn Q) : IsPVMIn fun c => ∑ b, Q (b, c) where
  star_eq c := by
    rw [star_sum]
    exact Finset.sum_congr rfl fun b _ => h.star_eq (b, c)
  idem c := by
    classical
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum, Finset.sum_eq_single b (fun b' _ hb' => ?_)
      fun hmem => absurd (Finset.mem_univ b) hmem]
    · exact h.idem (b, c)
    · exact h.orthogonal fun he => hb' (Prod.mk.injEq .. ▸ he).1.symm
  sum_eq_one := h.sum_marg_right
  orthogonal {c c'} hcc' := by
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun b' _ => h.orthogonal fun he => hcc' (Prod.mk.injEq .. ▸ he).2

end Marginals

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

/-- **A POVM is determined by its operators**; the other fields are propositions. -/
theorem ext' {M N : POVMIn X R} (h : ∀ x, M.op x = N.op x) : M = N := by
  obtain ⟨m, _, _⟩ := M
  obtain ⟨n, _, _⟩ := N
  obtain rfl : m = n := funext fun x => Subtype.ext (h x)
  rfl

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

/-- **The marginal of a jointly coarse-grained POVM is the coarse-graining of one component**:
the fibres of `(f, g)` over `{b} × C` partition the fibre of `f` over `b`. -/
theorem sum_op_map_prod [StarOrderedRing R] {B C : Type*} [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] (M : POVMIn X R) (f : X → B) (g : X → C) (b : B) :
    ∑ c, (M.map fun a => (f a, g a)).op (b, c) = (M.map f).op b := by
  classical
  simp only [map_op, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : f a = b
  · rw [ite_eq_left h, Finset.sum_eq_single (g a) (fun c _ hc => ite_eq_right fun he => hc (by
      rw [← (Prod.mk.injEq .. ▸ he : f a = b ∧ g a = c).2]))
      fun hmem => absurd (Finset.mem_univ (g a)) hmem, ite_eq_left (by rw [h])]
  · rw [ite_eq_right h]
    exact Finset.sum_eq_zero fun c _ => ite_eq_right fun he => h (Prod.mk.injEq .. ▸ he).1

/-- The other marginal. -/
theorem sum_op_map_prod' [StarOrderedRing R] {B C : Type*} [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] (M : POVMIn X R) (f : X → B) (g : X → C) (c : C) :
    ∑ b, (M.map fun a => (f a, g a)).op (b, c) = (M.map g).op c := by
  classical
  simp only [map_op, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : g a = c
  · rw [ite_eq_left h, Finset.sum_eq_single (f a) (fun b _ hb => ite_eq_right fun he => hb (by
      rw [← (Prod.mk.injEq .. ▸ he : f a = b ∧ g a = c).1]))
      fun hmem => absurd (Finset.mem_univ (f a)) hmem, ite_eq_left (by rw [h])]
  · rw [ite_eq_right h]
    exact Finset.sum_eq_zero fun b _ => ite_eq_right fun he => h (Prod.mk.injEq .. ▸ he).2

end POVMIn

end MIPRE

end
