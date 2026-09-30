/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.ConditionalConsistency
public import MIPRE.Foundations.Introspection.Measurements

@[expose] public section

/-! # Replacing a conditional hiding normalizer by its ideal prefix

The coarse outcome map may depend on the retained conditioning label. Positivity
of the ideal commuting prefix/fine-projector products lets us retain the fine
agreement without a factor depending on either outcome alphabet. The resulting
replacement costs three times each of the conditional, prefix, and fine errors.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the fine and conditioning
measurements of the second player are families in its algebra, and `A ⊗ B` is
`πA A * πB B`.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Classical

set_option linter.unusedSectionVars false

section Ring

variable {R : Type*} [Ring R] [StarRing R] {I Y Z : Type*} [Fintype I] [DecidableEq I]
  [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]

/-- Jointly reading two commuting projective measurements gives a projective measurement. -/
theorem isPVMIn_joint {A B : Type*} [Fintype A] [Fintype B] {P : A → R} {Q : B → R}
    (hP : IsPVMIn P) (hQ : IsPVMIn Q) (hc : ∀ a b, Commute (P a) (Q b)) :
    IsPVMIn (fun ab : A × B => P ab.1 * Q ab.2) where
  star_eq ab := by
    rw [star_mul, hP.star_eq, hQ.star_eq]
    exact (hc ab.1 ab.2).eq.symm
  idem ab := by
    rw [mul_assoc, ← mul_assoc (Q ab.2), (hc ab.1 ab.2).eq.symm,
      mul_assoc (P ab.1), hQ.idem, ← mul_assoc, hP.idem]
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, hQ.sum_eq_one, mul_one]
    exact hP.sum_eq_one
  orthogonal {ab ab'} h := by
    rw [mul_assoc, ← mul_assoc (Q ab.2), ← (hc ab'.1 ab.2).eq, mul_assoc, ← mul_assoc]
    by_cases h1 : ab.1 = ab'.1
    · have h2 : ab.2 ≠ ab'.2 := fun h2 => h (Prod.ext h1 h2)
      rw [hQ.orthogonal h2, mul_zero]
    · rw [hP.orthogonal h1, zero_mul]

/-- The ideal joint outcome: its prefix times the fine family coarsened with
the map selected by that prefix. -/
def conditionalIdeal (P : I → R) (Q : Y → R) (f : Y → I → Z) (p : Y × Z) : R :=
  Q p.1 * fibSumIn P (f p.1) p.2

theorem commute_fibSum_right (P : I → R) (Q : Y → R)
    (hc : ∀ y i, Commute (Q y) (P i)) (f : I → Z) (y : Y) (z : Z) :
    Commute (Q y) (fibSumIn P f z) := by
  apply Commute.sum_right
  intro i _
  exact hc y i

/-- Conditional ideal outcomes form a complete PVM although their coarse maps vary. -/
theorem conditionalIdeal_isPVM (P : I → R) (Q : Y → R) (f : Y → I → Z) (hP : IsPVMIn P)
    (hQ : IsPVMIn Q) (hc : ∀ y i, Commute (Q y) (P i)) : IsPVMIn (conditionalIdeal P Q f) where
  star_eq p :=
    (isPVMIn_joint hQ (isPVMIn_fibSumIn hP (f p.1))
      (commute_fibSum_right P Q hc _)).star_eq p
  idem p :=
    (isPVMIn_joint hQ (isPVMIn_fibSumIn hP (f p.1))
      (commute_fibSum_right P Q hc _)).idem p
  sum_eq_one := by
    simp only [conditionalIdeal, Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, (isPVMIn_fibSumIn hP _).sum_eq_one, mul_one]
    exact hQ.sum_eq_one
  orthogonal {p p'} h := by
    unfold conditionalIdeal
    rw [mul_assoc, ← mul_assoc (fibSumIn P (f p.1) p.2),
      ← (commute_fibSum_right P Q hc (f p.1) p'.1 p.2).eq, mul_assoc, ← mul_assoc]
    by_cases h1 : p.1 = p'.1
    · have h2 : p.2 ≠ p'.2 := fun h2 => h (Prod.ext h1 h2)
      rw [← h1, (isPVMIn_fibSumIn hP (f p.1)).orthogonal h2, mul_zero]
    · rw [hQ.orthogonal h1, zero_mul]

theorem conditionalIdeal_mul_normalizer (P : I → R) (Q : Y → R)
    (f : Y → I → Z) (hQ : IsPVMIn Q) (hc : ∀ y i, Commute (Q y) (P i)) (p : Y × Z) :
    conditionalIdeal P Q f p * Q p.1 = conditionalIdeal P Q f p := by
  unfold conditionalIdeal
  rw [mul_assoc, ← (commute_fibSum_right P Q hc (f p.1) p.1 p.2).eq,
    ← mul_assoc, hQ.idem]

end Ring

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] (Ψ : BipartiteModel 𝒞 𝒜 ℬ)
variable {I Y Z : Type*} [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y]
  [Fintype Z] [DecidableEq Z]

/-- Keyed coarse agreement dominates fine agreement when the ideal normalizers
commute with the fine ideal PVM. All extra cross terms are positive. -/
theorem conditional_coarse_overlap (M : I → 𝒜) (P : I → ℬ) (Q : Y → ℬ)
    (f : Y → I → Z) (hM : IsPVMIn M) (hP : IsPVMIn P) (hQ : IsPVMIn Q)
    (hc : ∀ y i, Commute (Q y) (P i)) :
    (∑ i, Ψ.bornProb (M i) (P i)) ≤
      ∑ p : Y × Z, Ψ.bornProb (fibSumIn M (f p.1) p.2) (conditionalIdeal P Q f p) := by
  have hjoint := isPVMIn_joint hQ hP hc
  have hfib (y : Y) (z : Z) :
      Ψ.bornProb (fibSumIn M (f y) z) (conditionalIdeal P Q f (y, z)) =
        ∑ i ∈ univ.filter (fun i => f y i = z),
          ∑ j ∈ univ.filter (fun j => f y j = z), Ψ.bornProb (M i) (Q y * P j) := by
    simp only [conditionalIdeal, fibSumIn, Finset.mul_sum]
    rw [Ψ.bornProb_sum_left]
    exact Finset.sum_congr rfl fun i _ => Ψ.bornProb_sum_right _ _ _
  have hdiag (y : Y) (z : Z) :
      (∑ i ∈ univ.filter (fun i => f y i = z), Ψ.bornProb (M i) (Q y * P i)) ≤
        Ψ.bornProb (fibSumIn M (f y) z) (conditionalIdeal P Q f (y, z)) := by
    rw [hfib]
    apply Finset.sum_le_sum
    intro i hi
    exact Finset.single_le_sum
      (fun j _ => Ψ.bornProb_nonneg (hM.nonneg i) (hjoint.nonneg (y, j))) hi
  have hsum (y : Y) :
      (∑ i, Ψ.bornProb (M i) (Q y * P i)) ≤
        ∑ z, Ψ.bornProb (fibSumIn M (f y) z) (conditionalIdeal P Q f (y, z)) := by
    calc
      _ = ∑ z, ∑ i ∈ univ.filter (fun i => f y i = z),
          Ψ.bornProb (M i) (Q y * P i) := (Finset.sum_fiberwise _ _ _).symm
      _ ≤ _ := Finset.sum_le_sum fun z _ => hdiag y z
  have hrecover : (∑ y, ∑ i, Ψ.bornProb (M i) (Q y * P i)) =
      ∑ i, Ψ.bornProb (M i) (P i) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Ψ.bornProb_sum_right, ← Finset.sum_mul, hQ.sum_eq_one, one_mul]
  rw [← hrecover, Fintype.sum_prod_type]
  exact Finset.sum_le_sum fun y _ => hsum y

/-- With the ideal prefix attached, keyed coarse-graining costs no more than
the fine cross-party squared error. -/
theorem conditional_coarse_ideal_distance (hΨ : ‖Ψ.ψ‖ = 1)
    (M : I → 𝒜) (P : I → ℬ) (Q : Y → ℬ)
    (f : Y → I → Z) (hM : IsPVMIn M) (hP : IsPVMIn P) (hQ : IsPVMIn Q)
    (hc : ∀ y i, Commute (Q y) (P i)) :
    (∑ p : Y × Z, Ψ.snorm
      (Ψ.πA (fibSumIn M (f p.1) p.2) * Ψ.πB (Q p.1) - Ψ.πB (conditionalIdeal P Q f p)) ^ 2) ≤
      ∑ i, Ψ.xSqNorm (M i) (P i) := by
  let C (p : Y × Z) := Ψ.πA (fibSumIn M (f p.1) p.2) * Ψ.πB (Q p.1)
  have hFib y := isPVMIn_fibSumIn hM (f y)
  have hCsa p : star (C p) = C p := by
    rw [Ψ.star_πA_mul_πB, (hFib p.1).star_eq, hQ.star_eq]
  have hC0 p : 0 ≤ Ψ.π (C p) := by
    rw [map_mul]
    exact ((Ψ.commute _ _).map Ψ.π).mul_nonneg (Ψ.π_πA_nonneg ((hFib p.1).nonneg p.2))
      (Ψ.π_πB_nonneg (hQ.nonneg p.1))
  have hCsum : ∑ p, Ψ.π (C p) ≤ 1 := by
    apply le_of_eq
    rw [← map_sum]
    simp only [C, Fintype.sum_prod_type]
    simp_rw [← Finset.sum_mul, ← map_sum, (hFib _).sum_eq_one, map_one, one_mul, ← map_sum,
      hQ.sum_eq_one, map_one]
  have hprod p : Ψ.πB (conditionalIdeal P Q f p) * C p =
      Ψ.πA (fibSumIn M (f p.1) p.2) * Ψ.πB (conditionalIdeal P Q f p) := by
    simp only [C]
    rw [← mul_assoc, ← (Ψ.commute _ _).eq, mul_assoc, ← map_mul,
      conditionalIdeal_mul_normalizer P Q f hQ hc]
  have hdist := submeasurement_agreement_dist Ψ.toStateModel hΨ
    (fun p => Ψ.πB (conditionalIdeal P Q f p)) C
    ((conditionalIdeal_isPVM P Q f hP hQ hc).map Ψ.πB) hCsa hC0 hCsum
  have heq p : Ψ.qform (Ψ.πB (conditionalIdeal P Q f p) * C p) =
      Ψ.bornProb (fibSumIn M (f p.1) p.2) (conditionalIdeal P Q f p) := by
    rw [hprod]
    rfl
  simp_rw [heq] at hdist
  have hcoarse := conditional_coarse_overlap Ψ M P Q f hM hP hQ hc
  have hfine := Ψ.one_sub_sum_bornProb_eq hΨ hM hP
  have horient : (∑ p : Y × Z, Ψ.snorm
      (Ψ.πA (fibSumIn M (f p.1) p.2) * Ψ.πB (Q p.1) - Ψ.πB (conditionalIdeal P Q f p)) ^ 2) =
      ∑ p : Y × Z, Ψ.snorm (Ψ.πB (conditionalIdeal P Q f p) - C p) ^ 2 := by
    apply Finset.sum_congr rfl
    intro p _
    rw [Ψ.snorm_sub_comm]
  rw [horient]
  linarith

omit [PartialOrder ℬ] [StarOrderedRing ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜] in
/-- Summing the complete keyed Alice PVM removes it from the normalizer error. -/
theorem conditional_normalizer_change (M : I → 𝒜) (R Q : Y → ℬ)
    (f : Y → I → Z) (hM : IsPVMIn M) :
    (∑ p : Y × Z, Ψ.snorm
      (Ψ.πA (fibSumIn M (f p.1) p.2) * Ψ.πB (R p.1) -
        Ψ.πA (fibSumIn M (f p.1) p.2) * Ψ.πB (Q p.1)) ^ 2) ≤
      ∑ y, Ψ.snorm (Ψ.πB (R y - Q y)) ^ 2 := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro y _
  have h := Ψ.sum_snorm_sq_mul_le (fun z => Ψ.πA (fibSumIn M (f y) z))
    (Ψ.isColContraction_of_isPVMIn ((isPVMIn_fibSumIn hM (f y)).map Ψ.πA)) (Ψ.πB (R y - Q y))
  simpa only [map_sub, mul_sub] using h

omit [PartialOrder ℬ] [StarOrderedRing ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜] in
/-- Replace the actual conditioning marginal by the commuting ideal prefix.
There is no factor depending on the fine, coarse, or conditioning alphabet. -/
theorem conditional_coarse_ideal_replacement [PartialOrder 𝒜] [StarOrderedRing 𝒜]
    [PartialOrder ℬ] [StarOrderedRing ℬ] (hΨ : ‖Ψ.ψ‖ = 1)
    (M : I → 𝒜) (P : I → ℬ) (Q : Y → ℬ) (B : Y × Z → ℬ) (f : Y → I → Z)
    (hM : IsPVMIn M) (hP : IsPVMIn P) (hQ : IsPVMIn Q)
    (hc : ∀ y i, Commute (Q y) (P i)) {α η ε : ℝ}
    (hfine : ∑ i, Ψ.xSqNorm (M i) (P i) ≤ ε)
    (hnorm : ∑ y, Ψ.snorm (Ψ.πB ((∑ z, B (y, z)) - Q y)) ^ 2 ≤ η)
    (hconditional : ∑ p : Y × Z, Ψ.snorm
      (Ψ.πB (B p) - Ψ.πA (fibSumIn M (f p.1) p.2) * Ψ.πB (∑ z, B (p.1, z))) ^ 2 ≤ α) :
    (∑ p : Y × Z, Ψ.snorm (Ψ.πB (B p) - Ψ.πB (conditionalIdeal P Q f p)) ^ 2) ≤
      3 * α + 3 * η + 3 * ε := by
  have hcoarse := conditional_coarse_ideal_distance Ψ hΨ M P Q f hM hP hQ hc
  have hnorm' := conditional_normalizer_change Ψ M (fun y => ∑ z, B (y, z)) Q f hM
  have htri := Ψ.sum_snorm_sq_triangle3 univ (fun p => Ψ.πB (B p))
    (fun p : Y × Z => Ψ.πA (fibSumIn M (f p.1) p.2) * Ψ.πB (∑ z, B (p.1, z)))
    (fun p : Y × Z => Ψ.πA (fibSumIn M (f p.1) p.2) * Ψ.πB (Q p.1))
    (fun p => Ψ.πB (conditionalIdeal P Q f p))
  linarith

end MIPRE.Introspection

end
