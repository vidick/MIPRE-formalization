/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.SubmeasurementCompletion

@[expose] public section

/-! # Retaining a classical fibre after twirling

The consistency marginal lets us retain the matching block of a nearby measurement.
An exactly consistent projective mirror moves the rightmost projector to the front,
where it is a contraction. No outcome-count factor enters the estimate.

Stated for a state model (Phase 4 of `planning/mipco-track.md`).
-/

noncomputable section

namespace MIPRE.Introspection

open Finset

set_option linter.unusedSectionVars false

variable {𝒞 : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] (Ψ : StateModel 𝒞)
  {Y A : Type*} [Fintype Y] [DecidableEq Y] [Fintype A] [DecidableEq A]

/-- Multiplication on the right by a projector is contractive when it has a commuting mirror. -/
theorem snorm_right_projector_le (P R E : 𝒞) (hRsa : star R = R) (hRid : R * R = R)
    (hPR : Ψ.π P Ψ.ψ = Ψ.π R Ψ.ψ) (hER : E * R = R * E) :
    Ψ.snorm (E * P) ^ 2 ≤ Ψ.snorm E ^ 2 := by
  have he : Ψ.snorm (E * P) = Ψ.snorm (R * E) := by
    simp only [StateModel.snorm, Op.snorm, map_mul, mul_apply_eq_comp, hPR]
    rw [← mul_apply_eq_comp, ← map_mul, hER, map_mul]
    rfl
  rw [he]
  have h := Ψ.snorm_mul_le (Ψ.bnd_one_of_isStarProjection ⟨hRid, hRsa⟩) E
  rw [one_mul] at h
  exact pow_le_pow_left₀ (Ψ.snorm_nonneg _) h 2


/-- A joint PVM element is unchanged by multiplication by its own first marginal. -/
theorem joint_mul_marginal {M : Y × A → 𝒞} (hM : IsPVMIn M) (y : Y) (a : A) :
    M (y, a) * (∑ b, M (y, b)) = M (y, a) := by
  rw [Finset.mul_sum]
  refine (Finset.sum_eq_single a ?_ ?_).trans (hM.idem (y, a))
  · intro b _ hba
    exact hM.orthogonal fun h => hba (Prod.mk.inj h).2.symm
  · intro h
    exact False.elim (h (mem_univ a))

/-- A row of a joint PVM is a column contraction. -/
theorem isColContraction_row {M : Y × A → 𝒞} (hM : IsPVMIn M) (y : Y) :
    Ψ.IsColContraction fun a => M (y, a) := by
  refine le_trans ?_ (Ψ.isColContraction_of_isPVMIn hM)
  rw [Fintype.sum_prod_type]
  exact Finset.single_le_sum
    (f := fun y' => ∑ a, star (Ψ.π (M (y', a))) * Ψ.π (M (y', a)))
    (fun y' _ => Finset.sum_nonneg fun a _ => star_mul_self_nonneg _) (Finset.mem_univ y)

/-- Keeping the matching target fibre costs twice the marginal error plus twice the original
error. -/
theorem retained_fibre_dist (M T : Y × A → 𝒞) (P R : Y → 𝒞) (hM : IsPVMIn M) (hR : IsPVMIn R)
    (hPR : ∀ y, Ψ.π (P y) Ψ.ψ = Ψ.π (R y) Ψ.ψ)
    (hMR : ∀ y a, M (y, a) * R y = R y * M (y, a))
    (hTR : ∀ y a, T (y, a) * R y = R y * T (y, a)) :
    (∑ p : Y × A, Ψ.snorm (M p - T p * P p.1) ^ 2) ≤
      2 * (∑ y, Ψ.snorm ((∑ a, M (y, a)) - P y) ^ 2) +
      2 * (∑ p : Y × A, Ψ.snorm (M p - T p) ^ 2) := by
  have hfirst y : (∑ a, Ψ.snorm (M (y, a) - M (y, a) * P y) ^ 2) ≤
      Ψ.snorm ((∑ a, M (y, a)) - P y) ^ 2 := by
    have he a : M (y, a) - M (y, a) * P y = M (y, a) * ((∑ b, M (y, b)) - P y) := by
      rw [mul_sub, joint_mul_marginal hM]
    simp_rw [he]
    exact Ψ.sum_snorm_sq_mul_le _ (isColContraction_row Ψ hM y) _
  have hfirstSum := Finset.sum_le_sum fun y (_ : y ∈ univ) => hfirst y
  rw [sum_prod_eq] at hfirstSum
  have hsecond : (∑ p : Y × A, Ψ.snorm (M p * P p.1 - T p * P p.1) ^ 2) ≤
      ∑ p : Y × A, Ψ.snorm (M p - T p) ^ 2 := by
    apply Finset.sum_le_sum
    intro p _
    rw [← sub_mul]
    apply snorm_right_projector_le Ψ _ (R p.1) _ (hR.star_eq p.1) (hR.idem p.1) (hPR p.1)
    rw [sub_mul, hMR p.1 p.2, hTR p.1 p.2, mul_sub]
  have htri := Ψ.sum_snorm_sq_triangle univ M (fun p => M p * P p.1) (fun p => T p * P p.1)
  linarith

end MIPRE.Introspection

end

end
