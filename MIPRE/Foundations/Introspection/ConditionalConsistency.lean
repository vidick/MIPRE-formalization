/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.RetainedFibre

@[expose] public section

/-! # Conditional consistency

The paper's `lem:conditional-consistency`, with constant two in the summed
squared state norm. The conditioning index may determine Alice's entire POVM.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`); the submeasurement is
self-adjoint in the joint algebra and positive on the Hilbert space, as the product of two
commuting positive operators of the two players is.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset

set_option linter.unusedSectionVars false

section State

variable {𝒞 : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] (Ψ : StateModel 𝒞)
  {I : Type*} [Fintype I]

/-- Agreement with a positive submeasurement controls distance to a PVM. -/
theorem submeasurement_agreement_dist (hΨ : ‖Ψ.ψ‖ = 1) (P C : I → 𝒞) (hP : IsPVMIn P)
    (hCsa : ∀ i, star (C i) = C i) (hC0 : ∀ i, 0 ≤ Ψ.π (C i)) (hCsum : ∑ i, Ψ.π (C i) ≤ 1) :
    (∑ i, Ψ.snorm (P i - C i) ^ 2) ≤ 2 * (1 - ∑ i, Ψ.qform (P i * C i)) := by
  classical
  have hC1 i : Ψ.π (C i) ≤ 1 :=
    (Finset.single_le_sum (fun j _ => hC0 j) (mem_univ i)).trans hCsum
  have hexp i : Ψ.snorm (P i - C i) ^ 2 = Ψ.qform (P i) +
      Ψ.qform (C i * C i) - 2 * Ψ.qform (P i * C i) := by
    have hsym : Ψ.qform (C i * P i) = Ψ.qform (P i * C i) := by
      rw [← Ψ.qform_star (P i * C i), star_mul, hP.star_eq, hCsa]
    rw [Ψ.snorm_sq_eq_qform, star_sub, hP.star_eq, hCsa, sub_mul, mul_sub, mul_sub, hP.idem,
      Ψ.qform_sub, Ψ.qform_sub, Ψ.qform_sub, hsym]
    ring
  have hmass : (∑ i, Ψ.qform (C i * C i)) ≤ 1 := by
    calc (∑ i, Ψ.qform (C i * C i)) ≤ ∑ i, Ψ.qform (C i) :=
          Finset.sum_le_sum fun i _ => Ψ.qform_mul_self_le (hC0 i) (hC1 i)
      _ = Op.qform Ψ.ψ (∑ i, Ψ.π (C i)) := by rw [Op.qform_sum]; rfl
      _ ≤ Op.qform Ψ.ψ 1 := Op.qform_mono _ hCsum
      _ = 1 := Op.qform_one _ hΨ
  simp_rw [hexp]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Ψ.qform_sum, hP.sum_eq_one, Ψ.qform_one hΨ]
  linarith

end State

section Bipartite

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] (Ψ : BipartiteModel 𝒞 𝒜 ℬ)
variable {X Y Z : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Z]
  [DecidableEq Z]

/-- Conditioning Alice's measurement on Bob's first two reported indices preserves consistency. -/
theorem conditional_consistency (hΨ : ‖Ψ.ψ‖ = 1)
    (A : Y → POVMIn (X × Z) 𝒜) (B : (X × Y) × Z → ℬ) (hB : IsPVMIn B) {δ : ℝ}
    (hagree : 1 - δ ≤ ∑ p : (X × Y) × Z, Ψ.bornProb ((A p.1.2).op (p.1.1, p.2)) (B p)) :
    (∑ p : (X × Y) × Z, Ψ.snorm
      (Ψ.πB (B p) - Ψ.πA ((A p.1.2).op (p.1.1, p.2)) * Ψ.πB (∑ z, B (p.1, z))) ^ 2) ≤
      2 * δ := by
  let R (i : X × Y) := ∑ z, B (i, z)
  let C (p : (X × Y) × Z) := Ψ.πA ((A p.1.2).op (p.1.1, p.2)) * Ψ.πB (R p.1)
  have hR : IsPVMIn R := hB.marg_left
  have hR0 (i : X × Y) : 0 ≤ Ψ.π (Ψ.πB (R i)) := by
    rw [← (hR.idem i), ← congrArg (· * R i) (hR.star_eq i)]
    exact Ψ.π_πB_nonneg (star_mul_self_nonneg _)
  have hCsa p : star (C p) = C p := by
    rw [Ψ.star_πA_mul_πB, (A p.1.2).star_op, hR.star_eq]
  have hC0 p : 0 ≤ Ψ.π (C p) := by
    rw [map_mul]
    exact ((Ψ.commute _ _).map Ψ.π).mul_nonneg (Ψ.π_πA_nonneg ((A p.1.2).op_nonneg _)) (hR0 p.1)
  have hAsum (i : X × Y) : (∑ z, (A i.2).op (i.1, z)) ≤ 1 := by
    calc (∑ z, (A i.2).op (i.1, z)) ≤ ∑ x, ∑ z, (A i.2).op (x, z) :=
          Finset.single_le_sum
            (fun x _ => Finset.sum_nonneg fun z _ => (A i.2).op_nonneg (x, z)) (mem_univ i.1)
      _ = 1 := by rw [← Fintype.sum_prod_type', POVMIn.sum_op]
  have hCsum : ∑ p, Ψ.π (C p) ≤ 1 := by
    have hterm (i : X × Y) : Ψ.π (Ψ.πA (∑ z, (A i.2).op (i.1, z))) * Ψ.π (Ψ.πB (R i)) ≤
        Ψ.π (Ψ.πB (R i)) := by
      have h := ((Ψ.commute (1 - ∑ z, (A i.2).op (i.1, z)) (R i)).map Ψ.π).mul_nonneg
        (Ψ.π_πA_nonneg (sub_nonneg.mpr (hAsum i))) (hR0 i)
      rw [map_sub, map_sub, map_one, map_one, sub_mul, one_mul, sub_nonneg] at h
      exact h
    calc (∑ p, Ψ.π (C p))
        = ∑ i, Ψ.π (Ψ.πA (∑ z, (A i.2).op (i.1, z))) * Ψ.π (Ψ.πB (R i)) := by
          simp only [C, Fintype.sum_prod_type, map_mul, map_sum, Finset.sum_mul]
      _ ≤ ∑ i, Ψ.π (Ψ.πB (R i)) := Finset.sum_le_sum fun i _ => hterm i
      _ = 1 := by rw [← map_sum, ← map_sum, hR.sum_eq_one, map_one, map_one]
  have hprod p : Ψ.πB (B p) * C p = Ψ.πA ((A p.1.2).op (p.1.1, p.2)) * Ψ.πB (B p) := by
    dsimp only [C, R]
    rw [← mul_assoc, ← (Ψ.commute _ _).eq, mul_assoc, ← map_mul, joint_mul_marginal hB]
  have h := submeasurement_agreement_dist Ψ.toStateModel hΨ (fun p => Ψ.πB (B p)) C
    (hB.map Ψ.πB) hCsa hC0 hCsum
  have heq p : Ψ.qform (Ψ.πB (B p) * C p) = Ψ.bornProb ((A p.1.2).op (p.1.1, p.2)) (B p) := by
    rw [hprod]
    rfl
  simp_rw [heq] at h
  exact h.trans (by linarith)

end Bipartite

end MIPRE.Introspection

end

end
