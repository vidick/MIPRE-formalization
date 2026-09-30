/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.RetainedFibre
public import MIPRE.Foundations.Introspection.BlockPOVM
public import MIPRE.Foundations.Introspection.Measurements

@[expose] public section

/-! # Completing the matching blocks of a twirled measurement

In a bipartite model whose first player's algebra carries a register, `Matrix V V 𝒜` (Phase 4 of
`planning/mipco-track.md`): a register operator `P` is `smulKron 1 P`, and a register projection
`P` with an ancilla operator `X` is `smulKron X P`.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical
open scoped ComplexOrder MatrixOrder

set_option linter.unusedSectionVars false

variable {V Y A : Type*} [Fintype V] [DecidableEq V] [Fintype Y] [DecidableEq Y]
  [Fintype A] [DecidableEq A]
variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [StarModule ℂ 𝒜] [PartialOrder 𝒜]
  [StarOrderedRing 𝒜] [StarProper 𝒜]

/-- Read a projective register, then use the POVM selected by its outcome on the ancilla. -/
def controlledPOVM (P : Y → Matrix V V ℂ) (hP : IsPVM P) (Q : Y → POVMIn A 𝒜) :
    POVMIn (Y × A) (Matrix V V 𝒜) where
  mats p := ⟨smulKron ((Q p.1).op p.2) (P p.1), by
    rw [selfAdjoint.mem_iff, star_smulKron, (Q p.1).star_op, ← star_eq_conjTranspose,
      hP.toIn.star_eq]⟩
  nonneg p := Subtype.coe_le_coe.mp (smulKron_nonneg_of_proj ((Q p.1).op_nonneg p.2)
    (by rw [hP.isSelfAdjoint, hP.idem]))
  normalized := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    change (∑ p : Y × A, smulKron ((Q p.1).op p.2) (P p.1)) = 1
    rw [Fintype.sum_prod_type]
    simp_rw [← smulKron_sum_left, POVMIn.sum_op, ← smulKron_sum_right, hP.sum_eq_one,
      smulKron_one_one]

theorem controlledPOVM_op (P : Y → Matrix V V ℂ) (hP : IsPVM P) (Q : Y → POVMIn A 𝒜)
    (p : Y × A) : (controlledPOVM P hP Q).op p = smulKron ((Q p.1).op p.2) (P p.1) := rfl

omit [StarModule ℂ 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜] in
/-- Multiplication by a readout projector retains exactly its own block. -/
theorem sum_blocks_mul_readout (P : Y → Matrix V V ℂ) (hP : IsPVM P) (Q : Y → 𝒜) (y : Y) :
    (∑ z, smulKron (Q z) (P z)) * smulKron 1 (P y) = smulKron (Q y) (P y) := by
  rw [Finset.sum_mul]
  simp_rw [smulKron_mul, mul_one, hP.mul_eq_ite]
  rw [Finset.sum_eq_single y]
  · simp
  · intro z _ hzy
    simp [hzy, smulKron_zero_right]
  · simp

omit [StarModule ℂ 𝒜] [StarProper 𝒜] in
/-- Every individual joint element is below the marginal that forgets its first outcome. -/
theorem joint_le_second_marginal (Q : POVMIn (Y × A) 𝒜) (y : Y) (a : A) :
    Q.op (y, a) ≤ (Q.map Prod.snd).op a := by
  rw [POVMIn.map_op]
  exact Finset.single_le_sum (fun p _ => Q.op_nonneg p) (by simp)

/-- The matching block is positive and dominated by the controlled marginal POVM. -/
theorem retained_block_le_completion (P : Y → Matrix V V ℂ) (hP : IsPVM P)
    (Q : Y → POVMIn (Y × A) 𝒜) (p : Y × A) :
    smulKron ((Q p.1).op p) (P p.1) ≤
      (controlledPOVM P hP (fun y => (Q y).map Prod.snd)).op p := by
  rw [controlledPOVM_op]
  apply sub_nonneg.mp
  rw [smulKron_sub_left]
  exact smulKron_nonneg_of_proj (sub_nonneg.mpr (joint_le_second_marginal (Q p.1) p.1 p.2))
    (by rw [hP.isSelfAdjoint, hP.idem])

variable {𝒞 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]

omit [StarModule ℂ 𝒜] [StarProper 𝒜] in
/-- Retain the matching ancillary block, using the exactly consistent mirror readout. -/
theorem block_retention_precompletion (Ψ : BipartiteModel 𝒞 (Matrix V V 𝒜) ℬ)
    (M : Y × A → Matrix V V 𝒜) (hM : IsPVMIn M)
    (P : Y → Matrix V V ℂ) (hP : IsPVM P) (Q : Y → POVMIn (Y × A) 𝒜)
    (R : Y → ℬ) (hR : IsPVMIn R)
    (hPR : ∀ y, Ψ.π (Ψ.πA (smulKron 1 (P y))) Ψ.ψ = Ψ.π (Ψ.πB (R y)) Ψ.ψ) :
    (∑ p : Y × A, Ψ.stateSqNorm (M p - smulKron ((Q p.1).op p) (P p.1))) ≤
      2 * (∑ y, Ψ.stateSqNorm ((∑ a, M (y, a)) - smulKron 1 (P y))) +
      2 * (∑ p : Y × A, Ψ.stateSqNorm (M p - ∑ z, smulKron ((Q z).op p) (P z))) := by
  have h := retained_fibre_dist Ψ.toStateModel (fun p => Ψ.πA (M p))
    (fun p => Ψ.πA (∑ z, smulKron ((Q z).op p) (P z))) (fun y => Ψ.πA (smulKron 1 (P y)))
    (fun y => Ψ.πB (R y)) (hM.map Ψ.πA) (hR.map Ψ.πB) hPR
    (fun y a => (Ψ.commute _ _).eq) (fun y a => (Ψ.commute _ _).eq)
  simp only [← map_mul, sum_blocks_mul_readout P hP, ← map_sub, ← map_sum] at h
  simpa only [BipartiteModel.stateSqNorm, BipartiteModel.stateNorm] using h

/-- Complete the retained blocks after averaging questions; the result is an actual family of
POVMs. -/
theorem block_retention_dist_avg {X : Type*} [Fintype X]
    (D : X → ℝ) (hD0 : ∀ x, 0 ≤ D x) (hD1 : ∑ x, D x = 1)
    (Ψ : BipartiteModel 𝒞 (Matrix V V 𝒜) ℬ) (hΨ : ‖Ψ.ψ‖ = 1)
    (M : X → Y × A → Matrix V V 𝒜) (hM : ∀ x, IsPVMIn (M x))
    (P : X → Y → Matrix V V ℂ) (hP : ∀ x, IsPVM (P x))
    (Q : X → Y → POVMIn (Y × A) 𝒜) (R : X → Y → ℬ) (hR : ∀ x, IsPVMIn (R x))
    (hPR : ∀ x y, Ψ.π (Ψ.πA (smulKron 1 (P x y))) Ψ.ψ = Ψ.π (Ψ.πB (R x y)) Ψ.ψ)
    {δ : ℝ} (hclose : ∑ x, D x *
      (2 * (∑ y, Ψ.stateSqNorm ((∑ a, M x (y, a)) - smulKron 1 (P x y))) +
       2 * (∑ p : Y × A, Ψ.stateSqNorm (M x p - ∑ z, smulKron ((Q x z).op p) (P x z)))) ≤ δ) :
    (∑ x, D x * ∑ p : Y × A, Ψ.stateSqNorm
      (M x p - smulKron (((Q x p.1).map Prod.snd).op p.2) (P x p.1))) ≤
      2 * δ + 4 * Real.sqrt δ := by
  let Bb x (p : Y × A) := smulKron ((Q x p.1).op p) (P x p.1)
  let Cc x := controlledPOVM (P x) (hP x) (fun y => (Q x y).map Prod.snd)
  have hret := Finset.sum_le_sum fun x (_ : x ∈ univ) =>
    mul_le_mul_of_nonneg_left
      (block_retention_precompletion Ψ (M x) (hM x) (P x) (hP x) (Q x) (R x) (hR x)
        (hPR x)) (hD0 x)
  have hret' : ∑ x, D x * ∑ p : Y × A, Ψ.snorm (Ψ.πA (M x p) - Ψ.πA (Bb x p)) ^ 2 ≤ δ := by
    simpa only [← map_sub, Bb, BipartiteModel.stateSqNorm, BipartiteModel.stateNorm] using
      hret.trans hclose
  have h := submeasurement_completion_dist_avg Ψ.toStateModel D hD0 hD1 hΨ
    (fun x p => Ψ.πA (M x p)) (fun x p => Ψ.πA (Bb x p))
    (fun x p => Ψ.πA ((Cc x).op p)) (fun x => (hM x).map Ψ.πA)
    (fun x p => Ψ.π_πA_nonneg (smulKron_nonneg_of_proj ((Q x p.1).op_nonneg p)
      (by rw [(hP x).isSelfAdjoint, (hP x).idem])))
    (fun x p => Ψ.π_πA_nonneg ((Cc x).op_nonneg p))
    (fun x => by rw [← map_sum, POVMIn.sum_op, map_one])
    (fun x p => OrderHomClass.mono (Ψ.π.comp Ψ.πA)
      (retained_block_le_completion (P x) (hP x) (Q x) p)) hret'
  simpa only [← map_sub, BipartiteModel.stateSqNorm, BipartiteModel.stateNorm,
    Cc, controlledPOVM_op] using h

end MIPRE.Introspection

end

end
