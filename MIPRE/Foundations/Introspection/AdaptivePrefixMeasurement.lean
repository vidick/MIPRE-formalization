/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.PrefixConditioning

@[expose] public section

/-! # Reassembling measurements across actual adaptive CL prefixes

The CL prefix projectors give orthogonal branches even though their coordinate
splits depend on the prefix. Residual PVMs therefore assemble to a genuine PVM,
and recombining a common answer alphabet preserves exactly the weighted
residual error, with no number-of-prefixes factor.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): a residual operator at the
prefix `y` is a block matrix over the remaining register with entries in any algebra, reinserted
behind the prefix projector by `prefixResidualOp`; residual measurements are measurements of these
block matrices (`IsPVMIn`, `POVMIn`), their errors are measured on the register model `Ξ.reg` of the
remaining coordinates, and the reinserted residual POVMs form one POVM of block matrices over the
ambient register (`prefixResidualPOVM`), nonnegative because `prefixResidualOp` is the
`⋆`-homomorphism `regSplitHom` applied to `smulKron M Q` with `Q` a projector
(`prefixResidualOp_nonneg`). The exact additivity of errors over the prefix branches holds on any
model whose first player's algebra is the block matrices over the ambient register.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical Honest
open scoped Kronecker
set_option linter.unusedSectionVars false

variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜]

/-- Reinsertion commutes with the adjoint: the prefix projector is self-adjoint. -/
theorem prefixResidualOp_conjTranspose [StarModule ℂ 𝒜] (P : CL.CLFun F ι ℓ) (k : ℕ)
    (y : ι → F) (M : Matrix (↥((CLChecks.prefixRegister P k y)ᶜ) → F) _ 𝒜) :
    prefixResidualOp P k y (star M) = star (prefixResidualOp P k y M) := by
  rw [prefixResidualOp, prefixResidualOp, ← map_star, star_smulKron]
  have hq : (prefixProjector P k y)ᴴ = prefixProjector P k y :=
    (readout_isPVM _).isSelfAdjoint y
  rw [hq]

/-- Residual operators from distinct prefixes have disjoint support in the
one ambient register, despite their different local coordinate types. -/
theorem prefixResidualOp_orthogonal (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y z : ι → F) (hyz : y ≠ z)
    (M : Matrix (↥((CLChecks.prefixRegister P k y)ᶜ) → F) _ 𝒜)
    (N : Matrix (↥((CLChecks.prefixRegister P k z)ᶜ) → F) _ 𝒜) :
    prefixResidualOp P k y M * prefixResidualOp P k z N = 0 := by
  let Q (x : ι → F) : Matrix (ι → F) (ι → F) 𝒜 := smulKron 1 (hidingPrefixOp P k (some x))
  have hM : prefixResidualOp P k y M * Q y = prefixResidualOp P k y M := by
    dsimp only [Q]
    rw [← prefixResidualOp_one P hP, ← prefixResidualOp_mul, mul_one]
  have hN : Q z * prefixResidualOp P k z N = prefixResidualOp P k z N := by
    dsimp only [Q]
    rw [← prefixResidualOp_one P hP, ← prefixResidualOp_mul, one_mul]
  have hQ : Q y * Q z = 0 := by
    simp only [Q, hidingPrefixOp_some, smulKron_mul, one_mul]
    rw [(readout_isPVM (P.truncate k).eval).orthogonal hyz, smulKron_zero_right]
  calc
    _ = (prefixResidualOp P k y M * Q y) * (Q z * prefixResidualOp P k z N) := by rw [hM, hN]
    _ = prefixResidualOp P k y M * (Q y * Q z) * prefixResidualOp P k z N := by
      simp only [mul_assoc]
    _ = 0 := by rw [hQ, mul_zero, zero_mul]

/-- The reinserted residual operators of a family of residual measurements sum to one: the prefix
projectors over all prefixes do. -/
theorem sum_prefixResidualOp_eq_one (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) {A : (ι → F) → Type*} [∀ y, Fintype (A y)]
    (M : (y : ι → F) → A y → Matrix (↥((CLChecks.prefixRegister P k y)ᶜ) → F)
      (↥((CLChecks.prefixRegister P k y)ᶜ) → F) 𝒜)
    (hM : ∀ y, ∑ a, M y a = 1) :
    ∑ y, ∑ a, prefixResidualOp P k y (M y a) = 1 := by
  simp_rw [← prefixResidualOp_sum, hM, prefixResidualOp_one P hP, hidingPrefixOp_some]
  rw [← smulKron_sum_right, (readout_isPVM (P.truncate k).eval).sum_eq_one, smulKron_one_one]

/-- Prefix-indexed residual PVMs give a projective joint measurement on the
ambient register. Residual answer alphabets may depend on the prefix. -/
theorem prefixResidual_isPVM [StarModule ℂ 𝒜] (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) {A : (ι → F) → Type*} [∀ y, Fintype (A y)]
    (M : (y : ι → F) → A y → Matrix (↥((CLChecks.prefixRegister P k y)ᶜ) → F)
      (↥((CLChecks.prefixRegister P k y)ᶜ) → F) 𝒜)
    (hM : ∀ y, IsPVMIn (M y)) :
    IsPVMIn (fun p : (y : ι → F) × A y => prefixResidualOp P k p.1 (M p.1 p.2)) where
  star_eq p := by rw [← prefixResidualOp_conjTranspose, (hM p.1).star_eq]
  idem p := by rw [← prefixResidualOp_mul, (hM p.1).idem]
  sum_eq_one := by
    rw [Fintype.sum_sigma]
    exact sum_prefixResidualOp_eq_one P hP k M fun y => (hM y).sum_eq_one
  orthogonal {p q} hpq := by
    obtain ⟨y, a⟩ := p
    obtain ⟨z, b⟩ := q
    by_cases hyz : y = z
    · subst hyz
      have hab : a ≠ b := fun hab => hpq (hab ▸ rfl)
      dsimp only
      rw [← prefixResidualOp_mul, (hM y).orthogonal hab, prefixResidualOp, smulKron_zero_left,
        map_zero]
    · exact prefixResidualOp_orthogonal P hP k y z hyz _ _

/-- If the answer alphabet is shared, the ambient PVM can forget its prefix
label and report only the common answer. -/
theorem prefixResidual_reassembled_isPVM [StarModule ℂ 𝒜] (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ) {A : Type*} [Fintype A]
    (M : (y : ι → F) → A → Matrix (↥((CLChecks.prefixRegister P k y)ᶜ) → F)
      (↥((CLChecks.prefixRegister P k y)ᶜ) → F) 𝒜)
    (hM : ∀ y, IsPVMIn (M y)) :
    IsPVMIn (fun a => ∑ y, prefixResidualOp P k y (M y a)) where
  star_eq a := by
    rw [star_sum]
    simp_rw [← prefixResidualOp_conjTranspose, (hM _).star_eq]
  idem a := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.mul_sum, Finset.sum_eq_single y]
    · rw [← prefixResidualOp_mul, (hM y).idem]
    · intro z _ hzy
      exact prefixResidualOp_orthogonal P hP k y z hzy.symm _ _
    · simp
  sum_eq_one := by
    rw [Finset.sum_comm]
    exact sum_prefixResidualOp_eq_one P hP k M fun y => (hM y).sum_eq_one
  orthogonal {a b} hab := by
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_eq_zero fun z _ => ?_
    by_cases hyz : y = z
    · subst hyz
      rw [← prefixResidualOp_mul, (hM y).orthogonal hab, prefixResidualOp, smulKron_zero_left,
        map_zero]
    · exact prefixResidualOp_orthogonal P hP k y z hyz _ _

section Reinserted

variable [StarModule ℂ 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜]

/-- A nonnegative residual operator stays nonnegative behind its prefix projector: it is the image
of `M ⊗ Q`, with `Q` a projector, under the `⋆`-homomorphism of the coordinate split. -/
theorem prefixResidualOp_nonneg (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F)
    {M : Matrix (↥((CLChecks.prefixRegister P k y)ᶜ) → F) _ 𝒜} (hM : 0 ≤ M) :
    0 ≤ prefixResidualOp P k y M := by
  have hsa : (prefixProjector P k y)ᴴ = prefixProjector P k y :=
    (readout_isPVM _).isSelfAdjoint y
  have hid : prefixProjector P k y * prefixProjector P k y = prefixProjector P k y :=
    (readout_isPVM _).idem y
  have hQ : (prefixProjector P k y)ᴴ * prefixProjector P k y = prefixProjector P k y := by
    rw [hsa, hid]
  have h := OrderHomClass.mono (regSplitHom (A := 𝒜) (ambientSplit (CLChecks.prefixRegister P k y)))
    (smulKron_nonneg_of_proj hM hQ)
  rwa [map_zero] at h

/-- **The residual POVMs reinserted behind their actual adaptive prefix projectors**: one POVM of
the ambient register, whose outcome records the prefix. Residual answer alphabets may depend on
the prefix. -/
def prefixResidualPOVM (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ) (k : ℕ)
    {A : (ι → F) → Type*} [∀ y, Fintype (A y)]
    (M : (y : ι → F) → POVMIn (A y) (Matrix (↥((CLChecks.prefixRegister P k y)ᶜ) → F)
      (↥((CLChecks.prefixRegister P k y)ᶜ) → F) 𝒜)) :
    POVMIn ((y : ι → F) × A y) (Matrix (ι → F) (ι → F) 𝒜) where
  mats p := ⟨prefixResidualOp P k p.1 ((M p.1).op p.2), by
    rw [selfAdjoint.mem_iff, ← prefixResidualOp_conjTranspose, (M p.1).star_op]⟩
  nonneg p := Subtype.coe_le_coe.mp (prefixResidualOp_nonneg P k p.1 ((M p.1).op_nonneg p.2))
  normalized := Subtype.ext (by
    rw [AddSubmonoidClass.coe_finsetSum]
    change ∑ p : (y : ι → F) × A y, prefixResidualOp P k p.1 ((M p.1).op p.2) = 1
    rw [Fintype.sum_sigma]
    exact sum_prefixResidualOp_eq_one P hP k (fun y => (M y).op) fun y => (M y).sum_op)

@[simp]
theorem prefixResidualPOVM_op (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ) (k : ℕ)
    {A : (ι → F) → Type*} [∀ y, Fintype (A y)]
    (M : (y : ι → F) → POVMIn (A y) (Matrix (↥((CLChecks.prefixRegister P k y)ᶜ) → F)
      (↥((CLChecks.prefixRegister P k y)ᶜ) → F) 𝒜)) (p : (y : ι → F) × A y) :
    (prefixResidualPOVM P hP k M).op p = prefixResidualOp P k p.1 ((M p.1).op p.2) := rfl

/-- Reinserted residual PVMs form a PVM. -/
theorem prefixResidualPOVM_isPVM (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ) (k : ℕ)
    {A : (ι → F) → Type*} [∀ y, Fintype (A y)]
    (M : (y : ι → F) → POVMIn (A y) (Matrix (↥((CLChecks.prefixRegister P k y)ᶜ) → F)
      (↥((CLChecks.prefixRegister P k y)ᶜ) → F) 𝒜)) (hM : ∀ y, IsPVMIn (M y).op) :
    IsPVMIn (prefixResidualPOVM P hP k M).op :=
  prefixResidual_isPVM P hP k (fun y => (M y).op) hM

end Reinserted

variable [StarModule ℂ 𝒜] {𝒞 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring ℬ]
  [StarRing ℬ] [Algebra ℂ ℬ]

/-- Orthogonal prefix branches add their squared errors exactly, on any model whose first
player's algebra is the block matrices over the ambient register. No projectivity or
self-adjointness is required of the residual errors. -/
theorem stateSqNorm_sum_prefixResidualOp (Ψ : BipartiteModel 𝒞 (Matrix (ι → F) (ι → F) 𝒜) ℬ)
    (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ) (k : ℕ)
    (M : (y : ι → F) → Matrix (↥((CLChecks.prefixRegister P k y)ᶜ) → F)
      (↥((CLChecks.prefixRegister P k y)ᶜ) → F) 𝒜) :
    Ψ.stateSqNorm (∑ y, prefixResidualOp P k y (M y)) =
      ∑ y, Ψ.stateSqNorm (prefixResidualOp P k y (M y)) := by
  have hg : star (∑ y, prefixResidualOp P k y (M y)) *
      (∑ y, prefixResidualOp P k y (M y)) =
      ∑ y, star (prefixResidualOp P k y (M y)) * prefixResidualOp P k y (M y) := by
    rw [star_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.mul_sum]
    apply Finset.sum_eq_single y
    · intro z _ hzy
      rw [← prefixResidualOp_conjTranspose]
      exact prefixResidualOp_orthogonal P hP k y z hzy.symm _ _
    · simp
  rw [Ψ.stateSqNorm_eq, hg, map_sum, Ψ.qform_sum]
  exact Finset.sum_congr rfl fun y _ => (Ψ.stateSqNorm_eq _).symm

/-- Forgetting the prefix label preserves the exact conditional error law.
This is the concrete gluing step needed after local mixing and dilation. -/
theorem prefixResidual_reassembled_distance (Ξ : BipartiteModel 𝒞 𝒜 ℬ) (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ) {A : Type*} [Fintype A]
    (M N : (y : ι → F) → A → Matrix (↥((CLChecks.prefixRegister P k y)ᶜ) → F)
      (↥((CLChecks.prefixRegister P k y)ᶜ) → F) 𝒜) :
    (∑ a, (Ξ.reg (ι → F)).stateSqNorm
      ((∑ y, prefixResidualOp P k y (M y a)) - ∑ y, prefixResidualOp P k y (N y a))) =
      ∑ y, prefixWeight P k y * ∑ a,
        (Ξ.reg (↥((CLChecks.prefixRegister P k y)ᶜ) → F)).stateSqNorm (M y a - N y a) := by
  simp_rw [← Finset.sum_sub_distrib, ← prefixResidualOp_sub,
    stateSqNorm_sum_prefixResidualOp _ P hP, stateSqNorm_prefixResidualOp Ξ P hP]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

end MIPRE.Introspection

end

end
