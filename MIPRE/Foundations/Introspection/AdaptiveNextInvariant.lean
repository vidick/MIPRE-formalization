/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AdaptiveNextFactor

/-! # Closing the next-prefix measurement invariant

The next residual PVM is constructed from the previous prefix and current
coordinate branch. Unattainable next prefixes receive a fixed default PVM;
their ambient operators are zero. The answer component, including any dummy
answer, is retained without an additional support assumption.
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Matrix Classical Weyl
set_option linter.unusedSectionVars false

variable {ι F H A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype A] [DecidableEq A] {ℓ : ℕ}

abbrev AttainableStageCoordinate (P : CL.CLFun F ι ℓ) (k : ℕ) :=
  (y : ↥(prefixOutcomes P k)) × (Fin (Fintype.card (P.factorOfPrefix k y)) → F)

theorem exists_advancePrefix_source (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (v : ι → F) (hv : v ∈ prefixOutcomes P (k + 1)) :
    ∃ p : AttainableStageCoordinate P k, advancePrefix P k p.1 p.2 = v := by
  obtain ⟨x, _, rfl⟩ := mem_image.mp hv
  exact ⟨⟨⟨(P.truncate k).eval x, mem_image.mpr ⟨x, mem_univ _, rfl⟩⟩,
    (adaptiveLinearOutcome P k x).2⟩, advancePrefix_eval hP k x⟩

def nextPrefixSource (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (v : ι → F) (hv : v ∈ prefixOutcomes P (k + 1)) :
    AttainableStageCoordinate P k := (exists_advancePrefix_source P hP k v hv).choose

theorem nextPrefixSource_advance (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (v : ι → F) (hv : v ∈ prefixOutcomes P (k + 1)) :
    advancePrefix P k (nextPrefixSource P hP k v hv).1
      (nextPrefixSource P hP k v hv).2 = v :=
  (exists_advancePrefix_source P hP k v hv).choose_spec

/-- Transport the already constructed residual block to an equal next label. -/
def nextResidualOpAt (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F) (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F)
    (v : ι → F) (hv : advancePrefix P k y z = v)
    (N : Matrix (((↥(stageRemaining P k y \ P.factorOfPrefix k y) → F) × H) × A)
      (((↥(stageRemaining P k y \ P.factorOfPrefix k y) → F) × H) × A) ℂ) :
    Matrix ((stageRemaining P (k + 1) v → F) × (H × A))
      ((stageRemaining P (k + 1) v → F) × (H × A)) ℂ :=
  hv ▸ nextResidualOp P hP k y z N

theorem nextResidualOpAt_isPVM (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F) (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F)
    (v : ι → F) (hv : advancePrefix P k y z = v)
    (N : A → Matrix (((↥(stageRemaining P k y \ P.factorOfPrefix k y) → F) × H) × A) _ ℂ)
    (hN : IsPVM N) : IsPVM (nextResidualOpAt P hP k y z v hv ∘ N) := by
  subst v
  exact nextResidualOp_isPVM P hP k y z N hN

theorem prefixResidualOp_nextResidualOpAt (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F) (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F)
    (v : ι → F) (hv : advancePrefix P k y z = v)
    (N : Matrix (((↥(stageRemaining P k y \ P.factorOfPrefix k y) → F) × H) × A) _ ℂ) :
    prefixResidualOp P (k + 1) (advancePrefix P k y z) (nextResidualOp P hP k y z N) =
      prefixResidualOp P (k + 1) v (nextResidualOpAt P hP k y z v hv N) := by
  subst v
  rfl

/-- The residual projectors after advancing to the next prefix. -/
def nextPrefixResidual (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (a₀ : A) (D : AdaptiveDilationFamily P k H A) (v : ι → F) (a : A) :
    Matrix ((stageRemaining P (k + 1) v → F) × (H × A))
      ((stageRemaining P (k + 1) v → F) × (H × A)) ℂ :=
  if hv : v ∈ prefixOutcomes P (k + 1) then
    let p := nextPrefixSource P hP k v hv
    nextResidualOpAt P hP k p.1 p.2 v (nextPrefixSource_advance P hP k v hv) (D p.1 p.2 a)
  else readout (fun _ => a₀) a

theorem nextPrefixResidual_isPVM (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (a₀ : A) (D : AdaptiveDilationFamily P k H A)
    (hD : ∀ y z, IsPVM (D y z)) (v : ι → F) :
    IsPVM (nextPrefixResidual P hP k a₀ D v) := by
  by_cases hv : v ∈ prefixOutcomes P (k + 1)
  · let p := nextPrefixSource P hP k v hv
    have he : nextPrefixResidual P hP k a₀ D v =
        nextResidualOpAt P hP k p.1 p.2 v (nextPrefixSource_advance P hP k v hv) ∘ D p.1 p.2 := by
      funext a
      simp only [nextPrefixResidual, dif_pos hv, Function.comp_apply, p]
    rw [he]
    exact nextResidualOpAt_isPVM P hP k p.1 p.2 v _ _ (hD p.1 p.2)
  · have he : nextPrefixResidual P hP k a₀ D v =
        readout (fun _ : (stageRemaining P (k + 1) v → F) × (H × A) => a₀) := by
      funext a
      simp only [nextPrefixResidual, dif_neg hv]
    rw [he]
    exact readout_isPVM _

/-- Retain the original residual answer and advance only the prefix label. -/
def advanceStageAnswer (P : CL.CLFun F ι ℓ) (k : ℕ) (p : AdaptiveStageAnswer P k A) :
    (ι → F) × A := (advancePrefix P k p.1 p.2.1, p.2.2)

theorem adaptiveReplacementJointOp_off_prefix (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ) (D : AdaptiveDilationFamily P k H A)
    (p : AdaptiveStageAnswer P k A) (hp : p.1 ∉ prefixOutcomes P k) :
    adaptiveReplacementJointOp P hP k D p = 0 :=
  prefixResidualOp_eq_zero P k p.1 hp _

theorem adaptiveReplacementJointOp_off_next (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ) (D : AdaptiveDilationFamily P k H A)
    (p : AdaptiveStageAnswer P k A)
    (hp : (advanceStageAnswer P k p).1 ∉ prefixOutcomes P (k + 1)) :
    adaptiveReplacementJointOp P hP k D p = 0 := by
  by_cases hy : p.1 ∈ prefixOutcomes P k
  · rw [adaptiveReplacementJointOp_next_factor P hP k D p.1 hy]
    exact prefixResidualOp_eq_zero P (k + 1) _ hp _
  · exact adaptiveReplacementJointOp_off_prefix P hP k D p hy

theorem advanceStageAnswer_injective_support (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ)
    (p q : AdaptiveStageAnswer P k A) (hp : p.1 ∈ prefixOutcomes P k)
    (hq : q.1 ∈ prefixOutcomes P k)
    (he : advanceStageAnswer P k p = advanceStageAnswer P k q) : p = q := by
  have hcoord := advancePrefix_injective hP k
    (a₁ := ⟨⟨p.1, hp⟩, p.2.1⟩) (a₂ := ⟨⟨q.1, hq⟩, q.2.1⟩) (congrArg Prod.fst he)
  have ha : p.2.2 = q.2.2 := congrArg Prod.snd he
  cases p with | mk y p =>
    cases q with | mk y' q =>
      have hy : y = y' := congrArg (fun r : AttainableStageCoordinate P k => r.1.val) hcoord
      subst y'
      have hz : p.1 = q.1 := by
        have hh := Sigma.mk.inj_iff.mp hcoord
        exact eq_of_heq hh.2
      exact congrArg (Sigma.mk y) (Prod.ext hz ha)

/-- The actual advanced joint PVM has the required next-prefix product form.
All off-image branches vanish exactly; no conclusion-shaped premise is used. -/
theorem adaptiveReplacementJointOp_next_reassembly (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ) (a₀ : A)
    (D : AdaptiveDilationFamily P k H A) (v : ι → F) (a : A) :
    fibSum (adaptiveReplacementJointOp P hP k D) (advanceStageAnswer P k) (v, a) =
      prefixResidualOp P (k + 1) v (nextPrefixResidual P hP k a₀ D v a) := by
  by_cases hv : v ∈ prefixOutcomes P (k + 1)
  · let p := nextPrefixSource P hP k v hv
    let q : AdaptiveStageAnswer P k A := ⟨p.1, (p.2, a)⟩
    have hq : advanceStageAnswer P k q = (v, a) :=
      Prod.ext (nextPrefixSource_advance P hP k v hv) rfl
    have hm : q ∈ univ.filter (fun r => advanceStageAnswer P k r = (v, a)) := by simp [hq]
    have heq : fibSum (adaptiveReplacementJointOp P hP k D) (advanceStageAnswer P k) (v, a) =
        adaptiveReplacementJointOp P hP k D q := by
      apply Finset.sum_eq_single_of_mem q hm
      intro r hr hrq
      apply adaptiveReplacementJointOp_off_prefix P hP k D r
      intro hrg
      exact hrq (advanceStageAnswer_injective_support P hP k r q hrg p.1.property
        ((mem_filter.mp hr).2.trans hq.symm))
    rw [heq]
    change adaptiveReplacementJointOp P hP k D ⟨p.1.val, (p.2, a)⟩ = _
    rw [adaptiveReplacementJointOp_next_factor P hP k D p.1 p.1.property]
    have hp := nextPrefixSource_advance P hP k v hv
    change prefixResidualOp P (k + 1) (advancePrefix P k p.1 p.2)
      (nextResidualOp P hP k p.1 p.2 (D p.1 p.2 a)) = _
    simp only [nextPrefixResidual, dif_pos hv]
    exact prefixResidualOp_nextResidualOpAt P hP k p.1 p.2 v hp _
  · rw [prefixResidualOp_eq_zero P (k + 1) v hv]
    apply Finset.sum_eq_zero
    intro p hp
    apply adaptiveReplacementJointOp_off_next P hP k D p
    have he : (advanceStageAnswer P k p).1 = v := congrArg Prod.fst (mem_filter.mp hp).2
    simpa only [he] using hv

/-- The reassembled next-prefix family is a projective measurement on the
same ambient register and the single enlarged auxiliary space. -/
theorem nextPrefixJoint_isPVM (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (a₀ : A) (D : AdaptiveDilationFamily P k H A)
    (hD : ∀ y z, IsPVM (D y z)) :
    IsPVM (fun p : (ι → F) × A =>
      prefixResidualOp P (k + 1) p.1 (nextPrefixResidual P hP k a₀ D p.1 p.2)) := by
  have h := isPVM_fibSum (adaptiveReplacementJointOp_isPVM P hP k D hD)
    (advanceStageAnswer P k)
  have he : fibSum (adaptiveReplacementJointOp P hP k D) (advanceStageAnswer P k) =
      (fun p : (ι → F) × A =>
        prefixResidualOp P (k + 1) p.1 (nextPrefixResidual P hP k a₀ D p.1 p.2)) := by
    funext p
    exact adaptiveReplacementJointOp_next_reassembly P hP k a₀ D p.1 p.2
  rwa [he] at h

end MIPRE.Introspection
end
