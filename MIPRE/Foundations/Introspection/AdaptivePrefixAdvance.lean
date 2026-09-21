/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AdaptiveZFactor
import MIPRE.Foundations.Introspection.SamplingRegister

/-! # Advancing actual adaptive prefix labels

Adding the next selected-coordinate answer preserves the preceding claimed
prefix and the next remaining register. For attainable old prefixes, the
old label and the new coordinate answer are both recovered exactly. The
actual next sampler output is the advance by its selected linear readout.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

/-- Add a current-coordinate answer to the preceding ambient prefix label. -/
def advancePrefix (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F)
    (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F) : ι → F :=
  y + coordinateInsert (P.factorOfPrefix k y) z

namespace CLChecks

/-- Reading the claimed prefix only uses its selected prefix coordinates. -/
theorem outputPrefix_eq_of_agree (P : CL.CLFun F ι ℓ) (k : ℕ) (y x : ι → F)
    (hag : ∀ i ∈ prefixRegister P k y, x i = y i) :
    P.outputPrefix k x = P.outputPrefix k y := by
  induction P generalizing k y x with
  | zero => cases k <;> rfl
  | cons S L next ih =>
    cases k with
    | zero => rfl
    | succ k =>
      have he : CL.proj S x = CL.proj S y := by
        ext i
        by_cases hi : i ∈ S
        · simp only [CL.proj_apply, if_pos hi]
          exact hag i (mem_union_left _ hi)
        · simp [CL.proj_apply, hi]
      rw [CL.CLFun.outputPrefix_cons, CL.CLFun.outputPrefix_cons, he]
      congr 1
      apply ih
      intro i hi
      by_cases hiS : i ∈ S
      · simp [CL.proj_apply, hiS]
      · simpa only [CL.proj_apply, mem_compl, hiS, not_false_eq_true, if_true] using
          hag i (mem_union_right S hi)

end CLChecks

theorem advancePrefix_old_prefix {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y : ι → F)
    (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F) :
    P.outputPrefix k (advancePrefix P k y z) = P.outputPrefix k y := by
  apply CLChecks.outputPrefix_eq_of_agree
  intro i hi
  have hn : i ∉ P.factorOfPrefix k y := by
    intro hu
    exact (mem_sdiff.mp (CLChecks.stageFactor_subset_residual hP k y hu)).2 hi
  simp [advancePrefix, coordinateInsert, hn]

/-- The next support depends on the old prefix, and is unchanged by inserting
an arbitrary answer on the current selected factor. -/
theorem advancePrefix_register {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y : ι → F)
    (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F) :
    CLChecks.prefixRegister P (k + 1) (advancePrefix P k y z) =
      CLChecks.prefixRegister P (k + 1) y :=
  CLChecks.prefixRegister_congr hP k (advancePrefix_old_prefix hP k y z)

theorem advancePrefix_factor {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y : ι → F)
    (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F) :
    P.factorOfPrefix k (advancePrefix P k y z) = P.factorOfPrefix k y :=
  CLChecks.stageFactor_congr hP k (advancePrefix_old_prefix hP k y z)

theorem advancePrefix_remaining {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y : ι → F)
    (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F) :
    stageRemaining P (k + 1) (advancePrefix P k y z) = stageRemaining P (k + 1) y := by
  exact congrArg (fun S : Finset ι => Sᶜ) (advancePrefix_register hP k y z)

/-- The actual next sampler output is the advanced old label and selected
linear result in its concrete finite coordinate presentation. -/
theorem advancePrefix_eval {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (x : ι → F) :
    advancePrefix P k ((P.truncate k).eval x)
      (coordinateLinear (CLChecks.stageLinear P k ((P.truncate k).eval x))
        (coordinateRestrict (P.factorOfPrefix k ((P.truncate k).eval x)) x)) =
      (P.truncate (k + 1)).eval x := by
  rw [advancePrefix, coordinateLinear_restrict, coordinateInsert_restrict,
    CL.RegLinear.proj_apply]
  exact (CLChecks.truncate_eval_step hP k x).symm

variable [Fintype F] [DecidableEq F]

theorem outputPrefix_of_mem_prefixOutcomes {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y : ι → F) (hy : y ∈ prefixOutcomes P k) :
    P.outputPrefix k y = y := by
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
  rw [← hP.outputPrefix_eval k x, CLChecks.outputPrefix_outputPrefix hP _ (le_refl k)]

theorem advancePrefix_recover_prefix {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y : ι → F) (hy : y ∈ prefixOutcomes P k)
    (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F) :
    P.outputPrefix k (advancePrefix P k y z) = y := by
  rw [advancePrefix_old_prefix hP, outputPrefix_of_mem_prefixOutcomes hP k y hy]

theorem coordinateRestrict_old_prefix {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y : ι → F) (hy : y ∈ prefixOutcomes P k) :
    coordinateRestrict (P.factorOfPrefix k y) y = 0 := by
  have hp : CL.proj (CLChecks.prefixRegister P k y) y = y :=
    (CLChecks.proj_prefixRegister hP k y).trans (outputPrefix_of_mem_prefixOutcomes hP k y hy)
  ext j
  have hn : ((Fintype.equivFin (P.factorOfPrefix k y)).symm j).val ∉
      CLChecks.prefixRegister P k y :=
    (mem_sdiff.mp (CLChecks.stageFactor_subset_residual hP k y
      ((Fintype.equivFin (P.factorOfPrefix k y)).symm j).property)).2
  have hz := congrFun hp ((Fintype.equivFin (P.factorOfPrefix k y)).symm j)
  change y ((Fintype.equivFin (P.factorOfPrefix k y)).symm j) = 0
  exact (by simpa only [CL.proj_apply, if_neg hn] using hz.symm)

theorem advancePrefix_recover_coordinate {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y : ι → F) (hy : y ∈ prefixOutcomes P k)
    (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F) :
    coordinateRestrict (P.factorOfPrefix k y) (advancePrefix P k y z) = z := by
  rw [advancePrefix, map_add, coordinateRestrict_old_prefix hP k y hy,
    coordinateRestrict_insert, zero_add]

/-- On attainable old prefixes the advanced label uniquely determines both
the preceding prefix and the new selected-coordinate answer. -/
theorem advancePrefix_injective {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) :
    Function.Injective (fun p : (y : ↥(prefixOutcomes P k)) ×
        (Fin (Fintype.card (P.factorOfPrefix k y)) → F) => advancePrefix P k p.1 p.2) := by
  rintro ⟨y, z⟩ ⟨y', z'⟩ he
  have hy : y = y' := by
    apply Subtype.ext
    have hh := congrArg (P.outputPrefix k) he
    simpa only [advancePrefix_recover_prefix hP k y y.property,
      advancePrefix_recover_prefix hP k y' y'.property] using hh
  cases hy
  have hz := congrArg (coordinateRestrict (P.factorOfPrefix k y)) he
  have hzz : z = z' := by
    simpa only [advancePrefix_recover_coordinate hP k y y.property] using hz
  cases hzz
  rfl

/-- The old sampled prefix together with the next selected linear outcome. -/
def adaptiveLinearOutcome (P : CL.CLFun F ι ℓ) (k : ℕ) (x : ι → F) :
    (y : ι → F) × (Fin (Fintype.card (P.factorOfPrefix k y)) → F) :=
  ⟨(P.truncate k).eval x,
    coordinateLinear (CLChecks.stageLinear P k ((P.truncate k).eval x))
      (coordinateRestrict (P.factorOfPrefix k ((P.truncate k).eval x)) x)⟩

theorem advancePrefix_adaptiveLinearOutcome {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (x : ι → F) :
    advancePrefix P k (adaptiveLinearOutcome P k x).1 (adaptiveLinearOutcome P k x).2 =
      (P.truncate (k + 1)).eval x := advancePrefix_eval hP k x

/-- The next prefix readout is exactly the coarse-graining of the old prefix
and current linear readout under the concrete next-label map. -/
theorem advancePrefix_readout {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (v : ι → F) :
    readout (P.truncate (k + 1)).eval v =
      fibSum (readout (adaptiveLinearOutcome P k))
        (fun p => advancePrefix P k p.1 p.2) v := by
  rw [fibSum_readout]
  congr 1
  funext x
  exact (advancePrefix_adaptiveLinearOutcome hP k x).symm

variable [Algebra (ZMod 2) F] {H : Type*} [Fintype H] [DecidableEq H]

/-- The actual selected linear outcome factors into the old prefix projector
and the local current-stage spectral readout. -/
theorem adaptiveLinear_readout_factor (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F) (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F) :
    (aOp (readout (adaptiveLinearOutcome P k) ⟨y, z⟩) : Matrix ((ι → F) × H) _ ℂ) =
      prefixResidualOp P k y (registerReadout (stageSplit P hP k y) wZ
        (coordinateLinear (CLChecks.stageLinear P k y)) z) := by
  rw [registerReadout_wZ, prefixResidualOp_readout P hP]
  congr 1
  ext x x'
  simp only [readout, Matrix.diagonal_apply]
  by_cases hxx : x = x'
  · subst x'
    simp only [if_true]
    apply if_congr _ rfl rfl
    by_cases hy : (P.truncate k).eval x = y
    · subst y
      simp only [adaptiveLinearOutcome, Sigma.mk.inj_iff, heq_eq_eq, true_and, Prod.mk.injEq]
      rfl
    · have hn : adaptiveLinearOutcome P k x ≠ ⟨y, z⟩ := by
        intro he
        exact hy (congrArg Sigma.fst he)
      simp [hn, hy]
  · simp [hxx]

/-- Reassembling old-prefix/current-linear projectors by the advanced label
gives exactly the next honest prefix measurement. -/
theorem advancePrefix_projector_assembly (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (v : ι → F) :
    (aOp (Honest.hidingPrefixOp P (k + 1) (some v)) : Matrix ((ι → F) × H) _ ℂ) =
      fibSum
        (fun p : (y : ι → F) × (Fin (Fintype.card (P.factorOfPrefix k y)) → F) =>
          prefixResidualOp P k p.1 (registerReadout (stageSplit P hP k p.1) wZ
            (coordinateLinear (CLChecks.stageLinear P k p.1)) p.2))
        (fun p => advancePrefix P k p.1 p.2) v := by
  rw [Honest.hidingPrefixOp_some, advancePrefix_readout hP, ← fibSum_aOp]
  apply Finset.sum_congr rfl
  intro p _
  exact adaptiveLinear_readout_factor P hP k p.1 p.2

end MIPRE.Introspection

end
