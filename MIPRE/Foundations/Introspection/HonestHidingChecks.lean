/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.HonestLabelSupport
import MIPRE.Foundations.Introspection.HonestHidingStep
import MIPRE.Foundations.Introspection.HidingRigidity

/-! # Exact recursion of the honest hiding checks

Adding one common local Z/dual outcome to two supported continuation answers
preserves the actual parsed hiding predicate. These are identities for the
source checks, including the later-answer choice of adaptive registers.
-/

noncomputable section

namespace MIPRE.Introspection.Honest

open Finset Matrix Classical Weyl
set_option linter.unusedSectionVars false

variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

private theorem supported_zero {V : Finset ι} {y : ι → F}
    (hy : CL.proj V y = y) {i : ι} (hi : i ∉ V) : y i = 0 := by
  have hh := congrFun hy i
  simpa only [CL.proj_apply, if_neg hi] using hh.symm

/-- The common local component and the supported tail are recovered by projection. -/
theorem proj_local_add {S V : Finset ι} (z : Fin (Fintype.card S) → F)
    (y : ι → F) (hy : CL.proj (V \ S) y = y) :
    CL.proj S (coordinateInsert S z + y) = coordinateInsert S z ∧
    CL.proj Sᶜ (coordinateInsert S z + y) = y := by
  constructor <;> funext i
  · by_cases hi : i ∈ S
    · have hz := supported_zero hy (show i ∉ V \ S by simp [hi])
      simp [CL.proj_apply, coordinateInsert, hi, hz]
    · simp [CL.proj_apply, coordinateInsert, hi]
  · by_cases hi : i ∈ S
    · have hz := supported_zero hy (show i ∉ V \ S by simp [hi])
      simp [CL.proj_apply, coordinateInsert, hi, hz]
    · simp [CL.proj_apply, coordinateInsert, hi]

private theorem proj_tail_local_add {S V T : Finset ι} (hT : T ⊆ V \ S)
    (z : Fin (Fintype.card S) → F) (y : ι → F) :
    CL.proj T (coordinateInsert S z + y) = CL.proj T y := by
  funext i
  by_cases hi : i ∈ T
  · have hn := (mem_sdiff.mp (hT hi)).2
    simp [CL.proj_apply, coordinateInsert, hi, hn]
  · simp [CL.proj_apply, hi]

private theorem proj_union_local_add {S V T : Finset ι} (hT : T ⊆ V \ S)
    (z : Fin (Fintype.card S) → F) (y : ι → F) (hy : CL.proj (V \ S) y = y) :
    CL.proj (S ∪ T) (coordinateInsert S z + y) = coordinateInsert S z + CL.proj T y := by
  funext i
  by_cases hi : i ∈ S
  · have hn : i ∉ T := fun hh => (mem_sdiff.mp (hT hh)).2 hi
    have hz := supported_zero hy (show i ∉ V \ S by simp [hi])
    simp [CL.proj_apply, coordinateInsert, hi, hn, hz]
  · by_cases ht : i ∈ T <;> simp [CL.proj_apply, coordinateInsert, hi, ht]

private theorem proj_union_compl_tail {S V T : Finset ι}
    (y : ι → F) (hy : CL.proj (V \ S) y = y) :
    CL.proj (S ∪ T)ᶜ y = CL.proj Tᶜ y := by
  funext i
  by_cases hi : i ∈ S
  · have hz := supported_zero hy (show i ∉ V \ S by simp [hi])
    simp [CL.proj_apply, hi, hz]
  · simp [CL.proj_apply, hi]

private theorem factorOfPrefix_subset {P : CL.CLFun F ι ℓ} {V : Finset ι}
    (h : P.SupportedOn V) (k : ℕ) (y : ι → F) : P.factorOfPrefix k y ⊆ V := by
  induction P generalizing V k y with
  | zero => simp
  | cons S L next ih =>
      cases k with
      | zero => exact h.1
      | succ k => exact (ih _ (h.2 _) k _).trans sdiff_subset

/-- Claimed prefixes follow the tail continuation chosen by the common local Z value. -/
theorem outputPrefix_local_add {S V : Finset ι} (L : CL.RegLinear F S)
    (next : (ι → F) → CL.CLFun F ι ℓ) (k : ℕ)
    (z : Fin (Fintype.card S) → F) (y : ι → F) (hy : CL.proj (V \ S) y = y) :
    (CL.CLFun.cons S L next).outputPrefix (k + 1) (coordinateInsert S z + y) =
      coordinateInsert S z + (next (coordinateInsert S z)).outputPrefix k y := by
  rw [CL.CLFun.outputPrefix_cons, (proj_local_add z y hy).1, (proj_local_add z y hy).2]

private theorem prefixRegister_local_add {S V : Finset ι} (L : CL.RegLinear F S)
    (next : (ι → F) → CL.CLFun F ι ℓ) (k : ℕ)
    (z : Fin (Fintype.card S) → F) (y : ι → F) (hy : CL.proj (V \ S) y = y) :
    CLChecks.prefixRegister (.cons S L next) (k + 1) (coordinateInsert S z + y) =
      S ∪ CLChecks.prefixRegister (next (coordinateInsert S z)) k y := by
  simp only [CLChecks.prefixRegister, (proj_local_add z y hy).1, (proj_local_add z y hy).2]

/-- The adjacent-hiding check lifts through an actual common adaptive local outcome. -/
theorem hidingNext_join {S V : Finset ι} (L : CL.RegLinear F S)
    (next : (ι → F) → CL.CLFun F ι ℓ)
    (h : (CL.CLFun.cons S L next).SupportedOn V) (k : ℕ)
    (z : (Fin (Fintype.card S) → F) × (Fin (Fintype.card S) → F))
    (u v : HideLabel F ι)
    (hu : CL.proj (V \ S) u.1 = u.1 ∧ CL.proj (V \ S) u.2.1 = u.2.1 ∧
      CL.proj (V \ S) u.2.2 = u.2.2)
    (hv : CL.proj (V \ S) v.1 = v.1 ∧ CL.proj (V \ S) v.2.1 = v.2.1 ∧
      CL.proj (V \ S) v.2.2 = v.2.2)
    (ht : CLChecks.hidingNext (next (coordinateInsert S z.1)) k u v) :
    CLChecks.hidingNext (.cons S L next) (k + 1) (joinHide S (z, u)) (joinHide S (z, v)) := by
  obtain ⟨hprefix, hdual, htail, hnew⟩ := ht
  dsimp only [CLChecks.hidingNext, joinHide]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [outputPrefix_local_add L next k z.1 u.1 hu.1,
      outputPrefix_local_add L next k z.1 v.1 hv.1, hprefix]
  · rw [prefixRegister_local_add L next (k + 1) z.1 v.1 hv.1,
      proj_union_local_add (CLChecks.prefixRegister_subset (h.2 _) _ _) z.2 u.2.1 hu.2.1,
      proj_union_local_add (CLChecks.prefixRegister_subset (h.2 _) _ _) z.2 v.2.1 hv.2.1,
      hdual]
  · rw [show k + 1 + 2 = (k + 2) + 1 by omega,
      prefixRegister_local_add L next (k + 2) z.1 v.1 hv.1,
      proj_union_compl_tail u.2.2 hu.2.2, proj_union_compl_tail v.2.2 hv.2.2, htail]
  · have hp := CLChecks.proj_outputPrefix_cons h (k + 1) (coordinateInsert S z.1 + v.1)
    rw [CL.CLFun.factorOfPrefix_cons_succ, hp.1, hp.2,
      (proj_local_add z.1 v.1 hv.1).1, (proj_local_add z.1 v.1 hv.1).2,
      proj_tail_local_add (factorOfPrefix_subset (h.2 _) _ _) z.2 v.2.1]
    simp only [CLChecks.dualReadout, (proj_local_add z.1 v.1 hv.1).1,
      (proj_local_add z.1 v.1 hv.1).2]
    exact hnew

/-- The terminal hiding/Read check lifts through a common local outcome.
The continuation has positive depth, as required when a terminal hiding level
is itself recursively inside the tail. -/
theorem hidingRead_join {A : Type*} {S V : Finset ι} (L : CL.RegLinear F S)
    (next : (ι → F) → CL.CLFun F ι ℓ) (hℓ : 0 < ℓ)
    (z : (Fin (Fintype.card S) → F) × (Fin (Fintype.card S) → F))
    (u : HideLabel F ι) (v : ReadLabel F ι) (a : A)
    (hu : CL.proj (V \ S) u.1 = u.1) (hv : CL.proj (V \ S) v.1 = v.1)
    (ht : CLChecks.hidingRead (next (coordinateInsert S z.1)) u (v.1, v.2, a)) :
    CLChecks.hidingRead (.cons S L next) (joinHide S (z, u))
      ((joinRead S (z, v)).1, (joinRead S (z, v)).2, a) := by
  obtain ⟨hprefix, hdual⟩ := ht
  dsimp only [CLChecks.hidingRead, joinHide, joinRead]
  constructor
  · rw [show ℓ + 1 - 1 = (ℓ - 1) + 1 by omega,
      outputPrefix_local_add L next (ℓ - 1) z.1 u.1 hu,
      outputPrefix_local_add L next (ℓ - 1) z.1 v.1 hv, hprefix]
  · rw [hdual]

/-- The first adjacent hiding check holds on the exact common X-tail labels
appearing in the stopping measurement and its next adaptive refinement. -/
theorem hidingNext_stop_join {S V : Finset ι} (L : CL.RegLinear F S)
    (next : (ι → F) → CL.CLFun F ι ℓ)
    (h : (CL.CLFun.cons S L next).SupportedOn V)
    (z : (Fin (Fintype.card S) → F) × (Fin (Fintype.card S) → F))
    (x : ↥(V \ S) → F) :
    CLChecks.hidingNext (.cons S L next) 0 (stopLabel S V (z.2, x))
      (joinHide S (z, stopHideAnswer (next (coordinateInsert S z.1)) (V \ S) x)) := by
  let Q := next (coordinateInsert S z.1)
  let t := insertRegister (V \ S) x
  let d := CLChecks.dualReadout Q 0 0 t
  let T := Q.factorOfPrefix 0 0
  have hQ : Q.SupportedOn (V \ S) := h.2 _
  have hT : T ⊆ V \ S := factorOfPrefix_subset hQ 0 0
  have hd : CL.proj (V \ S) d = d :=
    (stopHideAnswer_supported Q (V \ S) hQ x).2.1
  have hdT : CL.proj T d = d := dualReadout_first_supported Q t
  have hroot := proj_local_add (V := V) z.1 (0 : ι → F) (map_zero _)
  simp only [add_zero] at hroot
  have hp : CLChecks.prefixRegister Q 1 0 = T := by
    change CLChecks.prefixRegister Q 1 0 = Q.factorOfPrefix 0 0
    cases Q <;> simp [CLChecks.prefixRegister]
  have hcomp : (S ∪ T)ᶜ ⊆ Tᶜ := by
    intro i hi
    exact mem_compl.mpr fun ht => (mem_compl.mp hi) (mem_union_right S ht)
  change CLChecks.hidingNext (.cons S L next) 0
    (0, coordinateInsert S z.2, t)
    (coordinateInsert S z.1 + 0, coordinateInsert S z.2 + d, CL.proj Tᶜ t)
  simp only [add_zero, CLChecks.hidingNext, CL.CLFun.outputPrefix_zero]
  refine ⟨True.intro, ?_, ?_, ?_⟩
  · simp only [CLChecks.prefixRegister, hroot.1, hroot.2, union_empty]
    rw [(proj_local_add z.2 d hd).1, proj_coordinateInsert_of_subset (Subset.rfl)]
  · simp only [CLChecks.prefixRegister, hroot.1, hroot.2]
    change CL.proj (S ∪ CLChecks.prefixRegister Q 1 0)ᶜ t =
      CL.proj (S ∪ CLChecks.prefixRegister Q 1 0)ᶜ (CL.proj Tᶜ t)
    rw [hp, CL.proj_proj_of_subset hcomp]
  · simp only [CL.CLFun.factorOfPrefix_cons_succ, CL.CLFun.outputPrefix_cons,
      CLChecks.dualReadout, hroot.1, hroot.2, CL.CLFun.outputPrefix_zero, add_zero]
    change CL.proj T (coordinateInsert S z.2 + d) = d
    rw [proj_tail_local_add hT z.2 d, hdT]

end MIPRE.Introspection.Honest
