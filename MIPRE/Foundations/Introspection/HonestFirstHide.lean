/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AuxiliaryChecks
import MIPRE.Foundations.Introspection.Measurements
import MIPRE.Foundations.Introspection.TypedPredicate

/-! # The honest first hiding measurement

At the first hiding type no Z-prefix has yet been measured. The honest
measurement is exactly a coarse-graining of the full Pauli-X measurement:
read the dual map on the first CL register and retain the untouched X tail.
This constructs the measurement and proves perfect acceptance and commutation
on the Pauli-X/first-Hide edge, on the entire answer alphabet.
-/

noncomputable section

namespace MIPRE.Introspection.Honest

open Finset Matrix Classical Weyl
set_option linter.unusedSectionVars false

variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

def firstHideAnswer (P : CL.CLFun F ι ℓ) (x : ι → F) : (ι → F) × (ι → F) × (ι → F) :=
  (0, CLChecks.dualReadout P 0 0 x, CL.proj (P.factorOfPrefix 0 0)ᶜ x)

theorem dualReadout_first_supported (P : CL.CLFun F ι ℓ) (x : ι → F) :
    CL.proj (P.factorOfPrefix 0 0) (CLChecks.dualReadout P 0 0 x) =
      CLChecks.dualReadout P 0 0 x := by
  cases P with
  | zero => simp [CLChecks.dualReadout]
  | cons S L next =>
    simp only [CL.CLFun.factorOfPrefix_cons_zero, CLChecks.dualReadout]
    ext i
    by_cases hi : i ∈ S <;> simp [CL.proj_apply, coordinateInsert, hi]

/-- The reported dual value and untouched tail satisfy the source test exactly. -/
theorem firstHideAnswer_check (P : CL.CLFun F ι ℓ) (x : ι → F) :
    CLChecks.hidingPauli P x (firstHideAnswer P x) := by
  exact ⟨dualReadout_first_supported P x, (CL.proj_proj_self _ x).symm⟩

def firstHideOp (P : CL.CLFun F ι ℓ) (v : (ι → F) × (ι → F) × (ι → F)) :
    Matrix (ι → F) (ι → F) ℂ := synOf wX (firstHideAnswer P) v

/-- The first hiding family is an actual PVM, including zero outcomes off the honest image. -/
theorem firstHideOp_isPVM (P : CL.CLFun F ι ℓ) : IsPVM (firstHideOp P) := by
  have hX : IsPVM (proj (wX (F := F) (n := ι))) :=
    ⟨proj_conjTranspose isWeylFamily_wX,
      fun x => by rw [proj_mul_proj isWeylFamily_wX, if_pos rfl], sum_proj isWeylFamily_wX⟩
  exact hX.coarse (firstHideAnswer P)

/-- Pauli-X followed by first-Hide retains exactly the selected coarse label. -/
theorem pauli_mul_firstHide (P : CL.CLFun F ι ℓ) (x : ι → F)
    (v : (ι → F) × (ι → F) × (ι → F)) :
    proj wX x * firstHideOp P v = if firstHideAnswer P x = v then proj wX x else 0 := by
  unfold firstHideOp synOf
  rw [Finset.mul_sum]
  simp only [proj_mul_proj isWeylFamily_wX]
  by_cases h : firstHideAnswer P x = v
  · rw [if_pos h, Finset.sum_eq_single_of_mem x (by simp [h])]
    · simp
    · intro y _ hy
      simp [Ne.symm hy]
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro y hy
    have hxy : x ≠ y := by
      intro he
      subst y
      exact h (Finset.mem_filter.mp hy).2
    simp [hxy]

/-- The honest Pauli-X and first hiding operators commute on all answer labels. -/
theorem pauli_firstHide_commute (P : CL.CLFun F ι ℓ) (x : ι → F)
    (v : (ι → F) × (ι → F) × (ι → F)) : Commute (proj wX x) (firstHideOp P v) := by
  show _ * _ = _ * _
  unfold firstHideOp synOf
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  rw [proj_mul_proj isWeylFamily_wX, proj_mul_proj isWeylFamily_wX]
  by_cases h : x = y
  · subst y; rfl
  · simp [h, Ne.symm h]

/-- Every answer pair rejected on the first hiding edge has zero operator product. -/
theorem firstHide_reject_zero (P : CL.CLFun F ι ℓ) (x : ι → F)
    (v : (ι → F) × (ι → F) × (ι → F)) (h : ¬ CLChecks.hidingPauli P x v) :
    proj wX x * firstHideOp P v = 0 := by
  rw [pauli_mul_firstHide, if_neg]
  intro hv
  exact h (hv ▸ firstHideAnswer_check P x)

/-- The actual parsed Pauli-X/first-Hide predicate is the tested relation used above. -/
theorem firstHide_typed_check {P A : Type*} (L : Bool → CL.CLFun F ι ℓ)
    (X Z : P) (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : P → P → (ι → F) → (ι → F) → Bool) (w : Bool) (k : Fin ℓ) (hk : k.val = 0)
    (x : ι → F) (v : (ι → F) × (ι → F) × (ι → F)) :
    TypedPredicate.check L X Z id D DP (.inl X) (.inr (.hide k, w))
      (.pauli x) (.hide v.1 v.2.1 v.2.2) = decide (CLChecks.hidingPauli (L w) x v) := by
  simp [TypedPredicate.check, TypedPredicate.fits, TypedPredicate.directed, hk]

/-- A rejection by the full parsed predicate has zero honest operator product. -/
theorem firstHide_typed_reject_zero {P A : Type*} (L : Bool → CL.CLFun F ι ℓ)
    (X Z : P) (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : P → P → (ι → F) → (ι → F) → Bool) (w : Bool) (k : Fin ℓ) (hk : k.val = 0)
    (x : ι → F) (v : (ι → F) × (ι → F) × (ι → F))
    (h : TypedPredicate.check L X Z id D DP (.inl X) (.inr (.hide k, w))
      (.pauli x) (.hide v.1 v.2.1 v.2.2) = false) :
    proj wX x * firstHideOp (L w) v = 0 := by
  rw [firstHide_typed_check L X Z D DP w k hk] at h
  exact firstHide_reject_zero (L w) x v (of_decide_eq_false h)

end MIPRE.Introspection.Honest
