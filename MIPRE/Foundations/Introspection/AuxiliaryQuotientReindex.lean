/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AuxiliaryReindex
import MIPRE.Foundations.Introspection.TypedQuotientPredicate

/-! # Quotient hiding checks commute with coordinate permutations

Only equality of dual quotient classes is transported. The chosen canonical
representatives themselves need not commute with a permutation.
-/

noncomputable section
namespace MIPRE.Introspection.AuxiliaryQuotient
open Finset CL CLChecks AuxiliaryDual Classical
set_option linter.unusedSectionVars false
variable {F ι κ A PA PT : Type*} [Field F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {ℓ : ℕ}

theorem reindex_eq_iff (e : ι ≃ κ) (x y : ι → F) :
    reindexEquiv e x = reindexEquiv e y ↔ x = y := (reindexEquiv e).injective.eq_iff

theorem dot_reindex (e : ι ≃ κ) (x y : ι → F) :
    (∑ i, reindexEquiv e x i * reindexEquiv e y i) = ∑ i, x i * y i :=
  e.symm.sum_comp (fun i => x i * y i)

/-- Equality of stage-dual outputs is intrinsic, despite their chosen labels. -/
theorem stageDual_reindex_eq_iff (e : ι ≃ κ) (P : CLFun F ι ℓ)
    (k : ℕ) (y x z : ι → F) :
    stageDual (P.reindex e) k (reindexEquiv e y) (reindexEquiv e x) =
      stageDual (P.reindex e) k (reindexEquiv e y) (reindexEquiv e z) ↔
      stageDual P k y x = stageDual P k y z := by
  simp only [stageDual, registerDual_eq_iff_dot]
  simp only [← CL.RegLinear.toLinearMap_apply, stageLinear_toLinearMap,
    CLFun.mapOfPrefix_reindex, CLFun.factorOfPrefix_reindex, LinearMap.comp_apply,
    LinearEquiv.coe_coe, ← map_sub, ← reindexEquiv_proj]
  constructor
  · intro h v hv
    have hh := h (reindexEquiv e v) (by simp only [LinearEquiv.symm_apply_apply, hv, map_zero])
    rwa [dot_reindex] at hh
  · intro h v hv
    obtain ⟨u, rfl⟩ := (reindexEquiv (F := F) e).surjective v
    simp only [LinearEquiv.symm_apply_apply] at hv
    rw [dot_reindex]
    apply h u
    apply (reindexEquiv e).injective
    simpa only [map_zero] using hv

/-- Relabel all binary-register components, retaining ordinary and Pauli answers. -/
def answerEquiv (e : ι ≃ κ) : ParsedAnswer (ι → F) A PA ≃ ParsedAnswer (κ → F) A PA where
  toFun
    | .pauli a => .pauli a
    | .pair y a => .pair (reindexEquiv e y) a
    | .read y yp a => .read (reindexEquiv e y) (reindexEquiv e yp) a
    | .hide y yp x => .hide (reindexEquiv e y) (reindexEquiv e yp) (reindexEquiv e x)
  invFun
    | .pauli a => .pauli a
    | .pair y a => .pair ((reindexEquiv e).symm y) a
    | .read y yp a => .read ((reindexEquiv e).symm y) ((reindexEquiv e).symm yp) a
    | .hide y yp x => .hide ((reindexEquiv e).symm y) ((reindexEquiv e).symm yp)
        ((reindexEquiv e).symm x)
  left_inv a := by cases a <;> simp
  right_inv a := by cases a <;> simp

@[simp] theorem fits_answerEquiv (e : ι ≃ κ) (t : QuestionType PT ℓ)
    (a : ParsedAnswer (ι → F) A PA) :
    TypedPredicate.fits t (answerEquiv e a) = TypedPredicate.fits t a := by
  rcases t with p | ⟨t,w⟩
  · cases a <;> rfl
  · cases t <;> cases a <;> rfl

theorem hidingNext_reindex (e : ι ≃ κ) (P : CLFun F ι ℓ) (k : ℕ)
    (y yp x z zp v : ι → F) :
    hidingNext (P.reindex e) k
      (reindexEquiv e y, reindexEquiv e yp, reindexEquiv e x)
      (reindexEquiv e z, reindexEquiv e zp, reindexEquiv e v) ↔
      hidingNext P k (y, yp, x) (z, zp, v) := by
  simp only [hidingNext, outputPrefix_reindex, prefixRegister_reindex,
    ← CLChecks.map_compl, ← reindexEquiv_proj, reindex_eq_iff,
    stageDual_reindex_eq_iff]

theorem hidingPauli_reindex (e : ι ≃ κ) (P : CLFun F ι ℓ)
    (x y yp z : ι → F) :
    hidingPauli (P.reindex e) (reindexEquiv e x)
      (reindexEquiv e y, reindexEquiv e yp, reindexEquiv e z) ↔
      hidingPauli P x (y, yp, z) := by
  unfold hidingPauli
  rw [← map_zero (reindexEquiv (F := F) e), stageDual_reindex_eq_iff,
    CLFun.factorOfPrefix_reindex, ← CLChecks.map_compl, ← reindexEquiv_proj,
    ← reindexEquiv_proj, reindex_eq_iff]

theorem hidingRead_reindex (e : ι ≃ κ) (P : CLFun F ι ℓ)
    (y yp x z zp : ι → F) (a : A) :
    CLChecks.hidingRead (P.reindex e)
      (reindexEquiv e y, reindexEquiv e yp, reindexEquiv e x)
      (reindexEquiv e z, reindexEquiv e zp, a) ↔
      CLChecks.hidingRead P (y, yp, x) (z, zp, a) := by
  simp only [CLChecks.hidingRead, outputPrefix_reindex, reindex_eq_iff]

variable (e : ι ≃ κ) (L : Bool → CLFun F ι ℓ) (X Z : PT)
  (project : PA → ι → F) (D : (ι → F) → (ι → F) → A → A → Bool)

set_option backward.isDefEq.respectTransparency false in
theorem directed_reindex (t u : QuestionType PT ℓ)
    (a b : ParsedAnswer (ι → F) A PA) :
    directed (fun w => (L w).reindex e) X Z (fun a => reindexEquiv e (project a))
      (fun x y => D ((reindexEquiv e).symm x) ((reindexEquiv e).symm y))
      t u (answerEquiv e a) (answerEquiv e b) = directed L X Z project D t u a b := by
  fun_cases directed L X Z project D t u a b <;>
    simp_all only [directed, answerEquiv, Equiv.coe_fn_mk, CLChecks.sampling,
      CLFun.eval_reindex, CLChecks.reading, hidingRead_reindex, hidingNext_reindex,
      hidingPauli_reindex, reindex_eq_iff, LinearEquiv.symm_apply_apply,
      and_self, ↓reduceIte] <;> try rfl
  case case3 => exact decide_eq_decide.mpr Iff.rfl
  case case5 => exact decide_eq_decide.mpr Iff.rfl
  case case14 =>
    split <;> try rfl
    all_goals cases a <;> cases b <;> simp_all [-Bool.forall_bool]
    all_goals
      rename_i hbad
      exfalso
      apply hbad <;> rfl

theorem check_reindex (DP : PT → PT → PA → PA → Bool)
    (t u : QuestionType PT ℓ) (a b : ParsedAnswer (ι → F) A PA) :
    check (fun w => (L w).reindex e) X Z (fun a => reindexEquiv e (project a))
      (fun x y => D ((reindexEquiv e).symm x) ((reindexEquiv e).symm y))
      DP t u (answerEquiv e a) (answerEquiv e b) = check L X Z project D DP t u a b := by
  simp only [check, fits_answerEquiv, Equiv.apply_eq_iff_eq, directed_reindex]
  cases t <;> cases u <;> cases a <;> cases b <;> rfl

end MIPRE.Introspection.AuxiliaryQuotient
end
