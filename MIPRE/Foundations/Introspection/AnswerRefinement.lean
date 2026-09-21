/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Pasting

/-! # Deterministic graph refinement of measurement answers

The old answer is retained verbatim while its deterministic coordinate is
recorded in a first component. Thus every old operator occurs exactly once;
the construction preserves projectivity and all commutator sums exactly.
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Matrix Classical
set_option linter.unusedSectionVars false

variable {A C D K B : Type*} [Fintype A] [DecidableEq A]
  [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

/-- Record a deterministic coordinate without forgetting the original answer. -/
def graphRefinement (M : A → Matrix D D ℂ) (c : A → C) (p : C × A) : Matrix D D ℂ :=
  if p.1 = c p.2 then M p.2 else 0

theorem graphRefinement_graph (M : A → Matrix D D ℂ) (c : A → C) (a : A) :
    graphRefinement M c (c a, a) = M a := by simp [graphRefinement]

theorem graphRefinement_off_graph (M : A → Matrix D D ℂ) (c : A → C)
    (p : C × A) (hp : p.1 ≠ c p.2) : graphRefinement M c p = 0 := by
  simp [graphRefinement, hp]

theorem graphRefinement_sum_coordinate (M : A → Matrix D D ℂ) (c : A → C) (a : A) :
    (∑ z, graphRefinement M c (z, a)) = M a := by simp [graphRefinement]

theorem graphRefinement_sum_fun (M : A → Matrix D D ℂ) (c : A → C)
    (f : Matrix D D ℂ → ℝ) (hf : f 0 = 0) :
    (∑ p, f (graphRefinement M c p)) = ∑ a, f (M a) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [graphRefinement, apply_ite f, hf]

theorem graphRefinement_isPVM (M : A → Matrix D D ℂ) (c : A → C) (hM : IsPVM M) :
    IsPVM (graphRefinement M c) where
  isSelfAdjoint p := by
    by_cases hp : p.1 = c p.2 <;> simp [graphRefinement, hp, hM.isSelfAdjoint]
  idem p := by
    by_cases hp : p.1 = c p.2 <;> simp [graphRefinement, hp, hM.idem]
  sum_eq_one := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simpa only [graphRefinement_sum_coordinate] using hM.sum_eq_one

theorem graphRefinement_eq_fibSum (M : A → Matrix D D ℂ) (c : A → C) (p : C × A) :
    graphRefinement M c p = fibSum M (fun a => (c a, a)) p := by
  rcases p with ⟨z, a⟩
  simp only [fibSum, Finset.sum_filter, Prod.mk.injEq]
  rw [Finset.sum_eq_single a]
  · simp [graphRefinement, Prod.mk.injEq, eq_comm]
  · intro b _ hba
    simp [hba]
  · simp

theorem graphRefinement_fibSum {B : Type*} [DecidableEq B]
    (M : A → Matrix D D ℂ) (c : A → C) (f : C × A → B) (b : B) :
    fibSum (graphRefinement M c) f b = fibSum M (fun a => f (c a, a)) b := by
  simp only [fibSum, Finset.sum_filter, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single (c a)]
  · simp [graphRefinement]
  · intro z _ hz
    simp [graphRefinement, hz]
  · simp

/-- The alphabet change is ordinary deterministic POVM postprocessing. -/
def graphRefinementPOVM (M : POVM A D) (c : A → C) : POVM (C × A) D :=
  M.map (fun a => (c a, a))

theorem graphRefinementPOVM_mats (M : POVM A D) (c : A → C) (p : C × A) :
    ((graphRefinementPOVM M c).mats p).val =
      graphRefinement (fun a => (M.mats a).val) c p := by
  rw [graphRefinement_eq_fibSum]
  exact POVM.map_mats _ _ _

theorem graphRefinementPOVM_recover (M : POVM A D) (c : A → C) :
    (graphRefinementPOVM M c).map Prod.snd = M := by
  rw [graphRefinementPOVM, POVM.map_map]
  apply POVM.ext'
  intro a
  simp [POVM.map_mats]

theorem graphRefinementPOVM_isPVM (M : POVM A D) (c : A → C)
    (hM : IsPVM (fun a => (M.mats a).val)) :
    IsPVM (fun p => ((graphRefinementPOVM M c).mats p).val) := by
  simpa only [graphRefinementPOVM_mats] using graphRefinement_isPVM _ c hM

/-- A decoder may change labels only where the old effect vanishes. -/
theorem graphRefinementPOVM_decode (M : POVM A D) (c : A → C) (d : C × A → A)
    (hd : ∀ a, (M.mats a).val ≠ 0 → d (c a, a) = a) :
    (graphRefinementPOVM M c).map d = M := by
  rw [graphRefinementPOVM, POVM.map_map]
  apply POVM.ext'
  intro b
  simp only [POVM.map_mats, Finset.sum_filter]
  calc
    _ = ∑ a, if a = b then (M.mats a).val else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : (M.mats a).val = 0
      · simp [ha]
      · rw [hd a ha]
    _ = _ := by simp

variable [Fintype K] [DecidableEq K] [Fintype B]

/-- Refinement introduces no commutator loss, for any comparison operators. -/
theorem graphRefinement_commutator_sum (ψ : D × K → ℂ) (M : A → Matrix D D ℂ)
    (c : A → C) (N : B → Matrix D D ℂ) :
    (∑ p, ∑ b, stateSqNorm ψ
      (graphRefinement M c p * N b - N b * graphRefinement M c p)) =
      ∑ a, ∑ b, stateSqNorm ψ (M a * N b - N b * M a) := by
  apply graphRefinement_sum_fun
  simp [stateSqNorm, stateNorm, stateVec]

end MIPRE.Introspection
end
