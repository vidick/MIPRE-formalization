/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Pasting
public import MIPRE.Foundations.ModelStrategy

@[expose] public section

/-! # Deterministic graph refinement of measurement answers

The old answer is retained verbatim while its deterministic coordinate is
recorded in a first component. Thus every old operator occurs exactly once;
the construction preserves projectivity and all commutator sums exactly.

Stated for families in any ring, POVMs in an ordered `⋆`-ring and a bipartite model (Phase 4
of `planning/mipco-track.md`).
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Classical
set_option linter.unusedSectionVars false

variable {A C B : Type*} [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]

section Ring

variable {R : Type*} [Ring R]

/-- Record a deterministic coordinate without forgetting the original answer. -/
def graphRefinement (M : A → R) (c : A → C) (p : C × A) : R :=
  if p.1 = c p.2 then M p.2 else 0

theorem graphRefinement_sum_coordinate (M : A → R) (c : A → C) (a : A) :
    (∑ z, graphRefinement M c (z, a)) = M a := by simp [graphRefinement]

theorem graphRefinement_sum_fun (M : A → R) (c : A → C) (f : R → ℝ) (hf : f 0 = 0) :
    (∑ p, f (graphRefinement M c p)) = ∑ a, f (M a) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [graphRefinement, apply_ite f, hf]

theorem graphRefinement_isPVM [StarRing R] (M : A → R) (c : A → C) (hM : IsPVMIn M) :
    IsPVMIn (graphRefinement M c) where
  star_eq p := by
    by_cases hp : p.1 = c p.2 <;> simp [graphRefinement, hp, hM.star_eq]
  idem p := by
    by_cases hp : p.1 = c p.2 <;> simp [graphRefinement, hp, hM.idem]
  sum_eq_one := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simpa only [graphRefinement_sum_coordinate] using hM.sum_eq_one
  orthogonal := by
    intro p q hpq
    by_cases hp : p.1 = c p.2
    · by_cases hq : q.1 = c q.2
      · simp only [graphRefinement, hp, hq, ↓reduceIte]
        refine hM.orthogonal fun h => hpq ?_
        exact Prod.ext (by rw [hp, hq, h]) h
      · simp [graphRefinement, hq]
    · simp [graphRefinement, hp]

theorem graphRefinement_eq_fibSum (M : A → R) (c : A → C) (p : C × A) :
    graphRefinement M c p = fibSumIn M (fun a => (c a, a)) p := by
  rcases p with ⟨z, a⟩
  simp only [fibSumIn, Finset.sum_filter, Prod.mk.injEq]
  rw [Finset.sum_eq_single a]
  · simp [graphRefinement, eq_comm]
  · intro b _ hba
    simp [hba]
  · simp

theorem graphRefinement_fibSum {B : Type*} [DecidableEq B]
    (M : A → R) (c : A → C) (f : C × A → B) (b : B) :
    fibSumIn (graphRefinement M c) f b = fibSumIn M (fun a => f (c a, a)) b := by
  simp only [fibSumIn, Finset.sum_filter, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single (c a)]
  · simp [graphRefinement]
  · intro z _ hz
    simp [graphRefinement, hz]
  · simp

end Ring

section POVM

variable {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]

/-- The alphabet change is ordinary deterministic POVM postprocessing. -/
def graphRefinementPOVM (M : POVMIn A R) (c : A → C) : POVMIn (C × A) R :=
  M.map (fun a => (c a, a))

theorem graphRefinementPOVM_mats (M : POVMIn A R) (c : A → C) (p : C × A) :
    (graphRefinementPOVM M c).op p = graphRefinement M.op c p := by
  rw [graphRefinement_eq_fibSum]
  exact POVMIn.map_op _ _ _

theorem graphRefinementPOVM_recover (M : POVMIn A R) (c : A → C) :
    (graphRefinementPOVM M c).map Prod.snd = M := by
  rw [graphRefinementPOVM, POVMIn.map_map]
  apply POVMIn.ext'
  intro a
  simp only [POVMIn.map_op, Finset.sum_filter]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

theorem graphRefinementPOVM_isPVM (M : POVMIn A R) (c : A → C) (hM : IsPVMIn M.op) :
    IsPVMIn (graphRefinementPOVM M c).op := by
  have h : (graphRefinementPOVM M c).op = graphRefinement M.op c :=
    funext (graphRefinementPOVM_mats M c)
  rw [h]
  exact graphRefinement_isPVM _ c hM

/-- A decoder may change labels only where the old effect vanishes. -/
theorem graphRefinementPOVM_decode (M : POVMIn A R) (c : A → C) (d : C × A → A)
    (hd : ∀ a, M.op a ≠ 0 → d (c a, a) = a) :
    (graphRefinementPOVM M c).map d = M := by
  rw [graphRefinementPOVM, POVMIn.map_map]
  apply POVMIn.ext'
  intro b
  simp only [POVMIn.map_op, Finset.sum_filter]
  calc
    _ = ∑ a, if a = b then M.op a else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : M.op a = 0
      · simp [ha]
      · rw [hd a ha]
    _ = _ := by simp

end POVM

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [Fintype B]

/-- Refinement introduces no commutator loss, for any comparison operators. -/
theorem graphRefinement_commutator_sum (Ψ : BipartiteModel 𝒞 𝒜 ℬ) (M : A → 𝒜)
    (c : A → C) (N : B → 𝒜) :
    (∑ p, ∑ b, Ψ.stateSqNorm
      (graphRefinement M c p * N b - N b * graphRefinement M c p)) =
      ∑ a, ∑ b, Ψ.stateSqNorm (M a * N b - N b * M a) := by
  refine graphRefinement_sum_fun M c
    (fun Q => ∑ b, Ψ.stateSqNorm (Q * N b - N b * Q)) ?_
  simp only [zero_mul, mul_zero, sub_self, BipartiteModel.stateSqNorm,
    BipartiteModel.stateNorm, map_zero, Ψ.snorm_zero]
  simp

end MIPRE.Introspection
end

end
