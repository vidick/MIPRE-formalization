/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.AnswerRefinement
public import MIPRE.Foundations.Introspection.AdaptivePrefixAdvance
public import MIPRE.Foundations.Introspection.AdaptivePrefixReplacement

@[expose] public section

/-! # Refining actual Introspect answers for the adaptive stage

The stage coordinate is read from a valid full answer. A malformed answer is
retained as `none`, with coordinate zero; its operator is never discarded.
The second component retains the full old answer as a fixed tail alphabet.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the refinement is of a family in
any ring (a POVM in any ordered `⋆`-ring), and the commutator budget is that of the register model
`Ξ.reg (ι → F)` of an arbitrary auxiliary model.
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Matrix Classical Weyl
set_option linter.unusedSectionVars false

variable {ι F A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype A] [DecidableEq A] {ℓ : ℕ}

/-- Select the current coordinate, retaining malformed answers separately in
the tail rather than postulating that their operator vanishes. -/
def stageAnswerCoordinate (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F) :
    Option ((ι → F) × A) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F)
  | none => 0
  | some a => coordinateRestrict (P.factorOfPrefix k y) a.1

def stageAnswerRefinement {R : Type*} [Ring R] (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F)
    (M : Option ((ι → F) × A) → R) :=
  graphRefinement M (stageAnswerCoordinate P k y)

def stageAnswerRefinementPOVM {R : Type*} [Ring R] [StarRing R] [PartialOrder R]
    [StarOrderedRing R] (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F)
    (M : POVMIn (Option ((ι → F) × A)) R) :=
  graphRefinementPOVM M (stageAnswerCoordinate P k y)

section POVM

variable {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]

theorem stageAnswerRefinementPOVM_mats (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F)
    (M : POVMIn (Option ((ι → F) × A)) R) (p) :
    (stageAnswerRefinementPOVM P k y M).op p = stageAnswerRefinement P k y M.op p :=
  graphRefinementPOVM_mats _ _ _

theorem stageAnswerRefinementPOVM_isPVM (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F)
    (M : POVMIn (Option ((ι → F) × A)) R) (hM : IsPVMIn M.op) :
    IsPVMIn (stageAnswerRefinementPOVM P k y M).op :=
  graphRefinementPOVM_isPVM _ _ hM

end POVM

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]

/-- Both the Z and dual-X local commutator budgets pass to the actual stage
alphabet exactly, including the malformed outcome. -/
theorem stageAnswerRefinement_commutator [StarModule ℂ 𝒜] [StarModule ℂ ℬ] (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ) (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
    (M : (y : ι → F) → Option ((ι → F) × A) →
      Matrix (stageRemaining P k y → F) (stageRemaining P k y → F) 𝒜)
    (w : (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) →
      Matrix (Fin (Fintype.card (P.factorOfPrefix k y)) → F) _ ℂ)
    (L : (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) →ₗ[F]
      (Fin (Fintype.card (P.factorOfPrefix k y)) → F)) :
    prefixStageCommutatorError P hP k Ξ (fun y => stageAnswerRefinement P k y (M y)) w L =
      ∑ y, prefixWeight P k y * ∑ a, ∑ z,
        (Ξ.reg (stageRemaining P k y → F)).stateSqNorm
          (M y a * registerReadout (stageSplit P hP k y) (w y) (L y) z -
            registerReadout (stageSplit P hP k y) (w y) (L y) z * M y a) := by
  rw [prefixStageCommutatorError_eq]
  simp only [ambientCommutatorError_eq, registerCommutatorError]
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  exact graphRefinement_commutator_sum _ _ _ _

end MIPRE.Introspection
end

end
