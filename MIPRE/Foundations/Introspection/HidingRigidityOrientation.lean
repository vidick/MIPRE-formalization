/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.ConditionalNormalizerStepGame

@[expose] public section

/-! # Transferring honest hiding rigidity through the actual consistency loop

The two ideal families are exact mirrors on the EPR register with arbitrary
auxiliaries. The parsed game's same-type test therefore transfers Bob's
estimate to Alice with error `4 |E| epsilon + 2 beta`. No symmetry of the
Pauli predicate or of the full game is required.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the EPR register with arbitrary
auxiliaries is the register model `Ξ.reg (ι → F)`, exact mirrors are vector identities, and the
honest families enter as `smulKron 1 _`.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical

set_option linter.unusedSectionVars false

/-- An exact ideal mirror and one actual consistency relation transfer
rigidity to the other party without changing the outcome alphabet. -/
theorem sum_xSqNorm_mirror_transfer {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞]
    [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]
    (Ψ : BipartiteModel 𝒞 𝒜 ℬ) {I : Type*} [Fintype I]
    (M P : I → 𝒜) (N Q : I → ℬ)
    (hmirror : ∀ i, Ψ.π (Ψ.πA (P i)) Ψ.ψ = Ψ.π (Ψ.πB (Q i)) Ψ.ψ) :
    (∑ i, Ψ.xSqNorm (M i) (Q i)) ≤
      2 * (∑ i, Ψ.xSqNorm (M i) (N i)) + 2 * ∑ i, Ψ.xSqNorm (P i) (N i) := by
  have h := Ψ.sum_snorm_sq_triangle univ (fun i => Ψ.πA (M i))
    (fun i => Ψ.πB (N i)) (fun i => Ψ.πB (Q i))
  simp only [xSqNorm_eq_bOp_distance_of_mirror Ψ _ _ _ (hmirror _)]
  simpa only [BipartiteModel.xSqNorm, BipartiteModel.xNorm] using h

namespace TypedEstimates

variable {PauliType PauliAnswer F ι κ A : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A] {ℓ : ℕ}
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [StarModule ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [StarModule ℂ ℬ]
  [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ]
  [StarProper ℬ]

def hidingAliceError (L : Bool → CL.CLFun F ι ℓ) (w : Bool)
    (hL : (L w).SupportedOn univ) (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) 𝒜)) (j : Fin ℓ) : ℝ :=
  ∑ i, (Ξ.reg (ι → F)).xSqNorm
    (((MA (QuestionType.hide w j, 0)).map (hidingCoarse (L w) j.val)).op i)
    (smulKron 1 (Honest.hideCoarseOp (L w) j.val hL i))

def hidingBobError (L : Bool → CL.CLFun F ι ℓ) (w : Bool)
    (hL : (L w).SupportedOn univ) (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) ℬ)) (j : Fin ℓ) : ℝ :=
  ∑ i, (Ξ.reg (ι → F)).xSqNorm
    (smulKron 1 (Honest.hideCoarseOp (L w) j.val hL i))
    (((MB (QuestionType.hide w j, 0)).map (hidingCoarse (L w) j.val)).op i)

theorem hidingAliceError_nonneg (L : Bool → CL.CLFun F ι ℓ) (w : Bool)
    (hL : (L w).SupportedOn univ) (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) 𝒜)) (j : Fin ℓ) :
    0 ≤ hidingAliceError L w hL Ξ MA j :=
  Finset.sum_nonneg fun _ _ => BipartiteModel.xSqNorm_nonneg _ _ _

theorem hidingBobError_nonneg (L : Bool → CL.CLFun F ι ℓ) (w : Bool)
    (hL : (L w).SupportedOn univ) (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) ℬ)) (j : Fin ℓ) :
    0 ≤ hidingBobError L w hL Ξ MB j :=
  Finset.sum_nonneg fun _ _ => BipartiteModel.xSqNorm_nonneg _ _ _

/-- The same-type parsed test supplies the orientation transfer. The actual
measurements may be arbitrary POVMs in this lemma. -/
theorem hiding_register_orientation
    (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (Ξ : BipartiteModel 𝒞 𝒜 ℬ) (hΞ : ‖Ξ.ψ‖ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) 𝒜))
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) ℬ))
    {ε : ℝ} (hfail : 1 - (Ξ.reg (ι → F)).povmValue
      (parsedGame E X Z P L projectPauli D DP) MA MB ≤ ε)
    (w : Bool) (hL : (L w).SupportedOn univ) (j : Fin ℓ) :
    hidingAliceError L w hL Ξ MA j ≤
      4 * (TypeGraph.edges E X Z ℓ).card * ε + 2 * hidingBobError L w hL Ξ MB j := by
  have hunit : ‖(Ξ.reg (ι → F)).ψ‖ = 1 := by rw [BipartiteModel.norm_reg_ψ, hΞ]
  have hloop := aux_agreement_estimate E X Z P (questionCheck L X Z projectPauli D DP)
    (Ξ.reg (ι → F)) hunit MA MB hfail (.hide j) (.hide j) w w
    (TypeGraph.adj_self E X Z (.inr (.hide j,w)))
    (hidingCoarse (L w) j.val) (hidingCoarse (L w) j.val)
    (fun a b hab => congrArg (hidingCoarse (L w) j.val)
      (TypedPredicate.check_consistency L X Z projectPauli D (fun p s => DP p s 0 0) hab))
  have htransfer := sum_xSqNorm_mirror_transfer (Ξ.reg (ι → F))
    (fun i => ((MA (QuestionType.hide w j, 0)).map (hidingCoarse (L w) j.val)).op i)
    (fun i => smulKron (1 : 𝒜) (Honest.hideCoarseOp (L w) j.val hL i))
    (fun i => ((MB (QuestionType.hide w j, 0)).map (hidingCoarse (L w) j.val)).op i)
    (fun i => smulKron (1 : ℬ) (Honest.hideCoarseOp (L w) j.val hL i))
    (Honest.hideCoarseOp_registerState_mirror (L w) j.val hL Ξ)
  exact htransfer.trans (by dsimp only [hidingBobError]; linarith)

end TypedEstimates
end MIPRE.Introspection

end

end
