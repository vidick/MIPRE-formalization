/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.ConditionalNormalizerStepGame

/-! # Transferring honest hiding rigidity through the actual consistency loop

The two ideal families are exact mirrors on the EPR register with arbitrary
auxiliaries. The parsed game's same-type test therefore transfers Bob's
estimate to Alice with error `4 |E| epsilon + 2 beta`. No symmetry of the
Pauli predicate or of the full game is required.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical
open scoped Kronecker

set_option linter.unusedSectionVars false

/-- An exact ideal mirror and one actual consistency relation transfer
rigidity to the other party without changing the outcome alphabet. -/
theorem sum_xSqNorm_mirror_transfer
    {H K I : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
    [Fintype I] (ψ : H × K → ℂ)
    (M P : I → Matrix H H ℂ) (N Q : I → Matrix K K ℂ)
    (hmirror : ∀ i, aOp (P i) *ᵥ ψ = bOp (Q i) *ᵥ ψ) :
    (∑ i, xSqNorm ψ (M i) (Q i)) ≤
      2 * (∑ i, xSqNorm ψ (M i) (N i)) + 2 * ∑ i, xSqNorm ψ (P i) (N i) := by
  have h := sum_snorm_sq_triangle' ψ (fun i => aOp (M i))
    (fun i => bOp (N i)) (fun i => bOp (Q i))
  simpa only [← xSqNorm_eq_snorm_sq,
    ← xSqNorm_eq_bOp_distance_of_mirror ψ _ _ _ (hmirror _)] using h

namespace TypedEstimates

variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}

def hidingAliceError (L : Bool → CL.CLFun F ι ℓ) (w : Bool)
    (hL : (L w).SupportedOn univ) (ξ : H × K → ℂ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H)) (j : Fin ℓ) : ℝ :=
  ∑ i, xSqNorm (registerState (ι → F) ξ)
    ((((MA (QuestionType.hide w j, 0)).map (hidingCoarse (L w) j.val)).mats i).val)
    (aOp (Honest.hideCoarseOp (L w) j.val hL i) : Matrix ((ι → F) × K) _ ℂ)

def hidingBobError (L : Bool → CL.CLFun F ι ℓ) (w : Bool)
    (hL : (L w).SupportedOn univ) (ξ : H × K → ℂ)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × K)) (j : Fin ℓ) : ℝ :=
  ∑ i, xSqNorm (registerState (ι → F) ξ)
    (aOp (Honest.hideCoarseOp (L w) j.val hL i) : Matrix ((ι → F) × H) _ ℂ)
    ((((MB (QuestionType.hide w j, 0)).map (hidingCoarse (L w) j.val)).mats i).val)

theorem hidingAliceError_nonneg (L : Bool → CL.CLFun F ι ℓ) (w : Bool)
    (hL : (L w).SupportedOn univ) (ξ : H × K → ℂ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H)) (j : Fin ℓ) :
    0 ≤ hidingAliceError L w hL ξ MA j :=
  Finset.sum_nonneg fun _ _ => xSqNorm_nonneg _ _ _

theorem hidingBobError_nonneg (L : Bool → CL.CLFun F ι ℓ) (w : Bool)
    (hL : (L w).SupportedOn univ) (ξ : H × K → ℂ)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × K)) (j : Fin ℓ) :
    0 ≤ hidingBobError L w hL ξ MB j :=
  Finset.sum_nonneg fun _ _ => xSqNorm_nonneg _ _ _

/-- The same-type parsed test supplies the orientation transfer. The actual
measurements may be arbitrary POVMs in this lemma. -/
theorem hiding_register_orientation
    (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (ξ : H × K → ℂ) (hξ : star ξ ⬝ᵥ ξ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H))
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × K))
    {ε : ℝ} (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP)
      (registerState (ι → F) ξ) MA MB ≤ ε)
    (w : Bool) (hL : (L w).SupportedOn univ) (j : Fin ℓ) :
    hidingAliceError L w hL ξ MA j ≤
      4 * (TypeGraph.edges E X Z ℓ).card * ε + 2 * hidingBobError L w hL ξ MB j := by
  have hseed : star (registerEPR (ι → F)) ⬝ᵥ registerEPR (ι → F) = 1 := by
    rw [registerEPR_eq_weyl]
    exact Weyl.epr_unit
  have hunit := expVec_unit hseed hξ
  have hloop := aux_agreement_estimate E X Z P (questionCheck L X Z projectPauli D DP)
    (registerState (ι → F) ξ) hunit MA MB hfail (.hide j) (.hide j) w w
    (TypeGraph.adj_self E X Z (.inr (.hide j,w)))
    (hidingCoarse (L w) j.val) (hidingCoarse (L w) j.val)
    (fun a b hab => congrArg (hidingCoarse (L w) j.val)
      (TypedPredicate.check_consistency L X Z projectPauli D (fun p s => DP p s 0 0) hab))
  have htransfer := sum_xSqNorm_mirror_transfer (registerState (ι → F) ξ)
    (fun i => ((((MA (QuestionType.hide w j, 0)).map (hidingCoarse (L w) j.val)).mats i).val))
    (fun i => (aOp (Honest.hideCoarseOp (L w) j.val hL i) : Matrix ((ι → F) × H) _ ℂ))
    (fun i => ((((MB (QuestionType.hide w j, 0)).map (hidingCoarse (L w) j.val)).mats i).val))
    (fun i => (aOp (Honest.hideCoarseOp (L w) j.val hL i) : Matrix ((ι → F) × K) _ ℂ))
    (Honest.hideCoarseOp_registerState_mirror (L w) j.val hL ξ)
  exact htransfer.trans (by dsimp only [hidingBobError]; linarith)

end TypedEstimates
end MIPRE.Introspection

end
