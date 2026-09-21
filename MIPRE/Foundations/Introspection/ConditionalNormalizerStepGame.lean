/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.ConditionalNormalizerStepAux
import MIPRE.Foundations.Introspection.HidingNormalizer
import MIPRE.Foundations.Introspection.HidingNormalizerPrefix

/-! # A concrete adjacent hiding rigidity step in the actual parsed game

The state has the extracted EPR seed and an arbitrary normalized auxiliary
state. Only the preceding fine estimate and the Introspect-prefix estimate
are induction inputs. The actual game supplies the conditional relation and
propagates the required normalizer through its hiding/Read/Introspect chain.
-/

noncomputable section

namespace MIPRE.Introspection.TypedEstimates

open Finset Matrix Classical Honest
open scoped Kronecker

set_option linter.unusedSectionVars false

variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}

set_option backward.isDefEq.respectTransparency false in
/-- The actual next Hide measurement is rigid with no dimension or answer
alphabet factor. All ideal commutation, mirror, and accepted-answer facts are
proved from the construction. The remaining inputs are the preceding fine
rigidity and the Introspect-prefix estimate from sampling/Pauli extraction. -/
theorem hiding_next_register_rigidity
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
    {ε δ εfine : ℝ}
    (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP)
      (registerState (ι → F) ξ) MA MB ≤ ε)
    (w : Bool) (k j : Fin ℓ) (hk : k.val + 1 = j.val)
    (hL : (L w).SupportedOn univ)
    (hMA : IsPVM (fun a => ((MA (QuestionType.hide w k, 0)).mats a).val))
    (hMB : IsPVM (fun b => ((MB (QuestionType.hide w j, 0)).mats b).val))
    (hfine : ∑ i, xSqNorm (registerState (ι → F) ξ)
      ((((MA (QuestionType.hide w k, 0)).map (hidingCoarse (L w) k.val)).mats i).val)
      (aOp (hideCoarseOp (L w) k.val hL i) : Matrix ((ι → F) × K) _ ℂ) ≤ εfine)
    (hintro : ∑ y, snorm (registerState (ι → F) ξ) (bOp
      ((((MB (QuestionType.introspect w, 0)).map
        (reportedPrefix (L w) j.val .introspect)).mats y).val -
          (aOp (hidingPrefixOp (L w) j.val y) : Matrix ((ι → F) × K) _ ℂ))) ^ 2 ≤ δ) :
    (∑ z, xSqNorm (registerState (ι → F) ξ)
      (aOp (hideCoarseOp (L w) j.val hL z) : Matrix ((ι → F) × H) _ ℂ)
      ((((MB (QuestionType.hide w j, 0)).map (hidingCoarse (L w) j.val)).mats z).val)) ≤
        (6 + 48 * ((ℓ - j.val + 1 : ℕ) : ℝ) ^ 2) * (TypeGraph.edges E X Z ℓ).card * ε +
          6 * δ + 3 * εfine := by
  have hseed : star (registerEPR (ι → F)) ⬝ᵥ registerEPR (ι → F) = 1 := by
    rw [registerEPR_eq_weyl]
    exact Weyl.epr_unit
  have hunit : star (registerState (ι → F) ξ) ⬝ᵥ registerState (ι → F) ξ = 1 :=
    expVec_unit hseed hξ
  let Q (y : Option (ι → F)) : Matrix ((ι → F) × K) _ ℂ :=
    aOp (hidingPrefixOp (L w) (k.val + 1) y)
  have hi : ∑ y, snorm (registerState (ι → F) ξ) (bOp
      ((((MB (QuestionType.introspect w, 0)).map
        (reportedPrefix (L w) (k.val + 1) .introspect)).mats y).val - Q y)) ^ 2 ≤ δ := by
    simpa only [Q, hk] using hintro
  have hn := hidingNormalizer_estimate E X Z P L projectPauli D DP
    (registerState (ι → F) ξ) hunit MA MB hfail w k j hk hL Q hi
  have hp := hiding_next_normalizer_estimate E X Z P L projectPauli D DP
    (registerState (ι → F) ξ) hunit MA MB hfail w k j hk hL hMA hMB
    (fun i => (aOp (hideCoarseOp (L w) k.val hL i) : Matrix ((ι → F) × K) _ ℂ)) Q
    (hideCoarseOp_isPVM (L w) k.val hL).aOp (hidingPrefixOp_isPVM (L w) (k.val + 1)).aOp
    (hidingPrefixOp_aux_commute (H := K) (L w) k.val hL) hfine hn
  have hs := hideCoarseOp_aux_step_of_normalizer (L w) k.val (by omega) hL ξ
    (norm_evec_eq_one_of_unit hξ) (MB (QuestionType.hide w j, 0)) hMB hp
  rw [hk] at hs
  exact hs.trans_eq (by ring)

end MIPRE.Introspection.TypedEstimates
