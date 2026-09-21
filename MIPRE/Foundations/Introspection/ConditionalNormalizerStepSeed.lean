/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.ConditionalNormalizerStep
import MIPRE.Foundations.Introspection.ConditionalNormalizerIdealMirror
import MIPRE.Foundations.Introspection.HidingNormalizer

/-! # An actual adjacent hiding rigidity step on the EPR seed

All ideal measurements, commutation facts, exact mirrors, and label identities
are explicit. The remaining quantitative inputs are the preceding fine error,
the next prefix marginal error, and the actual parsed game's failure.
-/

noncomputable section

namespace MIPRE.Introspection.TypedEstimates

open Finset Matrix Classical Honest
open scoped Kronecker

set_option linter.unusedSectionVars false

variable {PauliType PauliAnswer F ι κ A : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A] {ℓ : ℕ}

set_option backward.isDefEq.respectTransparency false in
/-- A single actual adjacent hiding test propagates fine honest rigidity to
the next level with error `6 |E| ε + 3 η + 3 εfine`. This theorem assumes no
ideal commutation, exact-mirror, or accepted-answer contract. -/
theorem hiding_next_seed_rigidity
    (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (MA MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) (ι → F))
    {ε η εfine : ℝ}
    (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP)
      (registerEPR (ι → F)) MA MB ≤ ε)
    (w : Bool) (k j : Fin ℓ) (hk : k.val + 1 = j.val)
    (hL : (L w).SupportedOn univ)
    (hMA : IsPVM (fun a => ((MA (QuestionType.hide w k, 0)).mats a).val))
    (hMB : IsPVM (fun b => ((MB (QuestionType.hide w j, 0)).mats b).val))
    (hfine : ∑ i, xSqNorm (registerEPR (ι → F))
      ((((MA (QuestionType.hide w k, 0)).map (hidingCoarse (L w) k.val)).mats i).val)
      (hideCoarseOp (L w) k.val hL i) ≤ εfine)
    (hnorm : ∑ y, snorm (registerEPR (ι → F)) (bOp
      ((∑ z, (((MB (QuestionType.hide w j, 0)).map
        (hidingNextLater (L w) k.val)).mats (y, z)).val) -
          hidingPrefixOp (L w) j.val y)) ^ 2 ≤ η) :
    (∑ z, xSqNorm (registerEPR (ι → F)) (hideCoarseOp (L w) j.val hL z)
      ((((MB (QuestionType.hide w j, 0)).map (hidingCoarse (L w) j.val)).mats z).val)) ≤
        6 * (TypeGraph.edges E X Z ℓ).card * ε + 3 * η + 3 * εfine := by
  have hunit : star (registerEPR (ι → F)) ⬝ᵥ registerEPR (ι → F) = 1 := by
    rw [registerEPR_eq_weyl]
    exact Weyl.epr_unit
  have hnorm' : ∑ y, snorm (registerEPR (ι → F)) (bOp
      ((∑ z, (((MB (QuestionType.hide w j, 0)).map
        (hidingNextLater (L w) k.val)).mats (y, z)).val) -
          hidingPrefixOp (L w) (k.val + 1) y)) ^ 2 ≤ η := by simpa only [hk] using hnorm
  have hpaired := hiding_next_normalizer_estimate E X Z P L projectPauli D DP
    (registerEPR (ι → F)) hunit MA MB hfail w k j hk hL hMA hMB
    (hideCoarseOp (L w) k.val hL) (hidingPrefixOp (L w) (k.val + 1))
    (hideCoarseOp_isPVM (L w) k.val hL) (hidingPrefixOp_isPVM (L w) (k.val + 1))
    (hidingPrefixOp_commute_coarse (L w) k.val hL (hideLabelCoarse (L w) k.val)) hfine hnorm'
  have hstep := hideCoarseOp_step_of_normalizer (L w) k.val (by omega) hL
    (registerEPR (ι → F)) registerEPR_norm (MB (QuestionType.hide w j, 0)) hMB
    (hideCoarseOp_epr_mirror (L w) k.val hL)
    (hidingPrefixOp_epr_mirror (L w) (k.val + 1)) hpaired
  simpa only [hk] using hstep

end MIPRE.Introspection.TypedEstimates
