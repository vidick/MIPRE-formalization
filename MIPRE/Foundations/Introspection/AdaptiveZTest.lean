/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AdaptivePrefixCommutator
import MIPRE.Foundations.Introspection.ProductStageZTests

/-! # Actual Sample tests bound the conditional adaptive Z error

The product-form hypothesis is only the current strategy's induction form.
Its conditional Z-commutator estimate follows from actual parsed-game
success and primitive Pauli-Z extraction. All malformed Introspect answers
remain in the common option-valued residual alphabet.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false

theorem readout_some_comp {I C : Type*} [Fintype I] [DecidableEq I]
    [Fintype C] [DecidableEq C] (g : I → C) (c : C) :
    readout (fun i => some (g i)) (some c) = readout g c := by
  ext i j
  simp [readout]

theorem readout_none_comp {I C : Type*} [Fintype I] [DecidableEq I]
    [Fintype C] [DecidableEq C] (g : I → C) :
    readout (fun i => some (g i)) none = 0 := by
  ext i j
  simp [readout]

/-- The impossible `none` ideal contributes zero, without splitting the
actual measurement's outcome alphabet. -/
theorem option_readout_commutator_sum {I C H K B : Type*}
    [Fintype I] [DecidableEq I] [Fintype C] [DecidableEq C]
    [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] [Fintype B]
    (ψ : (I × H) × K → ℂ) (g : I → C)
    (M : B → Matrix (I × H) (I × H) ℂ) :
    (∑ b, ∑ c : Option C, stateSqNorm ψ
      (M b * aOp (readout (fun i => some (g i)) c) -
        aOp (readout (fun i => some (g i)) c) * M b)) =
    ∑ b, ∑ c : C, stateSqNorm ψ
      (M b * aOp (readout g c) - aOp (readout g c) * M b) := by
  have hz : stateSqNorm ψ (0 : Matrix (I × H) (I × H) ℂ) = 0 := by
    simp [stateSqNorm, stateNorm, stateVec]
  apply Finset.sum_congr rfl
  intro b _
  rw [Fintype.sum_option]
  simp only [readout_none_comp, readout_some_comp, aOp_zero,
    mul_zero, zero_mul, sub_self, hz, zero_add]

namespace TypedEstimates

variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType]
  [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype A] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K] {ℓ : ℕ}

set_option backward.isDefEq.respectTransparency false in
/-- The actual Sample joint measurement supplies the conditional Z estimate
for a strategy in the current adaptive product form. The prefix law, local
registers, and ideal readout identification are all discharged internally. -/
theorem introspect_adaptiveZ_commutator
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
    {ε η : ℝ}
    (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP)
      (registerState (ι → F) ξ) MA MB ≤ ε)
    (q : κ → ZMod 2) (hq : ∀ z, (P Z).eval z = q) (w : Bool)
    (hS : IsPVM (fun a => ((MB (QuestionType.sample w, 0)).mats a).val))
    (hZ : ∑ z, snorm (registerState (ι → F) ξ) (bOp
      ((((MB (QuestionType.pauli Z, q)).map (pauliProjection projectPauli)).mats z).val -
        (aOp (readout (some : (ι → F) → Option (ι → F)) z) :
          Matrix ((ι → F) × K) _ ℂ))) ^ 2 ≤ η)
    (hL : (L w).SupportedOn univ) (k : ℕ)
    (M : (y : ι → F) → Option ((ι → F) × A) →
      Matrix ((stageRemaining (L w) k y → F) × H) _ ℂ)
    (hform : ∀ a, (((MA (QuestionType.introspect w, 0)).map introspectPair).mats a).val =
      ∑ y, prefixResidualOp (L w) k y (M y a)) :
    (∑ y, prefixWeight (L w) k y * ∑ a, ∑ z,
      stateSqNorm (registerState (stageRemaining (L w) k y → F) ξ)
        (M y a * registerReadout (stageSplit (L w) hL k y) wZ LinearMap.id z -
          registerReadout (stageSplit (L w) hL k y) wZ LinearMap.id z * M y a)) ≤
      64 * η + 224 * (TypeGraph.edges E X Z ℓ).card * ε := by
  have ht := introspect_coarseZ_commutator_alice E X Z P L projectPauli D DP
    ξ hξ MA MB hfail q hq w hS hZ (adaptiveZOutcome (L w) k)
  have he := option_readout_commutator_sum (registerState (ι → F) ξ)
    (adaptiveZOutcome (L w) k)
    (fun a => (((MA (QuestionType.introspect w, 0)).map introspectPair).mats a).val)
  have hbound := he.symm.trans_le ht
  have hg := adaptiveZ_reassembled_commutator_sum (L w) hL k ξ M
  apply hg.symm.trans_le
  calc
    _ = ∑ a, ∑ c, stateSqNorm (registerState (ι → F) ξ)
        ((((MA (QuestionType.introspect w, 0)).map introspectPair).mats a).val *
            (aOp (readout (adaptiveZOutcome (L w) k) c) : Matrix ((ι → F) × H) _ ℂ) -
          (aOp (readout (adaptiveZOutcome (L w) k) c) : Matrix ((ι → F) × H) _ ℂ) *
            (((MA (QuestionType.introspect w, 0)).map introspectPair).mats a).val) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro c _
      rw [hform a]
    _ ≤ _ := hbound

end TypedEstimates
end MIPRE.Introspection

end
