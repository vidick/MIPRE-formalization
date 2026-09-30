/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.AdaptivePrefixCommutator
public import MIPRE.Foundations.Introspection.ProductStageZTests

@[expose] public section

/-! # Actual Sample tests bound the conditional adaptive Z error

The product-form hypothesis is only the current strategy's induction form.
Its conditional Z-commutator estimate follows from actual parsed-game
success and primitive Pauli-Z extraction. All malformed Introspect answers
remain in the common option-valued residual alphabet.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the extracted register state is
the register model `Ξ.reg (ι → F)` of a normalized auxiliary model `Ξ`, the product form is one of
matrices over the remaining registers with entries in its first algebra, and the honest readouts
enter as `smulKron 1 _`.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical Weyl
set_option linter.unusedSectionVars false

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]

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
theorem option_readout_commutator_sum {I C B : Type*}
    [Fintype I] [DecidableEq I] [Fintype C] [DecidableEq C] [Fintype B]
    (Ψ : BipartiteModel 𝒞 (Matrix I I 𝒜) ℬ) (g : I → C) (M : B → Matrix I I 𝒜) :
    (∑ b, ∑ c : Option C, Ψ.stateSqNorm
      (M b * smulKron 1 (readout (fun i => some (g i)) c) -
        smulKron 1 (readout (fun i => some (g i)) c) * M b)) =
    ∑ b, ∑ c : C, Ψ.stateSqNorm
      (M b * smulKron 1 (readout g c) - smulKron 1 (readout g c) * M b) := by
  have hz : Ψ.stateSqNorm (0 : Matrix I I 𝒜) = 0 := by
    simp [BipartiteModel.stateSqNorm, BipartiteModel.stateNorm, StateModel.snorm_zero]
  apply Finset.sum_congr rfl
  intro b _
  rw [Fintype.sum_option]
  simp only [readout_none_comp, readout_some_comp, smulKron_zero_right,
    mul_zero, zero_mul, sub_self, hz, zero_add]

namespace TypedEstimates

variable {PauliType PauliAnswer F ι κ A : Type*}
  [Fintype PauliType] [DecidableEq PauliType]
  [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype A] {ℓ : ℕ}

/-- The actual Sample joint measurement supplies the conditional Z estimate
for a strategy in the current adaptive product form. The prefix law, local
registers, and ideal readout identification are all discharged internally. -/
theorem introspect_adaptiveZ_commutator [StarModule ℂ 𝒜] [PartialOrder 𝒜]
    [StarOrderedRing 𝒜] [StarProper 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ] [StarProper ℬ]
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
    {ε η : ℝ}
    (hfail : 1 - (Ξ.reg (ι → F)).povmValue (parsedGame E X Z P L projectPauli D DP) MA MB ≤ ε)
    (q : κ → ZMod 2) (hq : ∀ z, (P Z).eval z = q) (w : Bool)
    (hS : IsPVMIn (MB (QuestionType.sample w, 0)).op)
    (hZ : ∑ z, (Ξ.reg (ι → F)).snorm ((Ξ.reg (ι → F)).πB
      (((MB (QuestionType.pauli Z, q)).map (pauliProjection projectPauli)).op z -
        smulKron 1 (readout (some : (ι → F) → Option (ι → F)) z))) ^ 2 ≤ η)
    (hL : (L w).SupportedOn univ) (k : ℕ)
    (M : (y : ι → F) → Option ((ι → F) × A) →
      Matrix (stageRemaining (L w) k y → F) (stageRemaining (L w) k y → F) 𝒜)
    (hform : ∀ a, ((MA (QuestionType.introspect w, 0)).map introspectPair).op a =
      ∑ y, prefixResidualOp (L w) k y (M y a)) :
    (∑ y, prefixWeight (L w) k y * ∑ a, ∑ z,
      (Ξ.reg (stageRemaining (L w) k y → F)).stateSqNorm
        (M y a * registerReadout (stageSplit (L w) hL k y) wZ LinearMap.id z -
          registerReadout (stageSplit (L w) hL k y) wZ LinearMap.id z * M y a)) ≤
      64 * η + 224 * (TypeGraph.edges E X Z ℓ).card * ε := by
  have ht := introspect_coarseZ_commutator_alice E X Z P L projectPauli D DP
    Ξ hΞ MA MB hfail q hq w hS hZ (adaptiveZOutcome (L w) k)
  have he := option_readout_commutator_sum (Ξ.reg (ι → F))
    (adaptiveZOutcome (L w) k)
    (fun a => ((MA (QuestionType.introspect w, 0)).map introspectPair).op a)
  have hbound := he.symm.trans_le ht
  have hg := adaptiveZ_reassembled_commutator_sum (L w) hL k Ξ M
  apply hg.symm.trans_le
  calc
    _ = ∑ a, ∑ c, (Ξ.reg (ι → F)).stateSqNorm
        (((MA (QuestionType.introspect w, 0)).map introspectPair).op a *
            smulKron (1 : 𝒜) (readout (adaptiveZOutcome (L w) k) c) -
          smulKron (1 : 𝒜) (readout (adaptiveZOutcome (L w) k) c) *
            ((MA (QuestionType.introspect w, 0)).map introspectPair).op a) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro c _
      rw [hform a]
    _ ≤ _ := hbound

end TypedEstimates
end MIPRE.Introspection

end

end
