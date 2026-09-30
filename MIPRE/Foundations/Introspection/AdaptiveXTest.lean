/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.AdaptiveDualLocal
public import MIPRE.Foundations.Introspection.AdaptivePrefixCommutator
public import MIPRE.Foundations.Introspection.ProductStageReadTests

@[expose] public section

/-! # Actual Read tests bound the conditional adaptive dual-X error

The current product-form equality identifies the full Introspect measurement.
The honest dual marginal factors into the prefix projector and the current
selected-register dual readout. Its local labels inject into the tested global
alphabet, so discarding the remaining nonnegative commutator terms introduces
no cardinality factor. No same-party distance is coarse-grained.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the extracted register state is
the register model `Ξ.reg (ι → F)` of a normalized auxiliary model `Ξ`, the product form is one of
matrices over the remaining registers with entries in its first algebra, and the honest dual
readout enters as `smulKron 1 _`.
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Matrix Weyl Classical
set_option linter.unusedSectionVars false

variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]

/-- The local dual outcome is embedded in the actual option-valued readout
alphabet, retaining the prefix which selected its register. -/
def adaptiveDualLabel (P : CL.CLFun F ι ℓ) (k : ℕ)
    (p : (y : ι → F) × (Fin (Fintype.card (P.factorOfPrefix k y)) → F)) :
    Option ((ι → F) × (ι → F)) :=
  some (p.1, coordinateInsert (P.factorOfPrefix k p.1) p.2)

theorem adaptiveDualLabel_injective (P : CL.CLFun F ι ℓ) (k : ℕ) :
    Function.Injective (adaptiveDualLabel P k) := by
  rintro ⟨y, z⟩ ⟨y', z'⟩ h
  have hp := Option.some.inj h
  have hy : y = y' := congrArg Prod.fst hp
  cases hy
  have hz : z = z' := by
    simpa only [coordinateRestrict_insert] using
      congrArg (coordinateRestrict (P.factorOfPrefix k y)) (congrArg Prod.snd hp)
  cases hz
  rfl

theorem adaptiveDualLabel_sum_le (P : CL.CLFun F ι ℓ) (k : ℕ)
    (f : Option ((ι → F) × (ι → F)) → ℝ) (hf : ∀ z, 0 ≤ f z) :
    (∑ p, f (adaptiveDualLabel P k p)) ≤ ∑ z, f z := by
  have he : (∑ z ∈ univ.image (adaptiveDualLabel P k), f z) =
      ∑ p, f (adaptiveDualLabel P k p) := by
    rw [Finset.sum_image]
    exact fun _ _ _ _ h => adaptiveDualLabel_injective P k h
  rw [← he]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun z _ _ => hf z)

/-- The actual global coarse dual commutator controls the concrete adaptive
weighted dual-X commutator, with coefficient one. -/
theorem adaptiveX_reassembled_commutator_le [StarModule ℂ 𝒜] (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ) (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
    {A : Type*} [Fintype A]
    (M : (y : ι → F) → A → Matrix (stageRemaining P k y → F) (stageRemaining P k y → F) 𝒜) :
    (∑ y, prefixWeight P k y * ∑ a, ∑ z,
      (Ξ.reg (stageRemaining P k y → F)).stateSqNorm
        (M y a * registerReadout (stageSplit P hP k y)
            wX (CL.lperp (coordinateLinear (CLChecks.stageLinear P k y))) z -
          registerReadout (stageSplit P hP k y)
            wX (CL.lperp (coordinateLinear (CLChecks.stageLinear P k y))) z * M y a)) ≤
      ∑ a, ∑ z, (Ξ.reg (ι → F)).stateSqNorm
        ((∑ y, prefixResidualOp P k y (M y a)) * smulKron 1 (Honest.readDualOp P k hP z) -
          smulKron 1 (Honest.readDualOp P k hP z) * (∑ y, prefixResidualOp P k y (M y a))) := by
  rw [← prefixResidual_reassembled_commutator_sum P hP k Ξ M
    (fun y z => registerReadout (𝒜 := 𝒜) (stageSplit P hP k y)
      wX (CL.lperp (coordinateLinear (CLChecks.stageLinear P k y))) z)]
  apply Finset.sum_le_sum
  intro a _
  have hs := adaptiveDualLabel_sum_le P k
    (fun z => (Ξ.reg (ι → F)).stateSqNorm
      ((∑ y, prefixResidualOp P k y (M y a)) * smulKron 1 (Honest.readDualOp P k hP z) -
        smulKron 1 (Honest.readDualOp P k hP z) * (∑ y, prefixResidualOp P k y (M y a))))
    (fun _ => (Ξ.reg (ι → F)).stateSqNorm_nonneg _)
  simpa only [adaptiveDualLabel, readDualOp_stage_factor] using hs

namespace TypedEstimates

variable {PauliType PauliAnswer κ A : Type*}
  [Fintype PauliType] [DecidableEq PauliType]
  [Fintype PauliAnswer]
  [Fintype κ] [DecidableEq κ] [Fintype A]

set_option maxHeartbeats 800000 in
/-- Actual parsed-game success and hiding rigidity supply the conditional
dual-X commutator estimate for the current adaptive product form. -/
theorem introspect_adaptiveX_commutator [StarModule ℂ 𝒜] [PartialOrder 𝒜]
    [StarOrderedRing 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
    [StarProper ℬ]
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
    {ε δ : ℝ}
    (hfail : 1 - (Ξ.reg (ι → F)).povmValue (parsedGame E X Z P L projectPauli D DP) MA MB ≤ ε)
    (w : Bool) (hL : (L w).SupportedOn univ) (j : Fin ℓ)
    (hMA : IsPVMIn (MA (QuestionType.hide w j, 0)).op)
    (hMB : IsPVMIn (MB (QuestionType.read w, 0)).op)
    (hfine : ∑ i, (Ξ.reg (ι → F)).xSqNorm
      (((MA (QuestionType.hide w j, 0)).map (hidingCoarse (L w) j.val)).op i)
      (smulKron 1 (Honest.hideCoarseOp (L w) j.val hL i)) ≤ δ)
    (M : (y : ι → F) → Option ((ι → F) × A) →
      Matrix (stageRemaining (L w) j.val y → F) (stageRemaining (L w) j.val y → F) 𝒜)
    (hform : ∀ a, ((MA (QuestionType.introspect w, 0)).map introFullPair).op a =
      ∑ y, prefixResidualOp (L w) j.val y (M y a)) :
    (∑ y, prefixWeight (L w) j.val y * ∑ a, ∑ z,
      (Ξ.reg (stageRemaining (L w) j.val y → F)).stateSqNorm
        (M y a * registerReadout (stageSplit (L w) hL j.val y)
            wX (CL.lperp (coordinateLinear (CLChecks.stageLinear (L w) j.val y))) z -
          registerReadout (stageSplit (L w) hL j.val y)
            wX (CL.lperp (coordinateLinear (CLChecks.stageLinear (L w) j.val y))) z * M y a)) ≤
      16 * ((32 * ((ℓ - j.val : ℕ) : ℝ) ^ 2 + 6) *
        (TypeGraph.edges E X Z ℓ).card * ε + 4 * δ) := by
  have ht := introspect_dual_commutator E X Z P L projectPauli D DP
    Ξ hΞ MA MB hfail w hL j hMA hMB hfine
  apply (adaptiveX_reassembled_commutator_le (L w) hL j.val Ξ M).trans
  simpa only [hform] using ht

end TypedEstimates
end MIPRE.Introspection

end

end
