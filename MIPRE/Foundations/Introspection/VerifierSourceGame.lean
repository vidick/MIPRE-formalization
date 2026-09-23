/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AuxiliaryDecisionSoundness
import MIPRE.Foundations.Introspection.SourcePaddingValue
import MIPRE.Foundations.Introspection.PauliSamplerParams
import MIPRE.Foundations.VerifierValue

/-! # The bounded verifier as the source of introspection

The semantic source game has exactly the verifier's distribution and decision
predicate. Padding preserves perfect PCC strategies and can be removed from
the soundness conclusion without any additional error.
-/

noncomputable section
namespace MIPRE.Introspection.VerifierSource
open CL Classical AuxiliaryProgram SourcePadding SourcePadding.Program

def predicate (V : Verifier 7) (n B : ℕ) :
    V.Questions (2^n) → V.Questions (2^n) → Verifier.Answers B → Verifier.Answers B → Bool :=
  fun x y a b => decide (V.decider.Accepts (2^n) (toBits x) (toBits y) a.val b.val)

theorem sourceGame_eq (V : Verifier 7) (n B : ℕ) :
    Honest.sourceGame (sourceFamily V n) (predicate V n B) = V.game (2^n) B := by
  unfold Honest.sourceGame SampledGame.game Verifier.game
  congr 1
  funext x y
  exact sampled_dist_eq_clDist _ _ x y

def paddedPredicate {n Q : ℕ} (V : Verifier 7) (hs : V.sampler.dim (2^n) ≤ Q) (B : ℕ) :
    (Fin Q → 𝔽₂) → (Fin Q → 𝔽₂) → Verifier.Answers B → Verifier.Answers B → Bool :=
  fun x y a b => AuxiliaryDecision.sourcePredicate V hs x y a.val b.val

theorem paddedPredicate_eq {n Q : ℕ} (V : Verifier 7) (hs : V.sampler.dim (2^n) ≤ Q) (B : ℕ) :
    paddedPredicate V hs B = SourcePadding.decider (firstEmbedding hs) (predicate V n B) := rfl

/-- Canonical registers contain the entire original question space. -/
theorem dimension_le_registerBits {c lam n : ℕ} (hc : 2 ≤ c) (V : Verifier 7)
    (hV : V.IsBounded lam) (hn : 1 ≤ n) :
    V.sampler.dim (2^n) ≤ SourceCompiler.registerBits c lam n := by
  have hs := (hV.1 (2^n) ((two_le_exp_index_iff n).mpr hn)).1
  have hR := PauliSamplerParameters.originalBound_three_le_registerBits hc lam n
  rw [SourceCompiler.originalBound_eq] at hR
  omega

/-- The padded source retains a perfect PCC strategy. -/
theorem padded_hasPerfectPCC {n Q B : ℕ} (V : Verifier 7)
    (hs : V.sampler.dim (2^n) ≤ Q) (h : V.HasPerfectPCC (2^n) B) :
    ∃ R : SyncStrategy (Honest.sourceGame (AuxiliaryDecision.padded V hs)
        (paddedPredicate V hs B)).doubled,
      R.IsPCC ∧ R.value = 1 := by
  have hsrc : ∃ R : SyncStrategy (Honest.sourceGame (sourceFamily V n) (predicate V n B)).doubled,
      R.IsPCC ∧ R.value = 1 := by
    rw [sourceGame_eq]
    exact h
  obtain ⟨R,hR,hv⟩ := hsrc
  obtain ⟨S,hS,hvS,_⟩ := SourcePadding.exists_perfectPCC (firstEmbedding hs)
    (sourceFamily V n) (predicate V n B) R hR hv
  have he : Honest.sourceGame (AuxiliaryDecision.padded V hs) (paddedPredicate V hs B) =
      Honest.sourceGame (SourcePadding.family (firstEmbedding hs) (sourceFamily V n))
        (SourcePadding.decider (firstEmbedding hs) (predicate V n B)) :=
    SourcePadding.sourceGame_depthFamily (firstEmbedding hs) (sourceFamily V n)
      (predicate V n B) (by decide) (fun w => (V.sampler.cl_exactlyOn _ _).supportedOn)
  rw [he]
  exact ⟨S,hS,hvS⟩

/-- Removing the padded coordinates loses no source-game value. -/
theorem padded_quantumValue_le {n Q B : ℕ} (V : Verifier 7)
    (hs : V.sampler.dim (2^n) ≤ Q) :
    quantumValue (Honest.sourceGame (AuxiliaryDecision.padded V hs)
      (paddedPredicate V hs B)) ≤ V.valStar (2^n) B := by
  have h := SourcePadding.quantumValue_depthFamily_le (firstEmbedding hs)
    (sourceFamily V n) (predicate V n B) (by decide)
    (fun w => (V.sampler.cl_exactlyOn _ _).supportedOn)
  rw [sourceGame_eq] at h
  exact h

end MIPRE.Introspection.VerifierSource
