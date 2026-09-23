/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.RestrictedSoundness
import MIPRE.Background.Introspection.ExplicitGame
import MIPRE.Foundations.Introspection.RestrictedErrorBounds
import MIPRE.Foundations.Introspection.SourcePaddingValue

/-! # Uniform conditional soundness and return to the unpadded source

The external input supplies actual QLD extraction witnesses with a uniform
two-term error profile. The restriction factor, the finite introspection loss,
the explicit-selector transport, and removal of source padding are proved here.
-/

noncomputable section
namespace MIPRE.Introspection.RestrictedSoundness
open Matrix Finset Classical BinaryComplete
set_option linter.unusedSectionVars false

/-- Ordered-edge loss in the complete introspection type graph. -/
def edgeCount (ℓ : ℕ) : ℝ :=
  (TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card

theorem edgeCount_one_le (ℓ : ℕ) : 1 ≤ edgeCount ℓ := by
  have h : 1 ≤ (TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card :=
    (TypeGraph.edges_nonempty QLD.adj (.pauli .X) (.pauli .Z) ℓ).card_pos
  unfold edgeCount
  exact_mod_cast h

/-- Uniform coefficient after restriction and the finite soundness argument. -/
def profileCoefficient (ℓ : ℕ) (a b : ℝ) : ℝ :=
  powerCoefficient (validSoundnessCoefficient ℓ (edgeCount ℓ) *
    (max 1 ((edgeCount ℓ) ^ b)) ^ rootExponent (6 * ℓ + 2)) a
      (rootExponent (6 * ℓ + 2))

theorem profileCoefficient_one_le (ℓ : ℕ) (a b : ℝ) :
    1 ≤ profileCoefficient ℓ a b := one_le_powerCoefficient _ _ _

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] {m t d ℓ : ℕ} [NeZero m]
  {A : Type} [Fintype A] [Nonempty A]
  (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (L : Bool → CL.CLFun (ZMod 2) (Coord m t) ℓ)
  (D : Seed m t → Seed m t → A → A → Bool)

/-- Conditional source soundness with constants independent of the strategy
error and verifier index. The input is QLD extraction, not source-game value. -/
theorem quantumValue_ge_of_qld_errorProfile
    (S : TensorProductStrategy
      (PauliRestriction.fullGame hm b L (BinaryComplete.project (d := d) b) D))
    (hL : ∀ w, (L w).ExactlyOn univ)
    {a β x ε : ℝ} (ha : 1 ≤ a) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hx : 1 ≤ x) (hε : 0 ≤ ε) (hfail : 1 - S.value ≤ ε)
    (extract : ∀ (R : TensorProductStrategy (QLD.qldGame (d := d) hm)) (η : ℝ),
      0 ≤ η → 1 - R.value ≤ η →
      Nonempty (Extraction hm b R (errorProfile a β x η))) :
    1 - errorProfile (profileCoefficient ℓ a β) (β * rootExponent (6 * ℓ + 2)) x ε ≤
      quantumValue (Honest.sourceGame L D) := by
  have he0 : 0 ≤ edgeCount ℓ := (by norm_num : (0 : ℝ) ≤ 1).trans (edgeCount_one_le ℓ)
  have hη : 0 ≤ edgeCount ℓ * ε := mul_nonneg he0 hε
  have hδ := errorProfile_nonneg (a := a) (b := β) (x := x)
    (by linarith) (by linarith) hη
  have hv := quantumValue_ge_of_qld_extraction hm b L D S hL hδ hfail
    (fun R hR => extract R (edgeCount ℓ * ε) hη hR)
  exact errorProfile_of_restricted_bound (6 * ℓ + 2)
    (by linarith [validSoundnessCoefficient_one_le ℓ he0]) ha hβ0 hβ1
    (edgeCount_one_le ℓ) hx hε le_rfl (quantumValue_nonneg _) hv

/-- The executable selector's complete finite game has the same conditional
source soundness bound, including mixed and auxiliary edges. -/
theorem explicit_quantumValue_ge_of_qld_errorProfile
    (χ : F → Fin m) (π : F ≃ F) (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)
    (S : TensorProductStrategy
      (ExplicitGame.game hm χ π b L (BinaryComplete.project (d := d) b) D))
    (hL : ∀ w, (L w).ExactlyOn univ)
    {a β x ε : ℝ} (ha : 1 ≤ a) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hx : 1 ≤ x) (hε : 0 ≤ ε) (hfail : 1 - S.value ≤ ε)
    (extract : ∀ (R : TensorProductStrategy (QLD.qldGame (d := d) hm)) (η : ℝ),
      0 ≤ η → 1 - R.value ≤ η →
      Nonempty (Extraction hm b R (errorProfile a β x η))) :
    1 - errorProfile (profileCoefficient ℓ a β) (β * rootExponent (6 * ℓ + 2)) x ε ≤
      quantumValue (Honest.sourceGame L D) := by
  apply quantumValue_ge_of_qld_errorProfile hm b L D
    (ExplicitGame.toLegacy hm χ π b L (BinaryComplete.project b) D S)
    hL ha hβ0 hβ1 hx hε _ extract
  rwa [ExplicitGame.toLegacy_value hm χ π hχ b L (BinaryComplete.project b) D]

section Padding
variable {I : Type} [Fintype I] [DecidableEq I] [DecidableEq A]

/-- After explicit finite-game soundness, spectator-coordinate padding is
removed with no further error or change to the uniform profile constants. -/
theorem padded_quantumValue_ge_of_qld_errorProfile
    (e : I ↪ Coord m t) (L₀ : Bool → CL.CLFun (ZMod 2) I ℓ)
    (D₀ : (I → ZMod 2) → (I → ZMod 2) → A → A → Bool)
    (hℓ : 0 < ℓ) (hL₀ : ∀ w, (L₀ w).ExactlyOn univ)
    (χ : F → Fin m) (π : F ≃ F) (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)
    (S : TensorProductStrategy (ExplicitGame.game hm χ π b
      (SourcePadding.depthFamily e L₀) (BinaryComplete.project (d := d) b)
      (SourcePadding.decider e D₀)))
    {a β x ε : ℝ} (ha : 1 ≤ a) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hx : 1 ≤ x) (hε : 0 ≤ ε) (hfail : 1 - S.value ≤ ε)
    (extract : ∀ (R : TensorProductStrategy (QLD.qldGame (d := d) hm)) (η : ℝ),
      0 ≤ η → 1 - R.value ≤ η →
      Nonempty (Extraction hm b R (errorProfile a β x η))) :
    1 - errorProfile (profileCoefficient ℓ a β) (β * rootExponent (6 * ℓ + 2)) x ε ≤
      quantumValue (Honest.sourceGame L₀ D₀) := by
  exact (explicit_quantumValue_ge_of_qld_errorProfile hm b
    (SourcePadding.depthFamily e L₀) (SourcePadding.decider e D₀) χ π hχ S
    (SourcePadding.depthFamily_exactlyOn e L₀ hℓ hL₀)
    ha hβ0 hβ1 hx hε hfail extract).trans
      (SourcePadding.quantumValue_depthFamily_le e L₀ D₀ hℓ (fun w => (hL₀ w).supportedOn))

end Padding

end MIPRE.Introspection.RestrictedSoundness
end
