/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.BinaryExtraction
import MIPRE.Foundations.Introspection.PauliErrorParameters

/-! # Conditional soundness with the actual canonical QLD parameters

The only external mathematical input is existence of field-register QLD
extraction witnesses with the three-term error bound. All parameter-tail
absorption, coordinate conversion, finite introspection soundness, explicit
selector transport, and source-padding removal are checked components.
-/

noncomputable section
namespace MIPRE.Introspection.RestrictedSoundness
open Finset Classical BinaryComplete SourceCompiler PauliSamplerParameters
set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {A I : Type} [Fintype A] [Nonempty A] [DecidableEq A] [Fintype I] [DecidableEq I]
  {ℓ : ℕ}

local instance canonical_neZero (c lam n : ℕ) : NeZero (registerPower c lam n) :=
  ⟨by have := registerPower_pos c lam n; omega⟩

/-- Source-game soundness directly from the degree-one QLD extraction bound
at the sampler's actual field size and point dimension. -/
theorem canonical_quantumValue_ge_of_field_extraction
    {a β : ℝ} (ha : 1 ≤ a) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (c lam n : ℕ) (hc : 2 ≤ c) (hcb : 2 * a + 2 ≤ (c : ℝ) * β)
    (hx : 2 ≤ lam * n)
    (hq : Fintype.card F = 2 ^ fieldBits c lam n)
    (hm : registerPower c lam n ∣ Fintype.card F)
    (b : Module.Basis (Fin (fieldBits c lam n)) (ZMod 2) F)
    (hb : LowDegree.IsSelfDualBasis b)
    (e : I ↪ Coord (registerPower c lam n) (fieldBits c lam n))
    (L : Bool → CL.CLFun (ZMod 2) I ℓ)
    (D : (I → ZMod 2) → (I → ZMod 2) → A → A → Bool)
    (hℓ : 0 < ℓ) (hL : ∀ w, (L w).ExactlyOn univ)
    (χ : F → Fin (registerPower c lam n)) (π : F ≃ F)
    (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)
    (S : TensorProductStrategy (ExplicitGame.game hm χ π b
      (SourcePadding.depthFamily e L) (BinaryComplete.project (d := 1) b)
      (SourcePadding.decider e D)))
    {ε : ℝ} (hε : 0 ≤ ε) (hfail : 1 - S.value ≤ ε)
    (extract : ∀ (R : TensorProductStrategy (QLD.qldGame (d := 1) hm)) (η : ℝ),
      0 ≤ η → 1 - R.value ≤ η → Nonempty (FieldExtraction hm R
        (PauliErrorParameters.qldError a β (registerPower c lam n) (Fintype.card F) η))) :
    1 - errorProfile
      (profileCoefficient ℓ (PauliErrorParameters.profileCoefficient a c) β)
      (β * rootExponent (6 * ℓ + 2)) (lam * n) ε ≤
      quantumValue (Honest.sourceGame L D) := by
  apply padded_quantumValue_ge_of_field_extraction hm b hb e L D hℓ hL χ π hχ S
    (PauliErrorParameters.profileCoefficient_one_le a c) hβ0 hβ1
    (by exact_mod_cast (show 1 ≤ lam * n by omega)) hε hfail
  intro R η hη hR
  obtain ⟨w⟩ := extract R η hη hR
  refine ⟨w.mono ?_⟩
  rw [hq]
  exact PauliErrorParameters.canonical_qldError_le_profile ha hβ0 hβ1 c hc hcb lam n hx η hη

end MIPRE.Introspection.RestrictedSoundness
end
