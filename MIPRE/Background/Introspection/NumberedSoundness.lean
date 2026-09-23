/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.NumberedComplete
import MIPRE.Background.Introspection.QLDExtractionAdapter

/-! # Source soundness with the actual finite register numbering

Coordinate relabeling is performed on the intrinsic quotient predicate. Dual
answers are only canonicalized afterwards in binary coordinates. Thus no
equivariance of the chosen canonical complement is used.
-/

noncomputable section
namespace MIPRE.Introspection.NumberedSoundness
open Matrix Finset CL Classical BinaryComplete RestrictedSoundness
set_option linter.unusedSectionVars false

variable {F A I : Type} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype I] [DecidableEq I] {m t d ℓ : ℕ} [NeZero m]
  (e : I ≃ Coord m t) (L : Bool → CLFun (ZMod 2) I ℓ)
  (D : (I → ZMod 2) → (I → ZMod 2) → A → A → Bool)
  (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (χ : F → Fin m) (π : F ≃ F)

private theorem reindexedGame_eq :
    AuxiliaryQuotient.reindexedGame e QLD.adj (.pauli .X) (.pauli .Z)
      (QLD.PauliCL.ExplicitSeed.binaryPresentation χ b) L
      (NumberedComplete.project (d := d) e b) D (ExplicitGame.pauliCheck hm π b) =
      BinaryComplete.explicitQuotientGame (d := d)
        (SourceReindex.family e L) (SourceReindex.decider e D) hm b χ π := by
  have hproj : (fun a : QLD.Answer F m d =>
      reindexEquiv e (NumberedComplete.project e b a)) = BinaryComplete.project b := by
    funext a
    exact (reindexEquiv e).apply_symm_apply _
  change AuxiliaryQuotient.game _ _ _ _ _ _ _ _ = _
  rw [hproj]
  rfl

/-- Relabel all answer coordinates, retaining the original shared state. -/
abbrev coordinateStrategy
    (S : TensorProductStrategy (NumberedComplete.game (d := d) e L D hm b χ π)) :=
  (AuxiliaryQuotient.reindexedStrategy e QLD.adj (.pauli .X) (.pauli .Z)
    (QLD.PauliCL.ExplicitSeed.binaryPresentation χ b) L
    (NumberedComplete.project e b) D (ExplicitGame.pauliCheck hm π b) S).copy
      (BinaryComplete.explicitQuotientGame (SourceReindex.family e L)
        (SourceReindex.decider e D) hm b χ π)

theorem coordinateStrategy_failure_le
    (S : TensorProductStrategy (NumberedComplete.game (d := d) e L D hm b χ π))
    {ε : ℝ} (hS : 1 - S.value ≤ ε) :
    1 - (coordinateStrategy e L D hm b χ π S).value ≤ ε := by
  have hv := (AuxiliaryQuotient.reindexedStrategy e QLD.adj (.pauli .X) (.pauli .Z)
    (QLD.PauliCL.ExplicitSeed.binaryPresentation χ b) L
    (NumberedComplete.project e b) D (ExplicitGame.pauliCheck hm π b) S).value_copy_le
      (BinaryComplete.explicitQuotientGame (SourceReindex.family e L)
        (SourceReindex.decider e D) hm b χ π)
      (fun _ _ => by rw [reindexedGame_eq e L D hm b χ π])
      (fun _ _ _ _ h => by rwa [reindexedGame_eq e L D hm b χ π] at h)
  rw [AuxiliaryQuotient.reindexedStrategy_value] at hv
  exact (sub_le_sub_left hv 1).trans hS

/-- Decode quotient duals in binary coordinates. -/
abbrev explicitStrategy
    (S : TensorProductStrategy (NumberedComplete.game (d := d) e L D hm b χ π)) :
    TensorProductStrategy (ExplicitGame.game hm χ π b (SourceReindex.family e L)
      (BinaryComplete.project (d := d) b) (SourceReindex.decider e D)) :=
  AuxiliaryQuotient.decodedStrategy QLD.adj (.pauli .X) (.pauli .Z)
      (QLD.PauliCL.ExplicitSeed.binaryPresentation χ b) (SourceReindex.family e L)
      (BinaryComplete.project b) (SourceReindex.decider e D) (ExplicitGame.pauliCheck hm π b)
      (coordinateStrategy e L D hm b χ π S)

/-- Undo the explicit seed selector after decoding the quotient duals. -/
abbrev legacyStrategy
    (S : TensorProductStrategy (NumberedComplete.game (d := d) e L D hm b χ π)) :=
  ExplicitGame.toLegacy hm χ π b (SourceReindex.family e L) (BinaryComplete.project b)
    (SourceReindex.decider e D) (explicitStrategy e L D hm b χ π S)

theorem legacyStrategy_failure_le
    (S : TensorProductStrategy (NumberedComplete.game (d := d) e L D hm b χ π))
    (hL : ∀ w, (L w).SupportedOn univ) (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)
    {ε : ℝ} (hS : 1 - S.value ≤ ε) :
    1 - (legacyStrategy e L D hm b χ π S).value ≤ ε := by
  have hv := ExplicitGame.toLegacy_value hm χ π hχ b (SourceReindex.family e L)
    (BinaryComplete.project b) (SourceReindex.decider e D) (explicitStrategy e L D hm b χ π S)
  apply (congrArg (fun x : ℝ => 1 - x) hv).le.trans
  apply AuxiliaryQuotient.decodedStrategy_failure_le
  · intro w
    simpa only [SourceReindex.family, map_univ_equiv] using (hL w).reindex e
  · exact coordinateStrategy_failure_le e L D hm b χ π S hS

set_option backward.isDefEq.respectTransparency false in
theorem legacyStrategy_supported_A
    (S : TensorProductStrategy (NumberedComplete.game (d := d) e L D hm b χ π))
    (hS : ParsedPauliSupported S.PA.toPOVM) :
    ParsedPauliSupported (legacyStrategy e L D hm b χ π S).PA.toPOVM := by
  intro W a ha
  change (legacyStrategy e L D hm b χ π S).PA.M (.inl (.pauli W),0) a ≠ 0 at ha
  have he := ExplicitGame.toLegacy_pauli_A hm χ π b (SourceReindex.family e L)
    (BinaryComplete.project b) (SourceReindex.decider e D)
    (explicitStrategy e L D hm b χ π S) W a
  have hd := AuxiliaryQuotient.decodedStrategy_pauli_A QLD.adj (.pauli .X) (.pauli .Z)
    (QLD.PauliCL.ExplicitSeed.binaryPresentation χ b) (SourceReindex.family e L)
    (BinaryComplete.project b) (SourceReindex.decider e D) (ExplicitGame.pauliCheck hm π b)
    (coordinateStrategy e L D hm b χ π S) (.pauli W) 0 a
  have hc : (coordinateStrategy e L D hm b χ π S).PA.M (.inl (.pauli W),0) a ≠ 0 := by
    intro hz
    exact ha (he.trans (hd.trans hz))
  change S.PA.M (.inl (.pauli W),0) ((AuxiliaryQuotient.answerEquiv e).symm a) ≠ 0 at hc
  obtain ⟨x,hx⟩ := hS W _ hc
  refine ⟨x, ?_⟩
  exact (Equiv.symm_apply_eq (e := AuxiliaryQuotient.answerEquiv e)).mp hx

set_option backward.isDefEq.respectTransparency false in
theorem legacyStrategy_supported_B
    (S : TensorProductStrategy (NumberedComplete.game (d := d) e L D hm b χ π))
    (hS : ParsedPauliSupported S.PB.toPOVM) :
    ParsedPauliSupported (legacyStrategy e L D hm b χ π S).PB.toPOVM := by
  intro W a ha
  change (legacyStrategy e L D hm b χ π S).PB.M (.inl (.pauli W),0) a ≠ 0 at ha
  have he := ExplicitGame.toLegacy_pauli_B hm χ π b (SourceReindex.family e L)
    (BinaryComplete.project b) (SourceReindex.decider e D)
    (explicitStrategy e L D hm b χ π S) W a
  have hd := AuxiliaryQuotient.decodedStrategy_pauli_B QLD.adj (.pauli .X) (.pauli .Z)
    (QLD.PauliCL.ExplicitSeed.binaryPresentation χ b) (SourceReindex.family e L)
    (BinaryComplete.project b) (SourceReindex.decider e D) (ExplicitGame.pauliCheck hm π b)
    (coordinateStrategy e L D hm b χ π S) (.pauli W) 0 a
  have hc : (coordinateStrategy e L D hm b χ π S).PB.M (.inl (.pauli W),0) a ≠ 0 := by
    intro hz
    exact ha (he.trans (hd.trans hz))
  change S.PB.M (.inl (.pauli W),0) ((AuxiliaryQuotient.answerEquiv e).symm a) ≠ 0 at hc
  obtain ⟨x,hx⟩ := hS W _ hc
  refine ⟨x, ?_⟩
  exact (Equiv.symm_apply_eq (e := AuxiliaryQuotient.answerEquiv e)).mp hx

/-- The precise actual QLD strategy used by the numbered source-game theorem. -/
abbrev qldStrategy
    (S : TensorProductStrategy (NumberedComplete.game (d := d) e L D hm b χ π)) :=
  restriction hm b (SourceReindex.family e L) (SourceReindex.decider e D)
    (legacyStrategy e L D hm b χ π S)

theorem qldStrategy_supported_A
    (S : TensorProductStrategy (NumberedComplete.game (d := d) e L D hm b χ π))
    (hS : ParsedPauliSupported S.PA.toPOVM) :
    PauliSupported (qldStrategy e L D hm b χ π S).PA.toPOVM := by
  intro W a ha
  change (qldStrategy e L D hm b χ π S).PA.M (.pauli W) a = 0
  rw [PauliRestriction.strategy_pauli_A]
  exact completePauliPOVM_invalid_of_supported _
    (legacyStrategy_supported_A e L D hm b χ π S hS W) W a ha

theorem qldStrategy_supported_B
    (S : TensorProductStrategy (NumberedComplete.game (d := d) e L D hm b χ π))
    (hS : ParsedPauliSupported S.PB.toPOVM) :
    PauliSupported (qldStrategy e L D hm b χ π S).PB.toPOVM := by
  intro W a ha
  change (qldStrategy e L D hm b χ π S).PB.M (.pauli W) a = 0
  rw [PauliRestriction.strategy_pauli_B]
  exact completePauliPOVM_invalid_of_supported _
    (legacyStrategy_supported_B e L D hm b χ π S hS W) W a ha

/-- A witness about the actual restricted strategy gives the source bound in
the original finite coordinates, with no coordinate or quotient penalty. -/
theorem quantumValue_ge_of_extraction
    (S : TensorProductStrategy (NumberedComplete.game (d := d) e L D hm b χ π))
    (hb : LowDegree.IsSelfDualBasis b) (hL : ∀ w, (L w).ExactlyOn univ)
    (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s) {ε δ : ℝ}
    (hδ : 0 ≤ δ) (hS : 1 - S.value ≤ ε)
    (w : FieldExtraction hm (qldStrategy e L D hm b χ π S) δ) :
    1 - validSoundnessCoefficient ℓ (edgeCount ℓ) *
      iteratedRoot (6 * ℓ + 2) (max ε δ) ≤ quantumValue (Honest.sourceGame L D) := by
  let wb := w.toBinary b hb
  have hv := RestrictedSoundness.quantumValue_ge_of_extraction hm b
    (SourceReindex.family e L) (SourceReindex.decider e D)
    (legacyStrategy e L D hm b χ π S) (SourceReindex.exactlyOn e L hL)
    wb.ξ wb.ξ_unit wb.VA wb.VB wb.VA_isometry wb.VB_isometry hδ
    (legacyStrategy_failure_le e L D hm b χ π S (fun w => (hL w).supportedOn) hχ hS)
    wb.state_error wb.X_error wb.Z_error
  exact hv.trans_eq (SourceReindex.quantumValue_eq e L D)

/-- Uniform profile absorption only needs a witness for this restriction,
rather than an extraction hypothesis quantified over arbitrary strategies. -/
theorem quantumValue_ge_of_errorProfile
    (S : TensorProductStrategy (NumberedComplete.game (d := d) e L D hm b χ π))
    (hb : LowDegree.IsSelfDualBasis b) (hL : ∀ w, (L w).ExactlyOn univ)
    (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)
    {a β x ε : ℝ} (ha : 1 ≤ a) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hx : 1 ≤ x) (hε : 0 ≤ ε) (hS : 1 - S.value ≤ ε)
    (w : FieldExtraction hm (qldStrategy e L D hm b χ π S)
      (errorProfile a β x (edgeCount ℓ * ε))) :
    1 - errorProfile (profileCoefficient ℓ a β) (β * rootExponent (6 * ℓ + 2)) x ε ≤
      quantumValue (Honest.sourceGame L D) := by
  have he0 : 0 ≤ edgeCount ℓ := (by norm_num : (0 : ℝ) ≤ 1).trans (edgeCount_one_le ℓ)
  have hδ := errorProfile_nonneg (a := a) (b := β) (x := x)
    (by linarith) (by linarith) (mul_nonneg he0 hε)
  have hv := quantumValue_ge_of_extraction e L D hm b χ π S hb hL hχ hδ hS w
  exact errorProfile_of_restricted_bound (6 * ℓ + 2)
    (by linarith [validSoundnessCoefficient_one_le ℓ he0]) ha hβ0 hβ1
    (edgeCount_one_le ℓ) hx hε le_rfl (quantumValue_nonneg _) hv

theorem qldStrategy_failure_le
    (S : TensorProductStrategy (NumberedComplete.game (d := d) e L D hm b χ π))
    (hL : ∀ w, (L w).SupportedOn univ) (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)
    {ε : ℝ} (hS : 1 - S.value ≤ ε) :
    1 - (qldStrategy e L D hm b χ π S).value ≤ edgeCount ℓ * ε :=
  PauliRestriction.strategy_failure_le hm b (SourceReindex.family e L)
    (BinaryComplete.project b) (SourceReindex.decider e D)
    (legacyStrategy e L D hm b χ π S) (.val 0) (.val 0)
    (legacyStrategy_failure_le e L D hm b χ π S hL hχ hS)

/-- Actual QLD soundness supplies the extraction witness; no external
extraction hypothesis remains. Only decoder-enforced Pauli support is used. -/
theorem quantumValue_ge_of_qld
    (S : TensorProductStrategy (NumberedComplete.game (d := d) e L D hm b χ π))
    (hd : 1 ≤ d) (hb : LowDegree.IsSelfDualBasis b)
    (hL : ∀ w, (L w).ExactlyOn univ) (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)
    (hA : ParsedPauliSupported S.PA.toPOVM) (hB : ParsedPauliSupported S.PB.toPOVM)
    {ε : ℝ} (hε : 0 ≤ ε) (hS : 1 - S.value ≤ ε) :
    1 - validSoundnessCoefficient ℓ (edgeCount ℓ) * iteratedRoot (6 * ℓ + 2)
      (max ε (QLD.errShape qldCoefficient qldExponent (edgeCount ℓ * ε)
        m d (Fintype.card F))) ≤ quantumValue (Honest.sourceGame L D) := by
  have hη : 0 ≤ edgeCount ℓ * ε := mul_nonneg
    ((by norm_num : (0 : ℝ) ≤ 1).trans (edgeCount_one_le ℓ)) hε
  obtain ⟨w⟩ := fieldExtraction_exists hm hd (qldStrategy e L D hm b χ π S)
    (qldStrategy_supported_A e L D hm b χ π S hA)
    (qldStrategy_supported_B e L D hm b χ π S hB) hη
    (qldStrategy_failure_le e L D hm b χ π S (fun w => (hL w).supportedOn) hχ hS)
  exact quantumValue_ge_of_extraction e L D hm b χ π S hb hL hχ
    (QLD.errShape_nonneg (by linarith [qldCoefficient_one_le]) hη) hS w

section Canonical
open SourceCompiler PauliSamplerParameters

local instance canonical_neZero (c lam n : ℕ) : NeZero (registerPower c lam n) :=
  ⟨Nat.ne_of_gt (registerPower_pos c lam n)⟩

/-- Uniform soundness for the actual canonical field and register parameters,
on the source's original coordinate type. All QLD tails are absorbed. -/
theorem canonical_quantumValue_ge
    (c lam n : ℕ) (hc : 2 ≤ c)
    (hcb : 2 * qldCoefficient + 2 ≤ (c : ℝ) * qldExponent)
    (hx : 2 ≤ lam * n) (hq : Fintype.card F = 2 ^ fieldBits c lam n)
    (hm : registerPower c lam n ∣ Fintype.card F)
    (b : Module.Basis (Fin (fieldBits c lam n)) (ZMod 2) F)
    (hb : LowDegree.IsSelfDualBasis b)
    (e : I ≃ Coord (registerPower c lam n) (fieldBits c lam n))
    (L : Bool → CLFun (ZMod 2) I ℓ)
    (D : (I → ZMod 2) → (I → ZMod 2) → A → A → Bool)
    (hL : ∀ w, (L w).ExactlyOn univ)
    (χ : F → Fin (registerPower c lam n)) (π : F ≃ F)
    (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)
    (S : TensorProductStrategy (NumberedComplete.game (d := 1) e L D hm b χ π))
    (hA : ParsedPauliSupported S.PA.toPOVM) (hB : ParsedPauliSupported S.PB.toPOVM)
    {ε : ℝ} (hε : 0 ≤ ε) (hS : 1 - S.value ≤ ε) :
    1 - errorProfile
      (profileCoefficient ℓ (PauliErrorParameters.profileCoefficient qldCoefficient c) qldExponent)
      (qldExponent * rootExponent (6 * ℓ + 2)) (lam * n) ε ≤
      quantumValue (Honest.sourceGame L D) := by
  have hη : 0 ≤ edgeCount ℓ * ε := mul_nonneg
    ((by norm_num : (0 : ℝ) ≤ 1).trans (edgeCount_one_le ℓ)) hε
  obtain ⟨w⟩ := degreeOne_fieldExtraction_exists hm (qldStrategy e L D hm b χ π S)
    (qldStrategy_supported_A e L D hm b χ π S hA)
    (qldStrategy_supported_B e L D hm b χ π S hB) hη
    (qldStrategy_failure_le e L D hm b χ π S (fun w => (hL w).supportedOn) hχ hS)
  apply quantumValue_ge_of_errorProfile e L D hm b χ π S hb hL hχ
    (PauliErrorParameters.profileCoefficient_one_le qldCoefficient c)
    qldExponent_pos qldExponent_lt_one.le
    (by exact_mod_cast (show 1 ≤ lam * n by omega)) hε hS
  refine w.mono ?_
  rw [hq]
  exact PauliErrorParameters.canonical_qldError_le_profile qldCoefficient_one_le
    qldExponent_pos qldExponent_lt_one.le c hc hcb lam n hx (edgeCount ℓ * ε) hη

end Canonical

end MIPRE.Introspection.NumberedSoundness
end
