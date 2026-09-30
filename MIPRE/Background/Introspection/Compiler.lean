/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Background.Introspection.CanonicalComplete
public import MIPRE.Background.Introspection.CompiledSoundness

@[expose] public section

/-! # Supplying the ambient introspection contract

The sampler, executable decision kernel, universal clock, all-index budgets,
honest PCC encoding, and actual QLD soundness theorem supply `Introspection 7`.
This is the ambient contract of blueprint `lem:introspection-supply`, with its
polynomial-exponent runtime convention and positive-index soundness domain.
The source-model statement for arbitrary levels remains a separate statement.

Phase 4 of `planning/mipco-track.md`: the compiler `seven` is defined with its constants chosen
explicitly, so that its soundness clause can be read in every value model
(`Introspection.seven_soundIn`): in every value model approached by projective strategies of
models where the Pauli basis test is sound, and by the projective strategies of the models it
dominates. Its `soundness` field is the instance at `val*`, where both hold
(`QLD.approxSoundIn_tensor`, `ValueModel.tensor_projApprox`); at `ω_co`, both hold as soon as the
test is sound in every commuting-operator model (`seven_soundIn_commuting`).
-/

noncomputable section
namespace MIPRE.Introspection
open Cost

/-- The compiler's parameter constant: an even constant large against the QLD constants. -/
def sevenConstant : ℕ :=
  (PauliErrorParameters.exists_even_constant RestrictedSoundness.qldCoefficient
    RestrictedSoundness.qldExponent_pos).choose

theorem sevenConstant_spec : 2 ≤ sevenConstant ∧ Even sevenConstant ∧
    2 * RestrictedSoundness.qldCoefficient + 2 ≤
      (sevenConstant : ℝ) * RestrictedSoundness.qldExponent :=
  (PauliErrorParameters.exists_even_constant RestrictedSoundness.qldCoefficient
    RestrictedSoundness.qldExponent_pos).choose_spec

theorem one_le_sevenConstant : 1 ≤ sevenConstant := by
  have := sevenConstant_spec.1
  omega

/-- The compiler's complexity constant. -/
def sevenC : ℕ :=
  (DecisionCompiler.resources_with_cutoff sevenConstant one_le_sevenConstant
    sevenConstant_spec.2.1 selfClockedUniversal).choose

theorem sevenC_spec :
    (∀ source lam n, (DecisionCompiler.output sevenConstant one_le_sevenConstant
      sevenConstant_spec.2.1 selfClockedUniversal source lam).Within n (budget sevenC lam n)) ∧
    (∀ source lam, (DecisionCompiler.output sevenConstant one_le_sevenConstant
      sevenConstant_spec.2.1 selfClockedUniversal source lam).decider.size ≤
        sevenC * (lam + 1) ^ sevenC) ∧
    ∀ lam n, DecisionCompiler.cutoffAt sevenConstant lam n ≤ ansBound sevenC lam n :=
  (DecisionCompiler.resources_with_cutoff sevenConstant one_le_sevenConstant
    sevenConstant_spec.2.1 selfClockedUniversal).choose_spec

/-- **The soundness clause of the compiler's output in a value model**: in every value model
approached by projective strategies of models where the Pauli basis test is sound, and by the
projective strategies of the models it dominates. -/
theorem sevenOutput_soundness (ω : ValueModel) (hω : ω.ProjApprox) (hA : QLD.ApproxSoundIn ω)
    (V : Verifier 7) (lam n : ℕ) (ε : ℝ) (hV : V.IsBounded lam) (hn : 1 ≤ n) (hε : 0 < ε)
    (hv : 1 - ε < (DecisionCompiler.output sevenConstant one_le_sevenConstant
      sevenConstant_spec.2.1 selfClockedUniversal (V.sampler.prog, V.decider.prog) lam).val ω n
        (ansBound sevenC lam n)) :
    1 - delta (CompiledSoundness.coefficient sevenConstant) CompiledSoundness.exponent lam n ε ≤
      V.val ω (2 ^ n) ((2 ^ n) ^ lam) := by
  apply CompiledSoundness.output_soundness ω hω hA sevenConstant sevenConstant_spec.1
    sevenConstant_spec.2.1 sevenConstant_spec.2.2 selfClockedUniversal V lam n
    (ansBound sevenC lam n) ε hV hn hε _ hv
  have hl := hV.two_le
  simpa only [DecisionCompiler.cutoffAt, show ¬(lam = 0 ∨ n = 0) by omega,
    ↓reduceIte] using sevenC_spec.2.2 lam n

/-- **The complete ambient introspection compiler for seven-level source verifiers.** Its only
rigidity input is the Pauli basis test; its soundness field is the tensor-product instance of
`sevenOutput_soundness`, where the test is the proved `thm:qld`. -/
def seven : MIPRE.Introspection 7 where
  a := CompiledSoundness.coefficient sevenConstant
  b := CompiledSoundness.exponent
  one_le_a := CompiledSoundness.coefficient_one_le sevenConstant
  b_pos := CompiledSoundness.exponent_pos
  b_le_one := CompiledSoundness.exponent_le_one
  C := sevenC
  sampler := PauliSampler.finalSampler sevenConstant one_le_sevenConstant sevenConstant_spec.2.1 7
  samplerProg := PauliSampler.finalCompiler sevenConstant 7
  samplerProg_eq := PauliSampler.finalCompiler_apply sevenConstant one_le_sevenConstant
    sevenConstant_spec.2.1 7
  compute := DecisionCompiler.compute sevenConstant selfClockedUniversal
  output := DecisionCompiler.output sevenConstant one_le_sevenConstant sevenConstant_spec.2.1
    selfClockedUniversal
  output_sampler := DecisionCompiler.output_sampler sevenConstant one_le_sevenConstant
    sevenConstant_spec.2.1 selfClockedUniversal
  output_decider := DecisionCompiler.output_decider sevenConstant one_le_sevenConstant
    sevenConstant_spec.2.1 selfClockedUniversal
  within := sevenC_spec.1
  decider_size := sevenC_spec.2.1
  completeness := CanonicalComplete.output_hasPerfectPCC sevenConstant sevenConstant_spec.1
    sevenConstant_spec.2.1 selfClockedUniversal sevenC sevenC_spec.2.2
  soundness V lam n ε hV hn hε hv :=
    sevenOutput_soundness .tensor ValueModel.tensor_projApprox QLD.approxSoundIn_tensor
      V lam n ε hV hn hε hv

/-- The ambient introspection compiler exists. -/
theorem exists_seven : Nonempty (MIPRE.Introspection 7) := ⟨seven⟩

/-- **Introspection is sound in every value model** approached by projective strategies of models
where the Pauli basis test is sound, and by the projective strategies of the models it
dominates. -/
theorem seven_soundIn (ω : ValueModel) (hω : ω.ProjApprox) (hA : QLD.ApproxSoundIn ω) :
    seven.SoundIn ω :=
  fun V lam n ε hV hn hε hv => sevenOutput_soundness ω hω hA V lam n ε hV hn hε hv

/-- **Introspection is sound in the commuting-operator model**, as soon as the Pauli basis test is
sound in the model of every commuting-operator strategy (`QLD.SoundCo`, Phase 5 of
`planning/mipco-track.md`). -/
theorem seven_soundIn_commuting (h : QLD.SoundCo) : seven.SoundIn .commuting :=
  seven_soundIn .commuting ValueModel.commuting_projApprox (QLD.approxSoundIn_commuting h)

end MIPRE.Introspection

end
