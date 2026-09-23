/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.CanonicalComplete
import MIPRE.Background.Introspection.CompiledSoundness

/-! # Supplying the ambient introspection contract

The sampler, executable decision kernel, universal clock, all-index budgets,
honest PCC encoding, and actual QLD soundness theorem supply `Introspection 7`.
This is the ambient contract of blueprint `lem:introspection-supply`, with its
polynomial-exponent runtime convention and positive-index soundness domain.
The source-model statement for arbitrary levels remains a separate statement.
-/

noncomputable section
namespace MIPRE.Introspection
open Cost

/-- The complete ambient introspection compiler for seven-level source verifiers.
Its only rigidity input is the proved QLD soundness theorem. -/
theorem exists_seven : Nonempty (MIPRE.Introspection 7) := by
  obtain ⟨c,hc,he,hcb⟩ := PauliErrorParameters.exists_even_constant
    RestrictedSoundness.qldCoefficient RestrictedSoundness.qldExponent_pos
  have hc1 : 1 ≤ c := by omega
  let U := selfClockedUniversal
  obtain ⟨C,hw,hs,hcut⟩ := DecisionCompiler.resources_with_cutoff c hc1 he U
  refine ⟨{
    a := CompiledSoundness.coefficient c
    b := CompiledSoundness.exponent
    one_le_a := CompiledSoundness.coefficient_one_le c
    b_pos := CompiledSoundness.exponent_pos
    b_le_one := CompiledSoundness.exponent_le_one
    C := C
    sampler := PauliSampler.finalSampler c hc1 he 7
    samplerProg := PauliSampler.finalCompiler c 7
    samplerProg_eq := PauliSampler.finalCompiler_apply c hc1 he 7
    compute := DecisionCompiler.compute c U
    output := DecisionCompiler.output c hc1 he U
    output_sampler := DecisionCompiler.output_sampler c hc1 he U
    output_decider := DecisionCompiler.output_decider c hc1 he U
    within := hw
    decider_size := hs
    completeness := CanonicalComplete.output_hasPerfectPCC c hc he U C hcut
    soundness := ?_ }⟩
  intro V lam n ε hV hn hε hv
  apply CompiledSoundness.output_soundness c hc he hcb U V lam n (ansBound C lam n)
    ε hV hn hε _ hv
  have hl := hV.two_le
  simpa only [DecisionCompiler.cutoffAt, show ¬(lam = 0 ∨ n = 0) by omega,
    ↓reduceIte] using hcut lam n

/-- A fixed choice of the proved introspection compiler for the compression pipeline. -/
def seven : MIPRE.Introspection 7 := Classical.choice exists_seven

end MIPRE.Introspection
