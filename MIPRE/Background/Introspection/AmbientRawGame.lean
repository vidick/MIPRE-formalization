/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Background.Introspection.AmbientVerifierTransport
public import MIPRE.Background.Introspection.DecisionKernelCanonical

@[expose] public section

/-! # Restricting the output verifier to its actual typed kernel

The outer answer alphabet is first reduced to the enforced binary cutoff.
Finite graph detyping then gives the same-state typed strategy with its fixed
loss factor, and carries perfect PCC completeness in the other direction.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the restriction is one of
projective strategies in any model, and the value identities hold in every value model.
-/

noncomputable section
namespace MIPRE.Introspection.DecisionCompiler
open Cost CL CL.Detyping CL.Detyping.Program
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

abbrev outerBound (c lam n : ℕ) :=
  answerBound (SourceCompiler.registerBits c lam n) (SourceCompiler.originalBound lam n)

abbrev rawPredicate (c : ℕ) (hc : 1 ≤ c) (he : Even c) (U : ClockedUniversalMachine)
    (source : Prog × Prog) (lam n : ℕ) :=
  DeciderProgram.typedPredicate (extendedSampler c hc he lam)
    (typedDecider c U (SourceDescriptionCompiler.clamp (source,lam)))
    (constantCutoff (outerBound c lam n)) n

abbrev rawGame (c : ℕ) (hc : 1 ≤ c) (he : Even c) (U : ClockedUniversalMachine)
    (source : Prog × Prog) (lam n : ℕ) :=
  typedGame graph (TypeGraph.edges_nonempty QLD.adj (.pauli .X) (.pauli .Z) 7)
    (DeciderProgram.sourceFamily (extendedSampler c hc he lam) n)
    (rawPredicate c hc he U source lam n)

theorem raw_accepts_iff (c : ℕ) (hc : 1 ≤ c) (he : Even c) (U : ClockedUniversalMachine)
    {lam n : ℕ} (V : Verifier 7) (hV : V.IsBounded lam)
    (q r : Question DecisionKernel.Label (Fin (PauliSampler.dimension c lam n)))
    (a b : Verifier.Answers (outerBound c lam n)) :
    (rawGame c hc he U (V.sampler.prog,V.decider.prog) lam n).D q r a b = true ↔
      DecisionKernel.program U (DecisionKernel.canonicalInput V lam n
        (SourceCompiler.registerBits c lam n) (SourceCompiler.originalBound lam n)
        (PauliSamplerParameters.parameters c lam n) q.1 r.1 (toBits q.2) (toBits r.2) a.val b.val) = true := by
  classical
  change @decide (a.val.length ≤ outerBound c lam n ∧ b.val.length ≤ outerBound c lam n ∧
    (typedDecider c U (SourceDescriptionCompiler.clamp ((V.sampler.prog,V.decider.prog),lam))).Accepts
      n q.1 (toBits q.2) r.1 (toBits r.2) a.val b.val) (Classical.propDecidable _) = true ↔ _
  simp only [decide_eq_true_eq,a.property,b.property,true_and]
  rw [typedDecider_accepts,SourceDescriptionCompiler.clamp_bounded V hV]
  dsimp only [DecisionPreparation.kernelInput]
  rw [show ClockSimulation.indexReader (encode (n,q.1,toBits q.2,r.1,toBits r.2,a.val,b.val)) = n
    from readNat_encode n]
  rfl

/-- Answers beyond the enforced cutoff never help, in every value model. -/
theorem output_val_cutoff (ω : ValueModel) (c : ℕ) (hc : 1 ≤ c) (he : Even c)
    (U : ClockedUniversalMachine) (source : Prog × Prog) {lam n B : ℕ} (hl : 1 ≤ lam)
    (hn : 1 ≤ n) (hB : outerBound c lam n ≤ B) :
    (output c hc he U source lam).val ω n B =
      (output c hc he U source lam).val ω n (outerBound c lam n) := by
  apply Verifier.val_eq_of_rejects _ ω hB
  intro x y a b hlong hacc
  have hh := (accepts_positive_bounds c U source.1 source.2 hl hn x y a b hacc).2.2
  change a.length ≤ outerBound c lam n ∧ b.length ≤ outerBound c lam n at hh
  rcases hlong with hlong | hlong <;> omega

/-- **The output verifier's value is the reference verifier's at the cutoff**, in every value
model. -/
theorem output_val_eq_reference (ω : ValueModel) (c : ℕ) (hc : 1 ≤ c) (he : Even c)
    (U : ClockedUniversalMachine) (source : Prog × Prog) {lam n B : ℕ} (hl : 1 ≤ lam)
    (hn : 1 ≤ n) (hB : outerBound c lam n ≤ B) :
    (output c hc he U source lam).val ω n B =
      ω.val ((reference c hc he U source lam n).game n (outerBound c lam n)) := by
  rw [output_val_cutoff ω c hc he U source hl hn hB, val_reference ω c hc he U source hl hn]
  rfl

/-- A perfect typed raw-kernel strategy gives completeness of the actual output. -/
theorem output_hasPerfectPCC_of_raw (c : ℕ) (hc : 1 ≤ c) (he : Even c)
    (U : ClockedUniversalMachine) (source : Prog × Prog) {lam n B : ℕ}
    (hl : 1 ≤ lam) (hn : 1 ≤ n) (hB : outerBound c lam n ≤ B)
    (S : SyncStrategy (rawGame c hc he U source lam n).doubled)
    (hS : S.IsPCC) (hv : S.value = 1) :
    (output c hc he U source lam).HasPerfectPCC n B := by
  apply Verifier.hasPerfectPCC_of_le _ hB
  apply (hasPerfectPCC_reference c hc he U source hl hn _).mpr
  exact DeciderProgram.verifier_hasPerfectPCC graph (extendedSampler c hc he lam)
    (typedDecider c U (SourceDescriptionCompiler.clamp (source,lam)))
    (constantCutoff (outerBound c lam n))
    (TypeGraph.symmetric QLD.adj (.pauli .X) (.pauli .Z))
    (TypeGraph.edges_nonempty QLD.adj (.pauli .X) (.pauli .Z) 7)
    (by decide) (typedDecider_total c U _) n S hS hv

def detypingLoss : ℝ := (16 : ℝ) ^ Fintype.card DecisionKernel.Label

theorem detypingLoss_nonneg : 0 ≤ detypingLoss := pow_nonneg (by norm_num) _

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- **A strategy for the reference verifier's game restricts to a typed raw strategy**, in the
same model, with the detyping loss. With `output_val_eq_reference`, a value of the output
verifier above `1 - ε` in a value model approached by projective strategies gives such a raw
strategy of failure at most `detypingLoss * ε`. -/
theorem exists_raw_failure_le (c : ℕ) (hc : 1 ≤ c) (he : Even c)
    (U : ClockedUniversalMachine) (source : Prog × Prog) {lam n : ℕ}
    {M : BipartiteModel 𝒞 𝒜 ℬ}
    (S : M.ProjStrat ((reference c hc he U source lam n).game n (outerBound c lam n)))
    {ε : ℝ} (hS : 1 - S.value ≤ ε) :
    ∃ R : M.ProjStrat (rawGame c hc he U source lam n), 1 - R.value ≤ detypingLoss * ε := by
  refine ⟨DeciderProgram.restrictAmbient graph (extendedSampler c hc he lam)
    (typedDecider c U (SourceDescriptionCompiler.clamp (source,lam)))
    (constantCutoff (outerBound c lam n))
    (TypeGraph.edges_nonempty QLD.adj (.pauli .X) (.pauli .Z) 7)
    (by decide) (typedDecider_total c U _) n S, ?_⟩
  have hr := DeciderProgram.restrictAmbient_failure_le graph (extendedSampler c hc he lam)
    (typedDecider c U (SourceDescriptionCompiler.clamp (source,lam)))
    (constantCutoff (outerBound c lam n))
    (TypeGraph.symmetric QLD.adj (.pauli .X) (.pauli .Z))
    (TypeGraph.edges_nonempty QLD.adj (.pauli .X) (.pauli .Z) 7)
    (by decide) (typedDecider_total c U _) n S
  exact hr.trans (mul_le_mul_of_nonneg_left hS detypingLoss_nonneg)

end MIPRE.Introspection.DecisionCompiler

end
