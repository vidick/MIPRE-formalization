/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.AmbientVerifierTransport
import MIPRE.Background.Introspection.DecisionKernelCanonical

/-! # Restricting the output verifier to its actual typed kernel

The outer answer alphabet is first reduced to the enforced binary cutoff.
Finite graph detyping then gives the same-state typed strategy with its fixed
loss factor, and carries perfect PCC completeness in the other direction.
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

theorem output_valStar_cutoff (c : ℕ) (hc : 1 ≤ c) (he : Even c) (U : ClockedUniversalMachine)
    (source : Prog × Prog) {lam n B : ℕ} (hl : 1 ≤ lam) (hn : 1 ≤ n)
    (hB : outerBound c lam n ≤ B) :
    (output c hc he U source lam).valStar n B =
      (output c hc he U source lam).valStar n (outerBound c lam n) := by
  apply Verifier.valStar_eq_of_rejects _ hB
  intro x y a b hlong hacc
  have hh := (accepts_positive_bounds c U source.1 source.2 hl hn x y a b hacc).2.2
  change a.length ≤ outerBound c lam n ∧ b.length ≤ outerBound c lam n at hh
  rcases hlong with hlong | hlong <;> omega

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

/-- An ambient value above `1-ε` supplies a typed raw strategy with the
detyping loss. The input answer bound can be any larger global budget. -/
theorem exists_raw_failure_le (c : ℕ) (hc : 1 ≤ c) (he : Even c)
    (U : ClockedUniversalMachine) (source : Prog × Prog) {lam n B : ℕ}
    (hl : 1 ≤ lam) (hn : 1 ≤ n) (hB : outerBound c lam n ≤ B)
    (ε : ℝ) (hv : 1-ε < (output c hc he U source lam).valStar n B) :
    ∃ S : TensorProductStrategy (rawGame c hc he U source lam n),
      1-S.value ≤ detypingLoss*ε := by
  rw [output_valStar_cutoff c hc he U source hl hn hB,
    valStar_reference c hc he U source hl hn] at hv
  let G := (reference c hc he U source lam n).game n (outerBound c lam n)
  let : Nonempty (TensorProductStrategy G) :=
    ⟨(SyncStrategy.const G.doubled ⟨[],by simp⟩).toTensorProductStrategy.undouble⟩
  obtain ⟨S,hS⟩ := (lt_ciSup_iff (TensorProductStrategy.bddAbove_range_value
    ((reference c hc he U source lam n).game n (outerBound c lam n)))).mp hv
  let R := DeciderProgram.restrictAmbient graph (extendedSampler c hc he lam)
    (typedDecider c U (SourceDescriptionCompiler.clamp (source,lam)))
    (constantCutoff (outerBound c lam n))
    (TypeGraph.edges_nonempty QLD.adj (.pauli .X) (.pauli .Z) 7)
    (by decide) (typedDecider_total c U _) n S
  refine ⟨R,?_⟩
  have hr := DeciderProgram.restrictAmbient_failure_le graph (extendedSampler c hc he lam)
    (typedDecider c U (SourceDescriptionCompiler.clamp (source,lam)))
    (constantCutoff (outerBound c lam n))
    (TypeGraph.symmetric QLD.adj (.pauli .X) (.pauli .Z))
    (TypeGraph.edges_nonempty QLD.adj (.pauli .X) (.pauli .Z) 7)
    (by decide) (typedDecider_total c U _) n S
  exact hr.trans (mul_le_mul_of_nonneg_left (by linarith) detypingLoss_nonneg)

end MIPRE.Introspection.DecisionCompiler
