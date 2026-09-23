/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.DecisionCompilerVerifier
import MIPRE.Foundations.CL.DetypingDeciderTransport
import MIPRE.Foundations.VerifierIndexTransport
import MIPRE.Foundations.Halting.Classes

/-! # The compiled verifier and its finite detyping game

The compiler shares its resource preparation between the graph router and the
typed decision kernel. Its acceptance agrees with the generic detyping compiler
at each positive index. The sampler wrapper preserves the CL presentations there.
-/

noncomputable section
namespace MIPRE.Introspection.DecisionCompiler
open Cost CL CL.Detyping CL.Detyping.Program
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

/-- A reference cutoff can be constant because comparison is at one index. -/
def constantCutoff (B : ℕ) : CutoffProgram where
  inner _ := B
  outer _ := B
  prog := Prog.const (encode (B,B))
  closed := trivial
  runs _ := ⟨_,Cost.Eval.const _ _⟩

def extendedSampler (c : ℕ) (hc : 1 ≤ c) (he : Even c) (lam : ℕ) :=
  Introspection.typedSampler 7 (PauliSampler.sampler c hc he lam)

/-- The generic detyping verifier with the same positive-index predicate. -/
def reference (c : ℕ) (hc : 1 ≤ c) (he : Even c) (U : ClockedUniversalMachine)
    (source : Prog × Prog) (lam n : ℕ) : Verifier 5 :=
  DeciderProgram.verifier graph (extendedSampler c hc he lam)
    (typedDecider c U (SourceDescriptionCompiler.clamp (source,lam)))
    (constantCutoff (answerBound (SourceCompiler.registerBits c lam n)
      (SourceCompiler.originalBound lam n))) (by decide) (typedDecider_total c U _)

theorem kernelInput_cons (c : ℕ) (M : DecisionPreparation.Metadata) (n : ℕ) (d : Data) :
    DecisionPreparation.kernelInput c M (.cons (encode n) d) =
      (.cons (encode n) d,M,unary (ansBound 5 M.2 n),2^n,
        PauliSamplerParameters.parameters c M.2 n,
        SourceCompiler.registerBits c M.2 n,SourceCompiler.originalBound M.2 n) := by
  simp only [DecisionPreparation.kernelInput]
  rw [show ClockSimulation.indexReader (.cons (encode n) d) = n from readNat_encode n]

set_option maxHeartbeats 600000 in
/-- Sharing preparation changes no positive-index acceptance decision. -/
theorem accepts_reference (c : ℕ) (hc : 1 ≤ c) (he : Even c) (U : ClockedUniversalMachine)
    (source : Prog × Prog) {lam n : ℕ} (hl : 1 ≤ lam) (hn : 1 ≤ n)
    (x y a b : BitStr) :
    (output c hc he U source lam).decider.Accepts n x y a b ↔
      (reference c hc he U source lam n).decider.Accepts n x y a b := by
  change (decider c U source.1 source.2 lam).Accepts n x y a b ↔ _
  rw [accepts_positive c U source.1 source.2 hl hn]
  have hi : ClockSimulation.indexReader (encode (n,x,y,a,b)) = n := readNat_encode n
  dsimp only [DecisionPreparation.kernelInput]
  have hM : (SourceDescriptionCompiler.clamp (source,lam)).2 = lam := rfl
  rw [hi,hM,untypedKernel_iff]
  change _ ↔ (DeciderProgram.decider graph (extendedSampler c hc he lam)
    (typedDecider c U (SourceDescriptionCompiler.clamp (source,lam)))
    (constantCutoff (answerBound (SourceCompiler.registerBits c lam n)
      (SourceCompiler.originalBound lam n)))).Accepts n x y a b
  rw [DeciderProgram.accepts_iff _ _ _ _ (typedDecider_total c U _)]
  simp only [PauliSamplerParameters.parameters, length_unary]
  change (_ ∧ _ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _ ∧ _ ∧ _)
  constructor
  · rintro ⟨hx,hy,ha,hb,h⟩
    refine ⟨hx,hy,ha,hb,?_⟩
    cases hedge : DeciderProgram.selectedEdge graph (graphOfBits x) (graphOfBits y) with
    | none => trivial
    | some uv =>
      simp only [hedge] at h ⊢
      refine ⟨ha,hb,?_⟩
      rw [typedDecider_accepts]
      dsimp only [DecisionPreparation.kernelInput]
      rw [show ClockSimulation.indexReader (encode (n,uv.1,x.drop (graphDim DecisionKernel.Label),
        uv.2,y.drop (graphDim DecisionKernel.Label),a,b)) = n from readNat_encode n,hM]
      exact h
  · rintro ⟨hx,hy,ha,hb,h⟩
    refine ⟨hx,hy,ha,hb,?_⟩
    cases hedge : DeciderProgram.selectedEdge graph (graphOfBits x) (graphOfBits y) with
    | none => trivial
    | some uv =>
      simp only [hedge] at h ⊢
      rcases h with ⟨_,_,hh⟩
      rw [typedDecider_accepts] at hh
      dsimp only [DecisionPreparation.kernelInput] at hh
      rw [show ClockSimulation.indexReader (encode (n,uv.1,x.drop (graphDim DecisionKernel.Label),
        uv.2,y.drop (graphDim DecisionKernel.Label),a,b)) = n from readNat_encode n,hM] at hh
      exact hh

theorem samplerAgreement_reference (c : ℕ) (hc : 1 ≤ c) (he : Even c)
    (U : ClockedUniversalMachine) (source : Prog × Prog) {lam n : ℕ}
    (hl : 1 ≤ lam) (hn : 1 ≤ n) :
    Verifier.SamplerAgreement (output c hc he U source lam) (reference c hc he U source lam n) n := by
  refine ⟨?_,fun w => ?_⟩
  · exact PauliSampler.finalSampler_dim_pos c hc he 7 lam n (by omega) (by omega)
  · exact PauliSampler.finalSampler_cl_pos c hc he 7 lam n (by omega) (by omega) w

theorem valStar_reference (c : ℕ) (hc : 1 ≤ c) (he : Even c)
    (U : ClockedUniversalMachine) (source : Prog × Prog) {lam n : ℕ}
    (hl : 1 ≤ lam) (hn : 1 ≤ n) (B : ℕ) :
    (output c hc he U source lam).valStar n B = (reference c hc he U source lam n).valStar n B :=
  Verifier.valStar_congr_at (samplerAgreement_reference c hc he U source hl hn)
    (accepts_reference c hc he U source hl hn)

theorem hasPerfectPCC_reference (c : ℕ) (hc : 1 ≤ c) (he : Even c)
    (U : ClockedUniversalMachine) (source : Prog × Prog) {lam n : ℕ}
    (hl : 1 ≤ lam) (hn : 1 ≤ n) (B : ℕ) :
    (output c hc he U source lam).HasPerfectPCC n B ↔
      (reference c hc he U source lam n).HasPerfectPCC n B :=
  Verifier.hasPerfectPCC_congr_at (samplerAgreement_reference c hc he U source hl hn)
    (accepts_reference c hc he U source hl hn)

/-- Empty questions admit the constant empty-answer PCC strategy. -/
theorem hasPerfectPCC_zero (c : ℕ) (hc : 1 ≤ c) (he : Even c)
    (U : ClockedUniversalMachine) (source : Prog × Prog) (lam n B : ℕ)
    (hz : lam = 0 ∨ n = 0) : (output c hc he U source lam).HasPerfectPCC n B := by
  apply Verifier.hasPerfectPCC_of_accepts_diagonal _ ⟨[],Nat.zero_le B⟩
  intro x y
  apply (accepts_zero c U source.1 source.2 lam n hz _ _ [] []).mpr
  have hd : (output c hc he U source lam).sampler.dim n = 0 :=
    PauliSampler.finalSampler_dim_zero c hc he 7 lam n (by rcases hz with h | h <;> simp [h])
  have hx : (toBits x).length = 0 := (length_toBits x).trans hd
  have hy : (toBits y).length = 0 := (length_toBits y).trans hd
  exact ⟨List.length_eq_zero_iff.mp hx,List.length_eq_zero_iff.mp hy,by simp,by simp⟩

end MIPRE.Introspection.DecisionCompiler
