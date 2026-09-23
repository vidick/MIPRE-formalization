/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.DecisionKernelGameInterface
import MIPRE.Background.Introspection.CanonicalGame
import MIPRE.Background.Introspection.AmbientRawGame

/-! # Decoding the actual compiled strategy into the canonical finite game -/

noncomputable section
namespace MIPRE.Introspection.CanonicalDecoded
open CL Cost SourceCompiler PauliSamplerParameters DecisionCompiler Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

abbrev Question (c lam n : ℕ) :=
  CL.Detyping.Question DecisionKernel.Label (Fin (PauliSampler.dimension c lam n))

/-- Decode each bounded binary answer according to its own question type. -/
def decode (c lam n : ℕ) (q : Question c lam n)
    (a : Verifier.Answers (outerBound c lam n)) :=
  DecisionKernel.Answer.decode (CanonicalGame.field c lam n) (registerPower c lam n)
    (registerBits c lam n) ((2^n)^lam) q.1 a.val

abbrev strategy (c : ℕ) (hc : 1 ≤ c) (he : Even c) (U : ClockedUniversalMachine)
    (lam n : ℕ) (V : Verifier 7) (hs : V.sampler.dim (2^n) ≤ registerBits c lam n)
    (S : TensorProductStrategy (rawGame c hc he U (V.sampler.prog,V.decider.prog) lam n)) :=
  S.mergeAnswersByQuestion (CanonicalGame.quotient c hc he lam n V hs)
    (decode c lam n) (decode c lam n)

/-- Kernel acceptance is preserved by this total, finite answer decoding. -/
theorem accepts (c : ℕ) (hc : 1 ≤ c) (he : Even c) (U : ClockedUniversalMachine)
    {lam n : ℕ} (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (hc2 : 2 ≤ c) (hs : V.sampler.dim (2^n) ≤ registerBits c lam n)
    (q r : Question c lam n) (a b : Verifier.Answers (outerBound c lam n))
    (h : (rawGame c hc he U (V.sampler.prog,V.decider.prog) lam n).D q r a b = true) :
    (CanonicalGame.quotient c hc he lam n V hs).D q r
      (decode c lam n q a) (decode c lam n r b) = true := by
  have hh := (raw_accepts_iff c hc he U V hV q r a b).mp h
  rw [originalBound_eq] at hh
  have hR := originalBound_three_le_registerBits hc2 lam n
  rw [originalBound_eq] at hR
  exact DecisionKernel.program_sound_numbered U V hV hn (fieldBits c lam n)
    (fieldBits_pos c lam n) (fieldBits_odd he lam n) (selectorBits c lam n)
    (selectorBits_le_fieldBits hc lam n) (CanonicalGame.divides c hc lam n) hs
    (four_le_registerBits hc2 lam n) hR (CanonicalGame.selector c hc lam n)
    q.1 r.1 q.2 r.2 a.val b.val hh

/-- Decoding preserves the question law and cannot lower the strategy value. -/
theorem value_le (c : ℕ) (hc : 1 ≤ c) (he : Even c) (U : ClockedUniversalMachine)
    {lam n : ℕ} (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (hc2 : 2 ≤ c) (hs : V.sampler.dim (2^n) ≤ registerBits c lam n)
    (S : TensorProductStrategy (rawGame c hc he U (V.sampler.prog,V.decider.prog) lam n)) :
    S.value ≤ (strategy c hc he U lam n V hs S).value := by
  apply S.value_le_mergeAnswersByQuestion
    (CanonicalGame.quotient c hc he lam n V hs) (decode c lam n) (decode c lam n)
  · intro q r
    rfl
  · exact accepts c hc he U V hV hn hc2 hs

theorem failure_le (c : ℕ) (hc : 1 ≤ c) (he : Even c) (U : ClockedUniversalMachine)
    {lam n : ℕ} (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (hc2 : 2 ≤ c) (hs : V.sampler.dim (2^n) ≤ registerBits c lam n)
    (S : TensorProductStrategy (rawGame c hc he U (V.sampler.prog,V.decider.prog) lam n))
    {ε : ℝ} (hS : 1-S.value ≤ ε) :
    1-(strategy c hc he U lam n V hs S).value ≤ ε :=
  (sub_le_sub_left (value_le c hc he U V hV hn hc2 hs S) 1).trans hS

private theorem measurement_supported (c lam n : ℕ) {H : Type*}
    [Fintype H] [DecidableEq H]
    (P : ProjectiveMeasurement (Question c lam n) (Verifier.Answers (outerBound c lam n))
      (Matrix H H ℂ)) :
    ∀ W a, (P.mergeByQuestion (decode c lam n)).M (.inl (.pauli W),0) a ≠ 0 →
      ∃ x, a = .pauli (.pauliAns x) := by
  intro W a ha
  by_contra hn
  apply ha
  rw [ProjectiveMeasurement.mergeByQuestion_M]
  apply Finset.sum_eq_zero
  intro b hb
  have heq := (Finset.mem_filter.mp hb).2
  exact (hn ⟨_,heq.symm⟩).elim

/-- Full Pauli effects are supported on genuine full Pauli outcomes for Alice. -/
theorem supported_A (c : ℕ) (hc : 1 ≤ c) (he : Even c) (U : ClockedUniversalMachine)
    (lam n : ℕ) (V : Verifier 7) (hs : V.sampler.dim (2^n) ≤ registerBits c lam n)
    (S : TensorProductStrategy (rawGame c hc he U (V.sampler.prog,V.decider.prog) lam n)) :
    ∀ W a, (strategy c hc he U lam n V hs S).PA.M (.inl (.pauli W),0) a ≠ 0 →
      ∃ x, a = .pauli (.pauliAns x) :=
  measurement_supported c lam n S.PA

/-- Full Pauli effects are supported on genuine full Pauli outcomes for Bob. -/
theorem supported_B (c : ℕ) (hc : 1 ≤ c) (he : Even c) (U : ClockedUniversalMachine)
    (lam n : ℕ) (V : Verifier 7) (hs : V.sampler.dim (2^n) ≤ registerBits c lam n)
    (S : TensorProductStrategy (rawGame c hc he U (V.sampler.prog,V.decider.prog) lam n)) :
    ∀ W a, (strategy c hc he U lam n V hs S).PB.M (.inl (.pauli W),0) a ≠ 0 →
      ∃ x, a = .pauli (.pauliAns x) :=
  measurement_supported c lam n S.PB

end MIPRE.Introspection.CanonicalDecoded
