/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.CanonicalGame
import MIPRE.Background.Introspection.AmbientRawGame
import MIPRE.Background.Introspection.DecisionKernelComplete
import MIPRE.Background.Introspection.DecisionKernelGameInterface
import MIPRE.Foundations.SyncMergeByQuestion

/-! # Completeness of the actual compiled introspection verifier

The finite honest PCC strategy supplies prefix, source-output, and Pauli-format
support. Encoding those outcomes preserves perfect play in the executable typed
game. Graph detyping and the zero-index wrapper finish the ambient contract.
-/

noncomputable section
namespace MIPRE.Introspection.CanonicalComplete
open Cost CL CanonicalGame SourceCompiler PauliSamplerParameters DecisionCompiler
open QLD.PauliCL.ExplicitSeed
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

abbrev Answer (c lam n : ℕ) :=
  ParsedAnswer (Fin (registerBits c lam n) → 𝔽₂) (Verifier.Answers ((2^n)^lam))
    (QLD.Answer (field c lam n).carrier (registerPower c lam n) 1)

def encodeAnswer (c : ℕ) (hc : 2 ≤ c) (lam n : ℕ) (a : Answer c lam n) :
    Verifier.Answers (outerBound c lam n) :=
  ⟨DecisionKernel.Answer.bits (field c lam n) a, by
    have hR := originalBound_three_le_registerBits hc lam n
    rw [originalBound_eq] at hR
    simpa only [outerBound,originalBound_eq,registerBits] using DecisionKernel.Answer.bits_length_le_cutoff
      (field c lam n) (registerPower_pos c lam n) (four_le_registerBits hc lam n) hR a⟩

theorem sourceOutput_of_support (c : ℕ) (hc : 1 ≤ c) (he : Even c) (lam n : ℕ) (V : Verifier 7)
    (hs : V.sampler.dim (2^n) ≤ registerBits c lam n)
    (S : SyncStrategy (guarded c hc he lam n V hs).doubled)
    (hi : ∀ side w payload y a,
      S.P.M (side,.inr (.introspect,w),payload) (.pair y a) ≠ 0 →
      ∃ x, (AuxiliaryDecision.padded V hs w).eval x = y)
    (q : Bool × CL.Detyping.Question DecisionKernel.Label (Fin (PauliSampler.dimension c lam n)))
    (a : Answer c lam n) (ha : S.P.M q a ≠ 0) :
    AuxiliaryDecision.sourceOutput (V.sampler.dim (2^n)) q.2.1
      (DecisionKernel.Answer.toRaw (field c lam n) a) := by
  rcases q with ⟨side,t,payload⟩
  rcases t with p | ⟨t,w⟩
  · cases a <;> trivial
  · cases t <;> cases a <;> try trivial
    exact AuxiliaryDecision.sourceOutput_of_attained V hs w _ (hi side w payload _ _ ha)

theorem pauliFormatted_of_support (c : ℕ) (hc : 1 ≤ c) (he : Even c) (lam n : ℕ)
    (V : Verifier 7) (hs : V.sampler.dim (2^n) ≤ registerBits c lam n)
    (S : SyncStrategy (guarded c hc he lam n V hs).doubled)
    (hp : ∀ side t payload a,
      S.P.M (side,.inl t,payload) (.pauli a) ≠ 0 →
      (binaryDecode (permutation c lam n) (basis c he lam n) t payload).fmtOk a = true)
    (q : Bool × CL.Detyping.Question DecisionKernel.Label (Fin (PauliSampler.dimension c lam n)))
    (a : Answer c lam n) (ha : S.P.M q a ≠ 0) :
    DecisionKernel.Answer.PauliFormatted (fieldBits c lam n) (fieldBits_pos c lam n)
      (fieldBits_odd he lam n) (selectorBits c lam n) _ _ q.2.1 (toBits q.2.2) a := by
  intro t b ht hb
  rcases q with ⟨side,label,payload⟩
  dsimp only at ht
  subst label
  subst a
  convert hp side t payload b ha using 1
  simp only [QLD.PauliBinaryProgram.questionOfBits, ofBits_toBits, binaryDecode,
    permutation, basis, field]
  rfl

theorem encoded_accepts (c : ℕ) (hc : 2 ≤ c) (he : Even c) (U : ClockedUniversalMachine)
    {lam n : ℕ} (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (hs : V.sampler.dim (2^n) ≤ registerBits c lam n)
    (q r : CL.Detyping.Question DecisionKernel.Label (Fin (PauliSampler.dimension c lam n)))
    (a b : Answer c lam n)
    (ha : DecisionKernel.Answer.PauliFormatted (fieldBits c lam n) (fieldBits_pos c lam n)
      (fieldBits_odd he lam n) (selectorBits c lam n) _ _ q.1 (toBits q.2) a)
    (hb : DecisionKernel.Answer.PauliFormatted (fieldBits c lam n) (fieldBits_pos c lam n)
      (fieldBits_odd he lam n) (selectorBits c lam n) _ _ r.1 (toBits r.2) b)
    (hga : PrefixGuard.holds (AuxiliaryDecision.padded V hs) q.1 a)
    (hgb : PrefixGuard.holds (AuxiliaryDecision.padded V hs) r.1 b)
    (hsa : AuxiliaryDecision.sourceOutput (V.sampler.dim (2^n)) q.1
      (DecisionKernel.Answer.toRaw (field c lam n) a))
    (hsb : AuxiliaryDecision.sourceOutput (V.sampler.dim (2^n)) r.1
      (DecisionKernel.Answer.toRaw (field c lam n) b))
    (h : (quotient c (by omega) he lam n V hs).D q r a b = true) :
    (rawGame c (by omega) he U (V.sampler.prog,V.decider.prog) lam n).D q r
      (encodeAnswer c hc lam n a) (encodeAnswer c hc lam n b) = true := by
  apply (raw_accepts_iff c (by omega) he U V hV q r _ _).mpr
  rw [originalBound_eq]
  have hR := originalBound_three_le_registerBits hc lam n
  rw [originalBound_eq] at hR
  exact DecisionKernel.program_complete_numbered U V hV hn (fieldBits c lam n)
    (fieldBits_pos c lam n) (fieldBits_odd he lam n) (selectorBits c lam n)
    (selectorBits_le_fieldBits (by omega) lam n) (divides c (by omega) lam n) hs
    (four_le_registerBits hc lam n) hR (selector c (by omega) lam n)
    q.1 r.1 q.2 r.2 a b ha hb hga hgb hsa hsb h

/-- The actual typed binary kernel has a perfect PCC strategy whenever the
source verifier does, using the finite honest strategy's support certificates. -/
theorem exists_raw_perfectPCC (c : ℕ) (hc : 2 ≤ c) (he : Even c) (U : ClockedUniversalMachine)
    {lam n : ℕ} (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (hv : V.HasPerfectPCC (2^n) ((2^n)^lam)) :
    ∃ R : SyncStrategy (rawGame c (by omega) he U (V.sampler.prog,V.decider.prog) lam n).doubled,
      R.IsPCC ∧ R.value = 1 := by
  classical
  let hc1 : 1 ≤ c := by omega
  let hs := VerifierSource.dimension_le_registerBits hc V hV hn
  obtain ⟨S,hS,hvS,hg,hi,hp⟩ := exists_perfectPCC c hc1 he lam n V hs hv
  let G := rawGame c hc1 he U (V.sampler.prog,V.decider.prog) lam n
  let f := fun (_ : Bool × CL.Detyping.Question DecisionKernel.Label
    (Fin (PauliSampler.dimension c lam n))) a => encodeAnswer c hc lam n a
  refine ⟨S.mergeAnswersByQuestion G.doubled f,?_,?_⟩
  · exact S.isPCC_mergeAnswersByQuestion G.doubled f (fun _ _ => rfl) hS
  · apply S.perfect_mergeAnswersByQuestion G.doubled f (fun _ _ => rfl) _ hvS
    intro q r a b _ ha hb hd
    have hfa := pauliFormatted_of_support c hc1 he lam n V hs S hp q a ha
    have hfb := pauliFormatted_of_support c hc1 he lam n V hs S hp r b hb
    have hsa := sourceOutput_of_support c hc1 he lam n V hs S hi q a ha
    have hsb := sourceOutput_of_support c hc1 he lam n V hs S hi r b hb
    rw [Game.doubled_D] at hd ⊢
    split_ifs at hd ⊢ with hside
    · have hacc := (PrefixGuard.game_accepts_iff (AuxiliaryDecision.padded V hs)
        Prod.fst (quotient c hc1 he lam n V hs) q.2 r.2 a b).mp hd
      exact encoded_accepts c hc he U V hV hn hs q.2 r.2 a b hfa hfb
        hacc.1 hacc.2.1 hsa hsb hacc.2.2

/-- Completeness for every source index, including the zero-index wrapper. -/
theorem output_hasPerfectPCC (c : ℕ) (hc : 2 ≤ c) (he : Even c) (U : ClockedUniversalMachine)
    (C : ℕ) (hcut : ∀ lam n, cutoffAt c lam n ≤ ansBound C lam n)
    (V : Verifier 7) (lam n : ℕ) (hV : V.IsBounded lam)
    (hv : V.HasPerfectPCC (2^n) ((2^n)^lam)) :
    (DecisionCompiler.output c (by omega) he U (V.sampler.prog,V.decider.prog) lam).HasPerfectPCC n
      (ansBound C lam n) := by
  by_cases hn : n = 0
  · exact hasPerfectPCC_zero c (by omega) he U _ lam n _ (Or.inr hn)
  have hl := hV.two_le
  have hn1 : 1 ≤ n := by omega
  obtain ⟨S,hS,hvS⟩ := exists_raw_perfectPCC c hc he U V hV hn1 hv
  apply output_hasPerfectPCC_of_raw c (by omega) he U _ (by omega) hn1 _ S hS hvS
  simpa only [cutoffAt, show ¬(lam = 0 ∨ n = 0) by omega, ↓reduceIte] using hcut lam n

end MIPRE.Introspection.CanonicalComplete
