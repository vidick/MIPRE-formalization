/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.DecisionKernelAuxiliary

/-! # Kernel soundness in the finite semantic answer alphabet -/

noncomputable section
namespace MIPRE.Introspection.DecisionKernel
open Cost SAT AuxiliaryAnswer
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

def finiteSourcePredicate {n Q R : ℕ} (V : Verifier 7) (hs : V.sampler.dim (2 ^ n) ≤ Q)
    (x y : Fin Q → CL.𝔽₂) (a b : Verifier.Answers R) : Bool :=
  AuxiliaryDecision.sourcePredicate V hs x y a.val b.val

def finitePauliCheck (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k) (j : ℕ)
    (hm : 2 ^ j ∣ Fintype.card (shoupBinField k hk).carrier) (x y : BitStr)
    (T U : QLD.Ty) : QLD.Answer (shoupBinField k hk).carrier (2 ^ j) 1 →
      QLD.Answer (shoupBinField k hk).carrier (2 ^ j) 1 → Bool :=
  QLD.accepts hm (QLD.PauliBinaryProgram.questionOfBits k hk hodd j T x)
    (QLD.PauliBinaryProgram.questionOfBits k hk hodd j U y)

/-- Accepted raw tuples decode into the actual finite quotient game. Neither
the Pauli field answers nor the original source answers retain an infinite byte alphabet. -/
theorem program_sound (W : ClockedUniversalMachine) {lam n : ℕ}
    (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k) (j : ℕ) (hj : j ≤ k)
    (hm : 2 ^ j ∣ Fintype.card (shoupBinField k hk).carrier)
    (hs : V.sampler.dim (2 ^ n) ≤ 2 ^ (2 ^ j) * k)
    (hQ : 4 ≤ 2 ^ (2 ^ j) * k) (hR : 3 * ((2 ^ n)^lam) ≤ 2 ^ (2 ^ j) * k)
    (T U : Label) (x y a b : BitStr)
    (h : program W (canonicalInput V lam n (2 ^ (2 ^ j) * k) ((2 ^ n)^lam)
      (unary k,unary j,unary (2 ^ j)) T U x y a b) = true) :
    AuxiliaryQuotient.check (AuxiliaryDecision.padded V hs) (.pauli .X) (.pauli .Z)
      (Answer.pauliProject (shoupSelfDualNormalBasis k hk hodd))
      (finiteSourcePredicate (R := (2 ^ n)^lam) V hs) (finitePauliCheck k hk hodd j hm x y) T U
      (Answer.decode (shoupBinField k hk) (2 ^ j) (2 ^ (2 ^ j) * k) ((2 ^ n)^lam) T a)
      (Answer.decode (shoupBinField k hk) (2 ^ j) (2 ^ (2 ^ j) * k) ((2 ^ n)^lam) U b) = true := by
  let p : PauliSamplerParameters.Parameters := (unary k,unary j,unary (2 ^ j))
  let Q := 2 ^ (2 ^ j) * k
  let R := (2 ^ n)^lam
  change program W (canonicalInput V lam n Q R p T U x y a b) = true at h
  let a₀ := decode Q T a
  let b₀ := decode Q U b
  let a₁ := ParsedAnswer.mapAnswer (bounded R) a₀
  let b₁ := ParsedAnswer.mapAnswer (bounded R) b₀
  have hf := program_auxiliary_facts W V lam n Q R p T U x y a b h
  have ha : payloadBound R a₀ := payloadBound_decode R T a hf.1
  have hb : payloadBound R b₀ := payloadBound_decode R U b hf.2.1
  have hraw := program_raw_quotient_sound W V hV hn k hk hodd j hj hm hs hQ hR T U x y a b h
  have hfinite : AuxiliaryQuotient.check (AuxiliaryDecision.padded V hs) (.pauli .X) (.pauli .Z)
      (Answer.rawProject p Q) (finiteSourcePredicate (R := R) V hs)
      (rawPauliCheck k hk hodd j hm x y) T U a₁ b₁ = true := by
    apply AuxiliaryQuotient.check_mapAnswer (AuxiliaryDecision.padded V hs) (.pauli .X)
      (.pauli .Z) (Answer.rawProject p Q) (AuxiliaryDecision.sourcePredicate V hs)
      (finiteSourcePredicate (R := R) V hs) (bounded R)
      (rawPauliCheck k hk hodd j hm x y) T U a₀ b₀ _ _ hraw
    · intro z w c d hc hd hD
      have hc' : c.length ≤ R := by simpa only [hc, payloadBound] using ha
      have hd' : d.length ≤ R := by simpa only [hd, payloadBound] using hb
      simpa only [finiteSourcePredicate, bounded_val _ hc', bounded_val _ hd'] using hD
    · intro z w c d hc hd hD
      have hc' : c.length ≤ R := by simpa only [hc, payloadBound] using hb
      have hd' : d.length ≤ R := by simpa only [hd, payloadBound] using ha
      simpa only [finiteSourcePredicate, bounded_val _ hc', bounded_val _ hd'] using hD
  apply AuxiliaryQuotient.check_mapPauli (AuxiliaryDecision.padded V hs) (.pauli .X)
    (.pauli .Z) (Answer.rawProject p Q) (Answer.pauliProject (shoupSelfDualNormalBasis k hk hodd))
    (finiteSourcePredicate (R := R) V hs) (Answer.pauliDecode (shoupBinField k hk) (2 ^ j))
    (rawPauliCheck k hk hodd j hm x y) (finitePauliCheck k hk hodd j hm x y)
    T U a₁ b₁ _ _ _ hfinite
  · intro t c ht hT hc
    subst T
    have hac : a = c := ParsedAnswer.pauli.inj hc
    subst c
    have hv := program_leftPauli_valid W V lam n Q R p t U x y a b h
    rcases ht with rfl | rfl
    all_goals exact (Answer.rawProject_pauliDecode k hk hodd j (2 ^ j) _ a hv).symm
  · intro u c hu hU hc
    subst U
    have hbc : b = c := ParsedAnswer.pauli.inj hc
    subst c
    have hv := program_rightPauli_valid W V lam n Q R p T u x y a b h
    rcases hu with rfl | rfl
    all_goals exact (Answer.rawProject_pauliDecode k hk hodd j (2 ^ j) _ b hv).symm
  · intro t u c d _ _ _ _ hD
    exact hD

end MIPRE.Introspection.DecisionKernel
end
