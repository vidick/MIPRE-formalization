/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.DecisionKernelAnswers
import MIPRE.Foundations.Introspection.AuxiliaryDecisionSoundness

/-! # Raw auxiliary soundness of the complete decision kernel -/

noncomputable section
namespace MIPRE.Introspection.DecisionKernel
open Cost Cost.PolyTimeFun SAT AuxiliaryAnswer
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

private theorem format_iff_valid (z : AuxiliaryDecision.Input QLD.Ty 7) :
    AuxiliaryDecision.format z = true ↔
      Valid (AuxiliaryDecision.width z) (AuxiliaryDecision.originalBound z)
        (AuxiliaryDecision.leftType z) (AuxiliaryDecision.leftBits z) := by
  rw [AuxiliaryDecision.format_apply]
  rcases AuxiliaryDecision.leftType z with p | ⟨t,w⟩
  · simp only [AuxiliaryAnswer.Valid]
  · cases t <;> simp only [AuxiliaryAnswer.Valid, decide_eq_true_eq]

theorem program_auxiliary_facts (W : ClockedUniversalMachine) (V : Verifier 7)
    (lam n Q R : ℕ) (p : PauliSamplerParameters.Parameters) (T U : Label) (x y a b : BitStr)
    (h : program W (canonicalInput V lam n Q R p T U x y a b) = true) :
    Valid Q R T a ∧ Valid Q R U b ∧ (T = U → a = b) := by
  let z := canonicalInput V lam n Q R p T U x y a b
  have hh := ((program_iff W z).mp h).2.2.2.2.2
  simp only [auxiliary, comp_apply] at hh
  have hs := (AuxiliaryDecision.check_iff (P := QLD.Ty) W (.pauli .X) (.pauli .Z) project
    (auxiliaryInput W z)).mp
    (AuxiliaryDecision.check_of_guarded (P := QLD.Ty) W (.pauli .X) (.pauli .Z) project
      (auxiliaryInput W z) hh)
  have hl := (format_iff_valid (auxiliaryInput W z)).mp hs.1
  have hr := (format_iff_valid (AuxiliaryDecision.swap (auxiliaryInput W z))).mp hs.2.1
  have he := hs.2.2.1
  change Valid (registerWidth z) (originalCutoff z) (leftType z) (leftBits z) at hl
  change Valid (registerWidth z) (originalCutoff z) (rightType z) (rightBits z) at hr
  change leftType z = rightType z → leftBits z = rightBits z at he
  have hQ : registerWidth z = Q := rfl
  have hR : originalCutoff z = R := rfl
  rw [hQ,hR] at hl hr
  obtain ⟨hT,hU,ha,hb⟩ := canonicalInput_fields V lam n Q R p T U x y a b
  exact ⟨by simpa only [z,hT,ha] using hl, by simpa only [z,hU,hb] using hr,
    by simpa only [z,hT,hU,ha,hb] using he⟩

theorem program_auxiliary_check (W : ClockedUniversalMachine) {lam n : ℕ}
    (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n) (Q R : ℕ)
    (p : PauliSamplerParameters.Parameters) (T U : Label) (x y a b : BitStr)
    (hab : Q ≤ a.length + b.length)
    (h : program W (canonicalInput V lam n Q R p T U x y a b) = true) :
    AuxiliaryDecision.check W (.pauli .X) (.pauli .Z) project
      (AuxiliaryDecision.canonical V lam n Q R p T U a b) = true := by
  have hh := ((program_iff W (canonicalInput V lam n Q R p T U x y a b)).mp h).2.2.2.2.2
  simp only [auxiliary, comp_apply] at hh
  rw [auxiliaryInput_canonical W V hV hn Q R p T U x y a b hab] at hh
  exact ((AuxiliaryDecision.guarded_iff (P := QLD.Ty) W (.pauli .X) (.pauli .Z) project
    (AuxiliaryDecision.canonical V lam n Q R p T U a b)).mp hh).2.2

theorem project_rawProject_canonical (V : Verifier 7) (lam n R : ℕ)
    (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k) (j m : ℕ)
    (W : QLD.Bas) (U : Label) (a b : BitStr)
    (ha : (QLD.PauliAnswerProgram.parser (.pauli W,unary m,unary k,unary 1,a)).1 = true) :
    project (AuxiliaryDecision.canonical V lam n (2 ^ m * k) R
      (unary k,unary j,unary m) (.inl (.pauli W)) U a b) =
      CL.toBits (Answer.rawProject (unary k,unary j,unary m) (2 ^ m * k) a) := by
  rw [project_canonicalInput V lam n (2 ^ m * k) R a b k hk hodd j m W U ha,
    Answer.rawProject_pauliDecode k hk hodd j m W a ha]
  rfl

/-- The Pauli decision relation after the actual raw question and answer decoders. -/
def rawPauliCheck (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k) (j : ℕ)
    (hm : 2 ^ j ∣ Fintype.card (shoupBinField k hk).carrier) (x y : BitStr)
    (T U : QLD.Ty) (a b : BitStr) : Bool :=
  QLD.accepts hm (QLD.PauliBinaryProgram.questionOfBits k hk hodd j T x)
    (QLD.PauliBinaryProgram.questionOfBits k hk hodd j U y)
    (QLD.PauliAnswerProgram.decodeBits (shoupBinField k hk) (2 ^ j) 1 T a)
    (QLD.PauliAnswerProgram.decodeBits (shoupBinField k hk) (2 ^ j) 1 U b)

/-- All auxiliary checks are sound on every accepted raw tuple. The short
Pauli/Pauli case is handled without allocating an artificial full prefix. -/
theorem program_raw_quotient_sound (W : ClockedUniversalMachine) {lam n : ℕ}
    (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k) (j : ℕ) (hj : j ≤ k)
    (hm : 2 ^ j ∣ Fintype.card (shoupBinField k hk).carrier)
    (hs : V.sampler.dim (2 ^ n) ≤ 2 ^ (2 ^ j) * k)
    (hQ : 4 ≤ 2 ^ (2 ^ j) * k) (hR : 3 * ((2 ^ n)^lam) ≤ 2 ^ (2 ^ j) * k)
    (T U : Label) (x y a b : BitStr)
    (h : program W (canonicalInput V lam n (2 ^ (2 ^ j) * k) ((2 ^ n)^lam)
      (unary k,unary j,unary (2 ^ j)) T U x y a b) = true) :
    AuxiliaryQuotient.check (AuxiliaryDecision.padded V hs) (.pauli .X) (.pauli .Z)
      (Answer.rawProject (unary k,unary j,unary (2 ^ j)) (2 ^ (2 ^ j) * k))
      (AuxiliaryDecision.sourcePredicate V hs) (rawPauliCheck k hk hodd j hm x y) T U
      (decode (2 ^ (2 ^ j) * k) T a) (decode (2 ^ (2 ^ j) * k) U b) = true := by
  let p : PauliSamplerParameters.Parameters := (unary k,unary j,unary (2 ^ j))
  let Q := 2 ^ (2 ^ j) * k
  let R := (2 ^ n)^lam
  change program W (canonicalInput V lam n Q R p T U x y a b) = true at h
  have hf := program_auxiliary_facts W V lam n Q R p T U x y a b h
  have hlen := ((program_iff W _).mp h).2.1
  rw [questionLengths_canonicalInput] at hlen
  simp only [p,length_unary] at hlen
  have hDP : ∀ t u, T = .inl t → U = .inl u →
      rawPauliCheck k hk hodd j hm x y t u a b = true := by
    intro t u ht hu
    subst T U
    exact ((program_pauli_iff V lam n Q R x y a b W k hk hodd j hj hm t u
      hlen.1 hlen.2).mp h).2.2.1
  have hpa : ∀ t, (t = QLD.Ty.pauli .X ∨ t = .pauli .Z) → T = .inl t →
      project (AuxiliaryDecision.canonical V lam n Q R p T U a b) =
        CL.toBits (Answer.rawProject p Q a) := by
    intro t ht hT
    subst T
    have hv := program_leftPauli_valid W V lam n Q R p t U x y a b h
    rcases ht with rfl | rfl
    all_goals exact project_rawProject_canonical V lam n R k hk hodd j (2 ^ j) _ U a b hv
  have hpb : ∀ u, (u = QLD.Ty.pauli .X ∨ u = .pauli .Z) → U = .inl u →
      project (AuxiliaryDecision.canonical V lam n Q R p U T b a) =
        CL.toBits (Answer.rawProject p Q b) := by
    intro u hu hU
    subst U
    have hv := program_rightPauli_valid W V lam n Q R p T u x y a b h
    rcases hu with rfl | rfl
    all_goals exact project_rawProject_canonical V lam n R k hk hodd j (2 ^ j) _ T b a hv
  have hcap (hab : Q ≤ a.length + b.length) :
      AuxiliaryQuotient.check (AuxiliaryDecision.padded V hs) (.pauli .X) (.pauli .Z)
        (Answer.rawProject p Q) (AuxiliaryDecision.sourcePredicate V hs)
        (rawPauliCheck k hk hodd j hm x y) T U (decode Q T a) (decode Q U b) = true :=
    AuxiliaryDecision.check_raw_sound (P := QLD.Ty) W (.pauli .X) (.pauli .Z) project V hV hn hs hQ hR
      (Answer.rawProject p Q) (rawPauliCheck k hk hodd j hm x y) T U a b hpa hpb hDP
      (program_auxiliary_check W V hV hn Q R p T U x y a b hab h)
  rcases T with t | ⟨t,w⟩
  · rcases U with u | ⟨u,v⟩
    · have hd := hDP t u rfl rfl
      simp only [AuxiliaryAnswer.decode, AuxiliaryQuotient.check, TypedPredicate.fits,
        AuxiliaryQuotient.directed, Bool.and_true, Bool.true_and]
      by_cases htu : t = u
      · subst u
        have hab := hf.2.2 rfl
        subst b
        simpa using hd
      · simp [htu, hd]
    · exact hcap (by have := valid_aux_length R u v b hf.2.1; omega)
  · exact hcap (by have := valid_aux_length R t w a hf.1; omega)

end MIPRE.Introspection.DecisionKernel
end
