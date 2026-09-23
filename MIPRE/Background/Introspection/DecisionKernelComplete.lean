/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.DecisionKernelEncoding
import MIPRE.Background.Introspection.DecisionKernelGameInterface

/-! # Honest completeness of the actual decision kernel -/

noncomputable section
namespace MIPRE.Introspection.DecisionKernel
open Cost Cost.PolyTimeFun SAT
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

private theorem mapAnswer_pauli {V A B PA : Type*} (f : A → B)
    (a : ParsedAnswer V A PA) (c : PA) :
    ParsedAnswer.mapAnswer f a = .pauli c ↔ a = .pauli c := by
  cases a <;> simp [ParsedAnswer.mapAnswer]

private theorem toRaw_pauli_inv {k m Q R : ℕ} (E : BinField k)
    (a : ParsedAnswer (Fin Q → CL.𝔽₂) (Verifier.Answers R) (QLD.Answer E.carrier m 1))
    (c : BitStr) (h : Answer.toRaw E a = .pauli c) :
    ∃ d, a = .pauli d ∧ c = QLD.PauliAnswerProgram.answerBits E d := by
  cases a <;> cases h
  exact ⟨_,rfl,rfl⟩

/-- Encoding bounded source answers and legal Pauli answers preserves every
accepted semantic quotient comparison. -/
theorem encoded_quotient {lam n : ℕ} (V : Verifier 7)
    (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k) (j : ℕ)
    (hm : 2^j ∣ Fintype.card (shoupBinField k hk).carrier)
    (hs : V.sampler.dim (2^n) ≤ 2^(2^j)*k)
    (T U : Label) (x y : BitStr)
    (a b : ParsedAnswer (Fin (2^(2^j)*k) → CL.𝔽₂) (Verifier.Answers ((2^n)^lam))
      (QLD.Answer (shoupBinField k hk).carrier (2^j) 1))
    (ha : Answer.PauliFormatted k hk hodd j _ _ T x a)
    (hb : Answer.PauliFormatted k hk hodd j _ _ U y b)
    (h : AuxiliaryQuotient.check (AuxiliaryDecision.padded V hs) (.pauli .X) (.pauli .Z)
      (Answer.pauliProject (shoupSelfDualNormalBasis k hk hodd))
      (finiteSourcePredicate V hs) (finitePauliCheck k hk hodd j hm x y) T U a b = true) :
    AuxiliaryQuotient.check (AuxiliaryDecision.padded V hs) (.pauli .X) (.pauli .Z)
      (Answer.rawProject (unary k,unary j,unary (2^j)) (2^(2^j)*k))
      (AuxiliaryDecision.sourcePredicate V hs) (rawPauliCheck k hk hodd j hm x y) T U
      (Answer.toRaw (shoupBinField k hk) a) (Answer.toRaw (shoupBinField k hk) b) = true := by
  let E := shoupBinField k hk
  let a₁ := ParsedAnswer.mapAnswer Subtype.val a
  let b₁ := ParsedAnswer.mapAnswer Subtype.val b
  have h₁ : AuxiliaryQuotient.check (AuxiliaryDecision.padded V hs) (.pauli .X) (.pauli .Z)
      (Answer.pauliProject (shoupSelfDualNormalBasis k hk hodd))
      (AuxiliaryDecision.sourcePredicate V hs) (finitePauliCheck k hk hodd j hm x y)
      T U a₁ b₁ = true := by
    exact AuxiliaryQuotient.check_mapAnswer (AuxiliaryDecision.padded V hs) (.pauli .X)
      (.pauli .Z) (Answer.pauliProject (shoupSelfDualNormalBasis k hk hodd))
      (finiteSourcePredicate V hs) (AuxiliaryDecision.sourcePredicate V hs) Subtype.val
      (finitePauliCheck k hk hodd j hm x y) T U a b
      (fun _ _ _ _ _ _ hd => hd) (fun _ _ _ _ _ _ hd => hd) h
  rw [Answer.toRaw_eq_map E T, Answer.toRaw_eq_map E U]
  apply AuxiliaryQuotient.check_mapPauli (AuxiliaryDecision.padded V hs) (.pauli .X)
    (.pauli .Z) (Answer.pauliProject (shoupSelfDualNormalBasis k hk hodd))
    (Answer.rawProject (unary k,unary j,unary (2^j)) (2^(2^j)*k))
    (AuxiliaryDecision.sourcePredicate V hs) (fun _ => QLD.PauliAnswerProgram.answerBits E)
    (finitePauliCheck k hk hodd j hm x y) (rawPauliCheck k hk hodd j hm x y)
    T U a₁ b₁ _ _ _ h₁
  · intro p c hp ht hc
    have hf := ha p c ht ((mapAnswer_pauli Subtype.val a c).mp hc)
    rcases hp with rfl | rfl
    all_goals exact (Answer.rawProject_answerBits k hk hodd j (2^j) _ _ c
      (Answer.questionOfBits_ty k hk hodd j _ x) hf)
  · intro p c hp hu hc
    have hf := hb p c hu ((mapAnswer_pauli Subtype.val b c).mp hc)
    rcases hp with rfl | rfl
    all_goals exact (Answer.rawProject_answerBits k hk hodd j (2^j) _ _ c
      (Answer.questionOfBits_ty k hk hodd j _ y) hf)
  · intro p q c d ht hu hc hd hD
    have hfc := ha p c ht ((mapAnswer_pauli Subtype.val a c).mp hc)
    have hfd := hb q d hu ((mapAnswer_pauli Subtype.val b d).mp hd)
    have hec := QLD.PauliAnswerProgram.decodeBits_answerBits E hk
      (QLD.PauliBinaryProgram.questionOfBits k hk hodd j p x) c hfc
    have hed := QLD.PauliAnswerProgram.decodeBits_answerBits E hk
      (QLD.PauliBinaryProgram.questionOfBits k hk hodd j q y) d hfd
    rw [Answer.questionOfBits_ty] at hec hed
    dsimp only [E] at hec hed
    simpa only [rawPauliCheck, E, hec, hed, finitePauliCheck] using hD

private theorem guarded_pauli (W : ClockedUniversalMachine)
    (ctx : AuxiliarySource.Context) (bounds : AuxiliaryDecision.Bounds)
    (t u : QLD.Ty) (a b : BitStr) (h : t = u → a = b) :
    AuxiliaryDecision.guarded W (.pauli .X) (.pauli .Z) project
      ((ctx,bounds),(.inl t,a),(.inl u,b)) = true := by
  apply (AuxiliaryDecision.guarded_iff W (.pauli .X) (.pauli .Z) project _).mpr
  refine ⟨?_,?_,?_⟩
  · exact AuxiliaryPrefixGuard.program_pauli W ctx bounds.1.1 t a
  · exact AuxiliaryPrefixGuard.program_pauli W ctx bounds.1.1 u b
  · apply (AuxiliaryDecision.check_iff W (.pauli .X) (.pauli .Z) project _).mpr
    refine ⟨?_,?_,?_,?_,?_⟩
    · rw [AuxiliaryDecision.format_apply]; rfl
    · rw [AuxiliaryDecision.format_apply]; rfl
    · intro he
      exact h (Sum.inl.inj he)
    · rw [AuxiliaryDecision.directed_apply]
      rfl
    · rw [AuxiliaryDecision.directed_apply]
      rfl

/-- The auxiliary part needs a full zero prefix only when one endpoint has
an auxiliary answer; Pauli-only pairs reduce to their byte consistency check. -/
theorem auxiliary_encoded_complete (W : ClockedUniversalMachine) {lam n : ℕ}
    (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k) (j : ℕ)
    (hm : 2^j ∣ Fintype.card (shoupBinField k hk).carrier)
    (hs : V.sampler.dim (2^n) ≤ 2^(2^j)*k)
    (hQ : 4 ≤ 2^(2^j)*k) (hR : 3*((2^n)^lam) ≤ 2^(2^j)*k)
    (T U : Label) (x y : BitStr)
    (a b : ParsedAnswer (Fin (2^(2^j)*k) → CL.𝔽₂) (Verifier.Answers ((2^n)^lam))
      (QLD.Answer (shoupBinField k hk).carrier (2^j) 1))
    (ha : Answer.PauliFormatted k hk hodd j _ _ T x a)
    (hb : Answer.PauliFormatted k hk hodd j _ _ U y b)
    (hga : PrefixGuard.holds (AuxiliaryDecision.padded V hs) T a)
    (hgb : PrefixGuard.holds (AuxiliaryDecision.padded V hs) U b)
    (hsa : AuxiliaryDecision.sourceOutput (V.sampler.dim (2^n)) T (Answer.toRaw (shoupBinField k hk) a))
    (hsb : AuxiliaryDecision.sourceOutput (V.sampler.dim (2^n)) U (Answer.toRaw (shoupBinField k hk) b))
    (h : AuxiliaryQuotient.check (AuxiliaryDecision.padded V hs) (.pauli .X) (.pauli .Z)
      (Answer.pauliProject (shoupSelfDualNormalBasis k hk hodd))
      (finiteSourcePredicate V hs) (finitePauliCheck k hk hodd j hm x y) T U a b = true) :
    auxiliary W (canonicalInput V lam n (2^(2^j)*k) ((2^n)^lam)
      (unary k,unary j,unary (2^j)) T U x y
      (Answer.bits (shoupBinField k hk) a) (Answer.bits (shoupBinField k hk) b)) = true := by
  let E := shoupBinField k hk
  let p : PauliSamplerParameters.Parameters := (unary k,unary j,unary (2^j))
  let Q := 2^(2^j)*k
  let R := (2^n)^lam
  let a₀ := Answer.toRaw E a
  let b₀ := Answer.toRaw E b
  have he := encoded_quotient V k hk hodd j hm hs T U x y a b ha hb h
  have hf := he
  simp only [AuxiliaryQuotient.check, Bool.and_eq_true] at hf
  have hfa := hf.1.1.1.1.1
  have hfb := hf.1.1.1.1.2
  have hcap (hab : Q ≤ (Answer.bits E a).length + (Answer.bits E b).length) :
      auxiliary W (canonicalInput V lam n Q R p T U x y (Answer.bits E a) (Answer.bits E b)) = true := by
    simp only [auxiliary, comp_apply]
    rw [auxiliaryInput_canonical W V hV hn Q R p T U x y _ _ hab]
    apply AuxiliaryDecision.guarded_complete W (.pauli .X) (.pauli .Z) project
      V hV hn hs hQ hR (Answer.rawProject p Q) (rawPauliCheck k hk hodd j hm x y)
      T U a₀ b₀ (Answer.answerBound_toRaw E a) (Answer.answerBound_toRaw E b)
      ((Answer.prefixGuard_toRaw E _ T a).mpr hga)
      ((Answer.prefixGuard_toRaw E _ U b).mpr hgb) hsa hsb _ _ he
    · intro t c ht hT hac
      have horig := toRaw_pauli_inv E a c hac
      obtain ⟨d,had,rfl⟩ := horig
      have hfmt := ha t d hT had
      subst a
      have hv := Answer.parser_answerBits E hk _ d hfmt
      rw [Answer.questionOfBits_ty] at hv
      subst T
      rcases ht with rfl | rfl
      all_goals exact project_rawProject_canonical V lam n R k hk hodd j (2^j) _ U _ _ hv
    · intro t c ht hU hbc
      have horig := toRaw_pauli_inv E b c hbc
      obtain ⟨d,hbd,rfl⟩ := horig
      have hfmt := hb t d hU hbd
      subst b
      have hv := Answer.parser_answerBits E hk _ d hfmt
      rw [Answer.questionOfBits_ty] at hv
      subst U
      rcases ht with rfl | rfl
      all_goals exact project_rawProject_canonical V lam n R k hk hodd j (2^j) _ T _ _ hv
  rcases T with t | ⟨t,w⟩
  · rcases U with u | ⟨u,v⟩
    · simp only [auxiliary, comp_apply, auxiliaryInput_apply]
      obtain ⟨ht,hu,ha',hb'⟩ := canonicalInput_fields V lam n Q R p (.inl t) (.inl u)
        x y (Answer.bits E a) (Answer.bits E b)
      rw [ht,hu,ha',hb']
      apply guarded_pauli
      intro htu
      subst u
      have hab := hf.1.1.1.2
      simp only [↓reduceIte, decide_eq_true_eq] at hab
      exact congrArg AuxiliaryAnswer.bits hab
    · apply hcap
      have hv := AuxiliaryDecision.valid_bits (.inr (u,v)) b₀ hfb (Answer.answerBound_toRaw E b)
      have hl := AuxiliaryAnswer.valid_aux_length R u v (Answer.bits E b) hv
      omega
  · apply hcap
    have hv := AuxiliaryDecision.valid_bits (.inr (t,w)) a₀ hfa (Answer.answerBound_toRaw E a)
    have hl := AuxiliaryAnswer.valid_aux_length R t w (Answer.bits E a) hv
    omega

/-- The complete executable kernel accepts the honest finite encodings.
All hypotheses concern the semantic game or the honest outcome support. -/
theorem program_complete (W : ClockedUniversalMachine) {lam n : ℕ}
    (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k) (j : ℕ) (hj : j ≤ k)
    (hm : 2^j ∣ Fintype.card (shoupBinField k hk).carrier)
    (hs : V.sampler.dim (2^n) ≤ 2^(2^j)*k)
    (hQ : 4 ≤ 2^(2^j)*k) (hR : 3*((2^n)^lam) ≤ 2^(2^j)*k)
    (T U : Label) (x y : BitStr)
    (hx : x.length = (3*2^j+3)*k) (hy : y.length = (3*2^j+3)*k)
    (a b : ParsedAnswer (Fin (2^(2^j)*k) → CL.𝔽₂) (Verifier.Answers ((2^n)^lam))
      (QLD.Answer (shoupBinField k hk).carrier (2^j) 1))
    (ha : Answer.PauliFormatted k hk hodd j _ _ T x a)
    (hb : Answer.PauliFormatted k hk hodd j _ _ U y b)
    (hga : PrefixGuard.holds (AuxiliaryDecision.padded V hs) T a)
    (hgb : PrefixGuard.holds (AuxiliaryDecision.padded V hs) U b)
    (hsa : AuxiliaryDecision.sourceOutput (V.sampler.dim (2^n)) T (Answer.toRaw (shoupBinField k hk) a))
    (hsb : AuxiliaryDecision.sourceOutput (V.sampler.dim (2^n)) U (Answer.toRaw (shoupBinField k hk) b))
    (h : AuxiliaryQuotient.check (AuxiliaryDecision.padded V hs) (.pauli .X) (.pauli .Z)
      (Answer.pauliProject (shoupSelfDualNormalBasis k hk hodd))
      (finiteSourcePredicate V hs) (finitePauliCheck k hk hodd j hm x y) T U a b = true) :
    program W (canonicalInput V lam n (2^(2^j)*k) ((2^n)^lam)
      (unary k,unary j,unary (2^j)) T U x y
      (Answer.bits (shoupBinField k hk) a) (Answer.bits (shoupBinField k hk) b)) = true := by
  let E := shoupBinField k hk
  let p : PauliSamplerParameters.Parameters := (unary k,unary j,unary (2^j))
  let Q := 2^(2^j)*k
  let R := (2^n)^lam
  have hf := h
  simp only [AuxiliaryQuotient.check, Bool.and_eq_true] at hf
  have hfa := hf.1.1.1.1.1
  have hfb := hf.1.1.1.1.2
  have hva (t : QLD.Ty) (ht : T = .inl t) :
      QLD.PauliBinaryProgram.endpointValid (p,t,x,Answer.bits E a) = true := by
    subst T
    cases a <;> simp only [TypedPredicate.fits, Bool.false_eq_true] at hfa
    rename_i c
    have hv := Answer.parser_answerBits E hk _ c (ha t c rfl rfl)
    rw [Answer.questionOfBits_ty] at hv
    exact hv
  have hvb (u : QLD.Ty) (hu : U = .inl u) :
      QLD.PauliBinaryProgram.endpointValid (p,u,y,Answer.bits E b) = true := by
    subst U
    cases b <;> simp only [TypedPredicate.fits, Bool.false_eq_true] at hfb
    rename_i c
    have hv := Answer.parser_answerBits E hk _ c (hb u c rfl rfl)
    rw [Answer.questionOfBits_ty] at hv
    exact hv
  apply (program_iff W _).mpr
  refine ⟨canonical_canonicalInput _ _ _ _ _ _ _ _ _ _ _ _,?_,?_,?_,?_,
    auxiliary_encoded_complete W V hV hn k hk hodd j hm hs hQ hR T U x y a b
      ha hb hga hgb hsa hsb h⟩
  · rw [questionLengths_canonicalInput]
    simpa only [length_unary] using And.intro hx hy
  · rcases T with t | ⟨t,w⟩
    · rw [leftPauliFormat_canonicalInput]
      exact hva t rfl
    · simp only [leftPauliFormat, PolyTimeFun.ite_apply, leftIsPauli, comp_apply,
        finiteFunction_apply, leftType, raw, canonicalInput, fst_apply,
        leftLabelField_encode, isPauli, Bool.false_eq_true, ↓reduceIte, const_apply]
  · rcases U with u | ⟨u,v⟩
    · rw [rightPauliFormat_canonicalInput]
      exact hvb u rfl
    · simp only [rightPauliFormat, PolyTimeFun.ite_apply, rightIsPauli, comp_apply,
        finiteFunction_apply, rightType, raw, canonicalInput, fst_apply,
        rightLabelField_encode, isPauli, Bool.false_eq_true, ↓reduceIte, const_apply]
  · rcases T with t | ⟨t,w⟩ <;> rcases U with u | ⟨u,v⟩
    case inl.inl =>
      rw [pauli_canonicalInput, QLD.PauliBinaryProgram.program_ofBits_iff k hk hodd j hj hm
        t u x y _ _ hx hy]
      refine ⟨hva t rfl,hvb u rfl,?_⟩
      cases a <;> simp only [TypedPredicate.fits, Bool.false_eq_true] at hfa
      cases b <;> simp only [TypedPredicate.fits, Bool.false_eq_true] at hfb
      rename_i c d
      have hec := QLD.PauliAnswerProgram.decodeBits_answerBits E hk
        (QLD.PauliBinaryProgram.questionOfBits k hk hodd j t x) c (ha t c rfl rfl)
      have hed := QLD.PauliAnswerProgram.decodeBits_answerBits E hk
        (QLD.PauliBinaryProgram.questionOfBits k hk hodd j u y) d (hb u d rfl rfl)
      rw [Answer.questionOfBits_ty] at hec hed
      dsimp only [E] at hec hed
      simpa only [Answer.bits, Answer.toRaw, ParsedAnswer.mapAnswer, ParsedAnswer.mapPauli,
        AuxiliaryAnswer.bits, hec, hed, finitePauliCheck] using hf.1.1.2
    all_goals simp only [pauli, PolyTimeFun.ite_apply, AuxiliaryProgram.andCheck_iff,
      leftIsPauli, rightIsPauli, comp_apply, finiteFunction_apply, leftType, rightType,
      raw, canonicalInput, fst_apply, leftLabelField_encode, rightLabelField_encode,
      isPauli, Bool.false_eq_true, true_and, and_false, false_and, ↓reduceIte, const_apply]

/-- The accepted finite pair can be supplied directly from the numbered
quotient game used by the honest strategy construction. -/
theorem program_complete_numbered (W : ClockedUniversalMachine) {lam n : ℕ}
    (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k) (j : ℕ) (hj : j ≤ k)
    (hm : 2^j ∣ Fintype.card (shoupBinField k hk).carrier)
    (hs : V.sampler.dim (2^n) ≤ 2^(2^j)*k)
    (hQ : 4 ≤ 2^(2^j)*k) (hR : 3*((2^n)^lam) ≤ 2^(2^j)*k)
    (χ : (shoupBinField k hk).carrier → Fin (2^j))
    (T U : Label) (x y : Fin ((3*2^j+3)*k) → CL.𝔽₂)
    (a b : ParsedAnswer (Fin (2^(2^j)*k) → CL.𝔽₂) (Verifier.Answers ((2^n)^lam))
      (QLD.Answer (shoupBinField k hk).carrier (2^j) 1))
    (ha : Answer.PauliFormatted k hk hodd j _ _ T (CL.toBits x) a)
    (hb : Answer.PauliFormatted k hk hodd j _ _ U (CL.toBits y) b)
    (hga : PrefixGuard.holds (AuxiliaryDecision.padded V hs) T a)
    (hgb : PrefixGuard.holds (AuxiliaryDecision.padded V hs) U b)
    (hsa : AuxiliaryDecision.sourceOutput (V.sampler.dim (2^n)) T (Answer.toRaw (shoupBinField k hk) a))
    (hsb : AuxiliaryDecision.sourceOutput (V.sampler.dim (2^n)) U (Answer.toRaw (shoupBinField k hk) b))
    (h : (NumberedComplete.game (d := 1)
      (QLD.PauliFullAnswerProgram.registerNumbering (2^j) k).symm
      (AuxiliaryDecision.padded V hs) (finiteSourcePredicate (R := (2^n)^lam) V hs)
      hm (shoupSelfDualNormalBasis k hk hodd) χ
      (QLD.PauliCL.ExplicitSeed.seedPermutation (shoupBinField k hk))).D (T,x) (U,y) a b = true) :
    program W (canonicalInput V lam n (2^(2^j)*k) ((2^n)^lam)
      (unary k,unary j,unary (2^j)) T U (CL.toBits x) (CL.toBits y)
      (Answer.bits (shoupBinField k hk) a) (Answer.bits (shoupBinField k hk) b)) = true := by
  apply program_complete W V hV hn k hk hodd j hj hm hs hQ hR T U
    (CL.toBits x) (CL.toBits y) (CL.length_toBits x) (CL.length_toBits y)
    a b ha hb hga hgb hsa hsb
  have hp : Answer.pauliProject (shoupSelfDualNormalBasis k hk hodd) =
      NumberedComplete.project (d := 1)
        (QLD.PauliFullAnswerProgram.registerNumbering (2^j) k).symm
        (shoupSelfDualNormalBasis k hk hodd) := by
    funext a
    exact pauliProject_eq_numbered _ a
  have hDP : finitePauliCheck k hk hodd j hm (CL.toBits x) (CL.toBits y) =
      fun T U => ExplicitGame.pauliCheck (d := 1) hm
        (QLD.PauliCL.ExplicitSeed.seedPermutation (shoupBinField k hk))
        (shoupSelfDualNormalBasis k hk hodd) T U x y := by
    funext T U
    exact finitePauliCheck_toBits k hk hodd j hm x y T U
  rw [hp,hDP]
  exact h

end MIPRE.Introspection.DecisionKernel
end
