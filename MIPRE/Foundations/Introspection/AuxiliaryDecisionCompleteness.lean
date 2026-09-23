/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AuxiliaryDecisionSoundness
import MIPRE.Foundations.Introspection.GuardedAuxiliaryProgram

/-! # Completeness of the executable auxiliary predicate

The semantic acceptance relation implies executable acceptance on the
attained prefixes and original-answer cutoffs of the honest strategy.
-/

noncomputable section
namespace MIPRE.Introspection.AuxiliaryDecision
open Cost Cost.PolyTimeFun AuxiliaryAnswer AuxiliaryProgram SourcePadding SourcePadding.Program
open Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
variable {P : Type*} [Fintype P] [DecidableEq P] [SizedEncoding P]
variable {parameters : Parameters}

/-- The original answer component is bounded independently of register data. -/
def answerBound {Q : ℕ} (R : ℕ) : ParsedAnswer (Fin Q → CL.𝔽₂) BitStr BitStr → Prop
  | .pair _ a | .read _ _ a => a.length ≤ R
  | _ => True

/-- Only Introspect endpoints claim a full source output. -/
def sourceOutput {Q : ℕ} (s : ℕ) : QuestionType P 7 →
    ParsedAnswer (Fin Q → CL.𝔽₂) BitStr BitStr → Prop
  | .inr (.introspect,_), .pair y _ => SourceCompiler.InSource s (CL.toBits y)
  | _, _ => True

theorem valid_bits {Q R : ℕ} (t : QuestionType P 7)
    (a : ParsedAnswer (Fin Q → CL.𝔽₂) BitStr BitStr)
    (hf : TypedPredicate.fits t a = true) (hb : answerBound R a) : Valid Q R t (bits a) := by
  rcases t with p | ⟨t,w⟩
  · cases a <;> simp_all [TypedPredicate.fits, Valid]
  · cases t <;> cases a <;> simp_all [TypedPredicate.fits, Valid, bits, answerBound,
      AnswerParser.pairValid, AnswerParser.tripleValid,
      AnswerParser.pairParts_pairBits _ _ _ (CL.length_toBits _),
      AnswerParser.tripleParts_tripleBits _ _ _ _ (CL.length_toBits _) (CL.length_toBits _),
      CL.length_toBits]

/-- Every attained padded output has the required zero suffix. -/
theorem sourceOutput_of_attained {n Q : ℕ} (V : Verifier 7)
    (hs : V.sampler.dim (2 ^ n) ≤ Q) (w : Bool) (y : Fin Q → CL.𝔽₂)
    (hy : ∃ x, (padded V hs w).eval x = y) :
    SourceCompiler.InSource (V.sampler.dim (2 ^ n)) (CL.toBits y) := by
  obtain ⟨x,rfl⟩ := hy
  rw [padded, depthFamily_eval (firstEmbedding hs) (sourceFamily V n) (by decide)
    (fun w => (V.sampler.cl_exactlyOn (2 ^ n) (Player.ofBool w)).supportedOn) w x]
  rw [family, CL.CLFun.eval_embed]
  exact ((source_bits_iff hs _ _).mpr rfl).1

theorem directed_cross_complete (U : ClockedUniversalMachine) (X Z : P)
    (project : PolyTimeFun (Input P 7) BitStr) {lam n Q : ℕ}
    (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (hs : V.sampler.dim (2 ^ n) ≤ Q) (hQ : 4 ≤ Q) (hR : 3 * ((2 ^ n)^lam) ≤ Q)
    (x y : Fin Q → CL.𝔽₂) (a b : BitStr) (ha : a.length ≤ (2 ^ n)^lam)
    (hb : b.length ≤ (2 ^ n)^lam)
    (hx : SourceCompiler.InSource (V.sampler.dim (2 ^ n)) (CL.toBits x))
    (hy : SourceCompiler.InSource (V.sampler.dim (2 ^ n)) (CL.toBits y))
    (h : sourcePredicate V hs x y a b = true) :
    directed U X Z project (canonical V lam n Q ((2 ^ n)^lam) parameters
      (.inr (.introspect,false)) (.inr (.introspect,true))
      (bits (.pair x a)) (bits (.pair y b))) = true := by
  apply (directed_cross U X Z project V hV hn _ _).mpr
  constructor
  · simp only [SourceCompiler.GuardReady, SourceCompiler.inputDim, SourceCompiler.inputQ,
      SourceCompiler.inputR, SourceCompiler.inputIndex, SourceCompiler.inputLeft,
      SourceCompiler.inputRight, SourceCompiler.leftParts, SourceCompiler.rightParts,
      comp_apply, pair_apply, fst_apply, snd_apply, DynamicParser.pairParts_apply, bits,
      AnswerParser.pairParts_pairBits _ _ _ (CL.length_toBits _)]
    exact ⟨hs,(hV.1 _ ((two_le_exp_index_iff n).mpr hn)).1,
      valid_bits (.inr (.introspect,false) : QuestionType P 7) (.pair x a) rfl ha,
      valid_bits (.inr (.introspect,true) : QuestionType P 7) (.pair y b) rfl hb,
      hx,hy,AnswerParser.pairBits_lt_outer _ _ hQ hR _ _ (CL.length_toBits _) ha,
      AnswerParser.pairBits_lt_outer _ _ hQ hR _ _ (CL.length_toBits _) hb⟩
  · simp only [SourceCompiler.leftParts, SourceCompiler.rightParts, comp_apply, pair_apply,
      SourceCompiler.inputQ, SourceCompiler.inputLeft, SourceCompiler.inputRight, fst_apply,
      snd_apply, DynamicParser.pairParts_apply, bits,
      AnswerParser.pairParts_pairBits _ _ _ (CL.length_toBits _)]
    simpa only [sourcePredicate, decide_eq_true_eq, toBits_pull_first] using h

/-- Semantic auxiliary comparisons are executable on correctly tagged,
bounded answers whose queried prefixes are attained. -/
theorem directed_complete (U : ClockedUniversalMachine) (X Z : P)
    (project : PolyTimeFun (Input P 7) BitStr) {lam n Q : ℕ}
    (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (hs : V.sampler.dim (2 ^ n) ≤ Q) (hQ : 4 ≤ Q) (hR : 3 * ((2 ^ n)^lam) ≤ Q)
    (π : BitStr → Fin Q → CL.𝔽₂) (t u : QuestionType P 7)
    (a b : ParsedAnswer (Fin Q → CL.𝔽₂) BitStr BitStr)
    (hfa : TypedPredicate.fits t a = true) (hfb : TypedPredicate.fits u b = true)
    (ha : answerBound ((2 ^ n)^lam) a) (hb : answerBound ((2 ^ n)^lam) b)
    (hga : PrefixGuard.holds (padded V hs) t a) (hgb : PrefixGuard.holds (padded V hs) u b)
    (hsa : sourceOutput (V.sampler.dim (2 ^ n)) t a)
    (hsb : sourceOutput (V.sampler.dim (2 ^ n)) u b)
    (hp : ∀ p c, (p = X ∨ p = Z) → t = .inl p → a = .pauli c →
      project (canonical V lam n Q ((2 ^ n)^lam) parameters t u (bits a) (bits b)) =
        CL.toBits (π c))
    (h : AuxiliaryQuotient.directed (padded V hs) X Z π (sourcePredicate V hs) t u a b = true) :
    directed U X Z project
      (canonical V lam n Q ((2 ^ n)^lam) parameters t u (bits a) (bits b)) = true := by
  rw [directed_canonical]
  generalize htu : (t,u) = tu
  fun_cases route X Z tu
  case case2 => rfl
  case case4 => rfl
  case case6 => rfl
  case case8 => rfl
  case case10 => rfl
  case case12 => rfl
  case case14 => rfl
  all_goals rcases Prod.mk.inj htu with ⟨rfl,rfl⟩
  all_goals cases a <;> cases b <;> simp_all only [TypedPredicate.fits, Bool.false_eq_true]
  case case1.pauli.pair w a z b =>
    simp only [AuxiliaryQuotient.directed, ↓reduceIte, decide_eq_true_eq] at h
    have hp' := hp Z a (Or.inr rfl) rfl rfl
    simp only [bits] at hp'
    rw [h] at hp'
    have he := (directed_z_sample U X Z project V lam n Q ((2 ^ n)^lam) w a z b).mpr hp'
    simpa only [directed_canonical, route, bits, ↓reduceIte] using he
  case case3.pair.pair w y a z b =>
    simp only [AuxiliaryQuotient.directed, ↓reduceIte, decide_eq_true_eq] at h
    have he := (directed_sampling (parameters := parameters) U X Z project V hV hn hs hQ hR w y z a b).mpr ⟨ha,hb,h⟩
    simpa only [directed_canonical, route, bits, ↓reduceIte] using he
  case case5.pair.read w y a z zp b =>
    simp only [AuxiliaryQuotient.directed, ↓reduceIte, decide_eq_true_eq] at h
    have he := (directed_reading (parameters := parameters) U X Z project V lam n hQ hR w y z zp a b).mpr ⟨ha,hb,h⟩
    simpa only [directed_canonical, route, bits, ↓reduceIte] using he
  case case7.hide.read k w v hkv y yp x z zp a =>
    have hk : k.val = 6 := by omega
    simp only [AuxiliaryQuotient.directed, hkv.2, and_self, ↓reduceIte,
      decide_eq_true_eq] at h
    have hkFin : k = 6 := Fin.ext hk
    subst k
    have he := (directed_last (parameters := parameters) (R := (2 ^ n)^lam) U X Z project V hV hn hs v 6 hkv.2 y yp x z zp a).mpr
      ⟨hga,hgb,h⟩
    simpa only [directed_canonical, route, bits, hkv.2, and_self, ↓reduceIte] using he
  case case9.hide.hide k w j v hkv y yp x z zp r =>
    simp only [AuxiliaryQuotient.directed, hkv.2, and_self, ↓reduceIte,
      decide_eq_true_eq] at h
    have hgb' : ∃ a, ((padded V hs v).truncate (k.val+1)).eval a =
        (padded V hs v).outputPrefix (k.val+1) z := by
      rw [hkv.2]
      exact hgb
    have he := (directed_next (parameters := parameters) (R := (2 ^ n)^lam) U X Z project V hV hn hs v k j hkv.2 y yp x z zp r).mpr
      ⟨hga,hgb',h⟩
    simpa only [directed_canonical, route, bits, hkv.2, and_self, ↓reduceIte] using he
  case case11.pauli.hide p k w hpk a y yp x =>
    have hk : k = 0 := Fin.ext hpk.2
    subst k
    simp only [AuxiliaryQuotient.directed, Fin.val_zero, and_self, ↓reduceIte,
      decide_eq_true_eq] at h
    have he := (directed_first U X Z project V hV hn hs w (π a) y yp x a
      (hp X a (Or.inl rfl) rfl rfl)).mpr h
    simpa only [directed_canonical, route, bits, Fin.val_zero, and_self, ↓reduceIte] using he
  case case13.pair.pair x a y b =>
    have he := directed_cross_complete (parameters := parameters) U X Z project V hV hn hs hQ hR x y a b
      ha hb hsa hsb h
    simpa only [directed_canonical, route] using he

/-- The executable local scan is exactly the semantic prefix guard. -/
theorem prefixGuard_canonical (U : ClockedUniversalMachine) {lam n Q : ℕ}
    (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (hs : V.sampler.dim (2 ^ n) ≤ Q) (R : ℕ) (t u : QuestionType P 7)
    (a : ParsedAnswer (Fin Q → CL.𝔽₂) BitStr BitStr) (b : BitStr)
    (hf : TypedPredicate.fits t a = true) :
    prefixGuard U (canonical V lam n Q R parameters t u (bits a) b) = true ↔
      PrefixGuard.holds (padded V hs) t a := by
  change AuxiliaryPrefixGuard.program U
    (queryContext V lam n false 0 (0 : Fin Q → CL.𝔽₂),Q,t,bits a) = true ↔ _
  rcases t with p | ⟨t,w⟩
  · cases a <;> simp_all only [TypedPredicate.fits, Bool.false_eq_true]
    exact ⟨fun _ => trivial, fun _ => AuxiliaryPrefixGuard.program_pauli _ _ _ _ _⟩
  · cases t <;> cases a <;> simp_all only [TypedPredicate.fits, Bool.false_eq_true]
    case introspect.pair y a =>
      exact ⟨fun _ => trivial, fun _ => AuxiliaryPrefixGuard.program_introspect _ _ _ _ _⟩
    case sample.pair y a =>
      exact ⟨fun _ => trivial, fun _ => AuxiliaryPrefixGuard.program_sample _ _ _ _ _⟩
    case read.read y yp a =>
      exact AuxiliaryPrefixGuard.program_read U V hV hn hs false w 0 0 y yp a
    case hide.hide k y yp x =>
      exact AuxiliaryPrefixGuard.program_hide U V hV hn hs false w 0 0 y yp x k

/-- Both semantic orientations and their local guards pass the complete
executable auxiliary kernel on honest, bounded source outputs. -/
theorem guarded_complete (U : ClockedUniversalMachine) (X Z : P)
    (project : PolyTimeFun (Input P 7) BitStr) {lam n Q : ℕ}
    (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (hs : V.sampler.dim (2 ^ n) ≤ Q) (hQ : 4 ≤ Q) (hR : 3 * ((2 ^ n)^lam) ≤ Q)
    (π : BitStr → Fin Q → CL.𝔽₂) (DP : P → P → BitStr → BitStr → Bool)
    (t u : QuestionType P 7) (a b : ParsedAnswer (Fin Q → CL.𝔽₂) BitStr BitStr)
    (ha : answerBound ((2 ^ n)^lam) a) (hb : answerBound ((2 ^ n)^lam) b)
    (hga : PrefixGuard.holds (padded V hs) t a) (hgb : PrefixGuard.holds (padded V hs) u b)
    (hsa : sourceOutput (V.sampler.dim (2 ^ n)) t a)
    (hsb : sourceOutput (V.sampler.dim (2 ^ n)) u b)
    (hpa : ∀ p c, (p = X ∨ p = Z) → t = .inl p → a = .pauli c →
      project (canonical V lam n Q ((2 ^ n)^lam) parameters t u (bits a) (bits b)) =
        CL.toBits (π c))
    (hpb : ∀ p c, (p = X ∨ p = Z) → u = .inl p → b = .pauli c →
      project (canonical V lam n Q ((2 ^ n)^lam) parameters u t (bits b) (bits a)) =
        CL.toBits (π c))
    (h : AuxiliaryQuotient.check (padded V hs) X Z π (sourcePredicate V hs) DP t u a b = true) :
    guarded U X Z project
      (canonical V lam n Q ((2 ^ n)^lam) parameters t u (bits a) (bits b)) = true := by
  simp only [AuxiliaryQuotient.check, Bool.and_eq_true] at h
  have hfa := h.1.1.1.1.1
  have hfb := h.1.1.1.1.2
  apply (guarded_iff U X Z project _).mpr
  refine ⟨(prefixGuard_canonical U V hV hn hs _ t u a (bits b) hfa).mpr hga,
    (prefixGuard_canonical U V hV hn hs _ u t b (bits a) hfb).mpr hgb, ?_⟩
  apply (check_iff U X Z project _).mpr
  refine ⟨(format_canonical V lam n Q _ t u _ _).mpr (valid_bits t a hfa ha),
    (format_canonical V lam n Q _ u t _ _).mpr (valid_bits u b hfb hb), ?_,
    directed_complete U X Z project V hV hn hs hQ hR π t u a b hfa hfb ha hb hga hgb
      hsa hsb hpa h.1.2,
    directed_complete U X Z project V hV hn hs hQ hR π u t b a hfb hfa hb ha hgb hga
      hsb hsa hpb h.2⟩
  intro htu
  change t = u at htu
  subst u
  have he := h.1.1.1.2
  simp only [↓reduceIte] at he
  by_cases hab : a = b
  · exact congrArg bits hab
  · simp only [hab, decide_false, Bool.false_eq_true] at he

end MIPRE.Introspection.AuxiliaryDecision
end
