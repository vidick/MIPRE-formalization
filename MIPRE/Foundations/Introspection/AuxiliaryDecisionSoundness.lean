/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AuxiliaryDecisionCorrect
import MIPRE.Foundations.Introspection.AuxiliaryAnswerCoding
import MIPRE.Foundations.Introspection.TypedQuotientPredicate

/-! # Semantic soundness of the executable auxiliary predicate

Canonical byte answers accepted by the executable checks satisfy the full
quotient predicate. The cross edge projects to the original bounded verifier.
-/

noncomputable section
namespace MIPRE.Introspection.AuxiliaryDecision
open Cost Cost.PolyTimeFun AuxiliaryAnswer AuxiliaryProgram SourcePadding SourcePadding.Program
open Classical
set_option maxHeartbeats 100000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
variable {P : Type*} [Fintype P] [DecidableEq P] [SizedEncoding P]
variable {parameters : Parameters}

/-- The source predicate on the padded register uses the original decision program. -/
def sourcePredicate {n Q : ℕ} (V : Verifier 7) (hs : V.sampler.dim (2 ^ n) ≤ Q)
    (x y : Fin Q → CL.𝔽₂) (a b : BitStr) : Bool :=
  decide (V.decider.Accepts (2 ^ n) (CL.toBits (CL.pull (firstEmbedding hs) x))
    (CL.toBits (CL.pull (firstEmbedding hs) y)) a b)

theorem directed_cross_sound (U : ClockedUniversalMachine) (X Z : P)
    (project : PolyTimeFun (Input P 7) BitStr) {lam n Q : ℕ}
    (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (hs : V.sampler.dim (2 ^ n) ≤ Q) (x y : Fin Q → CL.𝔽₂) (a b : BitStr)
    (h : directed U X Z project (canonical V lam n Q ((2 ^ n)^lam) parameters
      (.inr (.introspect,false)) (.inr (.introspect,true))
      (bits (.pair x a)) (bits (.pair y b))) = true) :
    sourcePredicate V hs x y a b = true := by
  have hh := (directed_cross U X Z project V hV hn _ _).mp h
  simp only [SourceCompiler.leftParts, SourceCompiler.rightParts, comp_apply, pair_apply,
    SourceCompiler.inputQ, SourceCompiler.inputLeft, SourceCompiler.inputRight, fst_apply,
    snd_apply, DynamicParser.pairParts_apply, bits,
    AnswerParser.pairParts_pairBits _ _ _ (CL.length_toBits _)] at hh
  simpa only [sourcePredicate, decide_eq_true_eq, toBits_pull_first] using hh.2

/-- Every executable directed comparison implies its quotient semantics. -/
theorem directed_sound (U : ClockedUniversalMachine) (X Z : P)
    (project : PolyTimeFun (Input P 7) BitStr) {lam n Q : ℕ}
    (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (hs : V.sampler.dim (2 ^ n) ≤ Q) (hQ : 4 ≤ Q) (hR : 3 * ((2 ^ n)^lam) ≤ Q)
    (π : BitStr → Fin Q → CL.𝔽₂) (t u : QuestionType P 7)
    (a b : ParsedAnswer (Fin Q → CL.𝔽₂) BitStr BitStr)
    (hp : ∀ p c, (p = X ∨ p = Z) → t = .inl p → a = .pauli c →
      project (canonical V lam n Q ((2 ^ n)^lam) parameters t u (bits a) (bits b)) =
        CL.toBits (π c))
    (h : directed U X Z project
      (canonical V lam n Q ((2 ^ n)^lam) parameters t u (bits a) (bits b)) = true) :
    AuxiliaryQuotient.directed (padded V hs) X Z π (sourcePredicate V hs) t u a b = true := by
  fun_cases AuxiliaryQuotient.directed (padded V hs) X Z π (sourcePredicate V hs) t u a b
  all_goals try simp only [decide_eq_true_eq]
  case case1 w a z b =>
    have he := (directed_z_sample U X Z project V lam n Q ((2 ^ n)^lam) w a z b).mp h
    have hpa := hp Z a (Or.inr rfl) rfl rfl
    simp only [bits] at hpa
    rw [hpa] at he
    have hh := congrArg (CL.ofBits Q) he
    simpa only [CL.ofBits_toBits] using hh
  case case3 w y a z b =>
    exact ((directed_sampling U X Z project V hV hn hs hQ hR w y z a b).mp h).2.2
  case case5 w y a z zp b =>
    exact ((directed_reading U X Z project V lam n hQ hR w y z zp a b).mp h).2.2
  case case7 k w v y yp x z zp a hw =>
    rcases hw with ⟨rfl,hk⟩
    exact ((directed_last U X Z project V hV hn hs w k hk y yp x z zp a).mp h).2.2
  case case9 k w j v y yp x z zp t hw =>
    rcases hw with ⟨rfl,hk⟩
    exact ((directed_next U X Z project V hV hn hs w k j hk y yp x z zp t).mp h).2.2
  case case11 p k w a y yp x hw =>
    rcases hw with ⟨rfl,hk⟩
    have hk0 : k = 0 := Fin.ext hk
    subst k
    exact (directed_first U p Z project V hV hn hs w (π a) y yp x a
      (hp p a (Or.inl rfl) rfl rfl)).mp h
  case case13 x a y b =>
    exact directed_cross_sound U X Z project V hV hn hs x y a b h

/-- The executable format check is the canonical auxiliary byte format. -/
theorem format_canonical (V : Verifier 7) (lam n Q R : ℕ)
    (t u : QuestionType P 7) (a b : BitStr) :
    format (canonical V lam n Q R parameters t u a b) = true ↔ Valid Q R t a := by
  rw [format_apply]
  rcases t with p | ⟨t,w⟩
  · change (true = true ↔ True)
    exact ⟨fun _ => trivial, fun _ => rfl⟩
  · cases t <;> simp only [leftType, left, canonical, comp_apply, fst_apply, snd_apply,
      width, bounds, originalBound, leftBits, Valid]
    all_goals exact ⟨of_decide_eq_true, decide_eq_true⟩

/-- The two executable orientations, formats and consistency together imply
the complete quotient predicate. Pauli acceptance is supplied by its parser. -/
theorem check_sound (U : ClockedUniversalMachine) (X Z : P)
    (project : PolyTimeFun (Input P 7) BitStr) {lam n Q : ℕ}
    (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (hs : V.sampler.dim (2 ^ n) ≤ Q) (hQ : 4 ≤ Q) (hR : 3 * ((2 ^ n)^lam) ≤ Q)
    (π : BitStr → Fin Q → CL.𝔽₂) (DP : P → P → BitStr → BitStr → Bool)
    (t u : QuestionType P 7) (a b : ParsedAnswer (Fin Q → CL.𝔽₂) BitStr BitStr)
    (ha : TypedPredicate.fits t a = true) (hb : TypedPredicate.fits u b = true)
    (hpa : ∀ p c, (p = X ∨ p = Z) → t = .inl p → a = .pauli c →
      project (canonical V lam n Q ((2 ^ n)^lam) parameters t u (bits a) (bits b)) =
        CL.toBits (π c))
    (hpb : ∀ p c, (p = X ∨ p = Z) → u = .inl p → b = .pauli c →
      project (canonical V lam n Q ((2 ^ n)^lam) parameters u t (bits b) (bits a)) =
        CL.toBits (π c))
    (hDP : ∀ p q x y, t = .inl p → u = .inl q → a = .pauli x → b = .pauli y →
      DP p q x y = true)
    (h : check U X Z project
      (canonical V lam n Q ((2 ^ n)^lam) parameters t u (bits a) (bits b)) = true) :
    AuxiliaryQuotient.check (padded V hs) X Z π (sourcePredicate V hs) DP t u a b = true := by
  have hh := (check_iff U X Z project _).mp h
  have he : t = u → bits a = bits b := hh.2.2.1
  have hd := directed_sound U X Z project V hV hn hs hQ hR π t u a b hpa hh.2.2.2.1
  have hr := directed_sound U X Z project V hV hn hs hQ hR π u t b a hpb hh.2.2.2.2
  simp only [AuxiliaryQuotient.check, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨ha,hb⟩,?_⟩,?_⟩,hd⟩,hr⟩
  · split
    · rename_i htu
      subst u
      have hab := (bits_eq_iff t a b ha hb).mp (he rfl)
      subst b
      simp only [decide_true]
    · rfl
  · rcases t with p | ⟨t,w⟩ <;> rcases u with q | ⟨u,v⟩ <;>
      cases a <;> cases b <;> try rfl
    exact hDP p q _ _ rfl rfl rfl rfl

/-- Soundness for every raw accepted answer, including the canonical parser
round trip needed to interpret same-type byte equality. -/
theorem check_raw_sound (U : ClockedUniversalMachine) (X Z : P)
    (project : PolyTimeFun (Input P 7) BitStr) {lam n Q : ℕ}
    (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (hs : V.sampler.dim (2 ^ n) ≤ Q) (hQ : 4 ≤ Q) (hR : 3 * ((2 ^ n)^lam) ≤ Q)
    (π : BitStr → Fin Q → CL.𝔽₂) (DP : P → P → BitStr → BitStr → Bool)
    (t u : QuestionType P 7) (a b : BitStr)
    (hpa : ∀ p, (p = X ∨ p = Z) → t = .inl p →
      project (canonical V lam n Q ((2 ^ n)^lam) parameters t u a b) = CL.toBits (π a))
    (hpb : ∀ p, (p = X ∨ p = Z) → u = .inl p →
      project (canonical V lam n Q ((2 ^ n)^lam) parameters u t b a) = CL.toBits (π b))
    (hDP : ∀ p q, t = .inl p → u = .inl q → DP p q a b = true)
    (h : check U X Z project
      (canonical V lam n Q ((2 ^ n)^lam) parameters t u a b) = true) :
    AuxiliaryQuotient.check (padded V hs) X Z π (sourcePredicate V hs) DP t u
      (decode Q t a) (decode Q u b) = true := by
  have hh := (check_iff U X Z project _).mp h
  have ha := bits_decode ((2 ^ n)^lam) t a
    ((format_canonical V lam n Q ((2 ^ n)^lam) t u a b).mp hh.1)
  have hb := bits_decode ((2 ^ n)^lam) u b
    ((format_canonical V lam n Q ((2 ^ n)^lam) u t b a).mp hh.2.1)
  apply check_sound U X Z project V hV hn hs hQ hR π DP t u
    (decode Q t a) (decode Q u b) (decode_fits _ _) (decode_fits _ _)
  · intro p c hp ht hc
    rw [ha,hb]
    subst t
    have : a = c := ParsedAnswer.pauli.inj hc
    subst c
    exact hpa p hp rfl
  · intro p c hp ht hc
    rw [hb,ha]
    subst u
    have : b = c := ParsedAnswer.pauli.inj hc
    subst c
    exact hpb p hp rfl
  · intro p q x y ht hu hx hy
    subst t u
    have hax : a = x := ParsedAnswer.pauli.inj hx
    have hby : b = y := ParsedAnswer.pauli.inj hy
    subst x y
    exact hDP p q rfl rfl
  · simpa only [ha,hb] using h

end MIPRE.Introspection.AuxiliaryDecision
end
