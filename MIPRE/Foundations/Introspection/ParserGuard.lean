/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.ParserAnswers
import MIPRE.Foundations.CL.DetypingProgCost
import MIPRE.Foundations.Verifier

/-! # Reject malformed introspection answers before a source call

The input is `encode (n, answerA, answerB)`. On two valid Introspect answers
the source receives `encode (n, yA, yB, aA, aB)`. The supplied index is retained,
so this wrapper can precede the exponential-index clock adapter. This module
does not implement the register projection from `Q` coordinates to a source
question space, or the other auxiliary edge tests.
-/

noncomputable section

namespace MIPRE.Introspection.AnswerParser

open Cost Cost.PolyTimeFun CL.Detyping.Program

def guardIndex : PolyTimeFun Data ℕ := readNat.comp treeHead
def guardLeft : PolyTimeFun Data BitStr := readBits.comp (treeHead.comp treeTail)
def guardRight : PolyTimeFun Data BitStr := readBits.comp (treeTail.comp treeTail)

def callArgument (Q : ℕ) (x : Data) : Data :=
  let a := pairParts Q (guardLeft x)
  let b := pairParts Q (guardRight x)
  encode (guardIndex x, a.1, b.1, a.2, b.2)

def callArgumentProg (Q : ℕ) : PolyTimeFun Data Data :=
  let a := (pairPartsProg Q).comp guardLeft
  let b := (pairPartsProg Q).comp guardRight
  encoded.comp (guardIndex.pair ((fst.comp a).pair
    ((fst.comp b).pair ((snd.comp a).pair (snd.comp b)))))

@[simp] theorem callArgumentProg_apply (Q : ℕ) (x : Data) :
    callArgumentProg Q x = callArgument Q x := by
  simp [callArgumentProg, callArgument]

def callReady (Q R : ℕ) (x : Data) : Prop :=
  x = encode (guardIndex x, guardLeft x, guardRight x) ∧
    pairValid Q R (guardLeft x) ∧ pairValid Q R (guardRight x)

instance (Q R : ℕ) (x : Data) : Decidable (callReady Q R x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def guardedRoute (Q R : ℕ) : PolyTimeFun Data (Bool × Data) :=
  let canonical := encoded.comp (guardIndex.pair (guardLeft.pair guardRight))
  let call := (const true).pair (ap₂ treePair (callArgumentProg Q) (const Data.nil))
  let reject := const (false, encode false)
  ite (ap₂ treeEq (PolyTimeFun.id Data) canonical)
    (ite ((pairCheck Q R).comp guardLeft)
      (ite ((pairCheck Q R).comp guardRight) call reject) reject) reject

private theorem nestedIf {α : Type*} (p q : Prop) [Decidable p] [Decidable q] (a b : α) :
    (if p then if q then a else b else b) = if p ∧ q then a else b := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem guardedRoute_apply (Q R : ℕ) (x : Data) :
    guardedRoute Q R x = if callReady Q R x then
      (true, .cons (callArgument Q x) .nil) else (false, encode false) := by
  simp only [guardedRoute, callReady, PolyTimeFun.ite_apply, ap₂_apply, comp_apply,
    pair_apply, id_apply, treeEq_apply, encoded_apply, const_apply, treePair_apply,
    callArgumentProg_apply, pairCheck_apply, decide_eq_true_eq]
  rw [nestedIf, nestedIf]
  simp only [and_assoc]
  rfl

@[simp] theorem guardIndex_cons (n : ℕ) (d : Data) :
    guardIndex (.cons (encode n) d) = n := by simp [guardIndex, readNat_encode]

theorem guardedRoute_preserves (Q R n : ℕ) (d a : Data)
    (h : guardedRoute Q R (.cons (encode n) d) = (true, a)) :
    ∃ q ctx, a = .cons (.cons (encode n) q) ctx := by
  rw [guardedRoute_apply] at h
  split_ifs at h with hr
  · have he := (Prod.mk.inj h).2.symm
    simp only [callArgument, guardIndex_cons, encode_prod] at he
    exact ⟨_, .nil, he⟩
  · cases (Prod.mk.inj h).1

/-- Actual program: invalid tuples return false before the source program is evaluated. -/
def guardedProg (Q R : ℕ) (source : Prog) : Prog :=
  Prog.routeOneCall (guardedRoute Q R) source snd

theorem guardedProg_closed (Q R : ℕ) {source : Prog} (hs : source.WellScoped 1) :
    (guardedProg Q R source).WellScoped 1 := Prog.routeOneCall_closed _ hs _

/-- Rejection needs no halting assumption about the source. -/
theorem guardedProg_reject (Q R : ℕ) (source : Prog) (x : Data)
    (h : ¬ callReady Q R x) :
    ∃ t, (guardedProg Q R source).Runs x (encode false) t :=
  Prog.routeOneCall_direct _ _ _ _ _ (by rw [guardedRoute_apply, if_neg h])

theorem guardedProg_call (Q R : ℕ) {source : Prog} (hs : source.WellScoped 1)
    (x r : Data) (t : ℕ) (h : callReady Q R x)
    (hr : source.Runs (callArgument Q x) r t) :
    ∃ time, (guardedProg Q R source).Runs x r time := by
  exact Prog.routeOneCall_indirect _ hs snd x _ .nil r t
    (by rw [guardedRoute_apply, if_pos h]) hr

theorem guardedProg_halts (Q R n : ℕ) {source : Prog} (hs : source.WellScoped 1)
    (halts : ∀ d, Halts source (.cons (encode n) d)) (d : Data) :
    Halts (guardedProg Q R source) (.cons (encode n) d) :=
  Prog.routeOneCall_halts _ hs _ n d halts (guardedRoute_preserves Q R n d)

/-- Full ambient input-size polynomial transfer for the guarded source call. -/
theorem guardedProg_haltsWithin (Q R n B k : ℕ) {source : Prog} (hs : source.WellScoped 1)
    (bound : ∀ d, HaltsWithin source (.cons (encode n) d) (B * (d.size + 1) ^ k))
    (d : Data) : HaltsWithin (guardedProg Q R source) (.cons (encode n) d)
      ((Prog.routeCost (guardedRoute Q R) snd B k).eval (Data.cons (encode n) d).size) :=
  Prog.routeOneCall_haltsWithin _ hs _ n B k d bound (guardedRoute_preserves Q R n d)

theorem callReady_input (Q R n : ℕ) (a b : BitStr) :
    callReady Q R (encode (n, a, b)) ↔ pairValid Q R a ∧ pairValid Q R b := by
  simp [callReady, guardIndex, guardLeft, guardRight, encode_prod, readNat_encode,
    readBits_encode]

theorem callArgument_input (Q n : ℕ) (a b : BitStr) :
    callArgument Q (encode (n, a, b)) =
      encode (n, (pairParts Q a).1, (pairParts Q b).1, (pairParts Q a).2,
        (pairParts Q b).2) := by
  simp [callArgument, guardIndex, guardLeft, guardRight, encode_prod, readNat_encode,
    readBits_encode]

/-- Every call has both full register lengths and the separate original-answer cutoffs. -/
theorem callReady_fields (Q R n : ℕ) (a b : BitStr)
    (h : callReady Q R (encode (n, a, b))) :
    (pairParts Q a).1.length = Q ∧ (pairParts Q b).1.length = Q ∧
      (pairParts Q a).2.length ≤ R ∧ (pairParts Q b).2.length ≤ R := by
  rw [callReady_input] at h
  exact ⟨h.1.2.1, h.2.2.1, h.1.2.2, h.2.2.2⟩

/-- On total sources, guarded acceptance is exactly valid parsing followed by source acceptance. -/
theorem guardedProg_accepts_iff (Q R n : ℕ) (source : MIPRE.Decider)
    (halts : ∀ d, Halts source.prog (.cons (encode n) d)) (a b : BitStr) :
    (∃ t, (guardedProg Q R source.prog).Runs (encode (n, a, b)) (encode true) t) ↔
      pairValid Q R a ∧ pairValid Q R b ∧
        source.Accepts n (pairParts Q a).1 (pairParts Q b).1
          (pairParts Q a).2 (pairParts Q b).2 := by
  by_cases h : callReady Q R (encode (n, a, b))
  · have hp := (callReady_input Q R n a b).mp h
    obtain ⟨r, t, hr⟩ := halts (encode ((pairParts Q a).1, (pairParts Q b).1,
      (pairParts Q a).2, (pairParts Q b).2))
    have hr' : source.prog.Runs (callArgument Q (encode (n, a, b))) r t := by
      rw [callArgument_input]
      exact hr
    obtain ⟨time, hout⟩ := guardedProg_call Q R source.closed _ r t h hr'
    constructor
    · rintro ⟨ta, ha⟩
      exact ⟨hp.1, hp.2, t, (hout.deterministic ha).1 ▸ hr⟩
    · rintro ⟨_, _, ta, ha⟩
      have he := (hr.deterministic ha).1
      exact ⟨time, he ▸ hout⟩
  · obtain ⟨time, hout⟩ := guardedProg_reject Q R source.prog _ h
    constructor
    · rintro ⟨ta, ha⟩
      have he := encode_injective (hout.deterministic ha).1
      cases he
    · rintro ⟨ha, hb, _⟩
      exact (h ((callReady_input Q R n a b).mpr ⟨ha, hb⟩)).elim

end MIPRE.Introspection.AnswerParser

end
