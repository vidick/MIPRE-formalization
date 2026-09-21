/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.DynamicParser
import MIPRE.Foundations.Introspection.ClockSimulation

/-! # Dynamic source-question projection and internal answer cutoff

The input carries `(n,Q,R,s,answerA,answerB)` with all four numbers in binary.
The guard validates the paper's tuple encoding, the separate original-answer
cutoff, and membership of both register strings in the zero-padded source
question space. Only then does it invoke the source on the first `s` bits.
-/

noncomputable section

namespace MIPRE.Introspection.SourceCompiler

open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)

abbrev GuardInput := ℕ × ℕ × ℕ × ℕ × BitStr × BitStr

def inputIndex : PolyTimeFun GuardInput ℕ := fst
def inputQ : PolyTimeFun GuardInput ℕ := fst.comp snd
def inputR : PolyTimeFun GuardInput ℕ := fst.comp (snd.comp snd)
def inputDim : PolyTimeFun GuardInput ℕ := fst.comp (snd.comp (snd.comp snd))
def inputLeft : PolyTimeFun GuardInput BitStr := fst.comp (snd.comp (snd.comp (snd.comp snd)))
def inputRight : PolyTimeFun GuardInput BitStr := snd.comp (snd.comp (snd.comp (snd.comp snd)))

def leftParts : PolyTimeFun GuardInput (BitStr × BitStr) :=
  DynamicParser.pairParts.comp (inputLeft.pair inputQ)
def rightParts : PolyTimeFun GuardInput (BitStr × BitStr) :=
  DynamicParser.pairParts.comp (inputRight.pair inputQ)

def InSource (s : ℕ) (y : BitStr) : Prop :=
  y.drop s = List.replicate (y.length - s) false

instance (s : ℕ) (y : BitStr) : Decidable (InSource s y) := inferInstanceAs (Decidable (_ = _))

def sourceCheck : PolyTimeFun (BitStr × ℕ) Bool :=
  let rest := DynamicParser.dropBits
  ap₂ treeEq (encoded.comp rest)
    (encoded.comp ((map (const false : PolyTimeFun Bool Bool)).comp rest))

theorem sourceCheck_iff (y : BitStr) (s : ℕ) : sourceCheck (y,s) = true ↔ InSource s y := by
  simp only [sourceCheck, ap₂_apply, comp_apply, encoded_apply, treeEq_apply,
    DynamicParser.dropBits_apply, decide_eq_true_eq, encode_injective.eq_iff]
  change y.drop s = (y.drop s).map (fun _ => false) ↔ InSource s y
  simp only [List.map_const', List.length_drop, InSource]

theorem InSource_padding {s Q : ℕ} {y : BitStr} (hy : y.length = Q) (h : InSource s y) :
    y = y.take s ++ List.replicate (Q-s) false := by
  rw [← hy, ← h]
  exact (List.take_append_drop s y).symm

def eight : PolyTimeFun ℕ ℕ :=
  (ap₂ natBit (const false) (PolyTimeFun.id ℕ)).comp
    ((ap₂ natBit (const false) (PolyTimeFun.id ℕ)).comp
      (ap₂ natBit (const false) (PolyTimeFun.id ℕ)))

@[simp] theorem eight_apply (n : ℕ) : eight n = 8*n := by simp [eight, Nat.bit_val]; omega

private def andCheck {α : Type*} [SizedEncoding α] (f g : PolyTimeFun α Bool) :
    PolyTimeFun α Bool := ite f g (const false)

private theorem andCheck_iff {α : Type*} [SizedEncoding α] (f g : PolyTimeFun α Bool) (x : α) :
    andCheck f g x = true ↔ f x = true ∧ g x = true := by
  simp only [andCheck, PolyTimeFun.ite_apply, const_apply]
  cases f x <;> simp

def GuardReady (x : GuardInput) : Prop :=
  inputDim x ≤ inputQ x ∧ inputDim x ≤ inputR x ∧
  AnswerParser.pairValid (inputQ x) (inputR x) (inputLeft x) ∧
  AnswerParser.pairValid (inputQ x) (inputR x) (inputRight x) ∧
  InSource (inputDim x) (leftParts x).1 ∧ InSource (inputDim x) (rightParts x).1 ∧
  (inputLeft x).length < 8*inputQ x ∧ (inputRight x).length < 8*inputQ x

instance (x : GuardInput) : Decidable (GuardReady x) := inferInstanceAs (Decidable (_ ∧ _))

def guardCheck : PolyTimeFun GuardInput Bool :=
  andCheck (ap₂ leNat inputDim inputQ) <|
  andCheck (ap₂ leNat inputDim inputR) <|
  andCheck (DynamicParser.pairCheck.comp (inputLeft.pair (inputQ.pair inputR))) <|
  andCheck (DynamicParser.pairCheck.comp (inputRight.pair (inputQ.pair inputR))) <|
  andCheck (sourceCheck.comp ((fst.comp leftParts).pair inputDim)) <|
  andCheck (sourceCheck.comp ((fst.comp rightParts).pair inputDim)) <|
  andCheck (ap₂ leNat (inc.comp (lengthNat.comp inputLeft)) (eight.comp inputQ))
    (ap₂ leNat (inc.comp (lengthNat.comp inputRight)) (eight.comp inputQ))

theorem guardCheck_iff (x : GuardInput) : guardCheck x = true ↔ GuardReady x := by
  simp only [guardCheck, andCheck_iff, ap₂_apply, comp_apply, pair_apply,
    leNat_apply, decide_eq_true_eq, DynamicParser.pairCheck_apply, fst_apply,
    sourceCheck_iff, inc_apply, lengthNat_apply, eight_apply, GuardReady, Nat.add_one_le_iff]

def projectedCall : PolyTimeFun GuardInput Data :=
  encoded.comp (inputIndex.pair
    ((DynamicParser.takeBits.comp ((fst.comp leftParts).pair inputDim)).pair
      ((DynamicParser.takeBits.comp ((fst.comp rightParts).pair inputDim)).pair
        ((snd.comp leftParts).pair (snd.comp rightParts)))))

theorem projectedCall_apply (x : GuardInput) : projectedCall x =
    encode (inputIndex x, (leftParts x).1.take (inputDim x),
      (rightParts x).1.take (inputDim x), (leftParts x).2, (rightParts x).2) := by
  simp [projectedCall, DynamicParser.takeBits_apply]

/-- All four original strings satisfy the internal original-game bound. -/
theorem GuardReady_cutoffs {x : GuardInput} (h : GuardReady x) :
    ((leftParts x).1.take (inputDim x)).length ≤ inputR x ∧
    ((rightParts x).1.take (inputDim x)).length ≤ inputR x ∧
    (leftParts x).2.length ≤ inputR x ∧ (rightParts x).2.length ≤ inputR x := by
  refine ⟨(List.length_take_le _ _).trans h.2.1, (List.length_take_le _ _).trans h.2.1, ?_, ?_⟩
  · simpa only [leftParts, comp_apply, pair_apply, DynamicParser.pairParts_apply] using h.2.2.1.2.2
  · simpa only [rightParts, comp_apply, pair_apply, DynamicParser.pairParts_apply] using h.2.2.2.1.2.2

/-- Projection produces questions of exactly the original sampler dimension. -/
theorem GuardReady_question_lengths {x : GuardInput} (h : GuardReady x) :
    ((leftParts x).1.take (inputDim x)).length = inputDim x ∧
    ((rightParts x).1.take (inputDim x)).length = inputDim x := by
  have hl : (leftParts x).1.length = inputQ x := by
    simpa only [leftParts,comp_apply,pair_apply,DynamicParser.pairParts_apply] using h.2.2.1.2.1
  have hr : (rightParts x).1.length = inputQ x := by
    simpa only [rightParts,comp_apply,pair_apply,DynamicParser.pairParts_apply] using h.2.2.2.1.2.1
  simp only [List.length_take,hl,hr,Nat.min_eq_left h.1,and_self]

/-- Both accepted register strings are the canonical zero-padded source questions. -/
theorem GuardReady_padding {x : GuardInput} (h : GuardReady x) :
    (leftParts x).1 = (leftParts x).1.take (inputDim x) ++
      List.replicate (inputQ x-inputDim x) false ∧
    (rightParts x).1 = (rightParts x).1.take (inputDim x) ++
      List.replicate (inputQ x-inputDim x) false := by
  have hl : (leftParts x).1.length = inputQ x := by
    simpa only [leftParts,comp_apply,pair_apply,DynamicParser.pairParts_apply] using h.2.2.1.2.1
  have hr : (rightParts x).1.length = inputQ x := by
    simpa only [rightParts,comp_apply,pair_apply,DynamicParser.pairParts_apply] using h.2.2.2.1.2.1
  exact ⟨InSource_padding hl h.2.2.2.2.1,InSource_padding hr h.2.2.2.2.2.1⟩

def readInput : PolyTimeFun Data GuardInput :=
  (readNat.comp treeHead).pair
    (((readNat.comp treeHead).comp treeTail).pair
      (((readNat.comp treeHead).comp (treeTail.comp treeTail)).pair
        (((readNat.comp treeHead).comp (treeTail.comp (treeTail.comp treeTail))).pair
          (((readBits.comp treeHead).comp (treeTail.comp (treeTail.comp (treeTail.comp treeTail)))).pair
            (readBits.comp (treeTail.comp (treeTail.comp (treeTail.comp (treeTail.comp treeTail)))))))))

@[simp] theorem readInput_encode (x : GuardInput) : readInput (encode x) = x := by
  rcases x with ⟨n,Q,R,s,a,b⟩
  simp [readInput, encode_prod, readNat_encode, readBits_encode]

def RawReady (x : Data) : Prop := x = encode (readInput x) ∧ GuardReady (readInput x)
instance (x : Data) : Decidable (RawReady x) := inferInstanceAs (Decidable (_ ∧ _))

def projectedRoute : PolyTimeFun Data (Bool × Data) :=
  let call := (const true).pair (ap₂ treePair (projectedCall.comp readInput) (const Data.nil))
  let reject := const (false, encode false)
  ite (ap₂ treeEq (PolyTimeFun.id Data) (encoded.comp readInput))
    (ite (guardCheck.comp readInput) call reject) reject

theorem projectedRoute_apply (x : Data) : projectedRoute x = if RawReady x then
    (true, .cons (projectedCall (readInput x)) .nil) else (false, encode false) := by
  simp only [projectedRoute, PolyTimeFun.ite_apply, ap₂_apply, comp_apply, id_apply,
    treeEq_apply, encoded_apply, pair_apply, const_apply, treePair_apply, decide_eq_true_eq]
  simp only [guardCheck_iff]
  by_cases hc : x = encode (readInput x)
  · rw [if_pos hc]
    by_cases hr : GuardReady (readInput x)
    · rw [if_pos hr, if_pos (show RawReady x from ⟨hc, hr⟩)]
    · rw [if_neg hr, if_neg (show ¬ RawReady x from fun h => hr h.2)]
  · rw [if_neg hc, if_neg (show ¬ RawReady x from fun h => hc h.1)]

def projectedProg (source : Prog) : Prog := routeOneCall projectedRoute source snd

theorem projectedProg_closed {source : Prog} (hs : source.WellScoped 1) :
    (projectedProg source).WellScoped 1 := routeOneCall_closed _ hs _

/-- Rejection evaluates no source code, even if that code diverges. -/
theorem projectedProg_reject (source : Prog) (x : Data) (h : ¬ RawReady x) :
    ∃ t, (projectedProg source).Runs x (encode false) t :=
  routeOneCall_direct _ _ _ _ _ (by rw [projectedRoute_apply, if_neg h])

theorem projectedProg_call {source : Prog} (hs : source.WellScoped 1) (x r : Data)
    (t : ℕ) (h : RawReady x) (hr : source.Runs (projectedCall (readInput x)) r t) :
    ∃ time, (projectedProg source).Runs x r time :=
  routeOneCall_indirect _ hs snd x _ .nil r t (by rw [projectedRoute_apply, if_pos h]) hr

theorem projectedProg_halts {source : Prog} (hs : source.WellScoped 1)
    (halts : ∀ x, Halts source x) (x : Data) : Halts (projectedProg source) x := by
  by_cases h : RawReady x
  · obtain ⟨r,t,hr⟩ := halts (projectedCall (readInput x))
    obtain ⟨time,ht⟩ := projectedProg_call hs x r t h hr
    exact ⟨r,time,ht⟩
  · obtain ⟨time,ht⟩ := projectedProg_reject source x h
    exact ⟨_,time,ht⟩

theorem projectedProg_accepts_iff {source : Prog} (hs : source.WellScoped 1)
    (halts : ∀ x, Halts source x) (x : Data) :
    (∃ t, (projectedProg source).Runs x (encode true) t) ↔
      RawReady x ∧ ∃ t, source.Runs (projectedCall (readInput x)) (encode true) t := by
  by_cases h : RawReady x
  · obtain ⟨r,t,hr⟩ := halts (projectedCall (readInput x))
    obtain ⟨time,ht⟩ := projectedProg_call hs x r t h hr
    constructor
    · rintro ⟨ta,ha⟩
      exact ⟨h,t,(ht.deterministic ha).1 ▸ hr⟩
    · rintro ⟨_,ta,ha⟩
      exact ⟨time,(hr.deterministic ha).1 ▸ ht⟩
  · obtain ⟨time,ht⟩ := projectedProg_reject source x h
    constructor
    · rintro ⟨ta,ha⟩
      cases encode_injective (ht.deterministic ha).1
    · rintro ⟨ha,_⟩
      exact (h ha).elim

end MIPRE.Introspection.SourceCompiler

end
