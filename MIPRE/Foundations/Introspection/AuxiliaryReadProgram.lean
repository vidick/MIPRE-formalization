/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.SourceCompilerGuard
import MIPRE.Foundations.Introspection.TypedPredicate

/-! # Executable full-register Introspect/Read comparison

The binary register length and original answer cutoff are input data. All
register fields have the full padded length. In particular the Read dual
answer is not required to vanish outside the original source register: the
same-depth padding puts those coordinates in the first zero-map factor.
The program checks canonical tuple syntax, the separate original answer
cutoff, and the strict outer cutoff before comparing the two relevant fields.
-/

noncomputable section
namespace MIPRE.Introspection.AuxiliaryProgram

open Cost Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
open SourceCompiler (GuardInput inputQ inputR inputLeft inputRight leftParts rightParts readInput)

def andCheck {α : Type*} [SizedEncoding α] (f g : PolyTimeFun α Bool) :
    PolyTimeFun α Bool := ite f g (const false)

theorem andCheck_iff {α : Type*} [SizedEncoding α] (f g : PolyTimeFun α Bool) (x : α) :
    andCheck f g x = true ↔ f x = true ∧ g x = true := by
  simp only [andCheck, PolyTimeFun.ite_apply, const_apply]
  cases f x <;> simp

def equal {α : Type*} [SizedEncoding α] {β : Type*} [SizedEncoding β]
    (f g : PolyTimeFun α β) : PolyTimeFun α Bool :=
  ap₂ treeEq (encoded.comp f) (encoded.comp g)

theorem equal_iff {α : Type*} [SizedEncoding α] {β : Type*} [SizedEncoding β]
    (f g : PolyTimeFun α β) (x : α) : equal f g x = true ↔ f x = g x := by
  simp only [equal, ap₂_apply, comp_apply, encoded_apply, treeEq_apply,
    decide_eq_true_eq, encode_injective.eq_iff]

def leftTriple : PolyTimeFun GuardInput (BitStr × BitStr × BitStr) :=
  DynamicParser.tripleParts.comp (inputLeft.pair inputQ)

def rightTriple : PolyTimeFun GuardInput (BitStr × BitStr × BitStr) :=
  DynamicParser.tripleParts.comp (inputRight.pair inputQ)

def outerCheck : PolyTimeFun GuardInput Bool :=
  andCheck (ap₂ leNat (inc.comp (lengthNat.comp inputLeft)) (SourceCompiler.eight.comp inputQ))
    (ap₂ leNat (inc.comp (lengthNat.comp inputRight)) (SourceCompiler.eight.comp inputQ))

theorem outerCheck_iff (x : GuardInput) : outerCheck x = true ↔
    (inputLeft x).length < 8 * inputQ x ∧ (inputRight x).length < 8 * inputQ x := by
  simp only [outerCheck, andCheck_iff, ap₂_apply, comp_apply, leNat_apply,
    decide_eq_true_eq, inc_apply, lengthNat_apply, SourceCompiler.eight_apply,
    Nat.add_one_le_iff]

/-- Full-Q pair format, including the original answer cutoff. -/
def pairLeft : PolyTimeFun GuardInput Bool :=
  DynamicParser.pairCheck.comp (inputLeft.pair (inputQ.pair inputR))

def pairRight : PolyTimeFun GuardInput Bool :=
  DynamicParser.pairCheck.comp (inputRight.pair (inputQ.pair inputR))

/-- Full-Q Read format: there is deliberately no original-subspace test on the dual field. -/
def readRight : PolyTimeFun GuardInput Bool :=
  (DynamicParser.tripleCheck false).comp (inputRight.pair (inputQ.pair inputR))

def hideLeft : PolyTimeFun GuardInput Bool :=
  (DynamicParser.tripleCheck true).comp (inputLeft.pair (inputQ.pair inputQ))

def hideRight : PolyTimeFun GuardInput Bool :=
  (DynamicParser.tripleCheck true).comp (inputRight.pair (inputQ.pair inputQ))

/-- The actual Introspect/Read branch, with all bounds supplied in binary. -/
def readingCheck : PolyTimeFun GuardInput Bool :=
  andCheck outerCheck <| andCheck pairLeft <| andCheck readRight <|
    andCheck (equal (fst.comp leftParts) (fst.comp rightTriple))
      (equal (snd.comp leftParts) (snd.comp (snd.comp rightTriple)))

theorem readingCheck_iff (x : GuardInput) : readingCheck x = true ↔
    (inputLeft x).length < 8 * inputQ x ∧ (inputRight x).length < 8 * inputQ x ∧
    AnswerParser.pairValid (inputQ x) (inputR x) (inputLeft x) ∧
    AnswerParser.tripleValid (inputQ x) (inputR x) false (inputRight x) ∧
    (leftParts x).1 = (rightTriple x).1 ∧ (leftParts x).2 = (rightTriple x).2.2 := by
  simp only [readingCheck, andCheck_iff, outerCheck_iff, pairLeft, readRight,
    comp_apply, pair_apply, DynamicParser.pairCheck_apply, DynamicParser.tripleCheck_apply,
    decide_eq_true_eq, equal_iff, fst_apply, snd_apply, and_assoc]

theorem toBits_injective {Q : ℕ} : Function.Injective (@CL.toBits Q) := by
  intro x y h
  simpa only [CL.ofBits_toBits] using congrArg (CL.ofBits Q) h

/-- Exact acceptance on full-register parsed answers, including arbitrary dual labels. -/
theorem readingCheck_vectors {Q R : ℕ} (hQ : 4 ≤ Q) (hR : 3 * R ≤ Q)
    (n s : ℕ) (y z zp : Fin Q → CL.𝔽₂) (a b : BitStr) :
    readingCheck (n,Q,R,s,AnswerParser.pairBits (CL.toBits y) a,
      AnswerParser.tripleBits (CL.toBits z) (CL.toBits zp) b) = true ↔
      a.length ≤ R ∧ b.length ≤ R ∧ CLChecks.reading (y,a) (z,zp,b) := by
  have hpair := AnswerParser.pairCheck_pairBits Q R (CL.toBits y) a
  have hread := AnswerParser.tripleCheck_tripleBits Q R false (CL.toBits z) (CL.toBits zp) b
  rw [AnswerParser.pairCheck_apply] at hpair
  rw [AnswerParser.tripleCheck_apply] at hread
  simp only [decide_eq_true_eq, CL.length_toBits, true_and,
    Bool.false_eq_true, if_false] at hpair hread
  rw [readingCheck_iff]
  simp only [SourceCompiler.inputQ, SourceCompiler.inputR, SourceCompiler.inputLeft,
    SourceCompiler.inputRight, SourceCompiler.leftParts, rightTriple,
    comp_apply, pair_apply, fst_apply, snd_apply, DynamicParser.pairParts_apply,
    DynamicParser.tripleParts_apply, AnswerParser.pairParts_pairBits _ _ _ (CL.length_toBits _),
    AnswerParser.tripleParts_tripleBits _ _ _ _ (CL.length_toBits _) (CL.length_toBits _),
    hpair, hread, toBits_injective.eq_iff, CLChecks.reading]
  constructor
  · rintro ⟨_,_,ha,hb,he⟩
    exact ⟨ha,hb,he⟩
  · rintro ⟨ha,hb,he⟩
    exact ⟨AnswerParser.pairBits_lt_outer Q R hQ hR _ _ (CL.length_toBits _) ha,
      AnswerParser.readBits_lt_outer Q R hQ hR _ _ _ (CL.length_toBits _) (CL.length_toBits _) hb,
      ha,hb,he⟩

/-- Reject arbitrary noncanonical input trees before running the supplied pure check. -/
def rawCheck (check : PolyTimeFun GuardInput Bool) : PolyTimeFun Data Bool :=
  andCheck (equal (PolyTimeFun.id Data) (encoded.comp readInput)) (check.comp readInput)

theorem rawCheck_iff (check : PolyTimeFun GuardInput Bool) (x : Data) :
    rawCheck check x = true ↔ x = encode (readInput x) ∧ check (readInput x) = true := by
  simp only [rawCheck, andCheck_iff, equal_iff, id_apply, comp_apply, encoded_apply]

@[simp] theorem rawCheck_encode (check : PolyTimeFun GuardInput Bool) (x : GuardInput) :
    rawCheck check (encode x) = check x := by
  simp [rawCheck, andCheck, equal, SourceCompiler.readInput_encode]

/-- Total runtime on every raw tree, independently of source-program termination. -/
theorem rawCheck_haltsWithin (check : PolyTimeFun GuardInput Bool) (x : Data) :
    HaltsWithin (rawCheck check).code x ((rawCheck check).timeBound.eval x.size) := by
  obtain ⟨t,ht,hr⟩ := (rawCheck check).computes x
  exact ⟨_,t,ht,hr⟩

theorem readingCheck_typed {PauliType PauliAnswer : Type*} {Q R ℓ : ℕ}
    (L : Bool → CL.CLFun CL.𝔽₂ (Fin Q) ℓ) (X Z : PauliType)
    (projectPauli : PauliAnswer → Fin Q → CL.𝔽₂)
    (D : (Fin Q → CL.𝔽₂) → (Fin Q → CL.𝔽₂) → BitStr → BitStr → Bool)
    (DP : PauliType → PauliType → PauliAnswer → PauliAnswer → Bool)
    (hQ : 4 ≤ Q) (hR : 3*R ≤ Q) (n s : ℕ) (w : Bool)
    (y z zp : Fin Q → CL.𝔽₂) (a b : BitStr) :
    readingCheck (n,Q,R,s,AnswerParser.pairBits (CL.toBits y) a,
      AnswerParser.tripleBits (CL.toBits z) (CL.toBits zp) b) = true ↔
      a.length ≤ R ∧ b.length ≤ R ∧
      TypedPredicate.check L X Z projectPauli D DP (.inr (.introspect,w))
        (.inr (.read,w)) (.pair y a) (.read z zp b) = true := by
  classical
  rw [readingCheck_vectors hQ hR]
  simp [TypedPredicate.check,TypedPredicate.fits,TypedPredicate.directed]

end MIPRE.Introspection.AuxiliaryProgram
end
