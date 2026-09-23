/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.DecisionKernelAnswers
import MIPRE.Background.Introspection.DecisionCompilerCutoff
import MIPRE.Foundations.Introspection.AuxiliaryDecisionCompleteness

/-! # Encoding finite honest answers for the actual decision kernel -/

noncomputable section
namespace MIPRE.Introspection.DecisionKernel.Answer
open Cost SAT
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- Forget only the finite source-answer bound and encode the Pauli payload.
All three full-register auxiliary formats retain their exact coordinates. -/
def toRaw {k m Q R : ℕ} (E : BinField k)
    (a : ParsedAnswer (Fin Q → CL.𝔽₂) (Verifier.Answers R) (QLD.Answer E.carrier m 1)) :
    ParsedAnswer (Fin Q → CL.𝔽₂) BitStr BitStr :=
  ParsedAnswer.mapPauli (fun _ => QLD.PauliAnswerProgram.answerBits E)
    (Sum.inl (QLD.Ty.pauli .X) : Label) (ParsedAnswer.mapAnswer Subtype.val a)

def bits {k m Q R : ℕ} (E : BinField k)
    (a : ParsedAnswer (Fin Q → CL.𝔽₂) (Verifier.Answers R) (QLD.Answer E.carrier m 1)) : BitStr :=
  AuxiliaryAnswer.bits (toRaw E a)

@[simp] theorem toRaw_pauli {k m Q R : ℕ} (E : BinField k) (a : QLD.Answer E.carrier m 1) :
    toRaw (Q := Q) (R := R) E (.pauli a) = .pauli (QLD.PauliAnswerProgram.answerBits E a) := rfl

theorem toRaw_eq_map {k m Q R : ℕ} (E : BinField k) (T : Label)
    (a : ParsedAnswer (Fin Q → CL.𝔽₂) (Verifier.Answers R) (QLD.Answer E.carrier m 1)) :
    toRaw E a = ParsedAnswer.mapPauli (fun _ => QLD.PauliAnswerProgram.answerBits E) T
      (ParsedAnswer.mapAnswer Subtype.val a) := by cases a <;> rfl

/-- Pauli format is the actual question's finite answer constructor condition. -/
def PauliFormatted (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k) (j Q R : ℕ)
    (T : Label) (x : BitStr)
    (a : ParsedAnswer (Fin Q → CL.𝔽₂) (Verifier.Answers R)
      (QLD.Answer (shoupBinField k hk).carrier (2^j) 1)) : Prop :=
  ∀ t c, T = .inl t → a = .pauli c →
    (QLD.PauliBinaryProgram.questionOfBits k hk hodd j t x).fmtOk c = true

theorem parser_answerBits {k m : ℕ} (E : BinField k) (hk : 1 ≤ k)
    (q : QLD.Question E.carrier m) (a : QLD.Answer E.carrier m 1)
    (ha : q.fmtOk a = true) :
    (QLD.PauliAnswerProgram.parser
      (q.ty,unary m,unary k,unary 1,QLD.PauliAnswerProgram.answerBits E a)).1 = true := by
  rw [QLD.PauliAnswerProgram.parser_answerBits E hk q a ha]

theorem rawProject_answerBits (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (j m : ℕ) (W : QLD.Bas) (q : QLD.Question (shoupBinField k hk).carrier m)
    (a : QLD.Answer (shoupBinField k hk).carrier m 1)
    (hq : q.ty = .pauli W) (ha : q.fmtOk a = true) :
    rawProject (unary k,unary j,unary m) (2^m*k)
      (QLD.PauliAnswerProgram.answerBits (shoupBinField k hk) a) =
      pauliProject (shoupSelfDualNormalBasis k hk hodd) a := by
  have hv := parser_answerBits (shoupBinField k hk) hk q a ha
  rw [hq] at hv
  rw [rawProject_pauliDecode k hk hodd j m W _ hv]
  simp only [pauliDecode, pauliLabel]
  rw [← hq, QLD.PauliAnswerProgram.decodeBits_answerBits (shoupBinField k hk) hk q a ha]

@[simp] theorem fits_toRaw {k m Q R : ℕ} (E : BinField k) (T : Label)
    (a : ParsedAnswer (Fin Q → CL.𝔽₂) (Verifier.Answers R) (QLD.Answer E.carrier m 1)) :
    TypedPredicate.fits T (toRaw E a) = TypedPredicate.fits T a := by
  rcases T with p | ⟨t,w⟩
  · cases a <;> rfl
  · cases t <;> cases a <;> rfl

theorem answerBound_toRaw {k m Q R : ℕ} (E : BinField k)
    (a : ParsedAnswer (Fin Q → CL.𝔽₂) (Verifier.Answers R) (QLD.Answer E.carrier m 1)) :
    AuxiliaryDecision.answerBound R (toRaw E a) := by
  cases a with
  | pauli a | hide y yp x => trivial
  | pair y a | read y yp a => exact a.property

theorem prefixGuard_toRaw {k m Q R : ℕ} (E : BinField k)
    (L : Bool → CL.CLFun CL.𝔽₂ (Fin Q) 7) (T : Label)
    (a : ParsedAnswer (Fin Q → CL.𝔽₂) (Verifier.Answers R) (QLD.Answer E.carrier m 1)) :
    PrefixGuard.holds L T (toRaw E a) ↔ PrefixGuard.holds L T a := by
  rcases T with p | ⟨t,w⟩
  · cases a <;> rfl
  · cases t <;> cases a <;> rfl

theorem valid_bits {k m Q R : ℕ} (E : BinField k) (T : Label)
    (a : ParsedAnswer (Fin Q → CL.𝔽₂) (Verifier.Answers R) (QLD.Answer E.carrier m 1))
    (ha : TypedPredicate.fits T a = true) : AuxiliaryAnswer.Valid Q R T (bits E a) :=
  AuxiliaryDecision.valid_bits T (toRaw E a) (by simpa using ha) (answerBound_toRaw E a)

private theorem flatten_vecBits_length {k m : ℕ} (E : BinField k) (v : Fin m → E.carrier) :
    (E.vecBits v).flatten.length = m*k := by
  have hf (rows : List BitStr) (h : ∀ row ∈ rows, row.length = k) :
      rows.flatten.length = rows.length*k := by
    induction rows with
    | nil => simp
    | cons row rows ih =>
      rw [List.flatten_cons, List.length_append, h row (by simp),
        ih (fun x hx => h x (by simp [hx])), List.length_cons]
      ring
  simpa only [E.length_vecBits] using hf (E.vecBits v) (fun row hr => E.width_vecBits v hr)

/-- All semantic Pauli constructors have short encodings at degree one,
including constructors excluded by the eventual question format. -/
theorem pauliBits_length_le {k m : ℕ} (E : BinField k) (hm : 1 ≤ m)
    (hQ : 3 ≤ 2^m*k) (a : QLD.Answer E.carrier m 1) :
    (QLD.PauliAnswerProgram.answerBits E a).length ≤ 2^m*k := by
  have hp : m+1 ≤ 2^m := Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := m))
  have h2 : 2 ≤ (2 : ℕ)^m :=
    Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hm
  have h1 : 1 ≤ (2 : ℕ)^m := Nat.one_le_pow _ _ (by decide)
  cases a with
  | val a =>
    simpa only [QLD.PauliAnswerProgram.answerBits, QLD.PauliAnswerProgram.answerRows,
      List.flatten_cons, List.flatten_nil, List.append_nil, E.length_toBits, one_mul] using
      Nat.mul_le_mul_right k h1
  | apoly a =>
    simpa only [QLD.PauliAnswerProgram.answerBits, QLD.PauliAnswerProgram.answerRows,
      flatten_vecBits_length] using Nat.mul_le_mul_right k h2
  | dpoly a =>
    simpa only [QLD.PauliAnswerProgram.answerBits, QLD.PauliAnswerProgram.answerRows,
      flatten_vecBits_length, mul_one] using Nat.mul_le_mul_right k hp
  | pauliAns a =>
    simp only [QLD.PauliAnswerProgram.answerBits, QLD.PauliAnswerProgram.answerRows,
      flatten_vecBits_length, le_refl]
  | bit a => simpa [QLD.PauliAnswerProgram.answerBits, QLD.PauliAnswerProgram.answerRows] using
      (show 1 ≤ 2^m*k by omega)
  | bitPair a => simpa [QLD.PauliAnswerProgram.answerBits, QLD.PauliAnswerProgram.answerRows] using
      (show 2 ≤ 2^m*k by omega)
  | bitTriple a =>
    simpa [QLD.PauliAnswerProgram.answerBits, QLD.PauliAnswerProgram.answerRows,
      List.ofFn_succ] using hQ

/-- Every finite honest answer lies below the actual compiler's outer cutoff. -/
theorem bits_length_le_cutoff {k m R : ℕ} (E : BinField k) (hm : 1 ≤ m)
    (hQ : 4 ≤ 2^m*k) (hR : 3*R ≤ 2^m*k)
    (a : ParsedAnswer (Fin (2^m*k) → CL.𝔽₂) (Verifier.Answers R) (QLD.Answer E.carrier m 1)) :
    (bits E a).length ≤ DecisionCompiler.answerBound (2^m*k) R := by
  have hcut : 8*(2^m*k) ≤ DecisionCompiler.answerBound (2^m*k) R := by
    unfold DecisionCompiler.answerBound
    exact Nat.mul_le_mul_left 8 ((le_max_left _ _).trans (le_max_right _ _))
  apply le_trans _ hcut
  cases a with
  | pauli a => exact (pauliBits_length_le E hm (by omega) a).trans (by omega)
  | pair y a =>
    change (AnswerParser.pairBits (CL.toBits y) a.val).length ≤ _
    exact (AnswerParser.pairBits_lt_outer _ _ hQ hR _ _ (CL.length_toBits _) a.property).le
  | read y yp a =>
    change (AnswerParser.tripleBits (CL.toBits y) (CL.toBits yp) a.val).length ≤ _
    exact (AnswerParser.readBits_lt_outer _ _ hQ hR _ _ _
      (CL.length_toBits _) (CL.length_toBits _) a.property).le
  | hide y yp x =>
    change (AnswerParser.tripleBits (CL.toBits y) (CL.toBits yp) (CL.toBits x)).length ≤ _
    exact (AnswerParser.hideBits_lt_outer _ hQ _ _ _
      (CL.length_toBits _) (CL.length_toBits _) (CL.length_toBits _)).le

end MIPRE.Introspection.DecisionKernel.Answer
end
