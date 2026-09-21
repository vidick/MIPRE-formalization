/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.CL.DetypingDeciderRoute

/-! # The paper's binary tuple encoding

These are binary strings inside answers, distinct from ambient `Data` encodings.
Each payload bit `b` is written `false,b`; each field ends in `true,false`.
The polynomial-time candidate reader is deliberately permissive. The answer
parser checks exact re-encoding before using any candidate.
-/

noncomputable section

namespace MIPRE.Introspection.AnswerParser

open Cost Cost.PolyTimeFun Polynomial

def doubleBits : BitStr → BitStr
  | [] => []
  | b :: bs => false :: b :: doubleBits bs

def field (bs : BitStr) : BitStr := doubleBits bs ++ [true, false]

@[simp] theorem doubleBits_length (bs : BitStr) :
    (doubleBits bs).length = 2 * bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [doubleBits, ih]; omega

@[simp] theorem field_length (bs : BitStr) : (field bs).length = 2 * bs.length + 2 := by
  simp [field]

/-- A field terminator distinguishes its endpoint from every encoded payload bit. -/
theorem field_append_injective (a b c d : BitStr)
    (h : field a ++ c = field b ++ d) : a = b ∧ c = d := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simpa [field, doubleBits] using h
    | cons bit bs => simp [field, doubleBits] at h
  | cons bit as ih =>
    cases b with
    | nil => simp [field, doubleBits] at h
    | cons bit' bs =>
      simp only [field, doubleBits, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨hab, hcd⟩ := ih bs h.2
      exact ⟨by rw [h.1, hab], hcd⟩

private def doubleStep : PolyTimeFun (BitStr × Bool) BitStr :=
  cons snd (cons (const false) fst)

private theorem doubleStep_size (s : BitStr) (b : Bool) :
    esize (doubleStep (s, b)) ≤ esize s + (C 6).eval (esize b) := by
  cases b <;> simp [doubleStep] <;> omega

private theorem double_fold (bs acc : BitStr) :
    (bs.foldl (fun s b => doubleStep (s, b)) acc).reverse =
      acc.reverse ++ doubleBits bs := by
  induction bs generalizing acc with
  | nil => simp [doubleBits]
  | cons b bs ih =>
    rw [List.foldl_cons, ih]
    simp [doubleStep, doubleBits, List.append_assoc]

/-- An actual ambient polynomial-time implementation of bit doubling. -/
def doubleProg : PolyTimeFun BitStr BitStr :=
  congr (reverse.comp ((foldlAdd doubleStep (C 6) doubleStep_size).comp
    ((PolyTimeFun.id BitStr).pair (const [])))) doubleBits (by
      intro bs
      simpa using double_fold bs [])

@[simp] theorem doubleProg_apply (bs : BitStr) : doubleProg bs = doubleBits bs := rfl

def fieldProg : PolyTimeFun BitStr BitStr :=
  ap₂ append doubleProg (const [true, false])

@[simp] theorem fieldProg_apply (bs : BitStr) : fieldProg bs = field bs := rfl

private def readStepFun (s : Bool × BitStr) (b : Bool) : Bool × BitStr :=
  if s.1 then (false, b :: s.2) else (true, s.2)

private def readStep : PolyTimeFun ((Bool × BitStr) × Bool) (Bool × BitStr) :=
  PolyTimeFun.ite (fst.comp fst)
    ((const false).pair (cons snd (snd.comp fst)))
    ((const true).pair (snd.comp fst))

private theorem readStep_apply (s : Bool × BitStr) (b : Bool) :
    readStep (s, b) = readStepFun s b := by
  rcases s with ⟨p, bs⟩
  cases p <;> simp [readStep, readStepFun, PolyTimeFun.ite_apply]

private theorem readStep_size (s : Bool × BitStr) (b : Bool) :
    esize (readStep (s, b)) ≤ esize s + (C 6).eval (esize b) := by
  rcases s with ⟨p, bs⟩
  cases p <;> cases b <;>
    simp [readStep_apply, readStepFun, esize_prod] <;> omega

/-- Read the second bit of each pair, discarding a trailing unmatched bit. -/
def undouble (bs : BitStr) : BitStr :=
  (bs.foldl readStepFun (false, [])).2.reverse

private theorem read_double_fold (bs acc : BitStr) :
    (doubleBits bs).foldl readStepFun (false, acc) = (false, bs.reverse ++ acc) := by
  induction bs generalizing acc with
  | nil => simp [doubleBits]
  | cons b bs ih => simp [doubleBits, List.foldl_cons, readStepFun, ih, List.append_assoc]

@[simp] theorem undouble_doubleBits (bs : BitStr) : undouble (doubleBits bs) = bs := by
  simp [undouble, read_double_fold]

def undoubleProg : PolyTimeFun BitStr BitStr :=
  congr (reverse.comp (snd.comp ((foldlAdd readStep (C 6) readStep_size).comp
    ((PolyTimeFun.id BitStr).pair (const (false, [])))))) undouble (by
      intro bs
      simp [undouble, readStep_apply])

@[simp] theorem undoubleProg_apply (bs : BitStr) : undoubleProg bs = undouble bs := rfl

/-- Candidate payload obtained by removing the presumed last delimiter pair. -/
def payload (bs : BitStr) : BitStr := undouble (bs.take (bs.length - 2))

def payloadProg : PolyTimeFun BitStr BitStr :=
  undoubleProg.comp (ap₂ take (PolyTimeFun.id BitStr)
    (length.comp (ap₂ drop (PolyTimeFun.id BitStr) (const (unary 2)))))

@[simp] theorem payloadProg_apply (bs : BitStr) : payloadProg bs = payload bs := by
  simp [payloadProg, payload]

@[simp] theorem payload_field (bs : BitStr) : payload (field bs) = bs := by
  simp only [payload, field_length, Nat.add_sub_cancel]
  rw [← doubleBits_length, field, List.take_left]
  exact undouble_doubleBits bs

end MIPRE.Introspection.AnswerParser

end
