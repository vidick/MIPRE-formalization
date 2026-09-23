/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Cost.FiniteChoice
import MIPRE.Foundations.Cost.FiniteEncoding
import MIPRE.Foundations.Introspection.ClockedSourceChecks
import MIPRE.Foundations.Introspection.AuxiliaryHidingNextProgram
import MIPRE.Foundations.Introspection.AuxiliaryHidingBoundaryProgram
import MIPRE.Foundations.Introspection.SourcePaddingQueryProg
import MIPRE.Foundations.Introspection.Types

/-! # The uniform auxiliary decision kernel

The finite type labels choose programs, including the fixed-depth hiding
scans. Source descriptions, the shared unary clock, dimensions and answer
bytes remain runtime data. Pauli arithmetic and conversion are supplied by
their separately verified uniform programs.
-/

noncomputable section
namespace MIPRE.Introspection.AuxiliaryDecision
open Cost Cost.PolyTimeFun AuxiliaryProgram CL.Detyping.Program
variable {P : Type*} [Fintype P] [DecidableEq P] [SizedEncoding P] {ℓ : ℕ}

abbrev Endpoint (P : Type*) (ℓ : ℕ) := QuestionType P ℓ × BitStr
abbrev Parameters := Unary × Unary × Unary
abbrev Bounds := (ℕ × ℕ × ℕ × Prog) × Parameters
abbrev Input (P : Type*) (ℓ : ℕ) :=
  (AuxiliarySource.Context × Bounds) × Endpoint P ℓ × Endpoint P ℓ

def context : PolyTimeFun (Input P ℓ) AuxiliarySource.Context := fst.comp fst
def bounds : PolyTimeFun (Input P ℓ) (ℕ × ℕ × ℕ × Prog) := fst.comp (snd.comp fst)
def pauliParameters : PolyTimeFun (Input P ℓ) Parameters := snd.comp (snd.comp fst)
def width : PolyTimeFun (Input P ℓ) ℕ := fst.comp bounds
def originalBound : PolyTimeFun (Input P ℓ) ℕ := fst.comp (snd.comp bounds)
def sourceDim : PolyTimeFun (Input P ℓ) ℕ := fst.comp (snd.comp (snd.comp bounds))
def sourceDecider : PolyTimeFun (Input P ℓ) Prog := snd.comp (snd.comp (snd.comp bounds))
def left : PolyTimeFun (Input P ℓ) (Endpoint P ℓ) := fst.comp snd
def right : PolyTimeFun (Input P ℓ) (Endpoint P ℓ) := snd.comp snd
def leftType : PolyTimeFun (Input P ℓ) (QuestionType P ℓ) := fst.comp left
def rightType : PolyTimeFun (Input P ℓ) (QuestionType P ℓ) := fst.comp right
def leftBits : PolyTimeFun (Input P ℓ) BitStr := snd.comp left
def rightBits : PolyTimeFun (Input P ℓ) BitStr := snd.comp right
def swap : PolyTimeFun (Input P ℓ) (Input P ℓ) := fst.pair (right.pair left)

omit [Fintype P] [DecidableEq P] in
@[simp] theorem swap_apply (ctx : AuxiliarySource.Context) (b : Bounds)
    (a d : Endpoint P ℓ) : swap ((ctx,b),a,d) = ((ctx,b),d,a) := rfl

def leftPair : PolyTimeFun (Input P ℓ) (BitStr × BitStr) :=
  DynamicParser.pairParts.comp (leftBits.pair width)
def rightPair : PolyTimeFun (Input P ℓ) (BitStr × BitStr) :=
  DynamicParser.pairParts.comp (rightBits.pair width)
def leftTriple : PolyTimeFun (Input P ℓ) (BitStr × BitStr × BitStr) :=
  DynamicParser.tripleParts.comp (leftBits.pair width)
def rightTriple : PolyTimeFun (Input P ℓ) (BitStr × BitStr × BitStr) :=
  DynamicParser.tripleParts.comp (rightBits.pair width)

/-- Pauli format validation is delegated to its field-aware parser. -/
def formatKind : QuestionType P ℓ → Fin 4
  | .inl _ => 0
  | .inr (.introspect, _) | .inr (.sample, _) => 1
  | .inr (.read, _) => 2
  | .inr (.hide _, _) => 3

def formatBranch (tag : Fin 4) : PolyTimeFun (Input P ℓ) Bool :=
  match tag.val with
  | 0 => const true
  | 1 => DynamicParser.pairCheck.comp (leftBits.pair (width.pair originalBound))
  | 2 => (DynamicParser.tripleCheck false).comp (leftBits.pair (width.pair originalBound))
  | _ => (DynamicParser.tripleCheck true).comp (leftBits.pair (width.pair width))

def format : PolyTimeFun (Input P ℓ) Bool :=
  choose ((finiteFunction formatKind).comp leftType) formatBranch (const false)

omit [DecidableEq P] in
theorem format_apply (x : Input P ℓ) :
    format x = match leftType x with
      | .inl _ => true
      | .inr (.introspect, _) | .inr (.sample, _) =>
          decide (AnswerParser.pairValid (width x) (originalBound x) (leftBits x))
      | .inr (.read, _) =>
          decide (AnswerParser.tripleValid (width x) (originalBound x) false (leftBits x))
      | .inr (.hide _, _) =>
          decide (AnswerParser.tripleValid (width x) (width x) true (leftBits x)) := by
  simp only [format, choose_apply, comp_apply, finiteFunction_apply]
  rcases ht : leftType x with p | ⟨t,w⟩
  · rfl
  · cases t <;> simp [formatKind, formatBranch, DynamicParser.pairCheck_apply,
      DynamicParser.tripleCheck_apply]

/-- Replace the player's role while retaining the common clock and source. -/
def contextWith (role : PolyTimeFun (Input P ℓ) Bool) :
    PolyTimeFun (Input P ℓ) AuxiliarySource.Context :=
  (AuxiliarySource.budget.comp context).pair ((AuxiliarySource.source.comp context).pair
    ((AuxiliarySource.index.comp context).pair (role.pair
      ((AuxiliarySource.level.comp context).pair (AuxiliarySource.inputPrefix.comp context)))))

def guardFields : PolyTimeFun (Input P ℓ) SourceCompiler.GuardInput :=
  (AuxiliarySource.index.comp context).pair (width.pair (originalBound.pair
    (sourceDim.pair (leftBits.pair rightBits))))

/-- Each directed auxiliary edge has one rule, a role and an optional hiding level. -/
def route (X Z : P) : QuestionType P ℓ × QuestionType P ℓ → Fin 8 × Bool × Option (Fin ℓ)
  | (.inl p, .inr (.sample, w)) => if p = Z then (0,w,none) else (7,w,none)
  | (.inr (.introspect,w), .inr (.sample,v)) => if w = v then (1,w,none) else (7,w,none)
  | (.inr (.introspect,w), .inr (.read,v)) => if w = v then (2,w,none) else (7,w,none)
  | (.inr (.hide k,w), .inr (.read,v)) =>
      if w = v ∧ k.val + 1 = ℓ then (3,w,none) else (7,w,none)
  | (.inr (.hide k,w), .inr (.hide j,v)) =>
      if w = v ∧ k.val + 1 = j.val then (4,w,some k) else (7,w,none)
  | (.inl p, .inr (.hide k,w)) => if p = X ∧ k.val = 0 then (5,w,none) else (7,w,none)
  | (.inr (.introspect,false), .inr (.introspect,true)) => (6,false,none)
  | _ => (7,false,none)

def metadata (X Z : P) : PolyTimeFun (Input P ℓ) (Fin 8 × Bool × Option (Fin ℓ)) :=
  (finiteFunction (route X Z)).comp (leftType.pair rightType)

def sourceContext (X Z : P) : PolyTimeFun (Input P ℓ) AuxiliarySource.Context :=
  contextWith (fst.comp (snd.comp (metadata X Z)))

def nextBranch (U : ClockedUniversalMachine) (X Z : P) (k : Option (Fin ℓ)) :
    PolyTimeFun (Input P ℓ) Bool :=
  match k with
  | none => const true
  | some k => (AuxiliaryHiding.check (SourcePadding.Program.factorFromContext U)
      (SourcePadding.Program.matrixFromContext U) k.val).comp
        ((sourceContext X Z).pair (leftTriple.pair rightTriple))

def branch (U : ClockedUniversalMachine) (X Z : P)
    (project : PolyTimeFun (Input P ℓ) BitStr) (tag : Fin 8) : PolyTimeFun (Input P ℓ) Bool :=
  match tag.val with
  | 0 => equal project (fst.comp rightPair)
  | 1 => (ClockedSourceChecks.sampling U).comp
      ((AuxiliarySource.budget.comp context).pair ((AuxiliarySource.source.comp context).pair
        ((const ℓ).pair ((fst.comp (snd.comp (metadata X Z))).pair guardFields))))
  | 2 => readingCheck.comp guardFields
  | 3 => (AuxiliaryBoundary.last (SourcePadding.Program.factorFromContext U)
      (SourcePadding.Program.matrixFromContext U) ℓ).comp
        ((sourceContext X Z).pair (leftTriple.pair
          ((fst.comp rightTriple).pair (fst.comp (snd.comp rightTriple)))))
  | 4 => choose (snd.comp (snd.comp (metadata X Z))) (nextBranch U X Z) (const true)
  | 5 => (AuxiliaryBoundary.first (SourcePadding.Program.factorFromContext U)
      (SourcePadding.Program.matrixFromContext U)).comp
        ((sourceContext X Z).pair (project.pair rightTriple))
  | 6 => (ClockedSourceChecks.cross U).comp
      ((AuxiliarySource.budget.comp context).pair (sourceDecider.pair guardFields))
  | _ => const true

/-- The complete directed auxiliary program, including the source game call. -/
def directed (U : ClockedUniversalMachine) (X Z : P)
    (project : PolyTimeFun (Input P ℓ) BitStr) : PolyTimeFun (Input P ℓ) Bool :=
  choose (fst.comp (metadata X Z)) (branch U X Z project) (const true)

theorem directed_apply (U : ClockedUniversalMachine) (X Z : P)
    (project : PolyTimeFun (Input P ℓ) BitStr) (x : Input P ℓ) :
    directed U X Z project x = branch U X Z project (route X Z (leftType x,rightType x)).1 x := by
  simp only [directed, choose_apply, comp_apply, fst_apply, metadata, finiteFunction_apply,
    pair_apply]

/-- Both orientations and exact same-type byte consistency are checked.
The Pauli predicate and its format checks are conjoined by the caller. -/
def check (U : ClockedUniversalMachine) (X Z : P)
    (project : PolyTimeFun (Input P ℓ) BitStr) : PolyTimeFun (Input P ℓ) Bool :=
  andCheck format (andCheck (format.comp swap)
    (andCheck (ite (equal leftType rightType) (equal leftBits rightBits) (const true))
      (andCheck (directed U X Z project) ((directed U X Z project).comp swap))))

theorem check_iff (U : ClockedUniversalMachine) (X Z : P)
    (project : PolyTimeFun (Input P ℓ) BitStr) (x : Input P ℓ) :
    check U X Z project x = true ↔ format x = true ∧ format (swap x) = true ∧
      (leftType x = rightType x → leftBits x = rightBits x) ∧
      directed U X Z project x = true ∧ directed U X Z project (swap x) = true := by
  simp only [check, andCheck_iff, comp_apply, PolyTimeFun.ite_apply, const_apply]
  simp only [equal, ap₂_apply, comp_apply, encoded_apply, treeEq_apply,
    encode_injective.eq_iff, decide_eq_true_eq]
  by_cases h : leftType x = rightType x <;> simp [h]

end MIPRE.Introspection.AuxiliaryDecision
end
