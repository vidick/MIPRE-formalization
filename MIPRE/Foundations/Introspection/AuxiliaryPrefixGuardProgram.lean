/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Cost.FiniteChoice
import MIPRE.Foundations.Introspection.AuxiliarySourceScan
import MIPRE.Foundations.Introspection.AuxiliaryReadProgram
import MIPRE.Foundations.Introspection.PrefixGuard

/-! # Executable local prefix guards

The question type selects one of the seven fixed scan depths. The full
register width, source program, clock and raw answer remain runtime data.
The caller's format check validates the tuple; here its first field is scanned.
-/

noncomputable section
namespace MIPRE.Introspection.AuxiliaryPrefixGuard
open Cost Cost.PolyTimeFun SourcePadding SourcePadding.Program AuxiliaryProgram
set_option linter.unusedSectionVars false
variable {P : Type*} [Fintype P] [DecidableEq P] [SizedEncoding P]

abbrev Input (P : Type*) := AuxiliarySource.Context × ℕ × QuestionType P 7 × BitStr

def context : PolyTimeFun (Input P) AuxiliarySource.Context := fst
def width : PolyTimeFun (Input P) ℕ := fst.comp snd
def label : PolyTimeFun (Input P) (QuestionType P 7) := fst.comp (snd.comp snd)
def answer : PolyTimeFun (Input P) BitStr := snd.comp (snd.comp snd)
def claim : PolyTimeFun (Input P) BitStr :=
  fst.comp (DynamicParser.tripleParts.comp (answer.pair width))

/-- The endpoint's role selects the source CL function. -/
def contextFor (w : Bool) : PolyTimeFun (Input P) AuxiliarySource.Context :=
  (AuxiliarySource.budget.comp context).pair ((AuxiliarySource.source.comp context).pair
    ((AuxiliarySource.index.comp context).pair ((const w).pair
      ((AuxiliarySource.level.comp context).pair (AuxiliarySource.inputPrefix.comp context)))))

def scan (U : ClockedUniversalMachine) (w : Bool) (k : ℕ) : PolyTimeFun (Input P) Bool :=
  fst.comp ((AuxiliaryScan.program (factorFromContext U) (matrixFromContext U) k).comp
    ((contextFor w).pair claim))

def branch (U : ClockedUniversalMachine) : QuestionType P 7 → PolyTimeFun (Input P) Bool
  | .inr (.hide k, w) => scan U w k.val
  | .inr (.read, w) => scan U w 6
  | _ => const true

/-- A uniform polynomial-time program; finite enumeration chooses control only. -/
def program (U : ClockedUniversalMachine) : PolyTimeFun (Input P) Bool :=
  choose label (branch U) (const true)

@[simp] theorem program_apply (U : ClockedUniversalMachine) (x : Input P) :
    program U x = branch U (label x) x := by
  simp [program]

@[simp] theorem program_pauli (U : ClockedUniversalMachine) (ctx : AuxiliarySource.Context)
    (Q : ℕ) (p : P) (bs : BitStr) : program U (ctx, Q, .inl p, bs) = true := by
  simp [label, branch]

@[simp] theorem program_introspect (U : ClockedUniversalMachine)
    (ctx : AuxiliarySource.Context) (Q : ℕ) (w : Bool) (bs : BitStr) :
    program (P := P) U (ctx, Q, .inr (.introspect, w), bs) = true := by
  simp [label, branch]

@[simp] theorem program_sample (U : ClockedUniversalMachine)
    (ctx : AuxiliarySource.Context) (Q : ℕ) (w : Bool) (bs : BitStr) :
    program (P := P) U (ctx, Q, .inr (.sample, w), bs) = true := by
  simp [label, branch]

theorem contextFor_queryContext (V : Verifier 7) (lam n : ℕ) (v w : Bool)
    (initialLevel : ℕ) {Q : ℕ} (initial : Fin Q → CL.𝔽₂)
    (t : QuestionType P 7) (bs : BitStr) :
    contextFor w (queryContext V lam n v initialLevel initial, Q, t, bs) =
      queryContext V lam n w initialLevel initial := rfl

/-- The scan flag is exactly prefix attainability for the actual bounded,
same-depth padded source. No query correctness assumption remains. -/
theorem scan_correct (U : ClockedUniversalMachine) {lam n Q : ℕ}
    (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (hQ : V.sampler.dim (2 ^ n) ≤ Q) (v w : Bool)
    (initialLevel : ℕ) (initial y yp : Fin Q → CL.𝔽₂) (last : BitStr)
    (t : QuestionType P 7) (k : ℕ) (hk : k ≤ 7) :
    scan U w k (queryContext V lam n v initialLevel initial, Q, t,
      AnswerParser.tripleBits (CL.toBits y) (CL.toBits yp) last) = true ↔
      ∃ x, ((depthFamily (firstEmbedding hQ) (sourceFamily V n) w).truncate k).eval x =
        (depthFamily (firstEmbedding hQ) (sourceFamily V n) w).outputPrefix k y := by
  have hp := (depthFamily_exactlyOn (firstEmbedding hQ) (sourceFamily V n)
    (by omega) (fun w => V.sampler.cl_exactlyOn (2 ^ n) (Player.ofBool w)) w).supportedOn
  have hqueries := AuxiliarySourceScan.queriesCorrectBelow U V hV hn hQ w
    initialLevel initial k hk
  simp only [scan, comp_apply, pair_apply, fst_apply, contextFor_queryContext, claim,
    answer, width, snd_apply, DynamicParser.tripleParts_apply,
    AnswerParser.tripleParts_tripleBits _ _ _ _ (CL.length_toBits _) (CL.length_toBits _)]
  constructor
  · intro hs
    obtain ⟨x, _, hx⟩ := AuxiliaryScan.program_sound (factorFromContext U)
      (matrixFromContext U) (queryContext V lam n w initialLevel initial) hp y k hqueries hs
    exact ⟨x, hx⟩
  · exact AuxiliaryScan.program_complete (factorFromContext U) (matrixFromContext U)
      (queryContext V lam n w initialLevel initial) hp y k hqueries

/-- Exact Hide guard on the canonical full-register answer encoding. -/
theorem program_hide {PA : Type*} (U : ClockedUniversalMachine) {lam n Q : ℕ}
    (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (hQ : V.sampler.dim (2 ^ n) ≤ Q) (v w : Bool)
    (initialLevel : ℕ) (initial y yp z : Fin Q → CL.𝔽₂) (k : Fin 7) :
    program (P := P) U (queryContext V lam n v initialLevel initial, Q, .inr (.hide k, w),
      AnswerParser.tripleBits (CL.toBits y) (CL.toBits yp) (CL.toBits z)) = true ↔
      PrefixGuard.holds (depthFamily (firstEmbedding hQ) (sourceFamily V n))
        (.inr (.hide k, w) : QuestionType P 7) (.hide y yp z : ParsedAnswer _ BitStr PA) := by
  rw [program_apply]
  change scan U w k.val _ = true ↔ _
  exact scan_correct U V hV hn hQ v w initialLevel initial y yp (CL.toBits z)
    (.inr (.hide k, w)) k.val (by omega)

/-- Exact Read guard; only its first six source stages are required. -/
theorem program_read {PA : Type*} (U : ClockedUniversalMachine) {lam n Q : ℕ}
    (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (hQ : V.sampler.dim (2 ^ n) ≤ Q) (v w : Bool)
    (initialLevel : ℕ) (initial y yp : Fin Q → CL.𝔽₂) (a : BitStr) :
    program (P := P) U (queryContext V lam n v initialLevel initial, Q, .inr (.read, w),
      AnswerParser.tripleBits (CL.toBits y) (CL.toBits yp) a) = true ↔
      PrefixGuard.holds (depthFamily (firstEmbedding hQ) (sourceFamily V n))
        (.inr (.read, w) : QuestionType P 7) (.read y yp a : ParsedAnswer _ BitStr PA) := by
  rw [program_apply]
  change scan U w 6 _ = true ↔ _
  exact scan_correct U V hV hn hQ v w initialLevel initial y yp a
    (.inr (.read, w)) 6 (by omega)

end MIPRE.Introspection.AuxiliaryPrefixGuard
