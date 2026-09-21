/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.ConditionalNormalizerStepAux
import MIPRE.Foundations.Introspection.TypedPrefixChain
import MIPRE.Foundations.Introspection.PauliAuxEstimates

/-! # The actual sampling outcomes and their ideal prefix readouts

All maps retain a dummy outcome for malformed answers. Coarse-graining the
ideal computational-basis measurement gives exactly the prefix measurement
used by the hiding induction, on the full ambient outcome alphabet.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false

/-- Coarse-graining a computational readout reads the composite function. -/
theorem fibSum_readout {I Y Z : Type*} [Fintype I] [DecidableEq I]
    [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
    (f : I → Y) (g : Y → Z) (z : Z) :
    fibSum (readout f) g z = readout (g ∘ f) z := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [fibSum, readout, Matrix.sum_apply, eq_comm]
  · simp [fibSum, readout, Matrix.sum_apply, hij]

namespace TypedEstimates

variable {PauliType PauliAnswer F ι A H K : Type*}
  [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

/-- The seed reported by a Sample answer. -/
def sampleSeed : ParsedAnswer (ι → F) A PauliAnswer → Option (ι → F)
  | .pair z _ => some z
  | _ => none

/-- The actual sampled question prefix, rather than the reported Introspect prefix. -/
def sampledQuestionPrefix (P : CL.CLFun F ι ℓ) (j : ℕ)
    (a : ParsedAnswer (ι → F) A PauliAnswer) : Option (ι → F) :=
  (sampleSeed a).map (P.truncate j).eval

variable (L : Bool → CL.CLFun F ι ℓ) (X Z : PauliType)
  (projectPauli : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PauliType → PauliType → PauliAnswer → PauliAnswer → Bool)

/-- The actual reversed Z/Sample edge compares the sampled seed with Bob's
projected Pauli answer; wrong constructors cannot be accepted. -/
theorem check_sample_pauliZ_seed (w : Bool)
    {a b : ParsedAnswer (ι → F) A PauliAnswer}
    (h : TypedPredicate.check L X Z projectPauli D DP
      (QuestionType.sample w) (QuestionType.pauli Z) a b = true) :
    sampleSeed a = pauliProjection projectPauli b := by
  have hf := TypedPredicate.check_formats L X Z projectPauli D DP h
  cases a <;> cases b <;> simp [TypedPredicate.fits] at hf
  rename_i z a b
  have hd := TypedPredicate.check_directed_reversed L X Z projectPauli D DP h
  simp only [TypedPredicate.directed, ↓reduceIte] at hd
  have he : projectPauli b = z := of_decide_eq_true hd
  exact congrArg some he.symm

/-- The actual Sample/Introspect edge preserves every CL prefix, with no
assumption that the claimed question is already in the CL image. -/
theorem check_sample_introspect_prefix (w : Bool) (hL : (L w).SupportedOn univ)
    (j : ℕ) {a b : ParsedAnswer (ι → F) A PauliAnswer}
    (h : TypedPredicate.check L X Z projectPauli D DP
      (QuestionType.sample w) (QuestionType.introspect w) a b = true) :
    sampledQuestionPrefix (L w) j a = reportedPrefix (L w) j .introspect b := by
  have hf := TypedPredicate.check_formats L X Z projectPauli D DP h
  cases a <;> cases b <;> simp [TypedPredicate.fits] at hf
  rename_i z a y b
  have hd := TypedPredicate.check_directed_reversed L X Z projectPauli D DP h
  simp only [TypedPredicate.directed, ↓reduceIte] at hd
  have he : y = (L w).eval z ∧ b = a :=
    @of_decide_eq_true _ (Classical.propDecidable _) hd
  simp only [sampledQuestionPrefix, sampleSeed, Option.map_some, reportedPrefix, he.1,
    hL.outputPrefix_eval]

variable [Fintype F] [DecidableEq F] [Fintype A] [Fintype PauliAnswer]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

/-- Processing the actual sampled seed produces the actual sampled-prefix POVM. -/
theorem sampledQuestionPrefix_mapped (P : CL.CLFun F ι ℓ) (j : ℕ)
    (M : POVM (ParsedAnswer (ι → F) A PauliAnswer) H) (y : Option (ι → F)) :
    fibSum (fun z => ((M.map sampleSeed).mats z).val)
      (Option.map (P.truncate j).eval) y =
      ((M.map (sampledQuestionPrefix P j)).mats y).val := by
  rw [fibSum, ← POVM.map_mats, POVM.map_map]
  rfl

/-- The same processing of ideal Z projectors is precisely the hiding prefix,
including its zero malformed outcome and every impossible ambient prefix. -/
theorem idealZ_prefix_fibSum (P : CL.CLFun F ι ℓ) (j : ℕ) (y : Option (ι → F)) :
    fibSum (fun z => (aOp (readout (some : (ι → F) → Option (ι → F)) z) :
      Matrix ((ι → F) × K) _ ℂ)) (Option.map (P.truncate j).eval) y =
      aOp (Honest.hidingPrefixOp P j y) := by
  rw [fibSum_aOp, fibSum_readout]
  rfl

end TypedEstimates
end MIPRE.Introspection

end
