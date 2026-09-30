/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.ConditionalNormalizerStepAux
public import MIPRE.Foundations.Introspection.TypedPrefixChain
public import MIPRE.Foundations.Introspection.PauliAuxEstimates

@[expose] public section

/-! # The actual sampling outcomes and their ideal prefix readouts

All maps retain a dummy outcome for malformed answers. Coarse-graining the
ideal computational-basis measurement gives exactly the prefix measurement
used by the hiding induction, on the full ambient outcome alphabet.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): nothing here involves a state,
so the translation is of the operators. A measurement is a POVM in any ordered `⋆`-ring (a
player's algebra; in the register model `Ξ.reg (ι → F)`, the matrices over `ι → F` with entries in
`Ξ`'s algebras), coarse-graining is `fibSumIn`, and the ideal Z readout and the hiding prefix,
honest register operators over `ℂ`, stay concrete and enter the matrices over any algebra as
`smulKron 1`, through which coarse-graining passes (`fibSumIn_smulKron_one`). The coarse-graining
of a readout (`fibSum_readout`) is an identity of complex register matrices and is unchanged.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical
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

variable {PauliType PauliAnswer F ι A : Type*}
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

/-- Processing the actual sampled seed produces the actual sampled-prefix POVM, for a POVM in any
ordered `⋆`-ring. -/
theorem sampledQuestionPrefix_mapped (P : CL.CLFun F ι ℓ) (j : ℕ)
    {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    (M : POVMIn (ParsedAnswer (ι → F) A PauliAnswer) R) (y : Option (ι → F)) :
    fibSumIn (M.map sampleSeed).op (Option.map (P.truncate j).eval) y =
      (M.map (sampledQuestionPrefix P j)).op y := by
  rw [fibSumIn, ← POVMIn.map_op, POVMIn.map_map]
  rfl

/-- The same processing of ideal Z projectors is precisely the hiding prefix,
including its zero malformed outcome and every impossible ambient prefix. Both are honest
register operators, embedded as `smulKron 1` in the matrices over any algebra. -/
theorem idealZ_prefix_fibSum {R : Type*} [Ring R] [Algebra ℂ R] (P : CL.CLFun F ι ℓ) (j : ℕ)
    (y : Option (ι → F)) :
    fibSumIn (fun z => smulKron (1 : R) (readout (some : (ι → F) → Option (ι → F)) z))
      (Option.map (P.truncate j).eval) y = smulKron 1 (Honest.hidingPrefixOp P j y) := by
  rw [fibSumIn_smulKron_one, ← fibSum_eq_fibSumIn, fibSum_readout]
  rfl

end TypedEstimates
end MIPRE.Introspection

end

end
