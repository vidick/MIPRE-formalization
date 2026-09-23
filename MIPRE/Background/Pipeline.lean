/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.Introspection.Compiler
import MIPRE.Background.Repetition.Verifier
import MIPRE.Foundations.Halting.Corollaries
import MIPRE.Foundations.Pipeline.Compress

/-!
# The pipeline with its supplied stages: `MIP* = RE` from answer reduction alone

`GapCompression.ofPipeline` builds the compression theorem from three stage contracts:
`Introspection 7`, `AnswerReduction 5` and `Repetition 7`. Two of them are now inhabited:

* `Introspection.seven` (`MIPRE/Background/Introspection/Compiler.lean`, blueprint
  `lem:introspection-supply`), whose only rigidity input is the Pauli basis test `thm:qld`;
* `repetition 7` (`MIPRE/Background/Repetition/Verifier.lean`, blueprint
  `thm:parallel-repetition`).

A universal machine is supplied too (`Cost.selfUniversal`, blueprint `lem:universal-tm`). This
file plugs all three in, so that every conditional consequence of chapter 7 — `thm:main`,
`cor:main-quantum`, `cor:value-uncomputable`, `thm:mipstar-eq-re` — is stated with the single
remaining hypothesis, an `AnswerReduction 5`.

Two reasons to state it now, before answer reduction exists. It is the first time the pipeline
is supplied from the supply side with the actual instances rather than hypotheses: the file
compiling is the check that `ofPipeline` composes with `Introspection.seven` and `repetition 7`
as they are. And it turns the last step into one line: an inhabitant of `AnswerReduction 5`
closes the `sorry` of `HaltingGameValue.halting_reduces_to_gameValue` through
`halting_reduces_to_gameValue_of_answerReduction`.
-/

namespace MIPRE

open Cost

/-- **The compression theorem from answer reduction alone**: `GapCompression.ofPipeline` with
the supplied introspection and repetition stages. -/
noncomputable def GapCompression.ofAnswerReduction (A : AnswerReduction 5) : GapCompression :=
  GapCompression.ofPipeline Introspection.seven A (repetition 7)

namespace Halting

variable (A : AnswerReduction 5)
include A

/-- **Halting reduces to the synchronous game value** (blueprint `thm:main`), conditionally on
answer reduction only. -/
theorem halting_reduces_to_gameValue_of_answerReduction :
    ∃ g : Nat.Partrec.Code → HaltingGameValue.GameData, Computable g ∧
      ∀ pc : Nat.Partrec.Code,
        (HaltingGameValue.HaltsOnEmptyInput pc → HaltingGameValue.gameValue (g pc).toGame = 1) ∧
        (¬ HaltingGameValue.HaltsOnEmptyInput pc →
          HaltingGameValue.gameValue (g pc).toGame ≤ 1 / 2) :=
  halting_reduces_to_gameValue_of (GapCompression.ofAnswerReduction A) Cost.selfUniversal

/-- **Halting reduces to the quantum value** (blueprint `cor:main-quantum`), conditionally on
answer reduction only. -/
theorem halting_reduction_quantum_of_answerReduction :
    ∃ g : Nat.Partrec.Code → HaltingGameValue.GameData, Computable g ∧
      ∀ pc : Nat.Partrec.Code,
        (HaltingGameValue.HaltsOnEmptyInput pc → quantumValue (g pc).game = 1) ∧
        (¬ HaltingGameValue.HaltsOnEmptyInput pc → quantumValue (g pc).game ≤ 1 / 2) :=
  halting_reduction_quantum_of (GapCompression.ofAnswerReduction A) Cost.selfUniversal

/-- **The synchronous value is uncomputable** (blueprint `cor:value-uncomputable`),
conditionally on answer reduction only. -/
theorem gameValue_uncomputable_of_answerReduction :
    ¬ ∃ f : HaltingGameValue.GameData → Bool, Computable f ∧
      (∀ d, HaltingGameValue.gameValue d.toGame = 1 → f d = true) ∧
      (∀ d, HaltingGameValue.gameValue d.toGame ≤ 1 / 2 → f d = false) :=
  gameValue_uncomputable_of (GapCompression.ofAnswerReduction A) Cost.selfUniversal

/-- **The quantum value is uncomputable** (blueprint `cor:value-uncomputable`, second clause),
conditionally on answer reduction only. -/
theorem quantumValue_uncomputable_of_answerReduction :
    ¬ ∃ f : HaltingGameValue.GameData → Bool, Computable f ∧
      (∀ d, quantumValue d.game = 1 → f d = true) ∧
      (∀ d, quantumValue d.game ≤ 1 / 2 → f d = false) :=
  quantumValue_uncomputable_of (GapCompression.ofAnswerReduction A) Cost.selfUniversal

/-- **`RE ⊆ MIP*`**, conditionally on answer reduction only. -/
theorem re_subset_mipstar_of_answerReduction {L : Set BitStr} (h : IsRE L) : MIPStar L :=
  re_subset_mipstar_of (GapCompression.ofAnswerReduction A) Cost.selfUniversal h

/-- **`MIP* = RE`** (blueprint `thm:mipstar-eq-re`), conditionally on answer reduction only:
introspection, parallel repetition and the universal machine are supplied. -/
theorem mipstar_eq_re_of_answerReduction : MIPStar = IsRE :=
  mipstar_eq_re_of (GapCompression.ofAnswerReduction A) Cost.selfUniversal

end Halting

end MIPRE
