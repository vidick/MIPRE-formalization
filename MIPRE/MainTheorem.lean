/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.HaltingGameValue
import MIPRE.Background.Pipeline
import MIPRE.Background.AnswerReduction.Instance

/-!
# `MIP* = RE`

The main theorem, proved: `HaltingGameValue.halting_reduces_to_gameValue` is the Mathlib-only
statement `HaltingGameValue.HaltingReducesToGameValue` of `MIPRE/HaltingGameValue.lean`
(Theorem 12.2 of "MIP* = RE", blueprint `thm:main`).

It is the pipeline of `MIPRE/Background/Pipeline.lean` with its last hypothesis supplied: gap
compression is built from introspection (`Introspection.seven`), answer reduction
(`AnswerReduction.answerReduction`, over the classical PCP decider) and parallel repetition
(`repetition 7`), and a universal machine (`Cost.selfUniversal`). The consequences of chapter 7
follow unconditionally: the reduction to the quantum value, the uncomputability of both values,
and `MIP* = RE`.
-/

/-- **Gap-preserving compression** (blueprint `thm:compression-target`), inhabited. -/
noncomputable def MIPRE.gapCompression : MIPRE.GapCompression :=
  MIPRE.GapCompression.ofAnswerReduction MIPRE.AnswerReduction.answerReduction

namespace HaltingGameValue

/-- **Theorem 12.2 of "MIP* = RE"** (blueprint `thm:main`): halting reduces to the synchronous
game value. -/
theorem halting_reduces_to_gameValue : HaltingReducesToGameValue :=
  MIPRE.Halting.halting_reduces_to_gameValue_of_answerReduction
    MIPRE.AnswerReduction.answerReduction

end HaltingGameValue

namespace MIPRE.Halting

open Cost

/-- **Halting reduces to the quantum value** (blueprint `cor:main-quantum`). -/
theorem halting_reduction_quantum :
    ∃ g : Nat.Partrec.Code → HaltingGameValue.GameData, Computable g ∧
      ∀ pc : Nat.Partrec.Code,
        (HaltingGameValue.HaltsOnEmptyInput pc → quantumValue (g pc).game = 1) ∧
        (¬ HaltingGameValue.HaltsOnEmptyInput pc → quantumValue (g pc).game ≤ 1 / 2) :=
  halting_reduction_quantum_of_answerReduction AnswerReduction.answerReduction

/-- **The synchronous value is uncomputable** (blueprint `cor:value-uncomputable`). -/
theorem gameValue_uncomputable :
    ¬ ∃ f : HaltingGameValue.GameData → Bool, Computable f ∧
      (∀ d, HaltingGameValue.gameValue d.toGame = 1 → f d = true) ∧
      (∀ d, HaltingGameValue.gameValue d.toGame ≤ 1 / 2 → f d = false) :=
  gameValue_uncomputable_of_answerReduction AnswerReduction.answerReduction

/-- **The quantum value is uncomputable** (blueprint `cor:value-uncomputable`, second clause). -/
theorem quantumValue_uncomputable :
    ¬ ∃ f : HaltingGameValue.GameData → Bool, Computable f ∧
      (∀ d, quantumValue d.game = 1 → f d = true) ∧
      (∀ d, quantumValue d.game ≤ 1 / 2 → f d = false) :=
  quantumValue_uncomputable_of_answerReduction AnswerReduction.answerReduction

/-- **`RE ⊆ MIP*`.** -/
theorem re_subset_mipstar {L : Set BitStr} (h : IsRE L) : MIPStar L :=
  re_subset_mipstar_of_answerReduction AnswerReduction.answerReduction h

/-- **`MIP* = RE`** (blueprint `thm:mipstar-eq-re`). -/
theorem mipstar_eq_re : MIPStar = IsRE :=
  mipstar_eq_re_of_answerReduction AnswerReduction.answerReduction

end MIPRE.Halting
