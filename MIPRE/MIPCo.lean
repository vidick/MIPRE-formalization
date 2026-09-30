/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.MainTheorem
public import MIPRE.Background.Repetition.VerifierCo
public import MIPRE.Foundations.ClassMIPCo

@[expose] public section

/-!
# `MIP^co = coRE`, conditionally on the commuting-operator soundness of compression

Lin's theorem (`Lin25`, blueprint `thm:mipco-eq-core`), with one hypothesis left open: that
the gap compression of the main theorem, `MIPRE.gapCompression`, is sound in the
commuting-operator value model (`GapCompression.Sound ValueModel.commuting`, blueprint
`def:compression-co-sound`) — the model-`co` case of the soundness clause of Lin's gap
compression theorem. Everything else is proved, once for both values, in the value-model
development (`Foundations/ValueModel.lean` and the halting reduction): the nested
compressibility criterion, the tabulation and the semidecider, the class transfer, and
`MIP^co ⊆ coRE` unconditionally (`MIPRE.MIPCo.isCoRE`). `planning/mipco-track.md` says what
discharging the hypothesis takes.

`mipco_eq_core_of_stages` states it with the hypothesis split into the commuting-operator
soundness clauses of the stages of the compression. Parallel repetition's is proved
(`repetitionCo_soundIn_commuting`, Phase 2); answer reduction's is proved from the soundness of
the low-individual-degree test in the commuting-operator model
(`AnswerReduction.answerReduction_soundIn_commuting`, Phase 3); and introspection's is proved from
the soundness of the Pauli basis test in the commuting-operator model
(`Introspection.seven_soundIn_commuting`, Phase 4). What remains are those two soundness
statements, `QLD.SoundCo` and `LIDT.Simul.SoundCo`. It goes through `gapCompressionCo`, the main
theorem's pipeline with the number of repetitions chosen against the smaller of the two
repetition constants (`repetitionCo`), since the commuting-operator repetition theorem has a
constant of its own; any gap compression sound in `ω_co` gives the theorem
(`Halting.mipco_eq_core_of`).

This module sits beside `MIPRE/MainTheorem.lean`, which `MIPRE/Foundations/` does not import,
because the hypothesis is about its `gapCompression`.
-/

namespace MIPRE

/-- **The halting reduction to the commuting-operator value**, given the commuting-operator
soundness of the compression of the main theorem. -/
theorem halting_reduction_commuting (hco : gapCompression.Sound .commuting) :
    ValueModel.commuting.HaltingReductionCoRE :=
  Halting.halting_reduction_commuting_of gapCompression Cost.selfUniversal hco

/-- **`coRE ⊆ MIP^co`**, given the commuting-operator soundness of compression. -/
theorem core_subset_mipco (hco : gapCompression.Sound .commuting) {L : Set Cost.BitStr}
    (h : IsCoRE L) : MIPCo L :=
  Halting.core_subset_mipclass_of_reduction .commuting (halting_reduction_commuting hco) h

/-- **`MIP^co = coRE`** (blueprint `thm:mipco-eq-core`), given the commuting-operator soundness
of compression; `MIP^co ⊆ coRE` needs no hypothesis (`MIPCo.isCoRE`). -/
theorem mipco_eq_core (hco : gapCompression.Sound .commuting) : MIPCo = IsCoRE :=
  Halting.mipclass_eq_core_of_reduction .commuting ValueModel.commuting_upperRE
    (halting_reduction_commuting hco)

/-- **The compression of the commuting-operator theorem**: the pipeline of the main theorem's
`gapCompression` — `Introspection.seven`, `AnswerReduction.answerReduction` — with the repetition
stage `repetitionCo 7`, the same procedure as `repetition 7` at the smaller of the two repetition
constants. The two compressions differ only in the number of repetitions the pipeline asks
for. -/
noncomputable def gapCompressionCo : GapCompression :=
  GapCompression.ofPipeline Introspection.seven AnswerReduction.answerReduction (repetitionCo 7)

/-- **`MIP^co = coRE` from the commuting-operator soundness of the Pauli basis test and of the
low-individual-degree test** (blueprint `cor:mipco-from-stages`): `gapCompressionCo` is sound in
`ω_co` as soon as each stage's soundness clause holds there (`GapCompression.ofPipeline_sound`);
parallel repetition's does (`repetitionCo_soundIn_commuting`), introspection's does once the Pauli
basis test is sound in the model of every commuting-operator strategy
(`Introspection.seven_soundIn_commuting`), and answer reduction's does once the
low-individual-degree test is sound in the commuting-operator model
(`AnswerReduction.answerReduction_soundIn_commuting`). This is the form Phases 5 and 6 of
`planning/mipco-track.md` discharge. -/
theorem mipco_eq_core_of_stages (hQ : QLD.SoundCo) (hL : LIDT.Simul.SoundCo) :
    MIPCo = IsCoRE :=
  Halting.mipco_eq_core_of gapCompressionCo Cost.selfUniversal
    (GapCompression.ofPipeline_sound (Introspection.seven_soundIn_commuting hQ)
      (AnswerReduction.answerReduction_soundIn_commuting hL) (repetitionCo_soundIn_commuting 7))

end MIPRE

end
