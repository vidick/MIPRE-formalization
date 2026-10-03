/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.MainTheorem
public import MIPRE.Background.Repetition.VerifierCo
public import MIPRE.Foundations.ClassMIPCo
public import MIPRE.Background.Repetition.DyadicApprox
public import MIPRE.Background.QLD.FinSoundness
public import MIPRE.Background.LIDT.Co.SoundFin

@[expose] public section

/-!
# `MIP^co = coRE`

Lin's theorem (`Lin25`), **unconditionally**: `mipco_eq_core` (blueprint
`thm:mipco-eq-core-unconditional`), with the halting reduction to the commuting-operator value,
`halting_reduction_commuting`, and `coRE ⊆ MIP^co`, `core_subset_mipco`, beside it. All three
rest on `gapCompressionCo_sound`: the gap compression `gapCompressionCo` is sound in the
commuting-operator value model (`GapCompression.Sound ValueModel.commuting`, blueprint
`def:compression-co-sound`). The rest of `MIP^co = coRE` is proved once for both values, in the
value-model development (`Foundations/ValueModel.lean`, the halting reduction and
`Foundations/ClassMIPCo.lean`): the nested compressibility criterion, the tabulation and the
semidecider, the class transfer, and `MIP^co ⊆ coRE` (`MIPRE.MIPCo.isCoRE`); any gap compression
sound in `ω_co` gives the theorem (`Halting.mipco_eq_core_of`).

`gapCompressionCo` is the main theorem's pipeline with the number of repetitions chosen against
the smaller of the two repetition constants (`repetitionCo`), since the commuting-operator
repetition theorem has a constant of its own. Its soundness in `ω_co` is the soundness clauses of
its stages there (`GapCompression.ofPipeline_sound`), and the module records the route to them
as a chain of conditional theorems whose hypotheses shrink.

`mipco_eq_core_of_stages` asks for the commuting-operator soundness of the Pauli basis test and
of the low-individual-degree test. Parallel repetition's clause is proved
(`repetitionCo_soundIn_commuting`, Phase 2); answer reduction's is proved from the soundness of
the low-individual-degree test in the commuting-operator model
(`AnswerReduction.answerReduction_soundIn_commuting`, Phase 3); and introspection's is proved from
the soundness of the Pauli basis test in the commuting-operator model
(`Introspection.seven_soundIn_commuting`, Phase 4). The first follows from the second
(`QLD.soundCo_of_lidt`, Phase 5), so `mipco_eq_core_of_lidt` states the theorem with the one
hypothesis `LIDT.Simul.SoundCo`.

No source proves `LIDT.Simul.SoundCo` (`reports/lidt-co-audit.md`), and Phase 6 replaces it by
`LIDT.Simul.SoundFin`, the soundness of the seeded test in every dyadic pair: a model whose two
algebras are each other's commutants, carry faithful tracial states
(`BipartiteModel.IsFinitePair`) and have unital dyadic matrix units
(`BipartiteModel.IsDyadicPair`). The two hypotheses are incomparable. What `SoundFin` buys is a
trace on both algebras, which a port of the vendored finite-dimensional proof needs for its
semidefinite step and for orthonormalization, and which an arbitrary vector state does not supply,
and, through the matrix units, no abelian projections, which orthonormalization needs too.
`gapCompressionCo_sound_of_lidtFin` and `mipco_eq_core_of_lidtFin` state the soundness and the
theorem with it: below `ω_co(G)` lies the value of a projective strategy in a dyadic pair
(`Repetition.commutingFinitePairApprox`, from Lin's tracial density and an amplification by the
twisted Pauli algebra), so answer reduction and the Pauli basis test, which use the hypothesis
only in the model of one near-optimal strategy and in its ancilla extensions, need it only there.
`LIDT.Simul.soundFin` (`MIPRE/Background/LIDT/Co/SoundFin.lean`, blueprint `thm:lidt-sound-fin`)
proves it, by the commuting-operator port of the vendored finite-dimensional soundness proof
(`planning/c6b-plan.md`).

This module sits beside `MIPRE/MainTheorem.lean`, which `MIPRE/Foundations/` does not import,
because `gapCompressionCo` is built from the stages of its pipeline.
-/

namespace MIPRE

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

/-- **`MIP^co = coRE` from the commuting-operator soundness of the low-individual-degree test
alone** (blueprint `cor:mipco-from-lidt`): the Pauli basis test is sound in the model of every
commuting-operator strategy as soon as the seeded low-individual-degree test is sound in the
commuting-operator model (`QLD.soundCo_of_lidt`, Phase 5 of `planning/mipco-track.md`), so the two
hypotheses of `mipco_eq_core_of_stages` are one. -/
theorem mipco_eq_core_of_lidt (hL : LIDT.Simul.SoundCo) : MIPCo = IsCoRE :=
  mipco_eq_core_of_stages (QLD.soundCo_of_lidt hL) hL

/-- **The compression is sound in `ω_co` if the low-individual-degree test is sound in dyadic
pairs** (blueprint `cor:mipco-from-lidt-fin`): `ω_co` is approached by projective strategies in
dyadic pairs (`Repetition.commutingFinitePairApprox`), and dyadic pairs are closed under ancilla
extensions, so the Pauli basis test is sound in the model of each approximating strategy
(`QLD.approxSoundIn_commuting_of_fin`), which is what introspection uses of it, and answer
reduction is sound in `ω_co` (`AnswerReduction.answerReduction_soundIn_commuting_fin`). -/
theorem gapCompressionCo_sound_of_lidtFin (h : LIDT.Simul.SoundFin) :
    gapCompressionCo.Sound .commuting :=
  GapCompression.ofPipeline_sound
    (Introspection.seven_soundIn .commuting ValueModel.commuting_projApprox
      (QLD.approxSoundIn_commuting_of_fin Repetition.commutingFinitePairApprox h))
    (AnswerReduction.answerReduction_soundIn_commuting_fin Repetition.commutingFinitePairApprox h)
    (repetitionCo_soundIn_commuting 7)

/-- **`MIP^co = coRE` from the soundness of the low-individual-degree test in dyadic pairs**
(blueprint `cor:mipco-from-lidt-fin`), the target of Phase 6 of `planning/mipco-track.md`, by
`gapCompressionCo_sound_of_lidtFin`. -/
theorem mipco_eq_core_of_lidtFin (h : LIDT.Simul.SoundFin) : MIPCo = IsCoRE :=
  Halting.mipco_eq_core_of gapCompressionCo Cost.selfUniversal
    (gapCompressionCo_sound_of_lidtFin h)

/-- **Compression is sound in the commuting-operator model** (blueprint
`thm:mipco-eq-core-unconditional`): the hypothesis of `gapCompressionCo_sound_of_lidtFin`, the
soundness of the seeded low-individual-degree test in every dyadic pair, is
`LIDT.Simul.soundFin`. -/
theorem gapCompressionCo_sound : gapCompressionCo.Sound .commuting :=
  gapCompressionCo_sound_of_lidtFin LIDT.Simul.soundFin

/-- **The halting reduction to the commuting-operator value** (blueprint
`thm:mipco-eq-core-unconditional`): `ω_co ≤ 1/2` on the machines that halt on the empty input,
`ω_co = 1` on the others. -/
theorem halting_reduction_commuting : ValueModel.commuting.HaltingReductionCoRE :=
  Halting.halting_reduction_commuting_of gapCompressionCo Cost.selfUniversal gapCompressionCo_sound

/-- **`coRE ⊆ MIP^co`** (blueprint `thm:mipco-eq-core-unconditional`). -/
theorem core_subset_mipco {L : Set Cost.BitStr} (h : IsCoRE L) : MIPCo L :=
  Halting.core_subset_mipclass_of_reduction .commuting halting_reduction_commuting h

/-- **`MIP^co = coRE`** (Lin, blueprint `thm:mipco-eq-core-unconditional`): the languages with
commuting-operator multiprover interactive proofs are exactly the co-recursively-enumerable ones.
The hypothesis of `mipco_eq_core_of_lidtFin`, the soundness of the seeded low-individual-degree
test in every dyadic pair, is `LIDT.Simul.soundFin`. -/
theorem mipco_eq_core : MIPCo = IsCoRE :=
  mipco_eq_core_of_lidtFin LIDT.Simul.soundFin

end MIPRE

end
