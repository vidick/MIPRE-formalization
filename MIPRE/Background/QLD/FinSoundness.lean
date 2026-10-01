/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.QLD.Soundness
public import MIPRE.Background.LIDT.FinModel
public import MIPRE.Foundations.FinitePairExpand

@[expose] public section

/-!
# The Pauli basis test from the low-individual-degree test in finite pairs

Phase 6 of `planning/mipco-track.md`. Introspection needs of the value model only that it be
approached by projective strategies of models in which the Pauli basis test is sound
(`QLD.ApproxSoundIn`), and the Pauli basis test is sound in a model as soon as the seeded
low-individual-degree test is sound in every ancilla extension of it by a unit vector
(`QLD.soundIn_of_lidt`). A finite pair has nonempty registers in every such extension, which is
again a finite pair (`BipartiteModel.IsFinitePair.expand`), and `ω_co` dominates every model in a
unit state (`ValueModel.commuting_dominatesPOVM`). So `LIDT.Simul.SoundFin`, with the
approximation of `ω_co` in finite pairs, gives `QLD.ApproxSoundIn` for `ω_co`
(`lem:qld-approx-co-fin`).
-/

namespace MIPRE.QLD

/-- **`ω_co` is approached in models where the Pauli basis test is sound**, given that the seeded
low-individual-degree test is sound in every finite pair and that `ω_co` is approached by
projective strategies in finite pairs (`lem:qld-approx-co-fin`). -/
theorem approxSoundIn_commuting_of_fin (hV : CommutingFinitePairApprox)
    (h : LIDT.Simul.SoundFin) : ApproxSoundIn .commuting := by
  sorry

end MIPRE.QLD

end
