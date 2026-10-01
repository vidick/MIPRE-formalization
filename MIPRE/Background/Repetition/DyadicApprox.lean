/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Repetition.Amplify
public import MIPRE.Background.Repetition.PauliAlgebra

@[expose] public section

/-!
# `ω_co` is approached by projective strategies in dyadic pairs

Work package T5 of C6b (`planning/c6b-plan.md`; `reports/c6b-paper-proofs.md`, §3): below
`ω_co(G)`, and above `0`, lies the value of a projective strategy for `G` in a dyadic pair
(`MIPRE.CommutingFinitePairApprox`, `lem:co-value-finite-pair`). The proof is that of the finite
pair form, run on an amplified strategy:

1. **Strict tracial reduction into dyadic pairs** (`exists_tracialStrategy_isDyadicPair`): below
   `ω_co(G)` lies the winning probability of a tracial strategy whose standard-form model is a
   dyadic pair in every state. It is Lin's strict tracial reduction followed by amplification by
   the twisted Pauli algebra (`Pauli.pauliStd`, which has unital dyadic matrix units,
   `Pauli.pauliStd_hasDyadicUnits`), at no cost in correlation (Theorems A and T).
2. **Projectivity** (`exists_projStrat_expand_stdModel`): the strategy is a projective strategy,
   of value its winning probability, of an ancilla extension of its standard-form model with
   nonempty registers, which is again a dyadic pair (`BipartiteModel.IsDyadicPair.expand`).
-/

namespace MIPRE.Repetition

/-- **`ω_co` is approached by projective strategies in dyadic pairs** (`lem:co-value-finite-pair`):
below `ω_co(G)`, and above `0`, lies the value of a projective strategy for `G` in a dyadic pair on
a Hilbert space of `Type`, the ancilla extension of the standard-form model of a tracial strategy
amplified by the twisted Pauli algebra. -/
theorem commutingFinitePairApprox : CommutingFinitePairApprox := by
  intro X Y A B _ _ _ _ G t ht h
  obtain ⟨_, _, _, _⟩ := nonempty_of_lt_commutingOperatorValue ht h
  rw [commutingOperatorValue_eq_omegaCO] at h
  obtain ⟨T, hT, hD⟩ := exists_tracialStrategy_isDyadicPair Pauli.pauliStd
    Pauli.pauliStd_hasDyadicUnits (toCR G) h
  obtain ⟨_, _, _, _, _, _, _, _, e, S, hS⟩ := exists_projStrat_expand_stdModel G T
  exact ⟨_, _, _, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, _,
    (hD _).expand e, S, hS ▸ hT⟩

end MIPRE.Repetition

end
