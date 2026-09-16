/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.GapCompression
import MIPRE.Foundations.GameDescription
import MIPRE.Foundations.GameDouble

/-!
# A verifier's game and its tabulation, in the synchronous value

`MIPRE.Verifier.quantumValue_toGame_eq_valStar` (`Foundations/Halting/Enumerate.lean`) carries
`val*` from `𝒱_n` to a game description tabulating it. This file is its synchronous counterpart,
which is what blueprint `thm:halting` item 1 needs: the witness there is a value-`1` *PCC*
strategy, so the conclusion is about the synchronous value, and the headline
`HaltingGameValue.halting_reduces_to_gameValue` is stated in `HaltingGameValue.gameValue`.

Given a game description `g` whose distribution and decision predicate match those of `𝒱_n`
along equivalences `eX`, `eA` of the alphabets:

* `Verifier.exists_perfectPCC_syncGame`: `V.HasPerfectPCC n T` (blueprint `def:pcc`, the
  completeness hypothesis of `thm:compression`) gives a value-`1` PCC synchronous strategy for
  `g.syncGame`, by `MIPRE.SyncStrategy.relabel`;
* `Verifier.syncValue_syncGame_eq_one` and `Verifier.gameValue_toGame_eq_one`: hence
  `MIPRE.syncValue g.syncGame = 1`, hence `HaltingGameValue.gameValue g.toGame = 1`, through
  `HaltingGameValue.GameData.gameValue_eq_syncValue`;
* `Verifier.gameValue_toGame_le_of_valStar_le`: in the other direction `val*(𝒱_n) ≤ c` gives
  `gameValue g.toGame ≤ c`, since `synval ≤ val*` (blueprint `lem:sync-le-valstar`). This is the
  soundness half, and it needs no PCC strategy.

Together these are the two bridges that separate `MIPRE.Halting.halting_reduction`, which
concludes in `val*`, from `thm:halting` as the blueprint states it.

## The doubled versions, and why they are the ones the tabulation uses

All four bridges above match `g` against `V.game n T` itself, which a game description can do
only where `𝒱_n` is synchronous (`MIPRE.Verifier.isSynchronousAt_of_game_matches`) — and the
class `B` of the halting reduction does not ask for synchronicity. The `_doubled` versions at
the end of this file match `g` against `V.doubledGame n T` instead, the game on `Bool × 𝒳`
of `Foundations/GameDouble.lean`, whose distribution avoids the diagonal outright. They carry
no synchronicity hypothesis and are what `MIPRE.Halting.tab_value` and `gameValue_tab_eq_one`
are proved from. Nothing above changes; the doubled statements are added beside them.
-/

namespace MIPRE

namespace Verifier

open HaltingGameValue (GameData)

variable {ℓ : ℕ} (V : Verifier ℓ) (n T : ℕ) (g : GameData)

/-- **The completeness bridge.** A game description whose question distribution and decision
predicate match those of `𝒱_n` along the two indexings inherits its value-`1` PCC strategy:
the strategy is relabeled along the equivalences by `MIPRE.SyncStrategy.relabel`, which keeps
both the value and the commutation condition. -/
theorem exists_perfectPCC_syncGame
    (eX : Fin (g.nX + 1) ≃ V.Questions n) (eA : Fin (g.nA + 1) ≃ Answers T)
    (hμ : ∀ i j, g.game.μ i j = V.sampler.dist n (eX i) (eX j))
    (hD : ∀ i j k l, g.game.D i j k l = (V.game n T).D (eX i) (eX j) (eA k) (eA l))
    (hV : V.HasPerfectPCC n T) :
    ∃ S : SyncStrategy g.syncGame, S.IsPCC ∧ S.value = 1 := by
  obtain ⟨hsync, S, hPCC, hval⟩ := hV
  refine ⟨S.relabel g.syncGame eX eA, S.isPCC_relabel hPCC g.syncGame eX eA hμ, ?_⟩
  rw [S.value_relabel g.syncGame eX eA hμ hD]
  exact hval

/-- **The completeness bridge, in the synchronous value.** -/
theorem syncValue_syncGame_eq_one
    (eX : Fin (g.nX + 1) ≃ V.Questions n) (eA : Fin (g.nA + 1) ≃ Answers T)
    (hμ : ∀ i j, g.game.μ i j = V.sampler.dist n (eX i) (eX j))
    (hD : ∀ i j k l, g.game.D i j k l = (V.game n T).D (eX i) (eX j) (eA k) (eA l))
    (hV : V.HasPerfectPCC n T) :
    syncValue g.syncGame = 1 := by
  obtain ⟨S, -, hval⟩ := V.exists_perfectPCC_syncGame n T g eX eA hμ hD hV
  refine le_antisymm (syncValue_le_one _) ?_
  rw [← hval]
  exact le_ciSup (SyncStrategy.bddAbove_range_value _) S

/-- **The completeness bridge, in the value of `HaltingGameValue`** — the value in which
`HaltingGameValue.halting_reduces_to_gameValue` is stated. -/
theorem gameValue_toGame_eq_one
    (eX : Fin (g.nX + 1) ≃ V.Questions n) (eA : Fin (g.nA + 1) ≃ Answers T)
    (hμ : ∀ i j, g.game.μ i j = V.sampler.dist n (eX i) (eX j))
    (hD : ∀ i j k l, g.game.D i j k l = (V.game n T).D (eX i) (eX j) (eA k) (eA l))
    (hV : V.HasPerfectPCC n T) :
    HaltingGameValue.gameValue g.toGame = 1 := by
  rw [g.gameValue_eq_syncValue]
  exact V.syncValue_syncGame_eq_one n T g eX eA hμ hD hV

/-- **The soundness bridge.** An upper bound on `val*(𝒱_n)` is an upper bound on the value of a
tabulation of it, in the value of `HaltingGameValue`: the quantum value transports along the
relabelings (`quantumValue_eq_of_equiv`) and dominates the synchronous value (blueprint
`lem:sync-le-valstar`). No PCC strategy is involved. -/
theorem gameValue_toGame_le_of_valStar_le {c : ℝ}
    (eX : Fin (g.nX + 1) ≃ V.Questions n) (eA : Fin (g.nA + 1) ≃ Answers T)
    (hμ : ∀ i j, g.game.μ i j = V.sampler.dist n (eX i) (eX j))
    (hD : ∀ i j k l, g.game.D i j k l = (V.game n T).D (eX i) (eX j) (eA k) (eA l))
    (hV : V.valStar n T ≤ c) :
    HaltingGameValue.gameValue g.toGame ≤ c := by
  rw [g.gameValue_eq_syncValue]
  refine (syncValue_le_quantumValue g.syncGame).trans ?_
  rwa [show g.syncGame.toGame = g.game from rfl,
    quantumValue_eq_of_equiv (V.game n T) g.game eX eX eA eA hμ hD]

/-! ## The doubled game, and the same bridges against it

Five, not four: the four above, plus `quantumValue_toGame_eq_valStar_doubled`, which is the
doubled form of `MIPRE.Verifier.quantumValue_toGame_eq_valStar` from
`Foundations/Halting/Enumerate.lean` and has no un-doubled counterpart in this file. -/

/-- **`𝒱_n` on the doubled question set.** Alice is asked `(false, x)`, Bob `(true, y)`.
Synchronous by construction — no hypothesis on the decider — because the distribution puts no
weight on the diagonal. -/
noncomputable def doubledGame : SynchronousGame (Bool × V.Questions n) (Answers T) :=
  (V.game n T).doubled

/-- **The doubled game has the value it doubles**, with no synchronicity hypothesis. -/
theorem quantumValue_doubledGame : quantumValue (V.doubledGame n T).toGame = V.valStar n T :=
  quantumValue_doubled (V.game n T)

/-- **The value bridge, doubled.** A game description matching `𝒱_n`'s *doubled* game along
relabelings of the two alphabets has the value of `𝒱_n` — the doubled replacement of
`quantumValue_toGame_eq_valStar`, and unlike it free of any synchronicity hypothesis. Note
that `hD` here is total, on every question pair including the diagonal: the doubled game
rejects off the tag block, exactly as a `GameData` does, so `quantumValue_eq_of_equiv` applies
unchanged and no support-restricted version of it is needed. -/
theorem quantumValue_toGame_eq_valStar_doubled
    (eX : Fin (g.nX + 1) ≃ Bool × V.Questions n) (eA : Fin (g.nA + 1) ≃ Answers T)
    (hμ : ∀ i j, g.game.μ i j = (V.doubledGame n T).μ (eX i) (eX j))
    (hD : ∀ i j k l, g.game.D i j k l = (V.doubledGame n T).D (eX i) (eX j) (eA k) (eA l)) :
    quantumValue g.game = V.valStar n T := by
  rw [← V.quantumValue_doubledGame n T]
  exact quantumValue_eq_of_equiv (V.doubledGame n T).toGame g.game eX eX eA eA hμ hD

/-- **The completeness bridge, doubled.** The value-`1` PCC strategy is first doubled
(`SyncStrategy.double`, which plays the same measurement at both tags) and then relabeled by
the existing `SyncStrategy.relabel`. -/
theorem exists_perfectPCC_syncGame_doubled
    (eX : Fin (g.nX + 1) ≃ Bool × V.Questions n) (eA : Fin (g.nA + 1) ≃ Answers T)
    (hμ : ∀ i j, g.game.μ i j = (V.doubledGame n T).μ (eX i) (eX j))
    (hD : ∀ i j k l, g.game.D i j k l = (V.doubledGame n T).D (eX i) (eX j) (eA k) (eA l))
    (hV : V.HasPerfectPCC n T) :
    ∃ S : SyncStrategy g.syncGame, S.IsPCC ∧ S.value = 1 := by
  obtain ⟨hsync, S, hPCC, hval⟩ := hV
  refine ⟨S.double.relabel g.syncGame eX eA,
    S.double.isPCC_relabel (SyncStrategy.isPCC_double hPCC) g.syncGame eX eA hμ, ?_⟩
  rw [S.double.value_relabel g.syncGame eX eA hμ hD, SyncStrategy.value_double, hval]

/-- **The completeness bridge, doubled, in the synchronous value.** -/
theorem syncValue_syncGame_eq_one_doubled
    (eX : Fin (g.nX + 1) ≃ Bool × V.Questions n) (eA : Fin (g.nA + 1) ≃ Answers T)
    (hμ : ∀ i j, g.game.μ i j = (V.doubledGame n T).μ (eX i) (eX j))
    (hD : ∀ i j k l, g.game.D i j k l = (V.doubledGame n T).D (eX i) (eX j) (eA k) (eA l))
    (hV : V.HasPerfectPCC n T) :
    syncValue g.syncGame = 1 := by
  obtain ⟨S, -, hval⟩ := V.exists_perfectPCC_syncGame_doubled n T g eX eA hμ hD hV
  refine le_antisymm (syncValue_le_one _) ?_
  rw [← hval]
  exact le_ciSup (SyncStrategy.bddAbove_range_value _) S

/-- **The completeness bridge, doubled, in the value of `HaltingGameValue`.** This is what
`MIPRE.Halting.gameValue_tab_eq_one` is proved from, and so what item 1 of blueprint
`thm:halting` rests on. -/
theorem gameValue_toGame_eq_one_doubled
    (eX : Fin (g.nX + 1) ≃ Bool × V.Questions n) (eA : Fin (g.nA + 1) ≃ Answers T)
    (hμ : ∀ i j, g.game.μ i j = (V.doubledGame n T).μ (eX i) (eX j))
    (hD : ∀ i j k l, g.game.D i j k l = (V.doubledGame n T).D (eX i) (eX j) (eA k) (eA l))
    (hV : V.HasPerfectPCC n T) :
    HaltingGameValue.gameValue g.toGame = 1 := by
  rw [g.gameValue_eq_syncValue]
  exact V.syncValue_syncGame_eq_one_doubled n T g eX eA hμ hD hV

/-- **The soundness bridge, doubled.** Its hypothesis is an upper bound on `val*` and nothing
is assumed of the decider. -/
theorem gameValue_toGame_le_of_valStar_le_doubled {c : ℝ}
    (eX : Fin (g.nX + 1) ≃ Bool × V.Questions n) (eA : Fin (g.nA + 1) ≃ Answers T)
    (hμ : ∀ i j, g.game.μ i j = (V.doubledGame n T).μ (eX i) (eX j))
    (hD : ∀ i j k l, g.game.D i j k l = (V.doubledGame n T).D (eX i) (eX j) (eA k) (eA l))
    (hV : V.valStar n T ≤ c) :
    HaltingGameValue.gameValue g.toGame ≤ c := by
  rw [g.gameValue_eq_syncValue]
  refine (syncValue_le_quantumValue g.syncGame).trans ?_
  rw [show g.syncGame.toGame = g.game from rfl,
    V.quantumValue_toGame_eq_valStar_doubled n T g eX eA hμ hD]
  exact hV

end Verifier

end MIPRE
