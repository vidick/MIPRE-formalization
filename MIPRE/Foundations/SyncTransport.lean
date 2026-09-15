/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.GapCompression
import MIPRE.Foundations.GameDescription

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

end Verifier

end MIPRE
