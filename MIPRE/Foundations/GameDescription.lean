/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Games
import MIPRE.HaltingGameValue

/-!
# Game descriptions, read as games of the foundations

`HaltingGameValue.GameData` (blueprint `def:game-description`) is the codable, first-order
description of a synchronous game, and `HaltingGameValue.GameData.toGame` interprets it in the
self-contained vocabulary of `MIPRE.HaltingGameValue`. The foundations
(`MIPRE.Foundations.Games`) have their own `MIPRE.SynchronousGame` and `MIPRE.Game`, with the
same fields; this file reads a description in that vocabulary, which is where the quantum value
`MIPRE.quantumValue` lives. The two structures agree field by field, so nothing is proved here
beyond the definitions.
-/

namespace HaltingGameValue.GameData

/-- The synchronous game described by `g`, as a `MIPRE.SynchronousGame`: the same distribution and
predicate as `toGame`. -/
noncomputable def syncGame (g : GameData) :
    MIPRE.SynchronousGame (Fin (g.nX + 1)) (Fin (g.nA + 1)) where
  μ := g.toGame.μ
  μ_nonneg := g.toGame.μ_nonneg
  μ_sum_one := g.toGame.μ_sum_one
  D := g.toGame.D
  synchronous := g.toGame.synchronous

/-- The game described by `g`, as a two-player game of the foundations. -/
noncomputable def game (g : GameData) :
    MIPRE.Game (Fin (g.nX + 1)) (Fin (g.nX + 1)) (Fin (g.nA + 1)) (Fin (g.nA + 1)) :=
  g.syncGame.toGame

theorem game_μ (g : GameData) (x y : Fin (g.nX + 1)) :
    g.game.μ x y = if g.totalWeight = 0 then (if x = 0 ∧ y = 0 then 1 else 0)
      else (g.questionWeight x.val y.val : ℝ) / (g.totalWeight : ℝ) := rfl

theorem game_D (g : GameData) (x y : Fin (g.nX + 1)) (a b : Fin (g.nA + 1)) :
    g.game.D x y a b =
      if x = y ∧ a ≠ b then false else decide ((x.val, y.val, a.val, b.val) ∈ g.acc) := rfl

end HaltingGameValue.GameData
