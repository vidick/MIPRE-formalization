/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/GameDescription.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.PartrecCode
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_HaltingGameValue

/-!
# Game descriptions, read as games of the foundations

`HaltingGameValue.GameData` (blueprint `def:game-description`) is the codable, first-order
description of a synchronous game, and `HaltingGameValue.GameData.toGame` interprets it in the
self-contained vocabulary of `MIPRE.HaltingGameValue`. The foundations
(`MIPRE.Foundations.Games`) have their own `MIPRE.SynchronousGame` and `MIPRE.Game`, with the
same fields; this file reads a description in that vocabulary, which is where the quantum value
`MIPRE.quantumValue` lives. The two structures agree field by field, so the two readings
`GameData.syncGame` and `GameData.game` are definitions, with nothing to prove about them.

The two *values* are a different matter: `HaltingGameValue.gameValue` and `MIPRE.syncValue` are
suprema over two parallel structures of synchronous strategies — `HaltingGameValue.SyncStrategy`
carries a question-indexed family of `POVM`s with a projectivity certificate, while
`MIPRE.SyncStrategy` carries a `MIPRE.ProjectiveMeasurement`. `GameData.toSyncStrategy` and
`GameData.ofSyncStrategy` repackage one as the other, in both directions and with the same
dimension and the same operators, so that

  `GameData.gameValue_eq_syncValue : gameValue g.toGame = MIPRE.syncValue g.syncGame`

identifies the two suprema. Both `MIPRE.SyncStrategy.value_eq` and
`HaltingGameValue.strategyValue` spell the value as
`∑ x y a b, μ x y ⬝ [D x y a b] ⬝ Tr(M^x_a M^y_b).re / d`, so the two strategy values agree by
definitional unfolding.
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

@[simp] theorem syncGame_μ (g : GameData) (x y : Fin (g.nX + 1)) :
    g.syncGame.μ x y = g.toGame.μ x y := rfl

@[simp] theorem syncGame_D (g : GameData) (x y : Fin (g.nX + 1)) (a b : Fin (g.nA + 1)) :
    g.syncGame.D x y a b = g.toGame.D x y a b := rfl

/-! ## The two synchronous values

`HaltingGameValue.gameValue g.toGame` and `MIPRE.syncValue g.syncGame` are suprema of the same
quantity over two packagings of the same strategies; the two packagings are exhibited here and
the suprema identified.
-/

/-- A synchronous strategy in the self-contained vocabulary of `MIPRE.HaltingGameValue`, read as
a synchronous strategy of the foundations: the same dimension, and the POVM elements as the
operators of the projective measurement (self-adjointness and normalization are the POVM's own,
projectivity its certificate). -/
noncomputable def toSyncStrategy (g : GameData) (S : SyncStrategy g.toGame) :
    MIPRE.SyncStrategy g.syncGame where
  d := S.d
  d_pos := S.d_pos
  P :=
    { M := fun x a => ((S.povm x).mats a).val
      selfAdjoint := fun x a => selfAdjoint.mem_iff.mp ((S.povm x).mats a).property
      projective := S.projective
      normalized := fun x => by
        have h := congrArg Subtype.val (S.povm x).normalized
        rwa [AddSubmonoidClass.coe_finsetSum, selfAdjoint.val_one] at h }

/-- A synchronous strategy of the foundations, read in the self-contained vocabulary: the same
dimension, and the operators of the projective measurement as the POVM elements (positivity
follows from projectivity, `MIPRE.SyncStrategy.povm`). -/
noncomputable def ofSyncStrategy (g : GameData) (S : MIPRE.SyncStrategy g.syncGame) :
    SyncStrategy g.toGame where
  d := S.d
  d_pos := S.d_pos
  povm x :=
    { mats := (S.povm x).mats
      nonneg := (S.povm x).nonneg
      normalized := (S.povm x).normalized }
  projective x a := S.P.projective x a

end HaltingGameValue.GameData
