/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.TailoredGameValue
public import MIPRE.Foundations.GameDescription
public import MIPRE.Tailored.Fourier
public import MIPRE.Tailored.SignedPerm
public import MIPRE.Tactics

@[expose] public section

/-!
# Tailored game descriptions, read as games of the foundations

`MIPRE/TailoredGameValue.lean` states `TMIP* = RE` in the self-contained vocabulary of
`MIPRE.HaltingGameValue`: its games are `HaltingGameValue.SynchronousGame`s, its value the
synchronous value `HaltingGameValue.gameValue`, and its strategies the permutation strategies
`TailoredGameValue.PermStrategy`. This file reads them in the foundations, where the quantum value
`MIPRE.quantumValue` lives, as `MIPRE/Foundations/GameDescription.lean` does for
`HaltingGameValue.GameData`.

* `HaltingGameValue.SynchronousGame.toMIPRE`: a synchronous game of the self-contained vocabulary,
  as a `MIPRE.SynchronousGame` — the same fields — and `gameValue_eq_syncValue`,
  `gameValue_le_quantumValue`: its synchronous value is `MIPRE.syncValue` of it, and is at most its
  quantum value. The strategy repackagings are `GameDescription.lean`'s, for any game.
* `TailoredGameData.syncGame`, `TailoredGameData.game`: a tailored game description read so.
* `PermStrategy.toSync`: a permutation strategy of a description is a synchronous strategy of it,
  with the same value. Its measurements are the Fourier transforms of commuting self-adjoint
  involutions — the observables are signed permutation matrices, so self-adjoint once involutive
  (`IsSignedPerm.isHermitian`) — hence projective (`isPVMIn_fourierProj`).
* `HasPerfectZPC.gameValue_eq_one`, `HasPerfectZPC.quantumValue_eq_one`: a perfect ZPC strategy
  gives synchronous and quantum value `1`.
-/

namespace HaltingGameValue.SynchronousGame

variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A] (G : SynchronousGame X A)

/-- The same game, as a `MIPRE.SynchronousGame`. -/
noncomputable def toMIPRE : MIPRE.SynchronousGame X A where
  μ := G.μ
  μ_nonneg := G.μ_nonneg
  μ_sum_one := G.μ_sum_one
  D := G.D
  synchronous := G.synchronous

/-- A synchronous strategy of the self-contained vocabulary, as one of the foundations: the same
dimension and operators. -/
noncomputable def toSyncStrategy (S : SyncStrategy G) : MIPRE.SyncStrategy G.toMIPRE where
  d := S.d
  d_pos := S.d_pos
  P :=
    { M := fun x a => ((S.povm x).mats a).val
      selfAdjoint := fun x a => selfAdjoint.mem_iff.mp ((S.povm x).mats a).property
      projective := S.projective
      normalized := fun x => by
        have h := congrArg Subtype.val (S.povm x).normalized
        rwa [AddSubmonoidClass.coe_finsetSum, selfAdjoint.val_one] at h }

/-- A synchronous strategy of the foundations, in the self-contained vocabulary. -/
noncomputable def ofSyncStrategy (S : MIPRE.SyncStrategy G.toMIPRE) : SyncStrategy G where
  d := S.d
  d_pos := S.d_pos
  povm x :=
    { mats := (S.povm x).mats
      nonneg := (S.povm x).nonneg
      normalized := (S.povm x).normalized }
  projective x a := S.P.projective x a

theorem value_toSyncStrategy (S : SyncStrategy G) :
    (G.toSyncStrategy S).value = strategyValue G S := by
  rw [MIPRE.SyncStrategy.value_eq]
  rfl

theorem strategyValue_ofSyncStrategy (S : MIPRE.SyncStrategy G.toMIPRE) :
    strategyValue G (G.ofSyncStrategy S) = S.value := by
  rw [MIPRE.SyncStrategy.value_eq]
  rfl

theorem strategyValue_nonneg (S : SyncStrategy G) : 0 ≤ strategyValue G S := by
  rw [← value_toSyncStrategy]
  exact (G.toSyncStrategy S).value_nonneg

theorem strategyValue_le_one (S : SyncStrategy G) : strategyValue G S ≤ 1 := by
  rw [← value_toSyncStrategy]
  exact (G.toSyncStrategy S).value_le_one

theorem bddAbove_range_strategyValue :
    BddAbove (Set.range fun S : SyncStrategy G => strategyValue G S) :=
  ⟨1, by rintro r ⟨S, rfl⟩; exact G.strategyValue_le_one S⟩

theorem gameValue_nonneg : 0 ≤ gameValue G :=
  Real.iSup_nonneg fun S => G.strategyValue_nonneg S

/-- **The two synchronous values agree.** -/
theorem gameValue_eq_syncValue : gameValue G = MIPRE.syncValue G.toMIPRE := by
  apply le_antisymm
  · refine Real.iSup_le (fun S => ?_) (MIPRE.syncValue_nonneg _)
    rw [← G.value_toSyncStrategy S]
    exact le_ciSup (MIPRE.SyncStrategy.bddAbove_range_value _) (G.toSyncStrategy S)
  · refine Real.iSup_le (fun S => ?_) G.gameValue_nonneg
    rw [← G.strategyValue_ofSyncStrategy S]
    exact le_ciSup G.bddAbove_range_strategyValue (G.ofSyncStrategy S)

/-- **The synchronous value is at most the quantum value** (`lem:sync-le-valstar`). -/
theorem gameValue_le_quantumValue : gameValue G ≤ MIPRE.quantumValue G.toMIPRE.toGame := by
  rw [G.gameValue_eq_syncValue]
  exact MIPRE.syncValue_le_quantumValue _

end HaltingGameValue.SynchronousGame

namespace TailoredGameValue

open HaltingGameValue

/-- The signed permutation matrices of the self-contained statement are the library's. -/
theorem signedPermMatrix_eq {m : ℕ} (σ : Equiv.Perm (Fin m)) (s : Fin m → Bool) :
    signedPermMatrix σ s = MIPRE.Tailored.signedPermMatrix σ s := rfl

namespace TailoredGameData

variable (g : TailoredGameData)

/-- A tailored game description, as a synchronous game of the foundations. -/
noncomputable abbrev syncGame : MIPRE.SynchronousGame (Fin (g.nV + 1)) (Fin g.ansLen → Bool) :=
  g.toGame.toMIPRE

/-- A tailored game description, as a two-player game of the foundations. -/
noncomputable abbrev game :
    MIPRE.Game (Fin (g.nV + 1)) (Fin (g.nV + 1)) (Fin g.ansLen → Bool) (Fin g.ansLen → Bool) :=
  g.syncGame.toGame

theorem gameValue_le_quantumValue : gameValue g.toGame ≤ MIPRE.quantumValue g.game :=
  g.toGame.gameValue_le_quantumValue

end TailoredGameData

namespace PermStrategy

variable {g : TailoredGameData} (S : PermStrategy g)

/-- The measurements are the library's Fourier transforms of the observables. -/
theorem proj_eq (x : Fin (g.nV + 1)) (a : Fin g.ansLen → Bool) :
    S.proj x a = MIPRE.Tailored.fourierProj (S.U x) a := rfl

/-- The observables are self-adjoint: involutive signed permutation matrices. -/
theorem star_U (x : Fin (g.nV + 1)) (i : Fin g.ansLen) : star (S.U x i) = S.U x i := by
  obtain ⟨σ, s, h⟩ := S.signedPerm x i
  have hM : MIPRE.Tailored.IsSignedPerm (S.U x i) := ⟨σ, s, h⟩
  exact (hM.isHermitian (S.invol x i)).eq

/-- The measurements are projective. -/
theorem isPVMIn_proj (x : Fin (g.nV + 1)) : MIPRE.IsPVMIn (S.proj x) := by
  have h : S.proj x = MIPRE.Tailored.fourierProj (S.U x) := funext (S.proj_eq x)
  rw [h]
  exact MIPRE.Tailored.isPVMIn_fourierProj (S.invol x) (S.star_U x) (fun i j => S.comm x i j)

/-- **A permutation strategy is a synchronous strategy**, with the same dimension and the Fourier
transforms as its measurements. -/
noncomputable def toSync : MIPRE.SyncStrategy g.syncGame where
  d := S.m
  d_pos := S.m_pos
  P :=
    { M := S.proj
      selfAdjoint := fun x a => (S.isPVMIn_proj x).star_eq a
      projective := fun x a => (S.isPVMIn_proj x).idem a
      normalized := fun x => (S.isPVMIn_proj x).sum_eq_one }

/-- **It has the same value.** -/
theorem value_toSync : S.toSync.value = S.value := by
  rw [MIPRE.SyncStrategy.value_eq]
  rfl

end PermStrategy

namespace TailoredGameData

variable {g : TailoredGameData}

/-- **A perfect ZPC strategy gives synchronous value `1`** in the foundations. -/
theorem HasPerfectZPC.syncValue_eq_one (h : g.HasPerfectZPC) : MIPRE.syncValue g.syncGame = 1 := by
  obtain ⟨S, hS⟩ := h
  refine le_antisymm (MIPRE.syncValue_le_one _) ?_
  rw [← hS, ← S.value_toSync]
  exact le_ciSup (MIPRE.SyncStrategy.bddAbove_range_value _) S.toSync

/-- **A perfect ZPC strategy gives synchronous value `1`.** -/
theorem HasPerfectZPC.gameValue_eq_one (h : g.HasPerfectZPC) : gameValue g.toGame = 1 := by
  rw [g.toGame.gameValue_eq_syncValue]
  exact h.syncValue_eq_one

/-- **A perfect ZPC strategy gives quantum value `1`.** -/
theorem HasPerfectZPC.quantumValue_eq_one (h : g.HasPerfectZPC) :
    MIPRE.quantumValue g.game = 1 := by
  refine le_antisymm (MIPRE.quantumValue_le_one _) ?_
  rw [← h.syncValue_eq_one]
  exact MIPRE.syncValue_le_quantumValue _

end TailoredGameData

end TailoredGameValue

end
