/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Repetition/TensorPower.lean (statement stub of MIPRE.exists_perfectPCC_repeat_doubled);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Background_Repetition_Direct
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_TensorFamily
import Definitions.Def_MIPRE_Background_Repetition_TensorPower

open MIPRE
open Matrix
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]

theorem MIPRE.exists_perfectPCC_repeat_doubled {G : Game X X A A} (k : ℕ)
    (h : ∃ S : SyncStrategy G.doubled, S.IsPCC ∧ S.value = 1) :
    ∃ S' : SyncStrategy (G.repeat k).doubled, S'.IsPCC ∧ S'.value = 1 := by sorry
