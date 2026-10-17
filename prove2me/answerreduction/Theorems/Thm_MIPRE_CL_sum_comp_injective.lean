/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Presentation.lean (statement stub of MIPRE.CL.sum_comp_injective);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Background_LIDT_Presentation

open MIPRE
open MIPRE.CL
open Finset

theorem MIPRE.CL.sum_comp_injective {κ ι F M : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F] [AddCommMonoid M] (e : κ → ι)
    (he : Function.Injective e) (g : (κ → F) → M) :
    ∑ x : ι → F, g (x ∘ e)
      = (Fintype.card F ^ (Fintype.card ι - Fintype.card κ)) • ∑ y : κ → F, g y := by sorry
