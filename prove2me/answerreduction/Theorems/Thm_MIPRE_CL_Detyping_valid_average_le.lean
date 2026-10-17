/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingSoundness.lean (statement stub of MIPRE.CL.Detyping.valid_average_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame

open MIPRE
open MIPRE.CL
open MIPRE.CL.Detyping
open Finset Classical
variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]

theorem MIPRE.CL.Detyping.valid_average_le (E : T → T → Prop) [DecidableRel E] (hne : (Graph.edges E).Nonempty)
    (f : (Graph.Coord T → ZMod 2) → (ι → ZMod 2) → ℝ) (hf : ∀ g v, 0 ≤ f g v) :
    (∑ g ∈ Graph.validSeeds E, ∑ v, f g v) /
        ((Graph.validSeeds E).card * Fintype.card (ι → ZMod 2)) ≤
      (16 : ℝ) ^ Fintype.card T *
        ((∑ g, ∑ v, f g v) / ((16 : ℝ) ^ Fintype.card T * Fintype.card (ι → ZMod 2))) := by sorry
