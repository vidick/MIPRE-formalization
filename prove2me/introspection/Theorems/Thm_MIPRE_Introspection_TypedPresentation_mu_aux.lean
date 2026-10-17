/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/TypedPresentation.lean (statement stub of MIPRE.Introspection.TypedPresentation.mu_aux);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_Introspection_Types
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPresentation

open MIPRE
open MIPRE.Introspection
open MIPRE.Introspection.TypedPresentation
open Finset Classical
variable {PauliType F ι : Type*} [Fintype ι] [DecidableEq ι] [Semiring F] {ℓ : ℕ}
variable [Fintype PauliType] [DecidableEq PauliType]
  {A B : Type*} [Fintype A] [Fintype B]

theorem MIPRE.Introspection.TypedPresentation.mu_aux (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) ι 3)
    (D : CL.Detyping.Question (QuestionType PauliType ℓ) ι →
      CL.Detyping.Question (QuestionType PauliType ℓ) ι → A → B → Bool)
    (t u : AuxType ℓ) (w w' : Bool)
    (h : TypeGraph.Adj E X Z (.inr (t, w)) (.inr (u, w'))) :
    (game E X Z ℓ P D).μ (.inr (t, w), 0) (.inr (u, w'), 0) =
      ((TypeGraph.edges E X Z ℓ).card : ℝ)⁻¹ := by sorry
