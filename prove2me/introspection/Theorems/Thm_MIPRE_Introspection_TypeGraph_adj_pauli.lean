/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/TypeGraph.lean (statement stub of MIPRE.Introspection.TypeGraph.adj_pauli);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_Introspection_Types
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph

open MIPRE
open MIPRE.Introspection
open MIPRE.Introspection.TypeGraph
open MIPRE.Introspection.QuestionType Finset
set_option linter.unusedSectionVars false
variable {PauliType : Type*} [DecidableEq PauliType] {ℓ : ℕ}

theorem MIPRE.Introspection.TypeGraph.adj_pauli (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (hE : ∀ p q, E p q = E q p) (hloop : ∀ p, E p p = true) (p q : PauliType) :
    adj (ℓ := ℓ) E X Z (pauli p) (pauli q) = E p q := by sorry
