/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/TypeGraph.lean (definition bundle: declarations the uploaded statements rest on);
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

/-! # The introspection type graph

The graph of `introspection.tex`, Figure `fig:type-graph-intro`: the Pauli
subgraph, two chains from Pauli-X through hiding levels to Read, two chains
from Pauli-Z through Sample and Introspect to Read, the cross-introspection
edge, and a loop at every vertex. The construction uses only the Pauli graph
and its two distinguished vertices; no rigidity conclusion is assumed.
-/

namespace MIPRE.Introspection.TypeGraph

open QuestionType Finset

variable {PauliType : Type*} [DecidableEq PauliType] {ℓ : ℕ}

set_option linter.unusedSectionVars false

/-- One orientation of each edge drawn in the source figure. -/
def oriented (E : PauliType → PauliType → Bool) (X Z : PauliType) :
    QuestionType PauliType ℓ → QuestionType PauliType ℓ → Bool
  | .inl p, .inl q => E p q
  | .inl p, .inr (.hide k, _) => decide (p = X ∧ k.val = 0)
  | .inl p, .inr (.sample, _) => decide (p = Z)
  | .inr (.hide k, w), .inr (.hide k', w') => decide (w = w' ∧ k.val + 1 = k'.val)
  | .inr (.hide k, w), .inr (.read, w') => decide (w = w' ∧ k.val + 1 = ℓ)
  | .inr (.sample, w), .inr (.introspect, w') => decide (w = w')
  | .inr (.introspect, w), .inr (.read, w') => decide (w = w')
  | .inr (.introspect, w), .inr (.introspect, w') => decide (w ≠ w')
  | _, _ => false

/-- The graph is undirected and has a self-loop at every type. -/
def adj (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (t u : QuestionType PauliType ℓ) : Bool :=
  decide (t = u) || oriented E X Z t u || oriented E X Z u t

/-- Propositional adjacency, for the graph sampler and finite detyping theorem. -/
abbrev Adj (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (t u : QuestionType PauliType ℓ) : Prop := adj E X Z t u = true

@[simp] theorem adj_self (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (t : QuestionType PauliType ℓ) : adj E X Z t t = true := by simp [adj]

variable [Fintype PauliType]

/-- The actual ordered edge set used by the typed game's distribution. -/
def edges (E : PauliType → PauliType → Bool) (X Z : PauliType) (ℓ : ℕ) :=
  CL.Graph.edges (Adj (ℓ := ℓ) E X Z)

end MIPRE.Introspection.TypeGraph
