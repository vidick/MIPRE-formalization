/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingQueries.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Theorems.Thm_MIPRE_CL_proj_add_proj_compl
import Theorems.Thm_MIPRE_CL_pull_proj_compl

/-! # Query routing for the detyped CL presentation

The semantic specification of all branches of `types.tex`, `def:detyped-sampler`.
The level indices of factor and linear queries are zero based, as in `CLFun`.
These are equalities of the actual presentations' queries, not extra assumptions
on a future sampler program.
-/

noncomputable section

namespace MIPRE.CL

open Finset Classical

namespace CLFun

variable {F ι : Type*} [Semiring F] [DecidableEq ι] {k ℓ : ℕ}

end CLFun

namespace Detyping

variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]

set_option linter.unusedSectionVars false

theorem content_proj_graph_compl (S : Finset (Graph.Coord T))
    (x : Coord T ι → ZMod 2) :
    pull .inr (proj (S.map Function.Embedding.inl)ᶜ x) = pull .inr x := by
  funext i
  simp [pull]

theorem graph_prefix (S : Finset (Graph.Coord T)) (x : Coord T ι → ZMod 2) :
    pull .inl (proj (S.map Function.Embedding.inl) x +
      proj (Sᶜ.map Function.Embedding.inl) (proj (S.map Function.Embedding.inl)ᶜ x)) =
      pull .inl x := by
  rw [pull_add, pull_proj, pull_proj, pull_proj_compl, proj_proj_self, proj_add_proj_compl]

end Detyping
end MIPRE.CL
