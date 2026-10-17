/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingProgBits.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingQueries

/-! # Contiguous graph and content encodings for detyping

The abstract sum of graph and content registers is numbered with the graph
first. Vector encodings are consequently ordinary concatenations of bit lists.
-/

noncomputable section

namespace MIPRE.CL.Detyping

open Finset Classical
set_option linter.unusedSectionVars false

variable {T : Type*} [Fintype T] [DecidableEq T]

abbrev graphDim (T : Type*) [Fintype T] := Fintype.card (Graph.Coord T)

def graphEquiv : Graph.Coord T ≃ Fin (graphDim T) := Fintype.equivFin _

def registerEquiv (s : ℕ) : Coord T (Fin s) ≃ Fin (graphDim T + s) :=
  (Equiv.sumCongr graphEquiv (Equiv.refl _)).trans finSumFinEquiv

def graphBits (g : Graph.Coord T → 𝔽₂) : Cost.BitStr :=
  toBits (push graphEquiv.toEmbedding g)

def graphOfBits (b : Cost.BitStr) : Graph.Coord T → 𝔽₂ :=
  pull graphEquiv.toEmbedding (ofBits (graphDim T) b)

@[simp] theorem graphOfBits_graphBits (g : Graph.Coord T → 𝔽₂) :
    graphOfBits (graphBits g) = g := by
  simp [graphBits, graphOfBits]

@[simp] theorem length_graphBits (g : Graph.Coord T → 𝔽₂) :
    (graphBits g).length = graphDim T := length_toBits _

/-- The actual numbered detyped CL presentation used by the machine interface. -/
def numbered {s ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Player)
    (P : T → CLFun 𝔽₂ (Fin s) ℓ) : CLFun 𝔽₂ (Fin (graphDim T + s)) (ℓ + 2) :=
  (presentation E w.toBool P).embed (registerEquiv s).toEmbedding

end MIPRE.CL.Detyping
