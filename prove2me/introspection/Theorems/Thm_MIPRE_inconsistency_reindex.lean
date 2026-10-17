/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/RegisterReindex.lean (statement stub of MIPRE.inconsistency_reindex);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B

open MIPRE
open Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {dA dB dA' dB' : Type*}
variable [Fintype dA] [Fintype dB] [Fintype dA'] [Fintype dB']
variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dA'] [DecidableEq dB']
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem MIPRE.inconsistency_reindex [DecidableEq A] (eA : dA ≃ dA') (eB : dB ≃ dB') (μ : X → ℝ)
    (ψ : dA × dB → ℂ) (M : X → POVM A dA) (N : X → POVM A dB) :
    inconsistency μ (reindexVec eA eB ψ) (fun x => (M x).reindex eA) (fun x => (N x).reindex eB)
      = inconsistency μ ψ M N := by sorry
