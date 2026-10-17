/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/POVMValue.lean (solution of MIPRE.bornProb_nonneg);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_POVMValue

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
omit [DecidableEq dA] [DecidableEq dB] in
theorem _root_.solution (ψ : dA × dB → ℂ) {EA : Matrix dA dA ℂ} {EB : Matrix dB dB ℂ}
    (hA : EA.PosSemidef) (hB : EB.PosSemidef) : 0 ≤ bornProb ψ EA EB :=
  (Complex.nonneg_iff.mp ((hA.kronecker hB).dotProduct_mulVec_nonneg ψ)).1
end MIPRE
