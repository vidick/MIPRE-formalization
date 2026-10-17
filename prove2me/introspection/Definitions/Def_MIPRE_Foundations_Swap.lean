/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Swap.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue

/-!
# Exchanging the two players

A game whose question distribution and decision predicate are both symmetric in the players is
unchanged by exchanging them, and so is the value of a strategy once the state is swapped
(`povmValue_swapVec_of_symm`). That is what turns a one-sided soundness statement --- one proved
about Alice's measurements, with Bob's only as the other party --- into the statement about
**Bob's**, with no second proof: apply it to `(MB, MA)` on `swapVec ψ`, and read the conclusion
back through `norm_stateVecB`.

The Pauli basis test is such a game: every rule of its decider is written in both orientations
(`MIPRE.QLD.accepts_symm`) and its sampler draws an *ordered* edge of a symmetric type graph
(`MIPRE.QLD.qldGame_mu_symm`). Its combining stage needs both players' commutation bounds, which
is why this is here.
-/

noncomputable section

namespace MIPRE

open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker

variable {X A dA dB : Type*} [Fintype X] [Fintype A] [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB]

omit [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB] in
@[simp] theorem swapVec_swapVec (ψ : dA × dB → ℂ) : swapVec (swapVec ψ) = ψ := rfl

end MIPRE

end
