/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryDegreeDecomposition.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryDegreeArithmetic
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryPrimality
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryPrimePower
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDegreeFactors

/-! # Executable prime-power decomposition of a unary requested degree -/

noncomputable section

namespace MIPRE.LowDegree.DegreeArithmetic

open Cost Cost.PolyTimeFun

/-- Enumerate all candidate prime indices in ascending order. -/
def ascendingUnary (u : Unary) : List Unary := (descendingUnary u).reverse

theorem descendingUnary_cons (u : Unary) :
    descendingUnary (() :: u) = (() :: u) :: descendingUnary u := by
  exact recordIterates_cons List.tail (() :: u) (() :: u)

/-- A polynomial-time ascending unary enumeration. -/
def ascendingUnaryProg : PolyTimeFun Unary (List Unary) := PolyTimeFun.reverse.comp descendingUnaryProg

@[simp] theorem ascendingUnaryProg_apply (u : Unary) : ascendingUnaryProg u = ascendingUnary u := rfl

/-- Prime indices paired with their maximal dividing prime power; neutral entries have power one. -/
def primePowerPairs (u : Unary) : List (Unary × Unary) :=
  (ascendingUnary u).map (fun q => (q, primePowerUnary u q))

/-- One globally polynomial-time prime-power decomposition program. -/
def primePowerPairsProg : PolyTimeFun Unary (List (Unary × Unary)) :=
  (mapWith (fst.pair (primePowerUnaryProg.comp (snd.pair fst)))).comp
    (ascendingUnaryProg.pair (PolyTimeFun.id _))

@[simp] theorem primePowerPairsProg_apply (u : Unary) : primePowerPairsProg u = primePowerPairs u := rfl

end MIPRE.LowDegree.DegreeArithmetic

end
