/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/FiniteCircuitArithmetization.lean (statement stub of MIPRE.SAT.Circuit.eval_iff_exists_finiteArith);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_Foundations_SAT_InputRouting
import Definitions.Def_MIPRE_Foundations_SAT_CircuitArithmetization
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteVariables
import Definitions.Def_MIPRE_Foundations_SAT_FiniteCircuitArithmetization

open MIPRE
open MIPRE.SAT
open MIPRE.SAT.Circuit
open MvPolynomial MIPRE.LowDegree
variable {F : Type*} [Field F]
variable [CharP F 2]

theorem MIPRE.SAT.Circuit.eval_iff_exists_finiteArith (C : Circuit) (hC : C.WellFormed) (x : ℕ → Bool) :
    C.eval x = true ↔ ∃ z : Fin (C.inputs + C.size) → Bool,
      (∀ i : Fin C.inputs, z (Fin.castAdd C.size i) = x i) ∧
      MvPolynomial.eval (fun i => (ofBool (z i) : F)) C.finiteArith = 1 := by sorry
