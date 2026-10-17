/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/CircuitArithmetization.lean (statement stub of MIPRE.SAT.Circuit.eval_gateArith);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_Foundations_SAT_InputRouting
import Definitions.Def_MIPRE_Foundations_SAT_CircuitArithmetization

open MIPRE
open MIPRE.SAT
open MIPRE.SAT.Circuit
open MvPolynomial MIPRE.LowDegree Finset
variable {F : Type*} [Field F]

theorem MIPRE.SAT.Circuit.eval_gateArith (C : Circuit) (k : ℕ) (g : Gate) (x w : ℕ → Bool)
    (href : ∀ u ∈ g.refs, u < k) :
    MvPolynomial.eval (Sum.elim (fun i => (ofBool (x i) : F)) (fun j => ofBool (w j)))
      (C.gateArith k g) = ofBool (g.eval
        (fun i => Sum.elim x w (C.inputRef k i)) (List.ofFn fun j : Fin k => w j)) := by sorry
