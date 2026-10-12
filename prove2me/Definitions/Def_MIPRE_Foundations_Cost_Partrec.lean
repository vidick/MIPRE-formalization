/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Partrec.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Partrec
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_MachineData

/-!
# Ambient evaluation is partial recursive

The step of the evaluation machine on data is primitive recursive (`primrec_stepData`),
so evaluation — its `PFun.fix` from the initial configuration — is partial recursive
(`partrec_evalData`), and agrees with `Eval` (`mem_evalData_iff`). Consequently a
polynomial-time function of the ambient model is Mathlib-computable, as soon as its input
is produced by a computable encoding (`PolyTimeFun.computable_comp`). This is the bridge
from the ambient model to Mathlib's computability used by the halting-problem form of the
compression lemma; the other bridge (from `Nat.Partrec.Code` into the model) is
`Cost/FromPartrec.lean`.
-/

namespace MIPRE.Cost

namespace Machine

open Primrec

/-! ## The step is primitive recursive -/

/-! ## Evaluation as a fixed point -/

/-- One iteration of the evaluation loop: stop with the value on a final configuration,
otherwise step. -/
def evalStep (d : Data) : Data ⊕ Data :=
  if IsFinalD d then Sum.inl (resultD d) else Sum.inr (stepData d)

/-- Evaluation of the program `p` (as data) on `x`, as a partial function: the fixed
point of the evaluation loop from the initial configuration. -/
def evalData (p x : Data) : Part Data :=
  PFun.fix (fun d => Part.some (evalStep d)) (initData p x)

end Machine

/-! ## Polynomial-time functions are computable -/

end MIPRE.Cost
