/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/ManyOne.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecBasis
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.RE
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Cost_Kleene
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Partrec
import Definitions.Def_MIPRE_Foundations_Cost_Partrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Semidecide

/-!
# The many-one reduction of an r.e. language to halting, in polynomial time

`Cost.exists_semidecider` turns an r.e. predicate on strings into a well-scoped program `S`
halting on `encode z` exactly on its members. The reduction to halting *on the empty input*
hard-codes `z` into `S` — the s-m-n theorem — and `hardcode` is linear time, so the map
`z ↦ M_z` is a `PolyTimeFun`. `Halting.exists_code_halts_of_isRE` is the same reduction on
Mathlib's `Nat.Partrec.Code` through `Code.curry`, with no time tracked; the polynomial-time
halting reduction (`planning/polytime-halting.md`) needs this one.

`hardcode p d` runs `p` on `cons d v` where `v` is the input, so on the empty input `nil` it
runs `p` on `cons d nil`; `Prog.onLeft p` is the program running `p` on the left component of
its input, and `M_z = hardcode (onLeft S) (encode z)`.
-/

namespace MIPRE.Cost

/-- On the input `cons d v`, run `p` on `d`; on `nil`, halt with `nil`. -/
def Prog.onLeft (p : Prog) : Prog := .elim 0 .nil (Prog.callVar 0 p)

/-- The reduction: `z ↦ hardcode (onLeft S) (encode z)`, in linear time. -/
noncomputable def haltingReduction (S : Prog) : PolyTimeFun BitStr Prog :=
  (PolyTimeFun.smn BitStr).comp ((PolyTimeFun.const (Prog.onLeft S)).pair (PolyTimeFun.id BitStr))

@[simp] theorem haltingReduction_apply (S : Prog) (z : BitStr) :
    haltingReduction S z = hardcode (Prog.onLeft S) (encode z) := rfl

end MIPRE.Cost
