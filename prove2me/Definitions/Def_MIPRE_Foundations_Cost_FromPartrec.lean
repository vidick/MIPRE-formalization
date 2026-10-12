/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/FromPartrec.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
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
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Definitions.Def_MIPRE_Foundations_Cost_Kleene

/-!
# From Mathlib's partial recursive functions into the ambient model

Mathlib's `Turing.ToPartrec.Code` is a small first-order language on lists of naturals
(`zero'`, `succ`, `tail`, `cons`, `comp`, `case`, `fix`) in which every partial recursive
function is computable (`Turing.ToPartrec.Code.exists_code`). It translates construct by
construct into the ambient language (`Prog.ofCode`), with lists of naturals encoded as
`cons`-chains of unary numerals (`encL`) and `fix` as a `loop`; `ofCode_sound` and
`ofCode_complete` are the two directions of the correctness of the translation.

`exists_compile` is the resulting bridge for the halting problem: a map `compile` from
`Nat.Partrec.Code` to programs, computable on descriptions, such that `compile pc` halts on
the empty input iff `pc` does on `0`: `compile pc` hardcodes the code number of `pc` into
the translation of a `ToPartrec.Code` for the universal partial function `n ↦ (ofNat n).eval 0`.
-/

namespace MIPRE.Cost

open Turing.ToPartrec (Code)

/-- Lists of naturals as data: a `cons`-chain of unary numerals. -/
def encL (v : List ℕ) : Data := Data.list (v.map Data.ofNat)

@[simp] theorem encL_nil : encL [] = .nil := rfl

@[simp] theorem encL_cons (n : ℕ) (v : List ℕ) : encL (n :: v) = .cons (.ofNat n) (encL v) := rfl

namespace Prog

/-- The body of the translation of `fix f`: run `f`, then dispatch on the head of the
result (stop with the tail if it is `0`, continue with the tail otherwise). -/
def fixBody (pf : Prog) : Prog :=
  .let_ (callVar 0 pf)
    (.elim 0 (.cons .nil .nil) (.elim 0 (.cons .nil (.var 1)) (.cons (.cons .nil .nil) (.var 3))))

/-- The `headI :: tail` assembly of the translation of `cons f fs`, in an environment
`[fs v, f v, v]`. -/
def consTail : Prog := .cons (.elim 1 .nil (.var 0)) (.var 0)

/-- Translation of `ToPartrec.Code` into the ambient language. -/
def ofCode : Code → Prog
  | .zero' => .cons .nil (.var 0)
  | .succ => .elim 0 (.cons (.cons .nil .nil) .nil) (.cons (.cons .nil (.var 0)) .nil)
  | .tail => .elim 0 .nil (.var 1)
  | .cons f fs => .let_ (ofCode f) (.let_ (callVar 1 (ofCode fs)) consTail)
  | .comp f g => .let_ (ofCode g) (ofCode f)
  | .case f g =>
    .elim 0 (callVar 0 (ofCode f))
      (.elim 0 (callVar 1 (ofCode f)) (.let_ (.cons (.var 1) (.var 3)) (callVar 0 (ofCode g))))
  | .fix f => .loop (fixBody (ofCode f))

/-! ## Forward runs of the pieces -/

/-- The result of the dispatch of `fixBody` on the value `fv` of `f`. -/
def fixFlag : List ℕ → Data
  | [] => .cons .nil .nil
  | 0 :: t => .cons .nil (encL t)
  | (_ + 1) :: t => .cons (.cons .nil .nil) (encL t)

/-! ## Soundness -/

/-! ## Completeness -/

end Prog

/-! ## The halting-problem bridge -/

/-- The universal partial function on code numbers: `n ↦ (decode n).eval 0`. -/
noncomputable def univPart (n : ℕ) : Part ℕ :=
  ((Encodable.decode n : Option Nat.Partrec.Code) : Part Nat.Partrec.Code).bind fun c => c.eval 0

end MIPRE.Cost
