/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/FromPartrec.lean (delta bundle: declarations the new statements need that the published bundle Def_MIPRE_Foundations_Cost_FromPartrec does not carry);
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
import Theorems.Thm_MIPRE_Cost_Prog_ofCode_complete
import Theorems.Thm_MIPRE_Cost_Prog_ofCode_sound

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

namespace Prog

/-! ## Forward runs of the pieces -/

/-! ## Soundness -/

/-! ## Completeness -/

/-- Halting of the translation of `c` on `encL v` is halting of `c` on `v`. -/
theorem ofCode_halts_iff (c : Code) (v : List ℕ) :
    Halts (ofCode c) (encL v) ↔ (c.eval v).Dom := by
  constructor
  · rintro ⟨r, t, h⟩
    obtain ⟨w, -, hw⟩ := ofCode_complete c v r t h
    exact Part.dom_iff_mem.2 ⟨w, hw⟩
  · intro h
    obtain ⟨w, hw⟩ := Part.dom_iff_mem.1 h
    obtain ⟨t, ht⟩ := ofCode_sound c v w hw
    exact ⟨_, t, ht⟩

end Prog

/-! ## The halting-problem bridge -/

end MIPRE.Cost
