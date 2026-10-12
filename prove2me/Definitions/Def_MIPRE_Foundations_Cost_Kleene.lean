/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Kleene.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
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

/-!
# Efficient Kleene recursion

The efficient fixed-point theorem `efficient_fixed_point` (blueprint `lem:kleene`;
[MNY, Lemma 2.3]), by the classical construction: for a polynomial-time map `F` on
programs, let `G` be the program that on `cons x v` (with `x` the description of a program
`x'`) computes `s(x', x') = hardcode x' (encode x')`, applies `F` to it, and runs the result
on `v` through the universal machine; the fixed point is `e = hardcode G (encode G)`, since
`e` on `v` is `G` on `cons (encode G) v`, which runs `F (hardcode G (encode G)) = F e` on
`v`. The time transfer is the universal machine's, plus the fixed cost of computing `F e`
and a copy of the input.
-/

namespace MIPRE.Cost

open Polynomial

namespace Prog

/-- The two-argument program of the fixed-point construction: on `cons x v`, compute the
description of `hardcode x' (encode x')` (where `x = encode x'`), apply `F` to it, and run
the result on `v` through the universal program `univ`. -/
def kleeneProg (univ : Prog) (F : PolyTimeFun Prog Prog) : Prog :=
  .elim 0 .nil
    (.let_ (.cons (.var 0) (.var 0))
      (.let_ (callVar 0 smnProg)
        (.let_ (callVar 0 F.code)
          (.let_ (.cons (.var 0) (.var 4))
            (callVar 0 univ)))))

end Prog

/-! ## The fixed point, as data

The construction is exposed (`kleeneFix`) with its overhead spelled out (`kleeneFix_runs_of`),
because the polynomial-time halting reduction (`planning/polytime-halting.md`) needs the overhead
of the fixed point of a *family* `F_M` of maps to be bounded uniformly in `M`: the existential
polynomial of `efficient_fixed_point` below depends on `F`, and only the explicit form shows how. -/

/-- The fixed point of `F` through the universal machine `U`: `hardcode G (encode G)` for the
program `G = kleeneProg U.univ F`. -/
def kleeneFix (U : UniversalMachine) (F : PolyTimeFun Prog Prog) : Prog :=
  hardcode (Prog.kleeneProg U.univ F) (encode (Prog.kleeneProg U.univ F))

/-- The fixed part of the overhead of the fixed point: the copies of the program, the
computation of `F (kleeneFix U F)`, and constants. -/
def kleeneOverhead (U : UniversalMachine) (F : PolyTimeFun Prog Prog) : ℕ :=
  7 * esize (Prog.kleeneProg U.univ F) + esize (kleeneFix U F) +
    F.timeBound.eval (esize (kleeneFix U F)) + 2 * esize (F (kleeneFix U F)) + 60

/-! ## The fixed-point theorem (blueprint `lem:kleene`; [MNY, Lemma 2.3]) -/

end MIPRE.Cost
