/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Interpreter.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_MachineData

/-!
# The self-interpreter, I: the step function as a program

Programs of the ambient model implementing the step function of the evaluation machine on
data (`Machine.stepData`, `Cost/MachineData.lean`): `stepEvProg` for "evaluate" controls,
`stepRetProg` for "return" controls, and `stepProg` combining them. Each is proved to
compute `stepData` on encoded configurations, at a cost quadratic in the size of the
configuration (the only non-constant work is the walk `getListProg` along the environment,
which copies the remaining environment at each of its steps).

Conventions: every sub-program is closed and receives its input, a tuple built with
`cons`, at variable `0`; tuples are taken apart with `elim` (free), and the pieces are read
back with `var` (paid by size). Tag dispatch on a unary numeral is a chain of `elim`s; the
case programs are called through `callVar` on a packaged tuple whose index grows by two
per level of the chain.
-/

namespace MIPRE.Cost

namespace Machine

open Prog

/-- Discharge a linear inequality between costs and sizes, after expanding the sizes of
constructors and of encoded configurations. -/
macro "size_omega" : tactic =>
  `(tactic| ((try simp only [Data.size_cons, Data.size_nil, Data.size_ofNat, Frame.toData,
      Cfg.toData, Ctrl.toData, evD, retD, Prog.toData, Data.list_cons, Data.list_nil,
      List.map_cons, List.map_nil] at *); all_goals omega))

/-! ## Projections at an arbitrary index -/

/-- `left` of the value of variable `i`. -/
def projLeft (i : ℕ) : Prog := .elim i .nil (.var 0)

/-- `right` of the value of variable `i`. -/
def projRight (i : ℕ) : Prog := .elim i .nil (.var 1)

/-! ## The environment walk -/

/-- Body of `getListProg`: on the state `cons env idx`, stop with `left env` if `idx` is
exhausted, else continue with `cons (right env) idx'`. -/
def getListBody : Prog :=
  .elim 0 .nil (.elim 1 (.cons .nil (projLeft 0))
    (.cons (.cons .nil .nil) (.cons (projRight 2) (.var 1))))

/-- `getListProg` on `cons env idx` computes `getList env (unaryToNat idx)`. -/
def getListProg : Prog := .loop getListBody

/-! ## The "evaluate" cases -/

/-- Cases of `stepEvProg`; input `cons body (cons env kont)`. After the two `elim`s the
environment is `[env, kont, body, cons env kont, input]`. -/
def evVar : Prog :=
  .elim 0 .nil (.elim 1 .nil (.let_ (.cons (.var 0) (.var 2))
    (.let_ (callVar 0 getListProg) (.cons (.cons (.cons .nil .nil) (.var 0)) (.var 5)))))

def evNil : Prog :=
  .elim 0 .nil (.elim 1 .nil (.cons (.const (.cons (.cons .nil .nil) .nil)) (.var 3)))

def evCons : Prog :=
  .elim 0 .nil (.elim 1 .nil (.elim 2 .nil
    (.cons (.cons .nil (.var 0)) (.cons (.var 2)
      (.cons (.cons (.const (.ofNat 0)) (.cons (.var 1) (.var 2))) (.var 3))))))

def evElim : Prog :=
  .elim 0 .nil (.elim 1 .nil (.elim 2 .nil (.elim 1 .nil
    (.let_ (.cons (.var 4) (.var 2)) (.let_ (callVar 0 getListProg)
      (.elim 0 (.cons (.cons .nil (.var 2)) (.var 9))
        (.cons (.cons .nil (.var 5)) (.cons (.cons (.var 0) (.cons (.var 1) (.var 8))) (.var 9)))))))))

def evLet : Prog :=
  .elim 0 .nil (.elim 1 .nil (.elim 2 .nil
    (.cons (.cons .nil (.var 0)) (.cons (.var 2)
      (.cons (.cons (.const (.ofNat 2)) (.cons (.var 1) (.var 2))) (.var 3))))))

def evLoop : Prog :=
  .elim 0 .nil (.elim 1 .nil
    (.cons (.cons .nil (.var 2)) (.cons (.var 0)
      (.cons (.cons (.const (.ofNat 3)) (.cons (.var 2) (.var 0))) (.var 1)))))

def evConst : Prog :=
  .elim 0 .nil (.elim 1 .nil (.cons (.cons (.cons .nil .nil) (.var 2)) (.var 3)))

/-! ## Tag dispatch -/

/-- `dispatch cs i idx`: case analysis on the unary numeral at variable `i`, calling the
`k`-th program of `cs` on the tuple at variable `idx + 2 k` (each level of the chain binds
two more variables). -/
def dispatch : List Prog → ℕ → ℕ → Prog
  | [], _, _ => .nil
  | [c], _, idx => callVar idx c
  | c :: c' :: cs, i, idx => .elim i (callVar idx c) (dispatch (c' :: cs) 1 (idx + 2))

/-! ## The "evaluate" step -/

/-- The case programs of `stepEvProg`, indexed by the tag of the program. -/
def evCases : List Prog := [evVar, evNil, evCons, evElim, evLet, evLoop, evConst]

/-- The step on "evaluate `p`"; input `cons (toData p) (cons env kont)`. -/
def stepEvProg : Prog :=
  .elim 0 .nil (.elim 1 .nil (.elim 2 .nil
    (.let_ (.cons (.var 1) (.cons (.var 2) (.var 3))) (.let_ (.var 1) (dispatch evCases 0 1)))))

/-- The environment in which the dispatch of `stepEvProg` runs, for a program with tag `k`
and body `body`. -/
def dispEnv (k : ℕ) (body env kont : Data) : Env :=
  [Data.ofNat k, .cons body (.cons env kont), .ofNat k, body, env, kont, .cons (.ofNat k) body,
    .cons env kont, .cons (.cons (.ofNat k) body) (.cons env kont)]

/-- Bound of one "evaluate" step in terms of `S = esize p + env.size + kont.size`. -/
def stepEvBound (S : ℕ) : ℕ := (S + 1) * (S + 30) + 100

/-! ## The "return" cases -/

/-- Cases of `stepRetProg`; input `cons v (cons env (cons fb k))` with `fb` the payload of
the top frame. After the three `elim`s the environment is
`[fb, k, env, cons fb k, v, cons env (cons fb k), input]`. -/
def retCons1 : Prog :=
  .elim 0 .nil (.elim 1 .nil (.elim 1 .nil (.elim 0 .nil
    (.cons (.cons .nil (.var 0)) (.cons (.var 1) (.cons (.cons (.const (.ofNat 1)) (.var 6)) (.var 3)))))))

def retCons2 : Prog :=
  .elim 0 .nil (.elim 1 .nil (.elim 1 .nil
    (.cons (.cons (.cons .nil .nil) (.cons (.var 0) (.var 4))) (.cons (.var 2) (.var 1)))))

def retLet1 : Prog :=
  .elim 0 .nil (.elim 1 .nil (.elim 1 .nil (.elim 0 .nil
    (.cons (.cons .nil (.var 0)) (.cons (.cons (.var 6) (.var 1)) (.var 3))))))

def retLoop1 : Prog :=
  .elim 0 .nil (.elim 1 .nil (.elim 1 .nil (.elim 0 .nil
    (.elim 6 (.cons (.const (.cons (.cons .nil .nil) .nil)) (.cons (.var 1) (.var 3)))
      (.elim 0 (.cons (.cons (.cons .nil .nil) (.var 1)) (.cons (.var 3) (.var 5)))
        (.cons (.cons .nil (.var 4)) (.cons (.cons (.var 3) (projRight 5))
          (.cons (.cons (.const (.ofNat 3)) (.cons (.var 4) (.cons (.var 3) (projRight 5))))
            (.var 7)))))))))

/-! ## The "return" step -/

/-- The case programs of `stepRetProg`, indexed by the tag of the top frame. -/
def retCases : List Prog := [retCons1, retCons2, retLet1, retLoop1]

/-- The step on "return `v`"; input `cons v (cons env kont)`. -/
def stepRetProg : Prog :=
  .elim 0 .nil (.elim 1 .nil (.elim 1 (.cons (.cons (.cons .nil .nil) (.var 2)) (.var 3))
    (.elim 0 .nil (.let_ (.cons (.var 6) (.cons (.var 4) (.cons (.var 1) (.var 3))))
      (.let_ (.var 1) (dispatch retCases 0 1))))))

/-- The environment in which the dispatch of `stepRetProg` runs, for a top frame with tag
`ftag` and payload `fb`. -/
def retDispEnv (ftag : ℕ) (fb v env k : Data) : Env :=
  [Data.ofNat ftag, .cons v (.cons env (.cons fb k)), .ofNat ftag, fb, .cons (.ofNat ftag) fb, k,
    env, .cons (.cons (.ofNat ftag) fb) k, v, .cons env (.cons (.cons (.ofNat ftag) fb) k),
    .cons v (.cons env (.cons (.cons (.ofNat ftag) fb) k))]

/-- Bound of one "return" step in terms of `S = v.size + env.size + kont.size`. -/
def stepRetBound (S : ℕ) : ℕ := 8 * S + 120

/-! ## The step -/

/-- The step function as a program: on the encoding of a configuration, the encoding of
the next configuration. -/
def stepProg : Prog :=
  .elim 0 .nil (.elim 0 .nil (.let_ (.cons (.var 1) (.var 3))
    (.elim 1 (callVar 0 stepEvProg) (callVar 2 stepRetProg))))

/-- Bound of one step of the interpreter in terms of the size of the configuration. -/
def stepBound (S : ℕ) : ℕ := (S + 1) * (S + 40) + 200

end Machine

end MIPRE.Cost
