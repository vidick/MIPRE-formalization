/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Universal.lean (definition bundle: declarations the uploaded statements rest on);
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

/-!
# The self-interpreter, II: the universal machines

The two universal machines of the toolkit (`Cost/Toolkit.lean`), built from the step
program `stepProg` of `Cost/Interpreter.lean`:

* `univProg` runs the evaluation machine (`Cost/Machine.lean`) from the initial
  configuration of `c` on `v` until a final configuration, as a `loop` whose body tests
  finality (`isFinalProg`) and otherwise steps. A halting run of cost `t` takes at most
  `3 t` machine steps (`eval_steps_count`), each on a configuration of size polynomial in
  `esize c + v.size + t` (`eval_steps_bound_forever`, `size_toData_le`), which gives the
  polynomial overhead (`UniversalMachine.time_le`); conversely a run of the loop is a
  machine run reaching a final configuration, hence a derivation (`halts_iff`).
* `univTProg` is the clocked variant: the loop additionally carries the remaining cost
  budget and a step budget `3 k + 1`, both in unary, and a size guard `Θ` (a polynomial in
  `k + esize c + v.size` computed in unary). The step budget makes the loop terminate; the
  cost budget, decremented by the exact cost of each step (`stepCostProg`, matching
  `stepCost`), decides whether the simulated run halts within cost `k`; the size guard keeps
  the configurations handled by the loop polynomially bounded even when the simulated run
  does not halt — it never fires on a run that halts within the budget, whose
  configurations are bounded by `Θ`.

This discharges `exists_efficient_universal` and `exists_clocked_universal` (blueprint
`lem:universal-tm`).
-/

namespace MIPRE.Cost

open Polynomial

namespace Machine

open Prog

/-! ## The final-configuration test -/

/-- On the encoding of a configuration: `cons nil r` if it is final with value `r`, `nil`
otherwise. -/
def isFinalProg : Prog :=
  .elim 0 .nil (.elim 0 .nil (.elim 0 .nil (.elim 5 .nil (.elim 1 (.cons .nil (.var 5)) .nil))))

/-! ## The interpreter loop -/

/-- Body of the interpreter loop: on a configuration, stop with its value if it is final,
otherwise continue with the next configuration. -/
def interpBody : Prog :=
  .let_ (callVar 0 isFinalProg)
    (.elim 0 (.cons (.cons .nil .nil) (callVar 1 stepProg)) (.cons .nil (.var 1)))

/-- Cost of one iteration of the interpreter loop on a configuration of size at most `S`. -/
def interpBodyBound (S : ℕ) : ℕ := stepBound S + 3 * S + 30

/-! ## The universal program -/

/-- On `cons c v`: the initial configuration of `c` on `v`, as data. -/
def univPrelude : Prog :=
  .elim 0 .nil (.cons (.cons .nil (.var 0)) (.cons (.cons (.var 1) .nil) .nil))

/-- The universal program: on `cons (encode c) v`, build the initial configuration of `c`
on `v` and run the interpreter loop. -/
def univProg : Prog := .let_ univPrelude (.loop interpBody)

/-- The size bound on the configurations of a halting run, in terms of
`X = esize c + v.size + t`. -/
def sigmaFun (X : ℕ) : ℕ := cfgSizeBound X (3 * X) X (2 * X)

/-- The time bound of the universal program, in terms of `X = esize c + v.size + t`. -/
def univBoundFun (X : ℕ) : ℕ := (3 * X + 1) * (interpBodyBound (sigmaFun X) + 1) + 2 * X + 11

/-! ## Unary arithmetic for the clock -/

/-- Loop body of `subProg`: on `cons a b` (unary), stop with the flagged difference
`cons (cons nil nil) (b - a)` if `a ≤ b`, with `nil` otherwise. -/
def subBody : Prog :=
  .elim 0 .nil (.elim 0 (.cons .nil (.cons (.cons .nil .nil) (.var 1)))
    (.elim 3 (.cons .nil .nil) (.cons (.cons .nil .nil) (.cons (.var 3) (.var 1)))))

/-- Unary subtraction with comparison: `subProg` on `cons (ofNat a) (ofNat b)` computes
`subResult a b`. -/
def subProg : Prog := .loop subBody

/-- The value of `subProg`: the flagged difference, or `nil` when `b < a`. -/
def subResult (a b : ℕ) : Data :=
  if a ≤ b then .cons (.cons .nil .nil) (.ofNat (b - a)) else .nil

/-- Cost bound of `subProg` on `cons (ofNat a) (ofNat b)`. -/
def subBound (a b : ℕ) : ℕ := (a + 1) * (2 * a + 2 * b + 14)

/-- Loop body of `tripleProg`: on `cons (ofNat n) (ofNat m)`, `ofNat (3 n + m)`. -/
def tripleBody : Prog :=
  .elim 0 .nil (.elim 0 (.cons .nil (.var 1))
    (.cons (.cons .nil .nil)
      (.cons (.var 1) (.cons .nil (.cons .nil (.cons .nil (.var 3)))))))

/-- `tripleProg` on `cons (ofNat n) (ofNat m)` computes `ofNat (3 n + m)`. -/
def tripleProg : Prog := .loop tripleBody

/-- Loop body of `repProg`: on `cons (ofNat n) (cons d acc)`, `n` copies of `d` consed
onto `acc`. -/
def repBody : Prog :=
  .elim 0 .nil (.elim 1 .nil (.elim 2 (.cons .nil (.var 1))
    (.cons (.cons .nil .nil) (.cons (.var 1) (.cons (.var 2) (.cons (.var 2) (.var 3)))))))

/-- `repProg` on `cons (ofNat n) (cons d (list acc))` computes `list (replicate n d ++ acc)`. -/
def repProg : Prog := .loop repBody

/-- Cost bound of `repProg` for `n` copies of a value of size `d` onto an accumulator of
size `a`. -/
def repBound (n d a : ℕ) : ℕ := (n + 1) * (4 * n + 4 * d + 2 * a + 30) + n * (n + 1) * (d + 1)

/-! ## The cost of a step, as a program -/

/-- Cost of a `var` step: `cons body env ↦ ofNat ((getList env body).size + 1)`. -/
def costVar : Prog :=
  .elim 0 .nil (.let_ (.cons (.var 1) (.var 0)) (.let_ (callVar 0 getListProg)
    (.let_ (callVar 0 sizeProg) (.cons .nil (.var 0)))))

/-- Cost of a `const` step: `cons d env ↦ ofNat d.size`. -/
def costConst : Prog := .elim 0 .nil (callVar 0 sizeProg)

/-- The case programs of the cost of an "evaluate" step, indexed by the tag. -/
def costCases : List Prog :=
  [costVar, .const (.ofNat 1), .const (.ofNat 1), .const (.ofNat 1), .const (.ofNat 1), .nil,
    costConst]

/-- The cost of an "evaluate" step; environment `[tag, payload, ctrl, rest, d]`. -/
def stepCostEv : Prog :=
  .elim 1 .nil (.let_ (.cons (.var 1) (projLeft 5)) (dispatch costCases 1 0))

/-- The cost of a "return" step: `1` at a `loop1` frame, `0` otherwise; environment
`[t₁, t₂, tag, payload, ctrl, rest, d]`. -/
def stepCostRet : Prog :=
  .elim 5 .nil (.elim 1 .nil (.elim 0 .nil (.elim 0 .nil (.elim 1 .nil
    (.elim 1 .nil (.const (.ofNat 1)))))))

/-- On the encoding of a configuration `c`: `ofNat (stepCost c)`. -/
def stepCostProg : Prog := .elim 0 .nil (.elim 0 .nil (.elim 0 stepCostEv stepCostRet))

/-- Cost bound of `stepCostProg` on a configuration of size `S`. -/
def stepCostBound (S : ℕ) : ℕ := (S + 1) * (7 * S + 32) + 13 * S + 50

/-! ## The clocked interpreter loop -/

/-- The state of the clocked loop: the configuration, the remaining cost budget, the
remaining step budget and the size guard (the last three in unary). -/
def clockState (d rem budget theta : Data) : Data := .cons d (.cons rem (.cons budget theta))

/-- Second half of a step of the clocked loop, after the cost subtraction succeeded:
step, then check the size of the new configuration against the guard; environment
`[cons nil nil, rem', sub, cr, nil, budget', nil, budget, theta, rem, r₂, d, r₁, s]`. -/
def clockRest : Prog :=
  .let_ (callVar 11 stepProg)
    (.let_ (.let_ (callVar 0 sizeProg) (.cons (.var 0) (.var 10)))
      (.let_ (callVar 0 subProg)
        (.elim 0 (.cons .nil .nil)
          (.cons (.cons .nil .nil)
            (.cons (.var 4) (.cons (.var 6) (.cons (.var 10) (.var 13))))))))

/-- The step of the clocked loop on a non-final configuration; environment
`[flag, budget, theta, rem, r₂, d, r₁, s]` with `flag = nil`: stop with `nil` if the step
budget is exhausted or the cost of the step exceeds the remaining cost budget, else
`clockRest`. -/
def clockStep : Prog :=
  .elim 1 (.cons .nil .nil)
    (.let_ (.cons (callVar 7 stepCostProg) (.var 5))
      (.let_ (callVar 0 subProg) (.elim 0 (.cons .nil .nil) clockRest)))

/-- Body of the clocked loop: stop with the flagged value of a final configuration,
otherwise `clockStep`. -/
def clockBody : Prog :=
  .elim 0 .nil (.elim 1 .nil (.elim 1 .nil (.let_ (callVar 4 isFinalProg)
    (.elim 0 clockStep (.cons .nil (.cons (.cons .nil .nil) (.var 1)))))))

/-- Cost bound of `sizeProg` on a value of size `s` (as in `sizeProg_runs`). -/
def sizeBound (s : ℕ) : ℕ := (s + 1) * (5 * s + 20) + s + 6

/-- Bound on the second half of a step of the clocked loop, in terms of the configuration
size `S`, the guard `Θ`, the remaining cost `rem` and the step budget `b`. -/
def clockRestBound (S Θ rem b : ℕ) : ℕ :=
  S + stepBound S + sizeBound (stepBound S) + subBound (stepBound S) Θ + 6 * stepBound S +
    6 * Θ + 2 * rem + 2 * b + 50

/-- Bound of one iteration of the clocked loop, on configurations of size at most `Θ`,
with cost budget at most `k` (and step budget at most `3 k + 1`). -/
def clockBodyBound (Θ k : ℕ) : ℕ :=
  stepCostBound Θ + subBound Θ k + stepBound Θ + sizeBound (stepBound Θ) +
    subBound (stepBound Θ) Θ + 6 * stepBound Θ + 12 * Θ + 30 * k + 200

/-- The environment of `clockStep` after the cost subtraction, on a configuration `c` with
remaining cost `rem`, step budget `b + 1` and guard `Θ`. -/
def clockEnv (c : Cfg) (rem b Θ : ℕ) (env : Env) : Env :=
  subResult (stepCost c) rem :: .cons (.ofNat (stepCost c)) (.ofNat rem) :: .nil :: .ofNat b ::
    .nil :: .ofNat (b + 1) :: .ofNat Θ :: .ofNat rem :: .cons (.ofNat (b + 1)) (.ofNat Θ) ::
    c.toData :: .cons (.ofNat rem) (.cons (.ofNat (b + 1)) (.ofNat Θ)) ::
    clockState c.toData (.ofNat rem) (.ofNat (b + 1)) (.ofNat Θ) :: env

/-! ## The semantics of the clocked loop -/

/-- The value of a configuration: the returned value, `nil` on an "evaluate" control. -/
def Cfg.val : Cfg → Data
  | ⟨.ret v, _, _⟩ => v
  | ⟨.ev _, _, _⟩ => .nil

open Classical in
/-- The result of the clocked loop from the `n`-th configuration of the run of `c₀`, with
step budget `b`, cost budget `k` and size guard `Θ`. -/
noncomputable def clockRun (c₀ : Cfg) (k Θ : ℕ) : ℕ → ℕ → Data
  | 0, n => if IsFinal (step^[n] c₀) then .cons (.cons .nil .nil) (step^[n] c₀).val else .nil
  | b + 1, n =>
    if IsFinal (step^[n] c₀) then .cons (.cons .nil .nil) (step^[n] c₀).val
    else if costSum c₀ (n + 1) ≤ k ∧ (step^[n + 1] c₀).toData.size ≤ Θ then
      clockRun c₀ k Θ b (n + 1)
    else .nil

/-! ## The clocked universal program -/

/-- The size guard of the clocked simulation, as a function of `X = k + esize c + v.size`:
`Y = 9 X + 4` (two applications of `tripleProg`)... -/
def guardFun (X : ℕ) : ℕ := 3 * (3 * X + 1) + 1

/-- ...the size of `Y` copies of `ofNat Y`... -/
def t1Fun (X : ℕ) : ℕ := guardFun X * (2 * guardFun X + 1 + 1) + 1

/-- ...and the size of `Y` copies of that list: the guard `Θ`. -/
def thetaFun (X : ℕ) : ℕ := guardFun X * (t1Fun X + 1) + 1

/-- The clocked universal program: on `cons (ofNat k) (cons (encode c) v)`, compute
`X = k + esize c + v.size` and the guard `Θ` in unary, build the initial configuration and
the state of the clocked loop, and run it with step budget `3 k + 1`. -/
def univTProg : Prog :=
  .elim 0 .nil (.elim 1 .nil
    (.let_ (callVar 0 sizeProg)
    (.let_ (callVar 2 sizeProg)
    (.let_ (.cons (.var 0) (.var 1))
    (.let_ (callVar 0 addProg)
    (.let_ (.cons (.var 6) (.var 0))
    (.let_ (callVar 0 addProg)
    (.let_ (.cons (.var 0) (.cons .nil .nil))
    (.let_ (callVar 0 tripleProg)
    (.let_ (.cons (.var 0) (.cons .nil .nil))
    (.let_ (callVar 0 tripleProg)
    (.let_ (.cons (.var 0) (.cons (.var 0) .nil))
    (.let_ (callVar 0 repProg)
    (.let_ (.cons (.var 2) (.cons (.var 0) .nil))
    (.let_ (callVar 0 repProg)
    (.let_ (callVar 0 sizeProg)
    (.let_ (.cons (.cons .nil (.var 15)) (.cons (.cons (.var 16) .nil) .nil))
    (.let_ (.cons (.var 18) (.cons .nil .nil))
    (.let_ (callVar 0 tripleProg)
    (.let_ (.cons (.var 2) (.cons (.var 20) (.cons (.var 0) (.var 3))))
      (.loop clockBody)))))))))))))))))))))

/-- Cost bound of `addProg` (as in `addProg_runs`). -/
def addBound (a b : ℕ) : ℕ := (a + 1) * (4 * a + 2 * b + 15)

/-- Cost bound of `tripleProg` (as in `tripleProg_runs`). -/
def tripleBound (n m : ℕ) : ℕ := (n + 1) * (8 * n + 2 * m + 30)

/-- The time bound of the clocked universal program, as a function of
`X = k + esize c + v.size`. -/
def univTBoundFun (X : ℕ) : ℕ :=
  2 * sizeBound X + addBound X X + addBound X X + tripleBound X 1 + tripleBound (3 * X + 1) 1 +
    tripleBound X 1 + repBound (guardFun X) (2 * guardFun X + 1) 1 +
    repBound (guardFun X) (t1Fun X) 1 + sizeBound (thetaFun X) +
    (3 * X + 2) * (clockBodyBound (thetaFun X) X + 1) +
    20 * thetaFun X + 20 * t1Fun X + 60 * guardFun X + 100 * X + 500

/-! ## Polynomial packaging -/

/-- `stepBound` as a polynomial. -/
noncomputable def stepPoly : Polynomial ℕ := (X + C 1) * (X + C 40) + C 200

/-- `interpBodyBound` as a polynomial. -/
noncomputable def interpBodyPoly : Polynomial ℕ := stepPoly + C 3 * X + C 30

/-- `sigmaFun` as a polynomial. -/
noncomputable def sigmaPoly : Polynomial ℕ :=
  X + X + (C 3 * X) * X + C 3 * X + (C 2 * X) * (X + X + (C 3 * X) * X + C 3 * X + C 10) +
    C 2 * X + C 8

/-- `univBoundFun` as a polynomial. -/
noncomputable def univPoly : Polynomial ℕ :=
  (C 3 * X + C 1) * (interpBodyPoly.comp sigmaPoly + C 1) + C 2 * X + C 11

/-- `sizeBound` of a polynomial. -/
noncomputable def sizePoly (p : Polynomial ℕ) : Polynomial ℕ :=
  (p + C 1) * (C 5 * p + C 20) + p + C 6

/-- `addBound` of polynomials. -/
noncomputable def addPoly (p q : Polynomial ℕ) : Polynomial ℕ :=
  (p + C 1) * (C 4 * p + C 2 * q + C 15)

/-- `tripleBound` of polynomials. -/
noncomputable def triplePoly (p q : Polynomial ℕ) : Polynomial ℕ :=
  (p + C 1) * (C 8 * p + C 2 * q + C 30)

/-- `repBound` of polynomials. -/
noncomputable def repPoly (p q r : Polynomial ℕ) : Polynomial ℕ :=
  (p + C 1) * (C 4 * p + C 4 * q + C 2 * r + C 30) + p * (p + C 1) * (q + C 1)

/-- `subBound` of polynomials. -/
noncomputable def subPoly (p q : Polynomial ℕ) : Polynomial ℕ :=
  (p + C 1) * (C 2 * p + C 2 * q + C 14)

/-- `stepCostBound` of a polynomial. -/
noncomputable def stepCostPoly (p : Polynomial ℕ) : Polynomial ℕ :=
  (p + C 1) * (C 7 * p + C 32) + C 13 * p + C 50

/-- `clockBodyBound` of polynomials. -/
noncomputable def clockBodyPoly (p q : Polynomial ℕ) : Polynomial ℕ :=
  stepCostPoly p + subPoly p q + stepPoly.comp p + sizePoly (stepPoly.comp p) +
    subPoly (stepPoly.comp p) p + C 6 * stepPoly.comp p + C 12 * p + C 30 * q + C 200

/-- `guardFun`, `t1Fun`, `thetaFun` as polynomials. -/
noncomputable def guardPoly : Polynomial ℕ := C 3 * (C 3 * X + C 1) + C 1

noncomputable def t1Poly : Polynomial ℕ := guardPoly * (C 2 * guardPoly + C 1 + C 1) + C 1

noncomputable def thetaPoly : Polynomial ℕ := guardPoly * (t1Poly + C 1) + C 1

/-- `univTBoundFun` as a polynomial. -/
noncomputable def univTPoly : Polynomial ℕ :=
  C 2 * sizePoly X + addPoly X X + addPoly X X + triplePoly X (C 1) +
    triplePoly (C 3 * X + C 1) (C 1) + triplePoly X (C 1) +
    repPoly guardPoly (C 2 * guardPoly + C 1) (C 1) + repPoly guardPoly t1Poly (C 1) +
    sizePoly thetaPoly + (C 3 * X + C 2) * (clockBodyPoly thetaPoly X + C 1) +
    C 20 * thetaPoly + C 20 * t1Poly + C 60 * guardPoly + C 100 * X + C 500

end Machine

end MIPRE.Cost
