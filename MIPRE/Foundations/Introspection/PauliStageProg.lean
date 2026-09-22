/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.SeededLineProg

/-! # Uniform programs for all three Pauli sampling stages

The field width, selector width and point dimension are inputs, as are the
type tag, prefix and vector. The five computational branches cover point,
axis line, diagonal line, Pauli and the remaining Pauli-test types. In
particular, neither a finite table of field elements nor a dimension-dependent
program is used.
-/

noncomputable section
namespace MIPRE.Introspection.PauliStageProgram
open Cost Cost.PolyTimeFun SAT SeededLineProgram LineProgram

/-- The field registers in their fixed sampler order. -/
abbrev Fields := List BitStr × List BitStr × BitStr × List BitStr × BitStr × BitStr
abbrev Parameters := Unary × Unary × Unary
/-- Kind and basis: `0` point, `1` axis, `2` diagonal, `3` Pauli, `4` full. -/
abbrev Tag := ℕ × Bool
abbrev Input := Parameters × Tag × Fields × Fields

def fieldWidth : PolyTimeFun Input Unary := fst.comp fst
def selectorWidth : PolyTimeFun Input Unary := fst.comp (snd.comp fst)
def dimension : PolyTimeFun Input Unary := snd.comp (snd.comp fst)
def kind : PolyTimeFun Input ℕ := fst.comp (fst.comp snd)
def basis : PolyTimeFun Input Bool := snd.comp (fst.comp snd)
def prefixData : PolyTimeFun Input Fields := fst.comp (snd.comp snd)
def vector : PolyTimeFun Input Fields := snd.comp (snd.comp snd)

def pointX : PolyTimeFun Fields (List BitStr) := fst
def pointZ : PolyTimeFun Fields (List BitStr) := fst.comp snd
def seed : PolyTimeFun Fields BitStr := fst.comp (snd.comp snd)
def direction : PolyTimeFun Fields (List BitStr) := fst.comp (snd.comp (snd.comp snd))
def scalarX : PolyTimeFun Fields BitStr := fst.comp (snd.comp (snd.comp (snd.comp snd)))
def scalarZ : PolyTimeFun Fields BitStr := snd.comp (snd.comp (snd.comp (snd.comp snd)))

def zeroField : PolyTimeFun Input BitStr := shoupZeroProg.comp fieldWidth
def zeroPoint : PolyTimeFun Input (List BitStr) := ap₂ replicate dimension zeroField
def pack {A : Type*} [SizedEncoding A]
    (x z : PolyTimeFun A (List BitStr)) (s : PolyTimeFun A BitStr)
    (v : PolyTimeFun A (List BitStr)) (rx rz : PolyTimeFun A BitStr) :
    PolyTimeFun A Fields := x.pair (z.pair (s.pair (v.pair (rx.pair rz))))
def zeros : PolyTimeFun Input Fields :=
  pack zeroPoint zeroPoint zeroField zeroPoint zeroField zeroField
def isKind (t : ℕ) : PolyTimeFun Input Bool := ap₂ ArrayProg.eqNat kind (const t)

def stageOne : PolyTimeFun Input Fields :=
  let s := ite (isKind 1) (seed.comp vector)
    (ite (isKind 2) (seed.comp vector) zeroField)
  pack zeroPoint zeroPoint s zeroPoint zeroField zeroField

def stageTwo : PolyTimeFun Input Fields :=
  let v := ite (isKind 2)
    (selectedDirectionProg.comp
      ((fieldWidth.pair (selectorWidth.pair (seed.comp prefixData))).pair (direction.comp vector)))
    zeroPoint
  pack zeroPoint zeroPoint zeroField v zeroField zeroField

def selectedPoint : PolyTimeFun Input (List BitStr) :=
  ite basis (pointZ.comp vector) (pointX.comp vector)

def finalPoint : PolyTimeFun Input (List BitStr) :=
  ite (isKind 1)
    (axisRepresentativeProg.comp
      ((fieldWidth.pair (selectorWidth.pair (seed.comp prefixData))).pair selectedPoint))
    (ite (isKind 2)
      (lineRepresentativeProg.comp
        (fieldWidth.pair (selectedPoint.pair (direction.comp prefixData)))) selectedPoint)

def pointFields : PolyTimeFun Input Fields :=
  pack (ite basis zeroPoint finalPoint) (ite basis finalPoint zeroPoint)
    zeroField zeroPoint zeroField zeroField

def fullFields : PolyTimeFun Input Fields :=
  pack (pointX.comp vector) (pointZ.comp vector) zeroField zeroPoint
    (scalarX.comp vector) (scalarZ.comp vector)

def stageThree : PolyTimeFun Input Fields :=
  ite (isKind 0) pointFields
    (ite (isKind 1) pointFields
      (ite (isKind 2) pointFields (ite (isKind 3) zeros fullFields)))

/-- A single program selects the requested stage; out-of-range stages return zero. -/
def linear : PolyTimeFun (ℕ × Input) Fields :=
  ite (ap₂ ArrayProg.eqNat fst (const 1)) (stageOne.comp snd)
    (ite (ap₂ ArrayProg.eqNat fst (const 2)) (stageTwo.comp snd)
      (ite (ap₂ ArrayProg.eqNat fst (const 3)) (stageThree.comp snd) (zeros.comp snd)))

@[simp] theorem linear_one (x : Input) : linear (1, x) = stageOne x := rfl
@[simp] theorem linear_two (x : Input) : linear (2, x) = stageTwo x := rfl
@[simp] theorem linear_three (x : Input) : linear (3, x) = stageThree x := rfl

theorem linear_runs (x : ℕ × Input) :
    ∃ t ≤ linear.timeBound.eval (esize x),
      linear.code.Runs (encode x) (encode (linear x)) t := linear.computes x

/-- Assemble three disjoint output registers without performing field arithmetic. -/
def assemble : PolyTimeFun (Fields × Fields × Fields) Fields :=
  pack (pointX.comp (snd.comp snd)) (pointZ.comp (snd.comp snd)) (seed.comp fst)
    (direction.comp (fst.comp snd)) (scalarX.comp (snd.comp snd))
    (scalarZ.comp (snd.comp snd))

def withPrefix : PolyTimeFun (Input × Fields) Input :=
  (fst.comp fst).pair ((fst.comp (snd.comp fst)).pair
    (snd.pair (vector.comp fst)))

def firstTwo : PolyTimeFun Input Fields :=
  let a := stageOne
  let b := stageTwo.comp (withPrefix.comp ((PolyTimeFun.id _).pair a))
  assemble.comp (a.pair (b.pair zeros))

def allThree : PolyTimeFun Input Fields :=
  let c := stageThree.comp (withPrefix.comp ((PolyTimeFun.id _).pair firstTwo))
  assemble.comp (firstTwo.pair (firstTwo.pair c))

/-- Uniform evaluation of each legal marginal, including both prefix-dependent stages. -/
def marginal : PolyTimeFun (ℕ × Input) Fields :=
  ite (ap₂ ArrayProg.eqNat fst (const 1)) (stageOne.comp snd)
    (ite (ap₂ ArrayProg.eqNat fst (const 2)) (firstTwo.comp snd)
      (ite (ap₂ ArrayProg.eqNat fst (const 3)) (allThree.comp snd) (zeros.comp snd)))

@[simp] theorem marginal_one (x : Input) : marginal (1, x) = stageOne x := rfl
@[simp] theorem marginal_two (x : Input) : marginal (2, x) = firstTwo x := rfl
@[simp] theorem marginal_three (x : Input) : marginal (3, x) = allThree x := rfl

end MIPRE.Introspection.PauliStageProgram
end
