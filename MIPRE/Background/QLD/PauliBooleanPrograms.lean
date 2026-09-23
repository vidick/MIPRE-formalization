/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.QLD.PauliAnswerCoding
import MIPRE.Background.QLD.PauliBranchPrograms
import MIPRE.Background.QLD.PauliArithmeticPrograms
import MIPRE.Foundations.Introspection.FieldQuestionProg

/-! # The uniform Boolean Pauli decision program

Both answers undergo the exact type-directed parser. A faithful finite type
route chooses consistency or one of the seven arithmetic rules. The finite
Magic Square metadata contains only type indices; field arithmetic, answer
tables and polynomial coefficients are processed by uniform programs.
-/

noncomputable section
namespace MIPRE.QLD.PauliBooleanProgram
open Cost Cost.PolyTimeFun SAT LowDegree LowDegree.BinaryLinear
  Introspection.PauliStageProgram Introspection.FieldLineCheck
  Introspection.FieldGammaProgram PauliArithmeticProgram
open LCS.MagicSquare

abbrev Payload := Ty × Fields × BitStr
abbrev Input := Parameters × Payload × Payload

def params : PolyTimeFun Input Parameters := fst
def width : PolyTimeFun Input Unary := fst.comp params
def dim : PolyTimeFun Input Unary := snd.comp (snd.comp params)
def endpoints : PolyTimeFun Input (Payload × Payload) := snd
def endpointTypes : PolyTimeFun Input (Ty × Ty) :=
  (fst.comp (fst.comp endpoints)).pair (fst.comp (snd.comp endpoints))
def route : PolyTimeFun Input PauliBranchProgram.Route :=
  PauliBranchProgram.routeProg.comp endpointTypes
def rule : PolyTimeFun Input ℕ := fst.comp route
def basis : PolyTimeFun Input ℕ := fst.comp (snd.comp (snd.comp route))
def oriented : PolyTimeFun Input (Payload × Payload) :=
  PauliBranchProgram.orientProg.comp ((fst.comp (snd.comp route)).pair endpoints)
def left : PolyTimeFun Input Payload := fst.comp oriented
def right : PolyTimeFun Input Payload := snd.comp oriented
def leftFields : PolyTimeFun Input Fields := fst.comp (snd.comp left)
def rightFields : PolyTimeFun Input Fields := fst.comp (snd.comp right)
def leftBits : PolyTimeFun Input BitStr := snd.comp (snd.comp left)
def rightBits : PolyTimeFun Input BitStr := snd.comp (snd.comp right)
def leftParser : PolyTimeFun Input (Bool × List BitStr) :=
  PauliAnswerProgram.parser.comp ((fst.comp left).pair
    (dim.pair (width.pair ((const (unary 1)).pair leftBits))))
def rightParser : PolyTimeFun Input (Bool × List BitStr) :=
  PauliAnswerProgram.parser.comp ((fst.comp right).pair
    (dim.pair (width.pair ((const (unary 1)).pair rightBits))))
def leftRows : PolyTimeFun Input (List BitStr) := snd.comp leftParser
def rightRows : PolyTimeFun Input (List BitStr) := snd.comp rightParser
def leftValue : PolyTimeFun Input BitStr := (nthD [] 0).comp leftRows

def bitAt : PolyTimeFun (ℕ × List BitStr) Bool :=
  (nthD false 0).comp (ArrayProg.getD [])

def boolEq : PolyTimeFun (Bool × Bool) Bool := finiteFunction (fun p => p.1 == p.2)
def boolAnd : PolyTimeFun (Bool × Bool) Bool := finiteFunction (fun p => p.1 && p.2)
def boolOr : PolyTimeFun (Bool × Bool) Bool := finiteFunction (fun p => p.1 || p.2)
def boolNot : PolyTimeFun Bool Bool := finiteFunction (! ·)

def point : PolyTimeFun Input (List BitStr) :=
  Introspection.FieldQuestionProgram.selectedPoint.comp (basis.pair leftFields)
def origin : PolyTimeFun Input (List BitStr) :=
  Introspection.FieldQuestionProgram.selectedPoint.comp (basis.pair rightFields)
def scalar : PolyTimeFun Input BitStr :=
  Introspection.FieldQuestionProgram.selectedScalar.comp (basis.pair rightFields)
def axis : PolyTimeFun Input (List BitStr) :=
  Introspection.FieldQuestionProgram.axisDirectionProg.comp
    (params.pair (seed.comp rightFields))

def consistency : PolyTimeFun Input Bool := ap₂ ArrayProg.eqBits leftBits rightBits
def axisCheck : PolyTimeFun Input Bool :=
  lineCheckProg.comp ((width.pair (origin.pair (axis.pair point))).pair
    (rightRows.pair leftValue))
def diagonalCheck : PolyTimeFun Input Bool :=
  lineCheckProg.comp ((width.pair (origin.pair ((direction.comp rightFields).pair point))).pair
    (rightRows.pair leftValue))
def tableCheck : PolyTimeFun Input Bool :=
  fullAnswerCheckProg.comp ((width.pair (point.pair rightRows)).pair leftValue)

/-- All commutation and Magic Square rules use the omega tuple at the right,
distinguished endpoint after the orientation normalization. -/
def gamma : PolyTimeFun Input Bool :=
  gammaProg.comp (width.pair
    ((zip.comp ((pointX.comp rightFields).pair (pointZ.comp rightFields))).pair
      ((scalarX.comp rightFields).pair (scalarZ.comp rightFields))))
def probe : PolyTimeFun Input Bool :=
  probeProg.comp (width.pair (leftValue.pair scalar))
def leftBit : PolyTimeFun Input Bool := bitAt.comp ((const 0).pair leftRows)
def rightBit : PolyTimeFun Input Bool := bitAt.comp ((const 0).pair rightRows)

def pairCheck : PolyTimeFun Input Bool :=
  ap₂ boolOr gamma (ap₂ boolEq leftBit (bitAt.comp (basis.pair rightRows)))
def probeCheck : PolyTimeFun Input Bool := ap₂ boolOr gamma (ap₂ boolEq probe rightBit)

def magicInfo : Ty × Ty → Bool × Bool × ℕ
  | (.con i, .var j) => (decide (j ∈ layout.V i), bit (game.b i), (cellIdx i j).val)
  | _ => (false, false, 0)

def magicTypes : PolyTimeFun Input (Ty × Ty) := (fst.comp left).pair (fst.comp right)
def magicMetadata : PolyTimeFun Input (Bool × Bool × ℕ) :=
  (finiteFunction magicInfo).comp magicTypes
def parityProg : PolyTimeFun (Bool × Bool × Bool) Bool :=
  finiteFunction (fun p => bit ((ofBool p.1 : ZMod 2) + ofBool p.2.1 + ofBool p.2.2))
def leftParity : PolyTimeFun Input Bool :=
  parityProg.comp ((bitAt.comp ((const 0).pair leftRows)).pair
    ((bitAt.comp ((const 1).pair leftRows)).pair (bitAt.comp ((const 2).pair leftRows))))
def magicCheck : PolyTimeFun Input Bool :=
  ap₂ boolOr (boolNot.comp gamma)
    (ap₂ boolAnd (fst.comp magicMetadata)
      (ap₂ boolAnd (ap₂ boolEq leftParity (fst.comp (snd.comp magicMetadata)))
        (ap₂ boolEq (bitAt.comp ((snd.comp (snd.comp magicMetadata)).pair leftRows)) rightBit)))

def probeEligible : Ty × Ty → Bool
  | (.point .X, .var j) => decide (j = v 0)
  | (.point .Z, .var j) => decide (j = v 4)
  | _ => false

def magicProbeCheck : PolyTimeFun Input Bool :=
  ap₂ boolOr (boolNot.comp gamma)
    (ap₂ boolAnd ((finiteFunction probeEligible).comp magicTypes) (ap₂ boolEq probe rightBit))

def checks : PolyTimeFun Input (List Bool) :=
  cons consistency (cons axisCheck (cons diagonalCheck (cons tableCheck
    (cons pairCheck (cons probeCheck (cons magicCheck (cons magicProbeCheck (const []))))))))

def program : PolyTimeFun Input Bool :=
  PauliBranchProgram.formatGuard.comp ((fst.comp leftParser).pair
    ((fst.comp rightParser).pair (PauliBranchProgram.selectProg.comp (route.pair checks))))

theorem program_apply (input : Input) : program input =
    ((leftParser input).1 && (rightParser input).1 &&
      [consistency input, axisCheck input, diagonalCheck input, tableCheck input,
        pairCheck input, probeCheck input, magicCheck input, magicProbeCheck input].getD
          (route input).1 true) := by
  simp only [program, comp_apply, pair_apply, fst_apply,
    PauliBranchProgram.formatGuard_apply, PauliBranchProgram.selectProg_apply,
    checks, cons_apply, const_apply]

theorem program_runs (input : Input) :
    ∃ t ≤ program.timeBound.eval (esize input),
      program.code.Runs (encode input) (encode (program input)) t := program.computes input

theorem program_rejects_left (input : Input) (h : (leftParser input).1 = false) :
    program input = false := by
  simp [program, PauliBranchProgram.formatGuard_apply, h]

theorem program_rejects_right (input : Input) (h : (rightParser input).1 = false) :
    program input = false := by
  simp [program, PauliBranchProgram.formatGuard_apply, h]

end MIPRE.QLD.PauliBooleanProgram
end
