/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/PcpFieldTests.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryFold
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_Foundations_SAT_GateProg
import Definitions.Def_MIPRE_Foundations_SAT_InputRouting
import Definitions.Def_MIPRE_Foundations_SAT_InputRoutingProg
import Definitions.Def_MIPRE_Foundations_SAT_CircuitArithmetization
import Definitions.Def_MIPRE_Foundations_SAT_GateFieldEval

/-!
# Executable field arithmetic for the two PCP tests

The literal list contains pairs of claimed answer values and sign coordinates.
The certificate list contains pairs of claimed certificate values and point
coordinates. The surrounding verifier supplies their prescribed lengths.
-/

namespace MIPRE.SAT.PcpFieldTests

open Cost LowDegree LowDegree.BinaryPolynomial

def literalProduct (p : BitStr) (l : List (BitStr × BitStr)) : BitStr :=
  arithmeticFold true p (oneBits p) (l.map (fun a => xorBits a.1 a.2))

def formulaValue (p φ : BitStr) (l : List (BitStr × BitStr)) : BitStr :=
  mulReduce p φ (literalProduct p l)

def certificateTerm (p : BitStr) (a : BitStr × BitStr) : BitStr :=
  mulReduce p a.1 (mulReduce p a.2 (xorBits (oneBits p) a.2))

def certificateValue (p : BitStr) (l : List (BitStr × BitStr)) : BitStr :=
  arithmeticFold false p (zeroBits p) (l.map (certificateTerm p))

def CorrectPairs (p : BitStr) (l : List (BitStr × BitStr)) : Prop :=
  ∀ a ∈ l, a.1.length = p.length ∧ a.2.length = p.length

variable {R : Type*} [CommRing R] [CharP R 2]

section Programs

open Cost.PolyTimeFun

noncomputable def literalProductProg : PolyTimeFun (BitStr × List (BitStr × BitStr)) BitStr :=
  (arithmeticFoldProg true).comp
    (fst.pair ((oneBitsProg.comp fst).pair ((map xorBitsProg).comp snd)))

@[simp] theorem literalProductProg_apply (p : BitStr) (l : List (BitStr × BitStr)) :
    literalProductProg (p, l) = literalProduct p l := rfl

noncomputable def formulaValueProg : PolyTimeFun (BitStr × BitStr × List (BitStr × BitStr)) BitStr :=
  mulReduceProg.comp (fst.pair ((fst.comp snd).pair
    (literalProductProg.comp (fst.pair (snd.comp snd)))))

@[simp] theorem formulaValueProg_apply (p φ : BitStr) (l : List (BitStr × BitStr)) :
    formulaValueProg (p, φ, l) = formulaValue p φ l := rfl

noncomputable def certificateTermProg : PolyTimeFun ((BitStr × BitStr) × BitStr) BitStr :=
  mulReduceProg.comp (snd.pair ((fst.comp fst).pair
    (mulReduceProg.comp (snd.pair ((snd.comp fst).pair
      (xorBitsProg.comp ((oneBitsProg.comp snd).pair (snd.comp fst))))))))

@[simp] theorem certificateTermProg_apply (a : BitStr × BitStr) (p : BitStr) :
    certificateTermProg (a, p) = certificateTerm p a := rfl

noncomputable def certificateValueProg : PolyTimeFun (BitStr × List (BitStr × BitStr)) BitStr :=
  (arithmeticFoldProg false).comp (fst.pair ((zeroBitsProg.comp fst).pair
    ((mapWith certificateTermProg).comp (snd.pair fst))))

@[simp] theorem certificateValueProg_apply (p : BitStr) (l : List (BitStr × BitStr)) :
    certificateValueProg (p, l) = certificateValue p l := rfl

end Programs

/-- Modulus, circuit value, claimed main certificate, literals, and zero terms. -/
abbrev TestInput := BitStr × BitStr × BitStr × List (BitStr × BitStr) × List (BitStr × BitStr)

def checks (a : TestInput) : Bool :=
  decide (a.2.2.1 = formulaValue a.1 a.2.1 a.2.2.2.1) &&
    decide (a.2.2.1 = certificateValue a.1 a.2.2.2.2)

/-- Both raw coefficient-vector equality tests, as one uniform ambient program. -/
noncomputable def checksProg : PolyTimeFun TestInput Bool :=
  let p : PolyTimeFun TestInput BitStr := PolyTimeFun.fst
  let φ := PolyTimeFun.fst.comp PolyTimeFun.snd
  let β := PolyTimeFun.fst.comp (PolyTimeFun.snd.comp PolyTimeFun.snd)
  let lits := PolyTimeFun.fst.comp (PolyTimeFun.snd.comp (PolyTimeFun.snd.comp PolyTimeFun.snd))
  let certs := PolyTimeFun.snd.comp (PolyTimeFun.snd.comp (PolyTimeFun.snd.comp PolyTimeFun.snd))
  let f := ArrayProg.eqBits.comp (β.pair (formulaValueProg.comp (p.pair (φ.pair lits))))
  let c := ArrayProg.eqBits.comp (β.pair (certificateValueProg.comp (p.pair certs)))
  PolyTimeFun.congr (PolyTimeFun.ite f c (PolyTimeFun.const false)) checks (by
    intro a
    change (if decide (a.2.2.1 = formulaValue a.1 a.2.1 a.2.2.2.1) then
      decide (a.2.2.1 = certificateValue a.1 a.2.2.2.2) else false) =
        (decide (a.2.2.1 = formulaValue a.1 a.2.1 a.2.2.2.1) &&
          decide (a.2.2.1 = certificateValue a.1 a.2.2.2.2))
    cases decide (a.2.2.1 = formulaValue a.1 a.2.1 a.2.2.2.1) <;> rfl)

@[simp] theorem checksProg_apply (a : TestInput) : checksProg a = checks a := rfl

end MIPRE.SAT.PcpFieldTests
