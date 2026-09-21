/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.SAT.InputRoutingProg
import MIPRE.Foundations.SAT.CircuitArithmetization
import MIPRE.Foundations.LowDegree.BinaryConstants

/-!
# Uniform field evaluation of a routed gate

Field elements are coefficient vectors modulo a supplied binary monic
polynomial. Gate indices stay binary, including on malformed inputs.
-/

namespace MIPRE.SAT.Circuit

open Cost LowDegree LowDegree.BinaryPolynomial

-- Retain concrete circuit-facing declarations for downstream compiled consumers.
/-- Circuit-facing zero coefficients, implemented by generic quotient arithmetic. -/
abbrev zeroBits := BinaryPolynomial.zeroBits
/-- Circuit-facing one coefficients, implemented by generic quotient arithmetic. -/
abbrev oneBits := BinaryPolynomial.oneBits
@[simp] theorem length_zeroBits (p : BitStr) : (zeroBits p).length = p.length :=
  BinaryPolynomial.length_zeroBits p
@[simp] theorem length_oneBits (p : BitStr) : (oneBits p).length = p.length :=
  BinaryPolynomial.length_oneBits p
@[simp] theorem evalBits_zeroBits {R : Type*} [CommRing R] (z : R) (p : BitStr) :
    BinaryPolynomial.evalBits z (zeroBits p) = 0 := BinaryPolynomial.evalBits_zeroBits z p
theorem evalBits_oneBits {R : Type*} [CommRing R] (z : R) (p : BitStr) (hp : p ≠ []) :
    BinaryPolynomial.evalBits z (oneBits p) = 1 := BinaryPolynomial.evalBits_oneBits z p hp
noncomputable abbrev zeroBitsProg : PolyTimeFun BitStr BitStr := BinaryPolynomial.zeroBitsProg
noncomputable abbrev oneBitsProg : PolyTimeFun BitStr BitStr := BinaryPolynomial.oneBitsProg
@[simp] theorem zeroBitsProg_apply (p : BitStr) : zeroBitsProg p = zeroBits p := rfl
@[simp] theorem oneBitsProg_apply (p : BitStr) : oneBitsProg p = oneBits p := rfl

variable {R : Type*} [CommRing R]

/-- Gate arithmetic on coefficient vectors. The input reader is supplied
separately so that the same arithmetic supports the routed copy links. -/
def gateBits (p : BitStr) (x : ℕ → BitStr) (w : List BitStr) : Gate → BitStr
  | .input i => x i
  | .const b => if b then oneBits p else zeroBits p
  | .and u v => mulReduce p (w.getD u []) (w.getD v [])
  | .or u v => xorBits (oneBits p)
      (mulReduce p (xorBits (oneBits p) (w.getD u []))
        (xorBits (oneBits p) (w.getD v [])))
  | .not u => xorBits (oneBits p) (w.getD u [])

/-- The corresponding field expression in characteristic two. -/
def gateValue (x w : ℕ → R) : Gate → R
  | .input i => x i
  | .const b => ofBool b
  | .and u v => w u * w v
  | .or u v => 1 + (1 + w u) * (1 + w v)
  | .not u => 1 + w u

theorem length_gateBits (p : BitStr) (x : ℕ → BitStr) (w : List BitStr) (g : Gate)
    (hx : ∀ i, g = .input i → (x i).length = p.length)
    (hw : ∀ j ∈ g.refs, (w.getD j []).length = p.length) :
    (gateBits p x w g).length = p.length := by
  cases g with
  | input i => exact hx i rfl
  | const b => cases b <;> simp [gateBits]
  | and u v => exact length_mulReduce p _ _ (hw u (by simp [Gate.refs]))
  | or u v =>
    have hu := hw u (by simp [Gate.refs])
    have ha : (xorBits (oneBits p) (w.getD u [])).length = p.length := by
      simp only [length_xorBits, length_oneBits, hu, min_self]
    simp only [gateBits, length_xorBits, length_oneBits, length_mulReduce p _ _ ha, min_self]
  | not u =>
    simp only [gateBits, length_xorBits, length_oneBits, hw u (by simp [Gate.refs]), min_self]

/-- Correctness of all five gate operations over every characteristic-two ring
containing a root of the supplied modulus. -/
theorem evalBits_gateBits [CharP R 2] (z : R) (p : BitStr) (hp : p ≠ [])
    (hroot : z ^ p.length = BinaryPolynomial.evalBits z p) (x : ℕ → BitStr) (w : List BitStr) (g : Gate)
    (hw : ∀ j ∈ g.refs, (w.getD j []).length = p.length) :
    BinaryPolynomial.evalBits z (gateBits p x w g) =
      gateValue (fun i => BinaryPolynomial.evalBits z (x i)) (fun j => BinaryPolynomial.evalBits z (w.getD j [])) g := by
  have h1 := evalBits_oneBits z p hp
  cases g with
  | input i => rfl
  | const b => cases b <;> simp [gateBits, gateValue, ofBool, h1]
  | and u v => exact evalBits_mulReduce z p _ _ (hw u (by simp [Gate.refs])) hroot
  | or u v =>
    have hu := hw u (by simp [Gate.refs])
    have hv := hw v (by simp [Gate.refs])
    have hlu : (xorBits (oneBits p) (w.getD u [])).length = p.length := by
      simp only [length_xorBits, length_oneBits, hu, min_self]
    have hlm := length_mulReduce p (xorBits (oneBits p) (w.getD u []))
      (xorBits (oneBits p) (w.getD v [])) hlu
    simp only [gateBits, gateValue]
    rw [evalBits_xor z _ _ (by simpa using hlm.symm),
      evalBits_mulReduce z p _ _ hlu hroot,
      evalBits_xor z _ _ (by simpa using hu.symm),
      evalBits_xor z _ _ (by simpa using hv.symm), h1]
  | not u =>
    simp only [gateBits, gateValue]
    rw [evalBits_xor z _ _ (by simpa using (hw u (by simp [Gate.refs])).symm), h1]

theorem gateValue_eq_eval_gateArith {F : Type*} [Field F] [CharP F 2]
    (C : Circuit) (k : ℕ) (g : Gate) (x w : ℕ → F) :
    gateValue (fun i => Sum.elim x w (C.inputRef k i)) w g =
      MvPolynomial.eval (Sum.elim x w) (C.gateArith k g) := by
  cases g <;> simp [gateValue, gateArith, CharTwo.sub_eq_add]

section Programs

open Cost.PolyTimeFun

/-- Modulus, external coordinates, gate coordinates, and preceding gate/value pairs. -/
abbrev FieldEnv := BitStr × List BitStr × List BitStr × List (Gate × BitStr)

def readInput (e : FieldEnv) (i : ℕ) : BitStr :=
  lastInputValue e.2.2.2 i (e.2.1.getD i [])

noncomputable def readInputProg : PolyTimeFun (FieldEnv × ℕ) BitStr :=
  lastInputValueProg.comp
    ((snd.pair ((ArrayProg.getD []).comp (snd.pair (fst.comp (snd.comp fst))))).pair
      ((snd.comp snd).comp (snd.comp fst)))

@[simp] theorem readInputProg_apply (e : FieldEnv) (i : ℕ) :
    readInputProg (e, i) = readInput e i := rfl

/-- Uniform polynomial-time field evaluation of one routed gate. -/
noncomputable def gateBitsProg : PolyTimeFun (FieldEnv × Gate) BitStr :=
  let p : PolyTimeFun FieldEnv BitStr := fst
  let w : PolyTimeFun FieldEnv (List BitStr) := fst.comp (snd.comp snd)
  let one := oneBitsProg.comp p
  let readW : PolyTimeFun (FieldEnv × ℕ) BitStr :=
    (ArrayProg.getD []).comp (snd.pair (w.comp fst))
  let a : PolyTimeFun (FieldEnv × (ℕ × ℕ)) BitStr := readW.comp (fst.pair (fst.comp snd))
  let b : PolyTimeFun (FieldEnv × (ℕ × ℕ)) BitStr := readW.comp (fst.pair (snd.comp snd))
  let both := mulReduceProg.comp ((p.comp fst).pair (a.pair b))
  let either := xorBitsProg.comp ((one.comp fst).pair
    (mulReduceProg.comp ((p.comp fst).pair
      ((xorBitsProg.comp ((one.comp fst).pair a)).pair
        (xorBitsProg.comp ((one.comp fst).pair b))))))
  congr (MIPRE.SAT.PolyTimeFun.casesGate readInputProg
    (ite snd (one.comp fst) (zeroBitsProg.comp (p.comp fst))) both either
    (xorBitsProg.comp ((one.comp fst).pair readW)))
    (fun eg => gateBits eg.1.1 (readInput eg.1) eg.1.2.2.1 eg.2) (by
      rintro ⟨e, g⟩
      cases g <;> rfl)

@[simp] theorem gateBitsProg_apply (e : FieldEnv) (g : Gate) :
    gateBitsProg (e, g) = gateBits e.1 (readInput e) e.2.2.1 g := rfl

end Programs

end MIPRE.SAT.Circuit
