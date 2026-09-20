/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryFold
import MIPRE.Foundations.SAT.GateFieldEval

/-!
# Executable field arithmetic for the two PCP tests

The literal list contains pairs of claimed answer values and sign coordinates.
The certificate list contains pairs of claimed certificate values and point
coordinates. The surrounding verifier supplies their prescribed lengths.
-/

namespace MIPRE.SAT.PcpFieldTests

open Cost LowDegree LowDegree.BinaryPolynomial Circuit

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

theorem length_literalProduct (p : BitStr) (l : List (BitStr × BitStr)) :
    (literalProduct p l).length = p.length := arithmeticFold_mul_width _ _ _ (length_oneBits p)

theorem length_formulaValue (p φ : BitStr) (l : List (BitStr × BitStr))
    (hφ : φ.length = p.length) : (formulaValue p φ l).length = p.length :=
  length_mulReduce _ _ _ hφ

theorem length_certificateTerm (p : BitStr) (a : BitStr × BitStr) (ha : a.1.length = p.length) :
    (certificateTerm p a).length = p.length := length_mulReduce _ _ _ ha

theorem length_certificateValue (p : BitStr) (l : List (BitStr × BitStr)) (hl : CorrectPairs p l) :
    (certificateValue p l).length = p.length := by
  apply arithmeticFold_add_width _ _ _ (length_zeroBits p)
  intro b hb
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
  exact length_certificateTerm p a (hl a ha).1

variable {R : Type*} [CommRing R] [CharP R 2]

theorem eval_literalProduct (z : R) (p : BitStr) (hp : p ≠ [])
    (hroot : z ^ p.length = BinaryPolynomial.evalBits z p)
    (l : List (BitStr × BitStr)) (hl : CorrectPairs p l) :
    BinaryPolynomial.evalBits z (literalProduct p l) =
      (l.map (fun a => BinaryPolynomial.evalBits z a.1 - BinaryPolynomial.evalBits z a.2)).prod := by
  rw [literalProduct, evalBits_arithmeticFold_mul z p _ _ (length_oneBits p) hroot,
    evalBits_oneBits z p hp, one_mul, List.map_map]
  congr 1
  apply List.map_congr_left
  intro a ha
  simp only [Function.comp_apply]
  rw [evalBits_xor z _ _ ((hl a ha).1.trans (hl a ha).2.symm), CharTwo.sub_eq_add]

theorem eval_formulaValue (z : R) (p : BitStr) (hp : p ≠ [])
    (hroot : z ^ p.length = BinaryPolynomial.evalBits z p)
    (φ : BitStr) (hφ : φ.length = p.length)
    (l : List (BitStr × BitStr)) (hl : CorrectPairs p l) :
    BinaryPolynomial.evalBits z (formulaValue p φ l) = BinaryPolynomial.evalBits z φ *
      (l.map (fun a => BinaryPolynomial.evalBits z a.1 - BinaryPolynomial.evalBits z a.2)).prod := by
  rw [formulaValue, evalBits_mulReduce z p _ _ hφ hroot, eval_literalProduct z p hp hroot l hl]

theorem eval_certificateTerm (z : R) (p : BitStr) (hp : p ≠ [])
    (hroot : z ^ p.length = BinaryPolynomial.evalBits z p)
    (a : BitStr × BitStr) (ha : a.1.length = p.length) (hb : a.2.length = p.length) :
    BinaryPolynomial.evalBits z (certificateTerm p a) = BinaryPolynomial.evalBits z a.1 *
      (BinaryPolynomial.evalBits z a.2 * (1 - BinaryPolynomial.evalBits z a.2)) := by
  rw [certificateTerm, evalBits_mulReduce z p _ _ ha hroot,
    evalBits_mulReduce z p _ _ hb hroot,
    evalBits_xor z _ _ ((length_oneBits p).trans hb.symm), evalBits_oneBits z p hp,
    CharTwo.sub_eq_add]

theorem eval_certificateValue (z : R) (p : BitStr) (hp : p ≠ [])
    (hroot : z ^ p.length = BinaryPolynomial.evalBits z p)
    (l : List (BitStr × BitStr)) (hl : CorrectPairs p l) :
    BinaryPolynomial.evalBits z (certificateValue p l) =
      (l.map (fun a => BinaryPolynomial.evalBits z a.1 *
        (BinaryPolynomial.evalBits z a.2 * (1 - BinaryPolynomial.evalBits z a.2)))).sum := by
  have hw : ∀ b ∈ l.map (certificateTerm p), b.length = p.length := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    exact length_certificateTerm p a (hl a ha).1
  rw [certificateValue, evalBits_arithmeticFold_add z p _ _ (length_zeroBits p) hw,
    evalBits_zeroBits, zero_add, List.map_map]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact eval_certificateTerm z p hp hroot a (hl a ha).1 (hl a ha).2

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

/-- Faithful coefficient decoding converts the two executable equality checks
into precisely the two algebraic field identities. -/
theorem checksProg_true_iff (z : R) (p : BitStr) (hp : p ≠ [])
    (hroot : z ^ p.length = BinaryPolynomial.evalBits z p)
    (faithful : ∀ a b : BitStr, a.length = p.length → b.length = p.length →
      (BinaryPolynomial.evalBits z a = BinaryPolynomial.evalBits z b ↔ a = b))
    (φ β : BitStr) (hφ : φ.length = p.length) (hβ : β.length = p.length)
    (lits certs : List (BitStr × BitStr)) (hl : CorrectPairs p lits) (hc : CorrectPairs p certs) :
    checksProg (p, φ, β, lits, certs) = true ↔
      BinaryPolynomial.evalBits z β = BinaryPolynomial.evalBits z φ *
        (lits.map (fun a => BinaryPolynomial.evalBits z a.1 - BinaryPolynomial.evalBits z a.2)).prod ∧
      BinaryPolynomial.evalBits z β =
        (certs.map (fun a => BinaryPolynomial.evalBits z a.1 *
          (BinaryPolynomial.evalBits z a.2 * (1 - BinaryPolynomial.evalBits z a.2)))).sum := by
  rw [checksProg_apply, checks, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
    ← faithful β (formulaValue p φ lits) hβ (length_formulaValue p φ lits hφ),
    ← faithful β (certificateValue p certs) hβ (length_certificateValue p certs hc),
    eval_formulaValue z p hp hroot φ hφ lits hl, eval_certificateValue z p hp hroot certs hc]

end MIPRE.SAT.PcpFieldTests
