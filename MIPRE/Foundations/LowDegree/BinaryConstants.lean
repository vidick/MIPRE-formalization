/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryPolynomial

/-! # Fixed-width zero and one for binary polynomial quotients -/

namespace MIPRE.LowDegree.BinaryPolynomial

open Cost

/-- Zero and one use the width of the supplied lower-coefficient vector. -/
def zeroBits (p : BitStr) : BitStr := List.replicate p.length false

def oneBits : BitStr → BitStr
  | [] => []
  | _ :: p => true :: List.replicate p.length false

@[simp] theorem length_zeroBits (p : BitStr) : (zeroBits p).length = p.length := by
  simp [zeroBits]

@[simp] theorem length_oneBits (p : BitStr) : (oneBits p).length = p.length := by
  cases p <;> simp [oneBits]

variable {R : Type*} [CommRing R]

@[simp] theorem evalBits_zeroBits (z : R) (p : BitStr) : evalBits z (zeroBits p) = 0 := by
  simp [zeroBits]

theorem evalBits_oneBits (z : R) (p : BitStr) (hp : p ≠ []) : evalBits z (oneBits p) = 1 := by
  cases p <;> simp_all [oneBits, ofBool]

open Cost.PolyTimeFun

noncomputable def zeroBitsProg : PolyTimeFun BitStr BitStr :=
  congr (replicate.comp (length.pair (const false))) zeroBits (by intro p; simp [zeroBits])

noncomputable def oneBitsProg : PolyTimeFun BitStr BitStr :=
  congr ((casesList (const [])
    (cons (const true) (zeroBitsProg.comp (snd.comp snd)))).comp
      ((const ()).pair (PolyTimeFun.id _))) oneBits (by intro p; cases p <;> rfl)

@[simp] theorem zeroBitsProg_apply (p : BitStr) : zeroBitsProg p = zeroBits p := rfl
@[simp] theorem oneBitsProg_apply (p : BitStr) : oneBitsProg p = oneBits p := rfl

end MIPRE.LowDegree.BinaryPolynomial
