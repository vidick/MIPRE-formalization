/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryFold.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.Data.ZMod.Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_length_mulReduce_le

/-! # Uniform sums and products of coefficient vectors -/

namespace MIPRE.LowDegree.BinaryPolynomial

open Cost Cost.PolyTimeFun Polynomial

def arithmeticStep (mul : Bool) (s : BitStr × BitStr) (b : BitStr) : BitStr × BitStr :=
  (s.1, if mul then mulReduce s.1 s.2 b else xorBits s.2 b)

theorem arithmeticStep_width (mul : Bool) (s : BitStr × BitStr) (b : BitStr) :
    (arithmeticStep mul s b).2.length ≤ s.2.length := by
  cases mul
  · change (xorBits s.2 b).length ≤ s.2.length
    rw [length_xorBits]
    exact min_le_left _ _
  · exact length_mulReduce_le _ _ _

theorem fold_arithmeticStep (mul : Bool) (l : List BitStr) (s : BitStr × BitStr) :
    (l.foldl (arithmeticStep mul) s).1 = s.1 ∧
      (l.foldl (arithmeticStep mul) s).2.length ≤ s.2.length := by
  induction l generalizing s with
  | nil => exact ⟨rfl, le_rfl⟩
  | cons b l ih =>
    obtain ⟨hp, hl⟩ := ih (arithmeticStep mul s b)
    exact ⟨hp, hl.trans (arithmeticStep_width mul s b)⟩

/-- Sum or product, starting from a supplied coefficient vector. -/
def arithmeticFold (mul : Bool) (p a : BitStr) (l : List BitStr) : BitStr :=
  (l.foldl (arithmeticStep mul) (p, a)).2

variable {R : Type*} [CommRing R] [CharP R 2]

noncomputable def arithmeticStepProg (mul : Bool) :
    PolyTimeFun ((BitStr × BitStr) × BitStr) (BitStr × BitStr) :=
  (fst.comp fst).pair (ite (const mul)
    (mulReduceProg.comp ((fst.comp fst).pair ((snd.comp fst).pair snd)))
    (xorBitsProg.comp ((snd.comp fst).pair snd)))

theorem arithmeticStep_bounded (mul : Bool) :
    FoldBounded (arithmeticStepProg mul) (5 * X + 5) := by
  intro l s pre post _
  change esize (pre.foldl (arithmeticStep mul) s) ≤ _
  obtain ⟨hp, hw⟩ := fold_arithmeticStep mul pre s
  have hs : esize s = esize s.1 + esize s.2 + 1 := rfl
  have hi := length_le_esize_list s.2
  have ho := esize_bitStr_le (pre.foldl (arithmeticStep mul) s).2
  rw [esize_prod, hp]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, esize_prod]
  omega

/-- Globally polynomial-time summation or multiplication of coefficient vectors.
The modulus and initial accumulator are explicit inputs. -/
noncomputable def arithmeticFoldProg (mul : Bool) :
    PolyTimeFun (BitStr × BitStr × List BitStr) BitStr :=
  congr (snd.comp
    ((foldl (arithmeticStepProg mul) (5 * X + 5) (arithmeticStep_bounded mul)).comp
      ((snd.comp snd).pair (fst.pair (fst.comp snd)))))
    (fun p => arithmeticFold mul p.1 p.2.1 p.2.2) (by intro p; rfl)

@[simp] theorem arithmeticFoldProg_apply (mul : Bool) (p a : BitStr) (l : List BitStr) :
    arithmeticFoldProg mul (p, a, l) = arithmeticFold mul p a l := rfl

end MIPRE.LowDegree.BinaryPolynomial
