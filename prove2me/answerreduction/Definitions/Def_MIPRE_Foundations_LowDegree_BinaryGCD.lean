/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryGCD.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Content
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNormalize
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDivision
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_divModBits_width

/-!
# Deterministic binary polynomial gcd

Euclidean division decreases the canonical divisor width. The original divisor
list supplies the iteration budget, and a zero-divisor state is absorbing.
The same width bound holds for malformed states, so the ambient program has a
global polynomial bound rather than a promise only on well-formed inputs.
-/

namespace MIPRE.LowDegree.BinaryPolynomial

open Cost Cost.PolyTimeFun Polynomial

/-- Two successive remainders in the Euclidean algorithm. -/
abbrev GCDState := BitStr × BitStr

/-- One bounded Euclidean iteration; its second input serves only as fuel. -/
def gcdStep (s : GCDState) (_ : Bool) : GCDState :=
  if s.2.isEmpty then s else (s.2, (divModBits s.2.dropLast s.1).2)

/-- Both state components stay within the original maximum width. -/
theorem gcdStep_width (s : GCDState) (b : Bool) :
    max (gcdStep s b).1.length (gcdStep s b).2.length ≤ max s.1.length s.2.length := by
  unfold gcdStep
  split
  · exact le_rfl
  · have h := (divModBits_width s.2.dropLast s.1).2
    simp only [List.length_dropLast] at h
    exact max_le (le_max_right _ _) (h.trans ((Nat.sub_le _ _).trans (le_max_right _ _)))

/-- An entire bounded loop retains the original width bound. -/
theorem fold_gcdStep_width (l : BitStr) (s : GCDState) :
    max (l.foldl gcdStep s).1.length (l.foldl gcdStep s).2.length ≤
      max s.1.length s.2.length := by
  induction l generalizing s with
  | nil => exact le_rfl
  | cons b l ih => exact (ih (gcdStep s b)).trans (gcdStep_width s b)

/-- The binary Euclidean algorithm uses one iteration per original divisor bit. -/
def gcdBits (a b : BitStr) : BitStr :=
  (b.foldl gcdStep (normalizeBits a, normalizeBits b)).1

noncomputable def isEmptyProg_BinaryGCD : PolyTimeFun BitStr Bool :=
  congr ((casesList (const true) (const false)).comp ((const ()).pair (PolyTimeFun.id _)))
    List.isEmpty (by intro a; cases a <;> rfl)

noncomputable def tailBitsProg : PolyTimeFun BitStr BitStr :=
  congr ((casesList (const []) (snd.comp snd)).comp ((const ()).pair (PolyTimeFun.id _)))
    List.tail (by intro a; cases a <;> rfl)

/-- Remove the implicit leading coefficient before passing a canonical divisor to division. -/
noncomputable def dropLastBitsProg : PolyTimeFun BitStr BitStr :=
  congr (PolyTimeFun.reverse.comp (tailBitsProg.comp PolyTimeFun.reverse)) List.dropLast (by
    intro a
    change a.reverse.tail.reverse = a.dropLast
    rw [List.tail_reverse, List.reverse_reverse])

@[simp] theorem dropLastBitsProg_apply (a : BitStr) : dropLastBitsProg a = a.dropLast := rfl

noncomputable def gcdStepProg : PolyTimeFun (GCDState × Bool) GCDState :=
  ite (isEmptyProg_BinaryGCD.comp (snd.comp fst)) fst
    ((snd.comp fst).pair (snd.comp (divModBitsProg.comp
      ((dropLastBitsProg.comp (snd.comp fst)).pair (fst.comp fst)))))

theorem gcdStep_bounded : FoldBounded gcdStepProg (10 * X + 10) := by
  intro l s pre post _
  change esize (pre.foldl gcdStep s) ≤ _
  have hw := fold_gcdStep_width pre s
  have h1 := esize_bitStr_le (pre.foldl gcdStep s).1
  have h2 := esize_bitStr_le (pre.foldl gcdStep s).2
  have hs1 := length_le_esize_list s.1
  have hs2 := length_le_esize_list s.2
  have hs : esize s = esize s.1 + esize s.2 + 1 := rfl
  change esize (pre.foldl gcdStep s).1 + esize (pre.foldl gcdStep s).2 + 1 ≤ _
  simp only [esize_prod, hs, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_X]
  omega

/-- A fixed deterministic ambient program for binary polynomial gcd. -/
noncomputable def gcdBitsProg : PolyTimeFun (BitStr × BitStr) BitStr :=
  congr (fst.comp ((foldl gcdStepProg (10 * X + 10) gcdStep_bounded).comp
    (snd.pair ((normalizeBitsProg.comp fst).pair (normalizeBitsProg.comp snd)))))
    (fun s => gcdBits s.1 s.2) (by intro s; rfl)

@[simp] theorem gcdBitsProg_apply (a b : BitStr) : gcdBitsProg (a, b) = gcdBits a b := rfl

end MIPRE.LowDegree.BinaryPolynomial
