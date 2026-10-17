/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryPower.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
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
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_length_mulReduce_le

/-!
# Binary exponentiation in a polynomial-basis field

The exponent remains a little-endian bit string. The loop performs one squaring
and at most one multiplication per bit and keeps fixed-width coefficient vectors.
Its polynomial bound also holds for malformed inputs.
-/

namespace MIPRE.LowDegree.BinaryPolynomial

open Cost Cost.PolyTimeFun Polynomial

abbrev PowerState := BitStr × BitStr × BitStr

def powerStep (s : PowerState) (b : Bool) : PowerState :=
  (s.1, mulReduce s.1 s.2.1 s.2.1,
    if b then mulReduce s.1 s.2.2 s.2.1 else s.2.2)

theorem powerStep_width (s : PowerState) (b : Bool) :
    (powerStep s b).1 = s.1 ∧
    (powerStep s b).2.1.length ≤ s.2.1.length ∧
    (powerStep s b).2.2.length ≤ s.2.2.length := by
  refine ⟨rfl, length_mulReduce_le _ _ _, ?_⟩
  cases b
  · exact le_rfl
  · exact length_mulReduce_le _ _ _

theorem fold_powerStep_width (l : BitStr) (s : PowerState) :
    (l.foldl powerStep s).1 = s.1 ∧
    (l.foldl powerStep s).2.1.length ≤ s.2.1.length ∧
    (l.foldl powerStep s).2.2.length ≤ s.2.2.length := by
  induction l generalizing s with
  | nil => exact ⟨rfl, le_rfl, le_rfl⟩
  | cons b l ih =>
    obtain ⟨hp, ha, hc⟩ := ih (powerStep s b)
    obtain ⟨_, ha', hc'⟩ := powerStep_width s b
    exact ⟨hp, ha.trans ha', hc.trans hc'⟩

/-- Repeated squaring with a binary exponent. -/
def powerBits (p a e : BitStr) : BitStr :=
  (e.foldl powerStep (p, a, oneBits p)).2.2

variable {R : Type*} [CommRing R] [CharP R 2]

noncomputable def powerStepProg : PolyTimeFun (PowerState × Bool) PowerState :=
  let p := fst.comp fst
  let a := fst.comp (snd.comp fst)
  let c := snd.comp (snd.comp fst)
  p.pair ((mulReduceProg.comp (p.pair (a.pair a))).pair
    (ite snd (mulReduceProg.comp (p.pair (c.pair a))) c))

theorem powerStep_bounded : FoldBounded powerStepProg (9 * X + 9) := by
  intro l s pre post _
  change esize (pre.foldl powerStep s) ≤ _
  obtain ⟨hp, ha, hc⟩ := fold_powerStep_width pre s
  have ha0 := length_le_esize_list s.2.1
  have hc0 := length_le_esize_list s.2.2
  have hsa := esize_bitStr_le (pre.foldl powerStep s).2.1
  have hsc := esize_bitStr_le (pre.foldl powerStep s).2.2
  have hs : esize s = esize s.1 + (esize s.2.1 + esize s.2.2 + 1) + 1 := rfl
  rw [esize_prod, esize_prod, hp]
  grw [hsa, hsc, ha, hc, ha0, hc0]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, esize_prod]
  omega

/-- One uniform ambient program for exponentiation with binary exponent input. -/
noncomputable def powerBitsProg : PolyTimeFun (BitStr × BitStr × BitStr) BitStr :=
  congr ((snd.comp snd).comp
    ((foldl powerStepProg (9 * X + 9) powerStep_bounded).comp
      ((snd.comp snd).pair
        (fst.pair ((fst.comp snd).pair (oneBitsProg.comp fst))))))
    (fun a => powerBits a.1 a.2.1 a.2.2) (by intro a; rfl)

@[simp] theorem powerBitsProg_apply (p a e : BitStr) :
    powerBitsProg (p, a, e) = powerBits p a e := rfl

end MIPRE.LowDegree.BinaryPolynomial
