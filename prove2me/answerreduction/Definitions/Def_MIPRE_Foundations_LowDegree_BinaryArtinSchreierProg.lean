/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryArtinSchreierProg.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNormalize

/-! # Effective substitution by the Artin–Schreier polynomial -/

namespace MIPRE.LowDegree.BinaryPolynomial

open Cost Cost.PolyTimeFun Polynomial

/-- One Horner step for substitution by `X² + X`. Both XOR inputs have equal width. -/
def artinSchreierStep (a : BitStr) (b : Bool) : BitStr :=
  b :: xorBits (false :: a) (a ++ [false])

@[simp] theorem artinSchreierStep_length (a : BitStr) (b : Bool) :
    (artinSchreierStep a b).length = a.length + 2 := by
  simp [artinSchreierStep]

/-- Substitute `X² + X`, then remove redundant trailing zero coefficients. -/
def substituteArtinSchreierBits (a : BitStr) : BitStr :=
  normalizeBits (a.foldr (fun b s => artinSchreierStep s b) [])

theorem fold_artinSchreierStep_length (l a : BitStr) :
    (l.foldl artinSchreierStep a).length = a.length + 2 * l.length := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    rw [List.foldl_cons, ih, artinSchreierStep_length, List.length_cons]
    omega

noncomputable def artinSchreierStepProg : PolyTimeFun (BitStr × Bool) BitStr :=
  cons snd (xorBitsProg.comp ((cons (const false) fst).pair
    (append.comp (fst.pair (const [false])))))

theorem artinSchreierStep_bounded : FoldBounded artinSchreierStepProg (12 * X + 1) := by
  intro l s pre post h
  change esize (pre.foldl artinSchreierStep s) ≤ _
  have hw := fold_artinSchreierStep_length pre s
  have he := esize_bitStr_le (pre.foldl artinSchreierStep s)
  have hs := length_le_esize_bitStr s
  have hl := length_le_esize_bitStr l
  have hp : pre.length ≤ l.length := by rw [h, List.length_append]; omega
  simp only [eval_add, eval_mul, eval_ofNat, eval_X, esize_prod]
  omega

/-- A single ambient polynomial-time program for `X² + X` substitution. -/
noncomputable def substituteArtinSchreierBitsProg : PolyTimeFun BitStr BitStr :=
  congr (normalizeBitsProg.comp ((foldl artinSchreierStepProg (12 * X + 1)
    artinSchreierStep_bounded).comp (reverse.pair (const []))))
    substituteArtinSchreierBits (by
      intro a
      change normalizeBits (a.reverse.foldl artinSchreierStep []) = _
      rw [List.foldl_reverse]
      rfl)

@[simp] theorem substituteArtinSchreierBitsProg_apply (a : BitStr) :
    substituteArtinSchreierBitsProg a = substituteArtinSchreierBits a := rfl

end MIPRE.LowDegree.BinaryPolynomial
