/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryNormalize

/-! # Effective substitution by the Artin–Schreier polynomial -/

namespace MIPRE.LowDegree.BinaryPolynomial

open Cost Cost.PolyTimeFun Polynomial

/-- One Horner step for substitution by `X² + X`. Both XOR inputs have equal width. -/
def artinSchreierStep (a : BitStr) (b : Bool) : BitStr :=
  b :: xorBits (false :: a) (a ++ [false])

@[simp] theorem artinSchreierStep_length (a : BitStr) (b : Bool) :
    (artinSchreierStep a b).length = a.length + 2 := by
  simp [artinSchreierStep]

/-- The Horner step has its stated semantics in every characteristic-two ring. -/
theorem evalBits_artinSchreierStep {R : Type*} [CommRing R] [CharP R 2]
    (z : R) (a : BitStr) (b : Bool) :
    evalBits z (artinSchreierStep a b) = ofBool b + (z ^ 2 + z) * evalBits z a := by
  rw [artinSchreierStep, evalBits_cons, evalBits_xor z _ _ (by simp)]
  simp only [evalBits_cons, evalBits_append, evalBits_nil, ofBool, Bool.false_eq_true,
    ↓reduceIte, mul_zero, add_zero, zero_add]
  ring

/-- Substitute `X² + X`, then remove redundant trailing zero coefficients. -/
def substituteArtinSchreierBits (a : BitStr) : BitStr :=
  normalizeBits (a.foldr (fun b s => artinSchreierStep s b) [])

theorem evalBits_substituteArtinSchreierBits {R : Type*} [CommRing R] [CharP R 2]
    (z : R) (a : BitStr) :
    evalBits z (substituteArtinSchreierBits a) = evalBits (z ^ 2 + z) a := by
  rw [substituteArtinSchreierBits, evalBits_normalizeBits]
  induction a with
  | nil => rfl
  | cons b a ih =>
    simp only [List.foldr_cons, evalBits_artinSchreierStep, evalBits_cons, ih]

/-- The executable substitution agrees with polynomial composition. -/
theorem polyOfBits_substituteArtinSchreierBits (a : BitStr) :
    polyOfBits (substituteArtinSchreierBits a) = (polyOfBits a).comp (X ^ 2 + X) := by
  rw [polyOfBits_eq_evalBits, evalBits_substituteArtinSchreierBits]
  exact (eval₂_polyOfBits Polynomial.C (X ^ 2 + X) a).symm

private theorem fold_artinSchreierStep_length (l a : BitStr) :
    (l.foldl artinSchreierStep a).length = a.length + 2 * l.length := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    rw [List.foldl_cons, ih, artinSchreierStep_length, List.length_cons]
    omega

/-- All inputs have linear output width, including redundant or zero inputs. -/
theorem substituteArtinSchreierBits_width (a : BitStr) :
    (substituteArtinSchreierBits a).length ≤ 2 * a.length := by
  apply (length_normalizeBits_le _).trans
  rw [← List.foldl_reverse, fold_artinSchreierStep_length]
  simp

private noncomputable def artinSchreierStepProg : PolyTimeFun (BitStr × Bool) BitStr :=
  cons snd (xorBitsProg.comp ((cons (const false) fst).pair
    (append.comp (fst.pair (const [false])))))

private theorem artinSchreierStep_bounded : FoldBounded artinSchreierStepProg (12 * X + 1) := by
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