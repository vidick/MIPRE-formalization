/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryCoprimeDegree.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.FieldTheory.Finite.Extension

/-! # Exact degrees of sums with coprime binary field degrees -/

noncomputable section

namespace MIPRE.LowDegree.BinaryFiniteField

open Polynomial

variable {R : Type*} [CommRing R] [CharP R 2]

theorem frobenius_comm (a b : ℕ) (x : R) :
    iterateFrobenius R 2 a (iterateFrobenius R 2 b x) =
      iterateFrobenius R 2 b (iterateFrobenius R 2 a x) := by
  rw [← iterateFrobenius_add_apply, Nat.add_comm a b, iterateFrobenius_add_apply]

omit [CharP R 2] in
theorem iterate_add_delta (F : R →+ R) (x d : R)
    (hx : F x = x + d) (hd : F d = d) (n : ℕ) : F^[n] x = x + n • d := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, map_add, map_nsmul, hx, hd, succ_nsmul]
    abel

omit [CharP R 2] in
theorem nsmul_delta_eq_zero (F : R →+ R) (x : R) (n : ℕ)
    (hd : F (F x - x) = F x - x) (hx : F^[n] x = x) : n • (F x - x) = 0 := by
  have h := iterate_add_delta F x (F x - x) (by abel) hd n
  rw [hx] at h
  exact (add_left_cancel (show x + n • (F x - x) = x + 0 by simpa using h.symm))

variable {L : Type*} [Field L] [Algebra (ZMod 2) L]

end MIPRE.LowDegree.BinaryFiniteField

end
