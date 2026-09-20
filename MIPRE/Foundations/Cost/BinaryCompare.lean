/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Cost.Reader
import MIPRE.Foundations.Cost.Numeric

/-!
# Polynomial-time comparison of binary natural numbers

The comparison scans coefficient bits directly, padding only by the supplied
bit-string lengths. It never expands a binary number to unary.
-/

namespace MIPRE.Cost

open Polynomial PolyTimeFun

private def compareStep (acc : Bool) (p : Bool × Bool) : Bool :=
  if p.1 then (if p.2 then acc else false) else (if p.2 then true else acc)

private theorem compare_fold (a b : BitStr) (acc : Bool) (h : a.length = b.length) :
    (a.zip b).foldl compareStep acc = true ↔
      bitsVal a < bitsVal b ∨ (bitsVal a = bitsVal b ∧ acc = true) := by
  induction a generalizing b acc with
  | nil =>
    have hb : b = [] := List.length_eq_zero_iff.mp h.symm
    subst b
    simp
  | cons a as ih =>
    cases b with
    | nil => simp at h
    | cons b bs =>
      simp only [List.zip_cons_cons, List.foldl_cons]
      rw [ih bs _ (by simpa using h)]
      cases a <;> cases b <;> cases acc <;>
        simp [compareStep, bitsVal_cons, Nat.bit] <;> omega

private theorem bitsVal_append_false (a : BitStr) (n : ℕ) :
    bitsVal (a ++ List.replicate n false) = bitsVal a := by
  induction a with
  | nil =>
    induction n with
    | zero => rfl
    | succ n ih => simpa [List.replicate_succ, bitsVal_cons, Nat.bit] using ih
  | cons b a ih => simp only [List.cons_append, bitsVal_cons, ih]

private theorem esize_bool_le (b : Bool) : esize b ≤ 3 := by cases b <;> decide

private noncomputable def compareStepProg : PolyTimeFun (Bool × (Bool × Bool)) Bool :=
  ite (fst.comp snd) (ite (snd.comp snd) fst (const false))
    (ite (snd.comp snd) (const true) fst)

private theorem compareStepProg_apply (b : Bool) (p : Bool × Bool) :
    compareStepProg (b, p) = compareStep b p := rfl

/-- Compare arbitrary little-endian strings, allowing leading zeroes. -/
noncomputable def PolyTimeFun.leBits : PolyTimeFun (BitStr × BitStr) Bool :=
  let scan := foldlAdd compareStepProg 3 (by
    intro s a
    have hb := esize_bool_le (compareStepProg (s, a))
    simp only [Polynomial.eval_ofNat]
    omega)
  let a : PolyTimeFun (BitStr × BitStr) BitStr :=
    append.comp (fst.pair (replicate.comp ((length.comp snd).pair (const false))))
  let b : PolyTimeFun (BitStr × BitStr) BitStr :=
    append.comp (snd.pair (replicate.comp ((length.comp fst).pair (const false))))
  congr (scan.comp ((zip.comp (a.pair b)).pair (const true)))
    (fun p => decide (bitsVal p.1 ≤ bitsVal p.2)) (by
      intro p
      simp only [scan, a, b, comp_apply, foldlAdd_apply, pair_apply, zip_apply,
        append_apply, fst_apply, snd_apply, replicate_apply, length_apply,
        length_unary, const_apply, compareStepProg_apply]
      apply Bool.eq_iff_iff.mpr
      rw [compare_fold _ _ true (by simp [Nat.add_comm])]
      simp only [bitsVal_append_false, and_true, decide_eq_true_eq]
      omega)

@[simp] theorem PolyTimeFun.leBits_apply (p : BitStr × BitStr) :
    leBits p = decide (bitsVal p.1 ≤ bitsVal p.2) := rfl

/-- Binary natural comparison, with a global polynomial cost in the encodings. -/
noncomputable def PolyTimeFun.leNat : PolyTimeFun (ℕ × ℕ) Bool :=
  let bits : PolyTimeFun ℕ BitStr := ofEncodeEq Nat.bits (fun _ => rfl)
  congr (leBits.comp ((bits.comp fst).pair (bits.comp snd)))
    (fun p => decide (p.1 ≤ p.2)) (by intro p; simp only [comp_apply, leBits_apply,
      pair_apply, bits, ofEncodeEq_apply, fst_apply, snd_apply, bitsVal_bits])

@[simp] theorem PolyTimeFun.leNat_apply (p : ℕ × ℕ) : leNat p = decide (p.1 ≤ p.2) := rfl

end MIPRE.Cost
