/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.ParserAnswers

/-! # Polynomial-time slicing at binary offsets

The requested offset is capped by the actual input length before it is
materialized as a unary scan. In particular a large binary bound does not
cause an exponentially large intermediate allocation.
-/

noncomputable section

namespace MIPRE.Introspection.DynamicParser

open Cost Cost.PolyTimeFun Polynomial

private def capStepFun (s : ℕ × Unary) (_ : Bool) : ℕ × Unary :=
  if s.2.length + 1 ≤ s.1 then (s.1, () :: s.2) else s

private def capStep : PolyTimeFun ((ℕ × Unary) × Bool) (ℕ × Unary) :=
  let state : PolyTimeFun ((ℕ × Unary) × Bool) (ℕ × Unary) := fst
  let num := fst.comp state
  let acc := snd.comp state
  ite (ap₂ leNat (inc.comp (unaryToBin.comp acc)) num)
    (num.pair (cons (const ()) acc)) state

private theorem capStep_apply (s : ℕ × Unary) (b : Bool) :
    capStep (s, b) = capStepFun s b := by
  simp [capStep, capStepFun, PolyTimeFun.ite_apply]

private theorem capStep_size (s : ℕ × Unary) (b : Bool) :
    esize (capStep (s, b)) ≤ esize s + (C 2).eval (esize b) := by
  rcases s with ⟨n, u⟩
  rw [capStep_apply]
  unfold capStepFun
  split_ifs <;> simp [esize_prod, show esize () = 1 from rfl]
  omega

private theorem cap_fold (bs : BitStr) (n : ℕ) (u : Unary) (hu : u.length ≤ n) :
    bs.foldl capStepFun (n, u) = (n, unary (min n (u.length + bs.length))) := by
  induction bs generalizing u with
  | nil => simpa [Nat.min_eq_right hu] using congrArg (n, ·) (unary_length u).symm
  | cons b bs ih =>
    rw [List.foldl_cons]
    by_cases hh : u.length + 1 ≤ n
    · rw [capStepFun, if_pos hh, ih (() :: u) (by simpa using hh)]
      congr 3
      simp [Nat.add_comm, Nat.add_left_comm]
    · have he : u.length = n := by omega
      rw [capStepFun, if_neg hh, ih u hu]
      congr 2
      simp [he]

/-- A uniform binary offset reader, outputting at most one unit per input bit. -/
def boundedOffset : PolyTimeFun (BitStr × ℕ) Unary :=
  congr (snd.comp ((foldlAdd capStep (C 2) capStep_size).comp
    (fst.pair (snd.pair (const [])))))
    (fun p => unary (min p.2 p.1.length)) (by
      rintro ⟨bs, n⟩
      simpa only [comp_apply, pair_apply, fst_apply, snd_apply, const_apply,
        foldlAdd_apply, capStep_apply, List.length_nil, Nat.zero_add] using
        congrArg Prod.snd (cap_fold bs n [] (by simp)))

@[simp] theorem boundedOffset_apply (bs : BitStr) (n : ℕ) :
    boundedOffset (bs, n) = unary (min n bs.length) := rfl

theorem boundedOffset_length_le (bs : BitStr) (n : ℕ) :
    (boundedOffset (bs, n)).length ≤ bs.length := by simp

/-- Taking a prefix with a binary index is polynomial in the input encoding size. -/
def takeBits : PolyTimeFun (BitStr × ℕ) BitStr := ap₂ take fst boundedOffset

@[simp] theorem takeBits_apply (bs : BitStr) (n : ℕ) : takeBits (bs, n) = bs.take n := by
  simp only [takeBits, ap₂_apply, fst_apply, boundedOffset_apply, take_apply, length_unary]
  by_cases hn : n ≤ bs.length
  · rw [Nat.min_eq_left hn]
  · rw [Nat.min_eq_right (by omega), List.take_length, List.take_of_length_le (by omega)]

/-- Dropping a prefix with a binary index uses the same bounded scan. -/
def dropBits : PolyTimeFun (BitStr × ℕ) BitStr := ap₂ drop fst boundedOffset

@[simp] theorem dropBits_apply (bs : BitStr) (n : ℕ) : dropBits (bs, n) = bs.drop n := by
  simp only [dropBits, ap₂_apply, fst_apply, boundedOffset_apply, drop_apply, length_unary]
  by_cases hn : n ≤ bs.length
  · rw [Nat.min_eq_left hn]
  · rw [Nat.min_eq_right (by omega), List.drop_length, List.drop_eq_nil_of_le (by omega)]

end MIPRE.Introspection.DynamicParser

end
