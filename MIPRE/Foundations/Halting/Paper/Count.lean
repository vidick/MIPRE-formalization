/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.Halting.Tabulate

@[expose] public section

/-!
# Counting seeds by their prefix

The class verifier of the polynomial-time halting reduction reads only the first `d` bits of
its seed of length `d + e`, so the number of seeds whose prefix satisfies a predicate is the
number of prefixes that do, times `2 ^ e` (`length_filter_take`). Together with
`length_filter_bitStrsOfLen` this turns the verifier's seed count into the numerator of the
compressed sampler's distribution `CL.clDist`.
-/

namespace MIPRE.Cost.Data

theorem bitStrsOfLen_succ (k : ℕ) :
    bitStrsOfLen (k + 1) = (bitStrsOfLen k).flatMap fun l => [false :: l, true :: l] := rfl

/-- Filtering the strings obtained by prepending a bit to each string of a list. -/
theorem length_filter_flatMap_bits (L : List BitStr) (p : BitStr → Bool) :
    ((L.flatMap fun l => [false :: l, true :: l]).filter p).length =
      (L.filter fun l => p (false :: l)).length + (L.filter fun l => p (true :: l)).length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.flatMap_cons, List.filter_append, List.length_append, ih]
    have h : ([false :: a, true :: a].filter p).length =
        (if p (false :: a) then 1 else 0) + (if p (true :: a) then 1 else 0) := by
      simp only [List.filter, List.length_nil]
      cases p (false :: a) <;> cases p (true :: a) <;> simp
    rw [h]
    simp only [List.filter_cons]
    cases p (false :: a) <;> cases p (true :: a) <;> simp <;> omega

/-- **Counting by prefix**: the strings of length `d + e` whose first `d` bits satisfy `Q`
number the strings of length `d` satisfying `Q`, times `2 ^ e`. -/
theorem length_filter_take (Q : BitStr → Bool) (d e : ℕ) :
    ((bitStrsOfLen (d + e)).filter fun r => Q (r.take d)).length =
      ((bitStrsOfLen d).filter Q).length * 2 ^ e := by
  induction d generalizing Q with
  | zero =>
    simp only [Nat.zero_add, List.take_zero, bitStrsOfLen]
    cases hq : Q [] <;> simp [hq, length_bitStrsOfLen]
  | succ d ih =>
    rw [show d + 1 + e = d + e + 1 by omega, bitStrsOfLen_succ, bitStrsOfLen_succ,
      length_filter_flatMap_bits, length_filter_flatMap_bits]
    simp only [List.take_succ_cons]
    rw [ih (fun s => Q (false :: s)), ih (fun s => Q (true :: s)), Nat.add_mul]

end MIPRE.Cost.Data

end
