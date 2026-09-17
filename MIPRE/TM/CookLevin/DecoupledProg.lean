/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.CookLevin.Decoupled

/-!
# The decoupled describer as a program, and `ℓ₀`

`ℓ₀ = ⌈log 2T⌉` is pinned by its specification, `2T ≤ 2^{ℓ₀} < 4T` for `T ≥ 1`, so it cannot
be replaced by the cheaper `Nat.size T + 1`, which is right except at powers of two, where it
gives `4T` and violates the strict bound. Written with `Nat.size` it is one more than
`⌈log T⌉` unless `T` is a power of two, and *that* shows on the bits of `T` as every bit but
the top one being zero — which is a fold, so `ℓ₀` is a program
(`planning/decoupled-5sat.md`, A1e).
-/

namespace MIPRE.TM.CookLevin.Desc

open Interp SAT Cost Cost.PolyTimeFun

/-! ## `ℓ₀`, the index length of the answer blocks -/

theorem bitsVal_append_singleton : ∀ (l : BitStr) (b : Bool),
    bitsVal (l ++ [b]) = bitsVal l + (if b then 2 ^ l.length else 0)
  | [], b => by cases b <;> simp [Nat.bit_val]
  | a :: l, b => by
    rw [List.cons_append, bitsVal_cons, bitsVal_append_singleton l b, bitsVal_cons,
      List.length_cons, Nat.bit_val, Nat.bit_val, pow_succ]
    cases b <;> cases a <;> simp <;> ring

/-- `⌈log 2T⌉`, read off the bits of `T`. -/
def lOf (T : ℕ) : ℕ :=
  if T.bits.dropLast.any id = false then Nat.size T else Nat.size T + 1

/-- **`ℓ₀` is the ceiling of the logarithm of `2T`.** -/
theorem lOf_spec (T : ℕ) (hT : 1 ≤ T) : 2 * T ≤ 2 ^ lOf T ∧ 2 ^ lOf T < 4 * T := by
  have hsz : 0 < Nat.size T := Nat.size_pos.2 hT
  have hk1 : Nat.size T = (Nat.size T - 1) + 1 := by omega
  have hlow : 2 ^ (Nat.size T - 1) ≤ T := Nat.lt_size.1 (by omega)
  have hhigh : T < 2 ^ ((Nat.size T - 1) + 1) := by rw [← hk1]; exact Nat.lt_size_self T
  have hlen : T.bits.length = (Nat.size T - 1) + 1 := by
    rw [Nat.size_eq_bits_len]; omega
  have hne : T.bits ≠ [] := by
    intro h
    rw [h, List.length_nil] at hlen
    omega
  have hdl : T.bits.dropLast.length = Nat.size T - 1 := by
    rw [List.length_dropLast, hlen]; omega
  have hdlt : bitsVal T.bits.dropLast < 2 ^ (Nat.size T - 1) := by
    rw [← hdl]; exact bitsVal_lt _
  have hval : T = bitsVal T.bits.dropLast +
      (if T.bits.getLast hne then 2 ^ (Nat.size T - 1) else 0) :=
    calc T = bitsVal T.bits := (bitsVal_bits T).symm
      _ = bitsVal (T.bits.dropLast ++ [T.bits.getLast hne]) := by
          rw [List.dropLast_append_getLast hne]
      _ = bitsVal T.bits.dropLast +
            (if T.bits.getLast hne then 2 ^ (Nat.size T - 1) else 0) := by
          rw [bitsVal_append_singleton, hdl]
  have hlast : T.bits.getLast hne = true := by
    by_contra hc
    rw [Bool.not_eq_true] at hc
    rw [hc, if_neg (by simp)] at hval
    omega
  rw [hlast, if_pos rfl] at hval
  rw [lOf]
  by_cases hany : T.bits.dropLast.any id = false
  · have hz : bitsVal T.bits.dropLast = 0 := (bitsVal_eq_zero_iff _).mpr hany
    rw [if_pos hany, hk1, pow_succ]
    omega
  · have hz : bitsVal T.bits.dropLast ≠ 0 := fun h =>
      hany ((bitsVal_eq_zero_iff _).mp h)
    rw [if_neg hany, hk1, pow_succ, pow_succ]
    omega

end MIPRE.TM.CookLevin.Desc
