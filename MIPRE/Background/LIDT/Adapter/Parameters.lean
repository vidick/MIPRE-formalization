/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.LIDT.Game
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The seeded-CL adapter, part 7: the parameter corollary

The reduction of `Adapter/Reduction.lean` concludes with the *canonical-line* error
`lidtError m d q k (3m ε)`, with `k` free subject to `k ≥ 400 m d`. Blueprint
`thm:lidt-cl-soundness` asks instead for

`δ_CL(ε, q, m, d, 1) = a (dm)^a (ε^b + q^{-b} + 2^{-bmd})`,

for universal `a ≥ 1` and `0 < b < 1`. `rem:lidt-cl-adapter` lists turning one into the other as
a separate quantitative obligation, to be done "honestly against the explicit constants"; this
file does it, and is stated separately from the reduction so that a failure here could not
silently weaken the reduction.

The choice is `b = 1/40000`, `a = 2·10^11` and `k = 400 m³ d + 400 m`. Term by term, with
`ε' = 3 m ε`:

* `ε'^b = (3m)^b ε^b ≤ 3m · ε^b`, since `x^b ≤ x` for `x ≥ 1` and `b ≤ 1`;
* `(d/q)^b = d^b · q^{-b} ≤ d · q^{-b}`, likewise;
* `exp(-k / (2560000 m²)) ≤ 2^{-bmd}`, which is where `k` is chosen: it needs
  `k ≥ 2560000 · b · m³ d · ln 2 = 64 (ln 2) m³ d ≈ 44.4 m³ d`, and `400 m³ d` clears it with
  room. The `400 m` summand is there only so that `k > 0` and `k ≥ 400 m d` hold for every
  `m, d ≥ 1`.

The prefactor is then `100000 k² m⁴ · 3md ≤ 1.92·10^11 (dm)^11`, using `k ≤ 800 m³ d`, and
`(dm)^11 ≤ (dm)^a`.

`d ≥ 1` is needed and not cosmetic: at `d = 0` the blueprint's `δ_CL` is identically zero, so no
positive error can be bounded by it.
-/

namespace MIPRE.LIDT

/-! ## The constants -/

/-- The exponent of `δ_CL`. -/
noncomputable def clB : ℝ := 1 / 40000

/-- The constant of `δ_CL`. -/
def clA : ℝ := 2 * 10 ^ 11

/-- The sampling parameter the corollary chooses for the canonical-line theorem. -/
def clK (m d : ℕ) : ℕ := 400 * m ^ 3 * d + 400 * m

/-- **`δ_CL` at `ldc = 1`** (blueprint `thm:lidt-cl-soundness`). -/
noncomputable def deltaCL (q m d : ℕ) (ε : ℝ) : ℝ :=
  clA * ((d * m : ℕ) : ℝ) ^ clA *
    (ε ^ clB + (q : ℝ) ^ (-clB) + (2 : ℝ) ^ (-(clB * m * d)))

theorem clB_eq : clB = 1 / 40000 := rfl

theorem clB_pos : 0 < clB := by rw [clB]; norm_num

theorem clB_lt_one : clB < 1 := by rw [clB]; norm_num

theorem one_le_clA : (1 : ℝ) ≤ clA := by rw [clA]; norm_num

/-! ## The sampling parameter -/

/-- `clK` clears the canonical-line theorem's hypothesis. -/
theorem le_clK (m d : ℕ) (hm : 1 ≤ m) : 400 * m * d ≤ clK m d := by
  have h1 : m ≤ m ^ 3 := Nat.le_self_pow (by norm_num) m
  have e1 : 400 * m ^ 3 * d = 400 * m * d * m ^ 2 := by ring
  rw [clK]
  have h2 : 400 * m * d ≤ 400 * m * d * m ^ 2 :=
    Nat.le_mul_of_pos_right _ (Nat.pow_pos hm)
  omega

theorem clK_pos (m d : ℕ) (_hm : 1 ≤ m) : 0 < clK m d := by
  rw [clK]
  have : 0 < 400 * m := by omega
  omega

/-- `clK` is at most `800 m³ d`, which is what bounds the prefactor. -/
theorem clK_le (m d : ℕ) (_hm : 1 ≤ m) (hd : 1 ≤ d) : clK m d ≤ 800 * m ^ 3 * d := by
  have h1 : m ≤ m ^ 3 := Nat.le_self_pow (by norm_num) m
  have h2 : m ^ 3 ≤ m ^ 3 * d := Nat.le_mul_of_pos_right _ hd
  have h3 : m ≤ m ^ 3 * d := le_trans h1 h2
  have e1 : 400 * m ^ 3 * d = 400 * (m ^ 3 * d) := by ring
  have e2 : 800 * m ^ 3 * d = 400 * (m ^ 3 * d) + 400 * (m ^ 3 * d) := by ring
  rw [clK, e1, e2]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left 400 h3) _

/-! ## The three terms -/

/-- **The exponential term.** This is where `clK` is chosen. -/
theorem exp_le_two_rpow (m d : ℕ) (hm : 1 ≤ m) :
    Real.exp (-(clK m d : ℝ) / (2560000 * (m : ℝ) ^ 2))
      ≤ (2 : ℝ) ^ (-(clB * m * d)) := by
  have hM : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hD : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hlog : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog0 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  -- `clK` is at least `400 m³ d`
  have hK : 400 * (m : ℝ) ^ 3 * d ≤ (clK m d : ℝ) := by
    rw [clK]
    push_cast
    nlinarith [hM, hD]
  have h1 : (m : ℝ) * d / 6400 ≤ (clK m d : ℝ) / (2560000 * (m : ℝ) ^ 2) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith [hK, hM, hD, sq_nonneg ((m : ℝ) - 1)]
  have h2 : Real.log 2 * (clB * m * d) ≤ (m : ℝ) * d / 6400 := by
    rw [clB]
    nlinarith [hlog, hM, hD, mul_nonneg (le_trans zero_le_one hM) hD]
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2), mul_neg]
  refine Real.exp_le_exp.mpr ?_
  rw [neg_div]
  linarith [h2.trans h1]

/-- **The `ε` term**: the adapter's factor `3m` comes out of the exponent. -/
theorem rpow_mul_le (m : ℕ) (hm : 1 ≤ m) (ε : ℝ) (hε : 0 ≤ ε) :
    (3 * (m : ℝ) * ε) ^ clB ≤ 3 * (m : ℝ) * ε ^ clB := by
  have hM : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h3m : (1 : ℝ) ≤ 3 * m := by linarith
  rw [Real.mul_rpow (by linarith) hε]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hε _)
  calc (3 * (m : ℝ)) ^ clB ≤ (3 * (m : ℝ)) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h3m (by rw [clB]; norm_num)
    _ = 3 * m := Real.rpow_one _

/-- **The `d/q` term.** -/
theorem rpow_div_le (d q : ℕ) (hd : 1 ≤ d) :
    ((d : ℝ) / (q : ℝ)) ^ clB ≤ (d : ℝ) * (q : ℝ) ^ (-clB) := by
  have hD : (1 : ℝ) ≤ d := by exact_mod_cast hd
  rw [Real.div_rpow (by linarith) (Nat.cast_nonneg _), Real.rpow_neg (Nat.cast_nonneg _),
    div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  calc (d : ℝ) ^ clB ≤ (d : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hD (by rw [clB]; norm_num)
    _ = d := Real.rpow_one _

/-! ## The prefactor -/

/-- **The prefactor.** `100000 k² m⁴ · 3md ≤ 1.92·10^11 (dm)^11 ≤ a (dm)^a`. -/
theorem prefactor_le (m d : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) :
    100000 * (clK m d : ℝ) ^ 2 * (m : ℝ) ^ 4 * (3 * (m : ℝ) * d)
      ≤ clA * ((d * m : ℕ) : ℝ) ^ clA := by
  have hM : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hD : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hKR : (clK m d : ℝ) ≤ 800 * (m : ℝ) ^ 3 * d := by
    have h := clK_le m d hm hd
    exact_mod_cast h
  have hKnn : (0 : ℝ) ≤ (clK m d : ℝ) := Nat.cast_nonneg _
  have hdm : 1 ≤ d * m := le_trans hd (Nat.le_mul_of_pos_right d hm)
  have hdm1 : (1 : ℝ) ≤ ((d * m : ℕ) : ℝ) := by exact_mod_cast hdm
  have hcast : ((d * m : ℕ) : ℝ) = (d : ℝ) * (m : ℝ) := by push_cast; ring
  have h11 : ((d * m : ℕ) : ℝ) ^ (11 : ℕ) ≤ ((d * m : ℕ) : ℝ) ^ clA := by
    rw [← Real.rpow_natCast (((d * m : ℕ) : ℝ)) 11]
    refine Real.rpow_le_rpow_of_exponent_le hdm1 ?_
    rw [clA]; norm_num
  calc 100000 * (clK m d : ℝ) ^ 2 * (m : ℝ) ^ 4 * (3 * (m : ℝ) * d)
      ≤ 100000 * (800 * (m : ℝ) ^ 3 * d) ^ 2 * (m : ℝ) ^ 4 * (3 * (m : ℝ) * d) := by
        gcongr
    _ = 192000000000 * ((m : ℝ) ^ 11 * (d : ℝ) ^ 3) := by ring
    _ ≤ 192000000000 * ((d : ℝ) * (m : ℝ)) ^ (11 : ℕ) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        have h3 : (d : ℝ) ^ 3 ≤ (d : ℝ) ^ (11 : ℕ) := pow_le_pow_right₀ hD (by norm_num)
        calc (m : ℝ) ^ 11 * (d : ℝ) ^ 3 ≤ (m : ℝ) ^ 11 * (d : ℝ) ^ (11 : ℕ) :=
              mul_le_mul_of_nonneg_left h3 (by positivity)
          _ = ((d : ℝ) * (m : ℝ)) ^ (11 : ℕ) := by ring
    _ = 192000000000 * ((d * m : ℕ) : ℝ) ^ (11 : ℕ) := by rw [hcast]
    _ ≤ clA * ((d * m : ℕ) : ℝ) ^ clA := by
        refine mul_le_mul ?_ h11 (by positivity) (by rw [clA]; norm_num)
        rw [clA]; norm_num

/-! ## The corollary -/

/-- **The parameter corollary.** At `k = clK m d` the canonical-line error on the adapter's
inflated failure `3 m ε` is below the blueprint's `δ_CL` at `ldc = 1`, with the explicit
constants `a = 2·10^11` and `b = 1/40000`. -/
theorem lidtError_le_deltaCL (m d q : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (ε : ℝ) (hε : 0 ≤ ε) :
    lidtError m d q (clK m d) (3 * m * ε) ≤ deltaCL q m d ε := by
  have hM : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hD : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have t1 : (3 * (m : ℝ) * ε) ^ clB ≤ 3 * (m : ℝ) * ε ^ clB := rpow_mul_le m hm ε hε
  have t2 : ((d : ℝ) / (q : ℝ)) ^ clB ≤ (d : ℝ) * (q : ℝ) ^ (-clB) := rpow_div_le d q hd
  have t3 : Real.exp (-(clK m d : ℝ) / (2560000 * (m : ℝ) ^ 2)) ≤ (2 : ℝ) ^ (-(clB * m * d)) :=
    exp_le_two_rpow m d hm
  rw [lidtError, deltaCL, ← clB_eq]
  set E : ℝ := ε ^ clB with hE
  set Q : ℝ := (q : ℝ) ^ (-clB) with hQ
  set T : ℝ := (2 : ℝ) ^ (-(clB * (m : ℝ) * (d : ℝ))) with hT
  have hEnn : (0 : ℝ) ≤ E := by rw [hE]; exact Real.rpow_nonneg hε _
  have hQnn : (0 : ℝ) ≤ Q := by rw [hQ]; exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hTnn : (0 : ℝ) ≤ T := by rw [hT]; exact Real.rpow_nonneg (by norm_num) _
  have hbr : (3 * (m : ℝ) * ε) ^ clB + ((d : ℝ) / (q : ℝ)) ^ clB
        + Real.exp (-(clK m d : ℝ) / (2560000 * (m : ℝ) ^ 2))
      ≤ 3 * (m : ℝ) * (d : ℝ) * (E + Q + T) := by
    have hmd1 : (1 : ℝ) ≤ (m : ℝ) * d := by nlinarith [hM, hD]
    have h1 : 3 * (m : ℝ) * E ≤ 3 * (m : ℝ) * (d : ℝ) * E := by
      nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 3 * (m : ℝ))
        (by linarith : (0:ℝ) ≤ (d : ℝ) - 1)) hEnn]
    have h2 : (d : ℝ) * Q ≤ 3 * (m : ℝ) * (d : ℝ) * Q := by
      nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ (d : ℝ))
        (by linarith : (0:ℝ) ≤ 3 * (m : ℝ) - 1)) hQnn]
    have h3 : T ≤ 3 * (m : ℝ) * (d : ℝ) * T := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 3 * ((m : ℝ) * d) - 1) hTnn]
    calc (3 * (m : ℝ) * ε) ^ clB + ((d : ℝ) / (q : ℝ)) ^ clB
          + Real.exp (-(clK m d : ℝ) / (2560000 * (m : ℝ) ^ 2))
        ≤ 3 * (m : ℝ) * E + (d : ℝ) * Q + T := by linarith [t1, t2, t3]
      _ ≤ 3 * (m : ℝ) * (d : ℝ) * E + 3 * (m : ℝ) * (d : ℝ) * Q
            + 3 * (m : ℝ) * (d : ℝ) * T := by linarith
      _ = 3 * (m : ℝ) * (d : ℝ) * (E + Q + T) := by ring
  have hPnn : (0 : ℝ) ≤ 100000 * (clK m d : ℝ) ^ 2 * (m : ℝ) ^ 4 := by positivity
  have hSnn : (0 : ℝ) ≤ E + Q + T := by linarith
  calc 100000 * (clK m d : ℝ) ^ 2 * (m : ℝ) ^ 4 *
          ((3 * (m : ℝ) * ε) ^ clB + ((d : ℝ) / (q : ℝ)) ^ clB
            + Real.exp (-(clK m d : ℝ) / (2560000 * (m : ℝ) ^ 2)))
      ≤ 100000 * (clK m d : ℝ) ^ 2 * (m : ℝ) ^ 4 * (3 * (m : ℝ) * (d : ℝ) * (E + Q + T)) :=
        mul_le_mul_of_nonneg_left hbr hPnn
    _ = (100000 * (clK m d : ℝ) ^ 2 * (m : ℝ) ^ 4 * (3 * (m : ℝ) * (d : ℝ))) * (E + Q + T) := by
        ring
    _ ≤ (clA * ((d * m : ℕ) : ℝ) ^ clA) * (E + Q + T) :=
        mul_le_mul_of_nonneg_right (prefactor_le m d hm hd) hSnn

end MIPRE.LIDT
