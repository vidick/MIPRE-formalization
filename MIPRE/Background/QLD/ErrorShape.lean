/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.SwapItemOne
import MIPRE.Background.QLD.PaddedLIDT

/-!
# The error shape of `thm:qld`

Blueprint `thm:qld` states its error in one closed form,

`δ_qld(ε, m, d, q) = a (md)^a (ε^b + q^{-b} + 2^{-bmd})`, for universal constants `a ≥ 1`,
`0 < b < 1`.

The proof produces something else: a chain of explicit errors, each a polynomial with square
roots in the one before it. `deltaQ` (`lem:qld-combined-points`) feeds `kappaPairs` and
`deltaPairsD`, which feed `deltaPairs` (`lem:qld-pairs-of-lines`, at the collision probability
`md/q + 1/q`), which feeds `deltaGS` (`lem:qld-global-success`); the seeded soundness theorem turns
that into `deltaLD = deltaCL q (4m) d deltaGS`; `deltaS` (`lem:qld-simultaneous`) and
`deltaSelfCons` (`lem:qld-pauli-selfcons`) follow; and item 1 of `lem:qld-swap`
(`MirrorSimul.exists_aux_close`) ends in `2 - 2 √(1 - η)` with `η = 2 √X + 2 X`. This file shows
every link is of the blueprint's form. It does so with a closure calculus rather than by bounding
the composite in one go, so that item 2's bound, built from the same operations, joins the class
by the same combinators.

## The class

`ErrSmall f` says that there are `a ≥ 1` and `0 < b < 1` with
`0 ≤ f ε m d q ≤ errShape a b ε m d q` at every tuple with `0 ≤ ε ≤ 1`, `m, d ≥ 1`, `q ≥ 2`. The
constants are quantified *first*: they may not depend on the parameters, which is what "universal"
means in the blueprint. The range costs nothing. `q ≥ 2` because `q = |F|`, and `ε ≤ 1` because a
failure probability above one may be read as one, the shape being monotone in `ε`
(`ErrSmall.exists_le_min_one`).

## Why it is closed

Write `S_b = ε^b + q^{-b} + 2^{-bmd}` (`errSum`). Three facts do all the work.

* On the range `S_b` is antitone in `b`, since `ε ≤ 1 ≤ q`, and `(md)^a` is monotone in `a`, since
  `md ≥ 1`. So two errors with different constants are both below the shape at the larger `a` and
  the smaller `b`: sums, nonnegative constant multiples and polynomial prefactors `(md)^r`.
* `t ↦ t^B` is subadditive for `0 < B ≤ 1` (`Real.rpow_add_le_add_rpow`), while `a^B ≤ a` and
  `((md)^a)^B ≤ (md)^a`; so `(a (md)^a S_b)^B ≤ a (md)^a S_{bB}`. Square roots are `B = 1/2`.
  This is the only operation that shrinks the exponent, and the chain applies it a fixed finite
  number of times, which is why `b` stays universal.
* Each term of `S_b` is at most one on the range, so `S_b ≤ 3` and `S_b · S_b ≤ 3 S_b`: products.

What is *not* in the class is a positive constant (`not_errSmall_one`, which also guards the
definition against being vacuous): at fixed `m, d` the shape tends to `a (md)^a 2^{-bmd}` as
`q → ∞` and `ε → 0`, and that tends to zero with `md`. So every constant in the chain has to arrive
multiplied by something small, and it does: `2/q`, `(md + 1)/q`.

## The base cases

`ε`, since `ε ≤ ε^{1/2}` on `[0, 1]`; `q^{-B}` and `2^{-Bmd}` for each `B > 0`; and
`md/q = (md) q^{-1}`. The seeded soundness theorem enters through `ErrSmall.deltaCL_comp`: at
`(q, 4m, d)` its error is `A (4md)^A (x^B + q^{-B} + 2^{-4Bmd})` with `A = clA`, `B = clB`, and
`(4md)^A = 4^A (md)^A`, `2^{-4Bmd} ≤ 2^{-Bmd}`, so it is small whenever `x` is. This is the
absorption `lidtError_le_deltaCL` performs for the canonical-line error, run once more.
`MIPRE/Foundations/Introspection/ErrorBounds.lean` does the same kind of normalization for the
introspection error, whose shape `a (x^a ε^b + x^{-b})` has no `2^{-bmd}` term.

## Item 1, and the trivial bound

`2 - 2 √(1 - η) ≤ 2 η` for every `η ≥ 0` (`two_sub_two_sqrt_one_sub`): for `η ≤ 1` because
`√t ≥ t` on `[0, 1]`, and for `η > 1` because `Real.sqrt` of a negative number is `0`. So item 1's
bound is small as soon as `η` is (`errSmall_swapItemOne`), and that holds whether or not item 1's
hypothesis `η < 1` does.

Where that hypothesis, or the regime `48 m d ≤ q`, fails, `thm:qld` takes the trivial bound.
`ErrSmall.of_cases` and `ErrSmall.of_regime` say that this is free: a bounded error that is small
wherever a small quantity `g` is below one is small, since `C ≤ C g` where it is not; and outside
`k m d ≤ q` the small quantity `k md/q` exceeds one.
-/

noncomputable section

namespace MIPRE.QLD

open MIPRE.LIDT

/-! ## The shape -/

/-- **The shape of `δ_qld`** (blueprint `thm:qld`): `a (md)^a (ε^b + q^{-b} + 2^{-bmd})`. -/
def errShape (a b ε : ℝ) (m d q : ℕ) : ℝ :=
  a * ((m : ℝ) * d) ^ a * (ε ^ b + (q : ℝ) ^ (-b) + (2 : ℝ) ^ (-(b * m * d)))

/-- **An error of the shape of `thm:qld`.** There are universal constants `a ≥ 1` and
`0 < b < 1` such that, at every parameter tuple with `0 ≤ ε ≤ 1`, `m, d ≥ 1` and `q ≥ 2`, the
error is nonnegative and at most `errShape a b ε m d q`. The constants come first: they may not
depend on `ε`, `m`, `d` or `q`. -/
def ErrSmall (f : ℝ → ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧ ∀ (ε : ℝ) (m d q : ℕ), 0 ≤ ε → ε ≤ 1 → 1 ≤ m → 1 ≤ d →
    2 ≤ q → 0 ≤ f ε m d q ∧ f ε m d q ≤ errShape a b ε m d q

/-- The bracket of the shape. -/
def errSum (b ε : ℝ) (m d q : ℕ) : ℝ :=
  ε ^ b + (q : ℝ) ^ (-b) + (2 : ℝ) ^ (-(b * m * d))

theorem errShape_eq (a b ε : ℝ) (m d q : ℕ) :
    errShape a b ε m d q = a * ((m : ℝ) * d) ^ a * errSum b ε m d q := rfl

section Terms

variable {ε : ℝ} {m d q : ℕ}

theorem errSum_nonneg (b : ℝ) (hε : 0 ≤ ε) (m d q : ℕ) : 0 ≤ errSum b ε m d q := by
  unfold errSum
  positivity

theorem one_le_md_real (hm : 1 ≤ m) (hd : 1 ≤ d) : (1 : ℝ) ≤ (m : ℝ) * d := by
  have hM : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hD : (1 : ℝ) ≤ d := by exact_mod_cast hd
  nlinarith

theorem one_le_q_real (hq : 2 ≤ q) : (1 : ℝ) ≤ q := by
  have : (2 : ℝ) ≤ q := by exact_mod_cast hq
  linarith

/-- **A smaller exponent makes every term larger**, since `ε ≤ 1 ≤ q` and `2 > 1`. -/
theorem errSum_anti {b b' : ℝ} (hb' : 0 < b') (hbb : b' ≤ b) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hq : 1 ≤ (q : ℝ)) : errSum b ε m d q ≤ errSum b' ε m d q := by
  unfold errSum
  have hmd : 0 ≤ (m : ℝ) * d := by positivity
  have h1 : ε ^ b ≤ ε ^ b' := Real.rpow_le_rpow_of_exponent_ge' hε0 hε1 hb'.le hbb
  have h2 : (q : ℝ) ^ (-b) ≤ (q : ℝ) ^ (-b') :=
    Real.rpow_le_rpow_of_exponent_le hq (by linarith)
  have h3 : (2 : ℝ) ^ (-(b * m * d)) ≤ (2 : ℝ) ^ (-(b' * m * d)) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have : b' * m * d ≤ b * m * d := by
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right hbb hmd
    linarith
  linarith

/-- **Each of the three terms is at most one**, so the bracket is at most three. -/
theorem errSum_le_three {b : ℝ} (hb : 0 ≤ b) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hq : 1 ≤ (q : ℝ)) :
    errSum b ε m d q ≤ 3 := by
  unfold errSum
  have h1 : ε ^ b ≤ 1 := Real.rpow_le_one hε0 hε1 hb
  have h2 : (q : ℝ) ^ (-b) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hq (by linarith)
  have hbmd : 0 ≤ b * m * d := by positivity
  have h3 : (2 : ℝ) ^ (-(b * m * d)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  linarith

/-- **A power `t ↦ t^B`, `0 ≤ B ≤ 1`, of the bracket is below the bracket at exponent `bB`**:
`t ↦ t^B` is subadditive. -/
theorem errSum_rpow_le {b B : ℝ} (hB0 : 0 ≤ B) (hB1 : B ≤ 1) (hε0 : 0 ≤ ε) :
    (errSum b ε m d q) ^ B ≤ errSum (b * B) ε m d q := by
  unfold errSum
  have hx : 0 ≤ ε ^ b := Real.rpow_nonneg hε0 _
  have hy : 0 ≤ (q : ℝ) ^ (-b) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hz : 0 ≤ (2 : ℝ) ^ (-(b * m * d)) := Real.rpow_nonneg (by norm_num) _
  calc (ε ^ b + (q : ℝ) ^ (-b) + (2 : ℝ) ^ (-(b * m * d))) ^ B
      ≤ (ε ^ b + (q : ℝ) ^ (-b)) ^ B + ((2 : ℝ) ^ (-(b * m * d))) ^ B :=
        Real.rpow_add_le_add_rpow (add_nonneg hx hy) hz hB0 hB1
    _ ≤ (ε ^ b) ^ B + ((q : ℝ) ^ (-b)) ^ B + ((2 : ℝ) ^ (-(b * m * d))) ^ B := by
        have := Real.rpow_add_le_add_rpow hx hy hB0 hB1
        linarith
    _ = ε ^ (b * B) + (q : ℝ) ^ (-(b * B)) + (2 : ℝ) ^ (-(b * B * m * d)) := by
        rw [← Real.rpow_mul hε0, ← Real.rpow_mul (Nat.cast_nonneg _),
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
          show -b * B = -(b * B) by ring, show -(b * m * d) * B = -(b * B * m * d) by ring]

end Terms

/-! ## The shape is closed under the operations the chain uses -/

section Shape

variable {ε : ℝ} {m d q : ℕ}

theorem errShape_nonneg {a b : ℝ} (ha : 0 ≤ a) (hε : 0 ≤ ε) : 0 ≤ errShape a b ε m d q := by
  rw [errShape_eq]
  have := errSum_nonneg b hε m d q
  positivity

theorem md_rpow_mono (hmd : 1 ≤ (m : ℝ) * d) {r r' : ℝ} (h : r ≤ r') :
    ((m : ℝ) * d) ^ r ≤ ((m : ℝ) * d) ^ r' :=
  Real.rpow_le_rpow_of_exponent_le hmd h

theorem one_le_md_rpow (hmd : 1 ≤ (m : ℝ) * d) {r : ℝ} (hr : 0 ≤ r) :
    1 ≤ ((m : ℝ) * d) ^ r :=
  Real.one_le_rpow hmd hr

/-- **The bracket alone is of the shape**, for any `a ≥ 1`. -/
theorem errSum_le_errShape {a b : ℝ} (ha : 1 ≤ a) (hε : 0 ≤ ε) (hmd : 1 ≤ (m : ℝ) * d) :
    errSum b ε m d q ≤ errShape a b ε m d q := by
  rw [errShape_eq]
  have h1 := one_le_md_rpow hmd (by linarith : (0 : ℝ) ≤ a)
  have hS := errSum_nonneg b hε m d q
  have : 1 ≤ a * ((m : ℝ) * d) ^ a := by nlinarith
  nlinarith

/-- **Weakening the constants**: a larger `a` and a smaller `b` give a larger shape. -/
theorem errShape_mono {a a' b b' : ℝ} (ha : 1 ≤ a) (haa : a ≤ a') (hb' : 0 < b') (hbb : b' ≤ b)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hmd : 1 ≤ (m : ℝ) * d) (hq : 1 ≤ (q : ℝ)) :
    errShape a b ε m d q ≤ errShape a' b' ε m d q := by
  rw [errShape_eq, errShape_eq]
  have h1 := md_rpow_mono hmd haa
  have h2 := errSum_anti (m := m) (d := d) hb' hbb hε0 hε1 hq
  have hX := one_le_md_rpow hmd (by linarith : (0 : ℝ) ≤ a)
  have hS := errSum_nonneg b hε0 m d q
  exact mul_le_mul (mul_le_mul haa h1 (by linarith) (by linarith)) h2 hS
    (mul_nonneg (by linarith) (by linarith))

/-- **Sums.** -/
theorem errShape_add {a₁ a₂ b₁ b₂ : ℝ} (ha₁ : 1 ≤ a₁) (ha₂ : 1 ≤ a₂) (hb₁ : 0 < b₁)
    (hb₂ : 0 < b₂) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hmd : 1 ≤ (m : ℝ) * d) (hq : 1 ≤ (q : ℝ)) :
    errShape a₁ b₁ ε m d q + errShape a₂ b₂ ε m d q
      ≤ errShape (a₁ + a₂) (min b₁ b₂) ε m d q := by
  have hb : 0 < min b₁ b₂ := lt_min hb₁ hb₂
  have S1 := errSum_anti (m := m) (d := d) hb (min_le_left _ _) hε0 hε1 hq
  have S2 := errSum_anti (m := m) (d := d) hb (min_le_right _ _) hε0 hε1 hq
  have X1 := md_rpow_mono hmd (show a₁ ≤ a₁ + a₂ by linarith)
  have X2 := md_rpow_mono hmd (show a₂ ≤ a₁ + a₂ by linarith)
  have hS1 := errSum_nonneg b₁ hε0 m d q
  have hS2 := errSum_nonneg b₂ hε0 m d q
  have hX1 := one_le_md_rpow hmd (by linarith : (0 : ℝ) ≤ a₁)
  have hX2 := one_le_md_rpow hmd (by linarith : (0 : ℝ) ≤ a₂)
  rw [errShape_eq, errShape_eq, errShape_eq]
  calc a₁ * ((m : ℝ) * d) ^ a₁ * errSum b₁ ε m d q + a₂ * ((m : ℝ) * d) ^ a₂ * errSum b₂ ε m d q
      ≤ a₁ * ((m : ℝ) * d) ^ (a₁ + a₂) * errSum (min b₁ b₂) ε m d q
        + a₂ * ((m : ℝ) * d) ^ (a₁ + a₂) * errSum (min b₁ b₂) ε m d q := by
        gcongr
    _ = (a₁ + a₂) * ((m : ℝ) * d) ^ (a₁ + a₂) * errSum (min b₁ b₂) ε m d q := by ring

/-- **Constant multiples.** -/
theorem errShape_const_mul {a b c : ℝ} (ha : 1 ≤ a) (hc : 0 ≤ c) (hε0 : 0 ≤ ε)
    (hmd : 1 ≤ (m : ℝ) * d) :
    c * errShape a b ε m d q ≤ errShape ((c + 1) * a) b ε m d q := by
  have hS := errSum_nonneg b hε0 m d q
  have X1 := md_rpow_mono hmd (show a ≤ (c + 1) * a by nlinarith)
  have hX := one_le_md_rpow hmd (by linarith : (0 : ℝ) ≤ a)
  rw [errShape_eq, errShape_eq]
  calc c * (a * ((m : ℝ) * d) ^ a * errSum b ε m d q)
      = (c * a) * ((m : ℝ) * d) ^ a * errSum b ε m d q := by ring
    _ ≤ ((c + 1) * a) * ((m : ℝ) * d) ^ ((c + 1) * a) * errSum b ε m d q := by
        have : c * a ≤ (c + 1) * a := by nlinarith
        gcongr

/-- **Polynomial prefactors** `(md)^r`, `r ≥ 0`. -/
theorem mdpow_mul_errShape {a b r : ℝ} (ha : 1 ≤ a) (hr : 0 ≤ r) (hε0 : 0 ≤ ε)
    (hmd : 1 ≤ (m : ℝ) * d) :
    ((m : ℝ) * d) ^ r * errShape a b ε m d q ≤ errShape (a + r) b ε m d q := by
  have hS := errSum_nonneg b hε0 m d q
  have hX := one_le_md_rpow hmd (by linarith : (0 : ℝ) ≤ a + r)
  rw [errShape_eq, errShape_eq]
  calc ((m : ℝ) * d) ^ r * (a * ((m : ℝ) * d) ^ a * errSum b ε m d q)
      = a * ((m : ℝ) * d) ^ (a + r) * errSum b ε m d q := by
        rw [Real.rpow_add (by linarith)]
        ring
    _ ≤ (a + r) * ((m : ℝ) * d) ^ (a + r) * errSum b ε m d q := by
        gcongr
        linarith

/-- **Powers `t ↦ t^B`, `0 ≤ B ≤ 1`**: the prefactor only shrinks, and the bracket is
subadditive. The exponent becomes `bB`. -/
theorem errShape_rpow_le {a b B : ℝ} (ha : 1 ≤ a) (hB0 : 0 ≤ B) (hB1 : B ≤ 1) (hε0 : 0 ≤ ε)
    (hmd : 1 ≤ (m : ℝ) * d) :
    (errShape a b ε m d q) ^ B ≤ errShape a (b * B) ε m d q := by
  have hS := errSum_nonneg b hε0 m d q
  have hX := one_le_md_rpow hmd (by linarith : (0 : ℝ) ≤ a)
  have hXB : (((m : ℝ) * d) ^ a) ^ B ≤ ((m : ℝ) * d) ^ a := by
    calc (((m : ℝ) * d) ^ a) ^ B ≤ (((m : ℝ) * d) ^ a) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hX hB1
      _ = ((m : ℝ) * d) ^ a := Real.rpow_one _
  have haB : a ^ B ≤ a := by
    calc a ^ B ≤ a ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le ha hB1
      _ = a := Real.rpow_one _
  have hSB := errSum_rpow_le (m := m) (d := d) (q := q) (b := b) hB0 hB1 hε0
  rw [errShape_eq, errShape_eq, Real.mul_rpow (by positivity) hS,
    Real.mul_rpow (by linarith) (by linarith)]
  have h1 : 0 ≤ a ^ B := Real.rpow_nonneg (by linarith) _
  have h2 : 0 ≤ (((m : ℝ) * d) ^ a) ^ B := Real.rpow_nonneg (by linarith) _
  have h3 : 0 ≤ (errSum b ε m d q) ^ B := Real.rpow_nonneg hS _
  gcongr

/-- **Products**: every term of the bracket is at most one, so the product of two brackets is
at most three times the bracket at the smaller exponent. -/
theorem errShape_mul {a₁ a₂ b₁ b₂ : ℝ} (ha₁ : 1 ≤ a₁) (ha₂ : 1 ≤ a₂) (hb₁ : 0 < b₁)
    (hb₂ : 0 < b₂) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hmd : 1 ≤ (m : ℝ) * d) (hq : 1 ≤ (q : ℝ)) :
    errShape a₁ b₁ ε m d q * errShape a₂ b₂ ε m d q
      ≤ errShape (3 * a₁ * a₂) (min b₁ b₂) ε m d q := by
  have hb : 0 < min b₁ b₂ := lt_min hb₁ hb₂
  have S1 := errSum_anti (m := m) (d := d) hb (min_le_left _ _) hε0 hε1 hq
  have S2 := errSum_anti (m := m) (d := d) hb (min_le_right _ _) hε0 hε1 hq
  have S3 := errSum_le_three (m := m) (d := d) hb.le hε0 hε1 hq
  have hS1 := errSum_nonneg b₁ hε0 m d q
  have hS2 := errSum_nonneg b₂ hε0 m d q
  have hS := errSum_nonneg (min b₁ b₂) hε0 m d q
  have hX := one_le_md_rpow hmd (by linarith : (0 : ℝ) ≤ a₁ + a₂)
  have hA : a₁ + a₂ ≤ 3 * a₁ * a₂ := by nlinarith
  have X2 := md_rpow_mono hmd hA
  have hSS : errSum b₁ ε m d q * errSum b₂ ε m d q ≤ 3 * errSum (min b₁ b₂) ε m d q := by
    calc errSum b₁ ε m d q * errSum b₂ ε m d q
        ≤ errSum (min b₁ b₂) ε m d q * errSum (min b₁ b₂) ε m d q := by gcongr
      _ ≤ 3 * errSum (min b₁ b₂) ε m d q := by nlinarith
  rw [errShape_eq, errShape_eq, errShape_eq]
  calc a₁ * ((m : ℝ) * d) ^ a₁ * errSum b₁ ε m d q * (a₂ * ((m : ℝ) * d) ^ a₂ * errSum b₂ ε m d q)
      = (a₁ * a₂) * ((m : ℝ) * d) ^ (a₁ + a₂) * (errSum b₁ ε m d q * errSum b₂ ε m d q) := by
        rw [Real.rpow_add (by linarith)]
        ring
    _ ≤ (a₁ * a₂) * ((m : ℝ) * d) ^ (a₁ + a₂) * (3 * errSum (min b₁ b₂) ε m d q) := by
        have : 0 ≤ a₁ * a₂ := by nlinarith
        gcongr
    _ = (3 * a₁ * a₂) * ((m : ℝ) * d) ^ (a₁ + a₂) * errSum (min b₁ b₂) ε m d q := by ring
    _ ≤ (3 * a₁ * a₂) * ((m : ℝ) * d) ^ (3 * a₁ * a₂) * errSum (min b₁ b₂) ε m d q := by
        have : 0 ≤ 3 * a₁ * a₂ := by nlinarith
        gcongr

end Shape

/-! ## The class `ErrSmall` and its closure -/

namespace ErrSmall

variable {f g : ℝ → ℕ → ℕ → ℕ → ℝ}

/-- **Monotonicity**: a nonnegative error below a small one is small. -/
theorem mono (hg : ErrSmall g)
    (h : ∀ (ε : ℝ) (m d q : ℕ), 0 ≤ ε → ε ≤ 1 → 1 ≤ m → 1 ≤ d → 2 ≤ q →
      0 ≤ f ε m d q ∧ f ε m d q ≤ g ε m d q) : ErrSmall f := by
  obtain ⟨a, b, ha, hb0, hb1, hg⟩ := hg
  refine ⟨a, b, ha, hb0, hb1, fun ε m d q hε0 hε1 hm hd hq => ?_⟩
  obtain ⟨h0, h1⟩ := h ε m d q hε0 hε1 hm hd hq
  exact ⟨h0, h1.trans (hg ε m d q hε0 hε1 hm hd hq).2⟩

/-- An error equal to a small one on the parameter range is small. -/
theorem congr (hg : ErrSmall g)
    (h : ∀ (ε : ℝ) (m d q : ℕ), 0 ≤ ε → ε ≤ 1 → 1 ≤ m → 1 ≤ d → 2 ≤ q →
      f ε m d q = g ε m d q) : ErrSmall f := by
  refine hg.mono fun ε m d q hε0 hε1 hm hd hq => ?_
  obtain ⟨a, b, _, _, _, hg⟩ := hg
  rw [h ε m d q hε0 hε1 hm hd hq]
  exact ⟨(hg ε m d q hε0 hε1 hm hd hq).1, le_rfl⟩

/-- A small error is nonnegative on the parameter range. -/
theorem nonneg (hf : ErrSmall f) {ε : ℝ} {m d q : ℕ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hm : 1 ≤ m)
    (hd : 1 ≤ d) (hq : 2 ≤ q) : 0 ≤ f ε m d q := by
  obtain ⟨a, b, _, _, _, hf⟩ := hf
  exact (hf ε m d q hε0 hε1 hm hd hq).1

/-- **Sums.** -/
theorem add (hf : ErrSmall f) (hg : ErrSmall g) :
    ErrSmall fun ε m d q => f ε m d q + g ε m d q := by
  obtain ⟨a₁, b₁, ha₁, hb₁, hb₁', hf⟩ := hf
  obtain ⟨a₂, b₂, ha₂, hb₂, hb₂', hg⟩ := hg
  refine ⟨a₁ + a₂, min b₁ b₂, by linarith, lt_min hb₁ hb₂, (min_le_left _ _).trans_lt hb₁',
    fun ε m d q hε0 hε1 hm hd hq => ?_⟩
  obtain ⟨hf0, hf1⟩ := hf ε m d q hε0 hε1 hm hd hq
  obtain ⟨hg0, hg1⟩ := hg ε m d q hε0 hε1 hm hd hq
  exact ⟨add_nonneg hf0 hg0, (add_le_add hf1 hg1).trans
    (errShape_add ha₁ ha₂ hb₁ hb₂ hε0 hε1 (one_le_md_real hm hd) (one_le_q_real hq))⟩

/-- **Constant multiples**, by a nonnegative constant. -/
theorem const_mul (hf : ErrSmall f) {c : ℝ} (hc : 0 ≤ c) :
    ErrSmall fun ε m d q => c * f ε m d q := by
  obtain ⟨a, b, ha, hb0, hb1, hf⟩ := hf
  refine ⟨(c + 1) * a, b, by nlinarith, hb0, hb1, fun ε m d q hε0 hε1 hm hd hq => ?_⟩
  obtain ⟨hf0, hf1⟩ := hf ε m d q hε0 hε1 hm hd hq
  exact ⟨mul_nonneg hc hf0, (mul_le_mul_of_nonneg_left hf1 hc).trans
    (errShape_const_mul ha hc hε0 (one_le_md_real hm hd))⟩

/-- **Division** by a nonnegative constant (at `c = 0` the quotient is `0`). -/
theorem div_const (hf : ErrSmall f) {c : ℝ} (hc : 0 ≤ c) :
    ErrSmall fun ε m d q => f ε m d q / c :=
  (hf.const_mul (inv_nonneg.mpr hc)).congr fun ε m d q _ _ _ _ _ => by rw [div_eq_inv_mul]

/-- **Polynomial prefactors** `(md)^r`, `r ≥ 0`. -/
theorem mdpow_mul (hf : ErrSmall f) {r : ℝ} (hr : 0 ≤ r) :
    ErrSmall fun ε m d q => ((m : ℝ) * d) ^ r * f ε m d q := by
  obtain ⟨a, b, ha, hb0, hb1, hf⟩ := hf
  refine ⟨a + r, b, by linarith, hb0, hb1, fun ε m d q hε0 hε1 hm hd hq => ?_⟩
  obtain ⟨hf0, hf1⟩ := hf ε m d q hε0 hε1 hm hd hq
  have hX : 0 ≤ ((m : ℝ) * d) ^ r := Real.rpow_nonneg (by positivity) _
  exact ⟨mul_nonneg hX hf0, (mul_le_mul_of_nonneg_left hf1 hX).trans
    (mdpow_mul_errShape ha hr hε0 (one_le_md_real hm hd))⟩

/-- **The polynomial prefactor `md`.** -/
theorem md_mul (hf : ErrSmall f) : ErrSmall fun ε m d q => (m : ℝ) * d * f ε m d q :=
  (hf.mdpow_mul zero_le_one).congr fun ε m d q _ _ _ _ _ => by rw [Real.rpow_one]

/-- **Powers `t ↦ t^B`, `0 < B ≤ 1`.** The exponent `b` becomes `bB`. -/
theorem rpow (hf : ErrSmall f) {B : ℝ} (hB0 : 0 < B) (hB1 : B ≤ 1) :
    ErrSmall fun ε m d q => f ε m d q ^ B := by
  obtain ⟨a, b, ha, hb0, hb1, hf⟩ := hf
  refine ⟨a, b * B, ha, mul_pos hb0 hB0, by nlinarith, fun ε m d q hε0 hε1 hm hd hq => ?_⟩
  obtain ⟨hf0, hf1⟩ := hf ε m d q hε0 hε1 hm hd hq
  exact ⟨Real.rpow_nonneg hf0 _, (Real.rpow_le_rpow hf0 hf1 hB0.le).trans
    (errShape_rpow_le ha hB0.le hB1 hε0 (one_le_md_real hm hd))⟩

/-- **Square roots.** -/
theorem sqrt (hf : ErrSmall f) : ErrSmall fun ε m d q => Real.sqrt (f ε m d q) :=
  (hf.rpow (B := 1 / 2) (by norm_num) (by norm_num)).congr
    fun ε m d q _ _ _ _ _ => Real.sqrt_eq_rpow _

/-- **Products.** -/
theorem mul (hf : ErrSmall f) (hg : ErrSmall g) :
    ErrSmall fun ε m d q => f ε m d q * g ε m d q := by
  obtain ⟨a₁, b₁, ha₁, hb₁, hb₁', hf⟩ := hf
  obtain ⟨a₂, b₂, ha₂, hb₂, hb₂', hg⟩ := hg
  refine ⟨3 * a₁ * a₂, min b₁ b₂, by nlinarith, lt_min hb₁ hb₂,
    (min_le_left _ _).trans_lt hb₁', fun ε m d q hε0 hε1 hm hd hq => ?_⟩
  obtain ⟨hf0, hf1⟩ := hf ε m d q hε0 hε1 hm hd hq
  obtain ⟨hg0, hg1⟩ := hg ε m d q hε0 hε1 hm hd hq
  exact ⟨mul_nonneg hf0 hg0, (mul_le_mul hf1 hg1 hg0 (errShape_nonneg (by linarith) hε0)).trans
    (errShape_mul ha₁ ha₂ hb₁ hb₂ hε0 hε1 (one_le_md_real hm hd) (one_le_q_real hq))⟩

/-- **The bracket's own terms.** An error below the bracket `ε^b + q^{-b} + 2^{-bmd}` at a fixed
`0 < b < 1` is small, with `a = 1`. -/
theorem of_le_errSum {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    (h : ∀ (ε : ℝ) (m d q : ℕ), 0 ≤ ε → ε ≤ 1 → 1 ≤ m → 1 ≤ d → 2 ≤ q →
      0 ≤ f ε m d q ∧ f ε m d q ≤ errSum b ε m d q) : ErrSmall f := by
  refine ⟨1, b, le_rfl, hb0, hb1, fun ε m d q hε0 hε1 hm hd hq => ?_⟩
  obtain ⟨h0, h1⟩ := h ε m d q hε0 hε1 hm hd hq
  exact ⟨h0, h1.trans (errSum_le_errShape le_rfl hε0 (one_le_md_real hm hd))⟩

end ErrSmall

/-! ## The class is not trivial

A guard on the definition, since everything else rests on it: a positive constant is not small.
At `ε = 0`, `m = 1` the shape is `a d^a (q^{-b} + 2^{-bd})`, and taking first `d` and then `q`
large makes it as small as desired. -/

open Filter Topology in
/-- **The constant `1` is not small.** -/
theorem not_errSmall_one : ¬ ErrSmall fun _ _ _ _ => 1 := by
  rintro ⟨a, b, ha, hb0, -, h⟩
  have hl : 0 < b * Real.log 2 := mul_pos hb0 (Real.log_pos (by norm_num))
  -- first `d`: the polynomial prefactor against the exponential term
  obtain ⟨d, hd1, hd⟩ : ∃ d : ℕ, 1 ≤ d ∧
      a * ((d : ℝ) ^ a * Real.exp (-(b * Real.log 2) * d)) < 1 / 2 := by
    have ht := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero a _ hl).const_mul a).comp
      tendsto_natCast_atTop_atTop
    rw [mul_zero] at ht
    obtain ⟨N, hN⟩ :=
      eventually_atTop.mp (ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
    exact ⟨max N 1, le_max_right _ _, hN _ (le_max_left _ _)⟩
  -- then `q`
  obtain ⟨q, hq2, hq⟩ : ∃ q : ℕ, 2 ≤ q ∧ a * (d : ℝ) ^ a * (q : ℝ) ^ (-b) < 1 / 2 := by
    have ht := ((tendsto_rpow_neg_atTop hb0).const_mul (a * (d : ℝ) ^ a)).comp
      tendsto_natCast_atTop_atTop
    rw [mul_zero] at ht
    obtain ⟨N, hN⟩ :=
      eventually_atTop.mp (ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
    exact ⟨max N 2, le_max_right _ _, hN _ (le_max_left _ _)⟩
  have h1 := (h 0 1 d q le_rfl zero_le_one le_rfl hd1 hq2).2
  have h2 : (2 : ℝ) ^ (-(b * ((1 : ℕ) : ℝ) * d)) = Real.exp (-(b * Real.log 2) * d) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    congr 1
    push_cast
    ring
  rw [errShape, h2, Real.zero_rpow hb0.ne', Nat.cast_one, one_mul] at h1
  have : a * (d : ℝ) ^ a * (0 + (q : ℝ) ^ (-b) + Real.exp (-(b * Real.log 2) * d))
      = a * (d : ℝ) ^ a * (q : ℝ) ^ (-b)
        + a * ((d : ℝ) ^ a * Real.exp (-(b * Real.log 2) * d)) := by
    ring
  linarith

/-! ## The base cases -/

/-- **`ε` is small**: `ε ≤ ε^{1/2}` on `[0, 1]`. -/
theorem errSmall_eps : ErrSmall fun ε _ _ _ => ε := by
  refine ErrSmall.of_le_errSum (b := 1 / 2) (by norm_num) (by norm_num)
    fun ε m d q hε0 hε1 _ _ _ => ⟨hε0, ?_⟩
  have h1 : ε ≤ ε ^ (1 / 2 : ℝ) := by
    calc ε = ε ^ (1 : ℝ) := (Real.rpow_one ε).symm
      _ ≤ ε ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_ge' hε0 hε1 (by norm_num) (by norm_num)
  have h2 : 0 ≤ (q : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h3 : 0 ≤ (2 : ℝ) ^ (-(1 / 2 * (m : ℝ) * d)) := Real.rpow_nonneg (by norm_num) _
  unfold errSum
  linarith

/-- **`√ε` is small.** -/
theorem errSmall_sqrt_eps : ErrSmall fun ε _ _ _ => Real.sqrt ε := errSmall_eps.sqrt

/-- **`q^{-B}` is small** for every `B > 0`. -/
theorem errSmall_q_rpow_neg {B : ℝ} (hB : 0 < B) : ErrSmall fun _ _ _ q => (q : ℝ) ^ (-B) := by
  have hb0 : 0 < min B (1 / 2) := lt_min hB (by norm_num)
  refine ErrSmall.of_le_errSum (b := min B (1 / 2)) hb0 ((min_le_right _ _).trans_lt (by norm_num))
    fun ε m d q hε0 _ _ _ hq => ⟨Real.rpow_nonneg (Nat.cast_nonneg _) _, ?_⟩
  have h1 : (q : ℝ) ^ (-B) ≤ (q : ℝ) ^ (-min B (1 / 2)) :=
    Real.rpow_le_rpow_of_exponent_le (one_le_q_real hq) (by linarith [min_le_left B (1 / 2)])
  have h2 : 0 ≤ ε ^ min B (1 / 2) := Real.rpow_nonneg hε0 _
  have h3 : 0 ≤ (2 : ℝ) ^ (-(min B (1 / 2) * (m : ℝ) * d)) := Real.rpow_nonneg (by norm_num) _
  unfold errSum
  linarith

/-- **`1/q` is small.** -/
theorem errSmall_inv_q : ErrSmall fun _ _ _ q => (q : ℝ)⁻¹ :=
  (errSmall_q_rpow_neg zero_lt_one).congr fun _ _ _ q _ _ _ _ _ => by
    rw [Real.rpow_neg_one]

/-- **`2^{-Bmd}` is small** for every `B > 0`. -/
theorem errSmall_two_rpow_neg {B : ℝ} (hB : 0 < B) :
    ErrSmall fun _ m d _ => (2 : ℝ) ^ (-(B * m * d)) := by
  have hb0 : 0 < min B (1 / 2) := lt_min hB (by norm_num)
  refine ErrSmall.of_le_errSum (b := min B (1 / 2)) hb0 ((min_le_right _ _).trans_lt (by norm_num))
    fun ε m d q hε0 _ _ _ _ => ⟨Real.rpow_nonneg (by norm_num) _, ?_⟩
  have hmd : 0 ≤ (m : ℝ) * d := by positivity
  have h1 : (2 : ℝ) ^ (-(B * m * d)) ≤ (2 : ℝ) ^ (-(min B (1 / 2) * m * d)) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have : min B (1 / 2) * m * d ≤ B * m * d := by
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right (min_le_left _ _) hmd
    linarith
  have h2 : 0 ≤ ε ^ min B (1 / 2) := Real.rpow_nonneg hε0 _
  have h3 : 0 ≤ (q : ℝ) ^ (-min B (1 / 2)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  unfold errSum
  linarith

/-- **`md/q` is small**: the collision probability of an axis-parallel line. -/
theorem errSmall_md_div_q : ErrSmall fun _ m d q => (m : ℝ) * d / q :=
  errSmall_inv_q.md_mul.congr fun _ _ _ _ _ _ _ _ _ => by rw [div_eq_mul_inv]

/-- **`c/q` is small** for every `c ≥ 0`. -/
theorem errSmall_const_div_q {c : ℝ} (hc : 0 ≤ c) : ErrSmall fun _ _ _ q => c / q :=
  (errSmall_inv_q.const_mul hc).congr fun _ _ _ _ _ _ _ _ _ => by rw [div_eq_mul_inv]

namespace ErrSmall

variable {f g : ℝ → ℕ → ℕ → ℕ → ℝ}

/-- **The prefactor `m²`**, which `δ_GS` carries: `m² ≤ (md)²`. -/
theorem m_mul_m_mul (hf : ErrSmall f) : ErrSmall fun ε m d q => (m : ℝ) * m * f ε m d q := by
  refine hf.md_mul.md_mul.mono fun ε m d q hε0 hε1 hm hd hq => ?_
  have hf0 := hf.nonneg hε0 hε1 hm hd hq
  have hM : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hD : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : (m : ℝ) ≤ m * d := by nlinarith
  have h2 : (m : ℝ) * m ≤ m * d * (m * d) := by nlinarith
  refine ⟨by positivity, ?_⟩
  calc (m : ℝ) * m * f ε m d q ≤ m * d * (m * d) * f ε m d q :=
        mul_le_mul_of_nonneg_right h2 hf0
    _ = m * d * (m * d * f ε m d q) := by ring

end ErrSmall

/-! ## The chain -/

/-- `δ_Q`, the error of `lem:qld-combined-points`. -/
theorem errSmall_deltaQ : ErrSmall fun ε _ _ _ => deltaQ ε := by
  unfold deltaQ
  exact (((errSmall_eps.const_mul (by norm_num)).sqrt.const_mul (by norm_num)).add
    (errSmall_eps.const_mul (by norm_num)).sqrt).add (errSmall_eps.const_mul (by norm_num))

theorem errSmall_kappaPairs : ErrSmall fun ε _ _ _ => kappaPairs ε := by
  unfold kappaPairs
  exact (errSmall_deltaQ.const_mul (by norm_num)).add (errSmall_eps.const_mul (by norm_num))

theorem errSmall_deltaPairsD : ErrSmall fun ε _ _ _ => deltaPairsD ε := by
  unfold deltaPairsD
  exact ((errSmall_kappaPairs.const_mul (by norm_num)).const_mul (by norm_num)).add
    ((((errSmall_eps.const_mul (by norm_num)).const_mul (by norm_num)).add
      ((errSmall_eps.const_mul (by norm_num)).const_mul (by norm_num))).const_mul (by norm_num))

/-- `δ_P`, the error of `lem:qld-pairs-of-lines`, at any small collision probability. -/
theorem ErrSmall.deltaPairs_comp {g : ℝ → ℕ → ℕ → ℕ → ℝ} (hg : ErrSmall g) :
    ErrSmall fun ε m d q => deltaPairs ε (g ε m d q) := by
  unfold deltaPairs
  have hD := errSmall_deltaPairsD
  exact ((hD.div_const (by norm_num)).add (hD.div_const (by norm_num)).sqrt).add
    (((hD.const_mul (by norm_num)).add
      ((errSmall_eps.const_mul (by norm_num)).sqrt.const_mul (by norm_num))).add
        (hg.const_mul (by norm_num))).sqrt

/-- `δ_GS`, the padded strategy's failure in the seeded test (`lem:qld-global-success`). -/
theorem errSmall_deltaGS : ErrSmall fun ε m d q => deltaGS q m d ε := by
  unfold deltaGS
  have hP : ErrSmall fun ε m d q => deltaPairs ε ((m * d : ℝ) / q + (q : ℝ)⁻¹) :=
    (errSmall_md_div_q.add errSmall_inv_q).deltaPairs_comp
  have hL : ErrSmall fun _ m d q => ((m : ℝ) * d + 1) / q := by
    refine (errSmall_md_div_q.const_mul (c := 2) (by norm_num)).mono
      fun ε m d q hε0 hε1 hm hd hq => ⟨by positivity, ?_⟩
    have hmd := one_le_md_real hm hd
    have hq0 : (0 : ℝ) < q := by linarith [one_le_q_real hq]
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hq0]
    linarith
  exact ((hP.m_mul_m_mul.const_mul (by norm_num)).add
    (errSmall_deltaQ.const_mul (by norm_num))).add hL

/-- **`δ_CL` at `(q, 4m, d)` is of the shape, with `4m` read as `m`**: `(4md)^A = 4^A (md)^A`,
and `2^{-B·4md} ≤ 2^{-Bmd}`. -/
theorem deltaCL_four_mul_le {q m d : ℕ} {x : ℝ} (hx : 0 ≤ x) :
    deltaCL q (4 * m) d x ≤ clA * 4 ^ clA * (((m : ℝ) * d) ^ clA *
      (x ^ clB + (q : ℝ) ^ (-clB) + (2 : ℝ) ^ (-(clB * m * d)))) := by
  have hA : 0 ≤ clA := by linarith [one_le_clA]
  have hB := clB_pos
  have hmd : 0 ≤ (m : ℝ) * d := by positivity
  have hcast : ((d * (4 * m) : ℕ) : ℝ) = 4 * ((m : ℝ) * d) := by push_cast; ring
  have h2 : (2 : ℝ) ^ (-(clB * ((4 * m : ℕ) : ℝ) * d)) ≤ (2 : ℝ) ^ (-(clB * m * d)) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have : clB * (m : ℝ) * d ≤ clB * ((4 * m : ℕ) : ℝ) * d := by
      push_cast
      nlinarith [mul_nonneg hB.le hmd]
    linarith
  have h0 : 0 ≤ x ^ clB + (q : ℝ) ^ (-clB) := by positivity
  unfold deltaCL
  rw [hcast, Real.mul_rpow (by norm_num) hmd]
  calc clA * (4 ^ clA * ((m : ℝ) * d) ^ clA)
        * (x ^ clB + (q : ℝ) ^ (-clB) + (2 : ℝ) ^ (-(clB * ((4 * m : ℕ) : ℝ) * d)))
      ≤ clA * (4 ^ clA * ((m : ℝ) * d) ^ clA)
        * (x ^ clB + (q : ℝ) ^ (-clB) + (2 : ℝ) ^ (-(clB * m * d))) := by gcongr
    _ = clA * 4 ^ clA * (((m : ℝ) * d) ^ clA *
      (x ^ clB + (q : ℝ) ^ (-clB) + (2 : ℝ) ^ (-(clB * m * d)))) := by ring

/-- **The seeded soundness theorem's error at `(q, 4m, d)`, fed a small failure probability, is
small.** -/
theorem ErrSmall.deltaCL_comp {g : ℝ → ℕ → ℕ → ℕ → ℝ} (hg : ErrSmall g) :
    ErrSmall fun ε m d q => deltaCL q (4 * m) d (g ε m d q) := by
  have hA : 0 ≤ clA := by linarith [one_le_clA]
  have hR : ErrSmall fun ε m d q => clA * 4 ^ clA * (((m : ℝ) * d) ^ clA *
      (g ε m d q ^ clB + (q : ℝ) ^ (-clB) + (2 : ℝ) ^ (-(clB * m * d)))) :=
    ((((hg.rpow clB_pos clB_lt_one.le).add (errSmall_q_rpow_neg clB_pos)).add
      (errSmall_two_rpow_neg clB_pos)).mdpow_mul hA).const_mul (by positivity)
  refine hR.mono fun ε m d q hε0 hε1 hm hd hq => ?_
  have hx := hg.nonneg hε0 hε1 hm hd hq
  refine ⟨?_, deltaCL_four_mul_le hx⟩
  unfold deltaCL
  positivity

/-- `δ_ld`, the seeded soundness theorem's error on the padded strategy (`lem:qld-global-pvm`). -/
theorem errSmall_deltaLD : ErrSmall fun ε m d q => deltaLD q m d ε := by
  unfold deltaLD
  exact errSmall_deltaGS.deltaCL_comp

/-- `δ_S`, the error of `lem:qld-simultaneous`, at any small `GlobalPair` error. -/
theorem ErrSmall.deltaS_comp {g : ℝ → ℕ → ℕ → ℕ → ℝ} (hg : ErrSmall g) :
    ErrSmall fun ε m d q => deltaS q (g ε m d q) ε := by
  have hP : ErrSmall fun ε m d q => deltaProd (g ε m d q) ε := by
    unfold deltaProd
    exact (hg.const_mul (by norm_num)).add
      ((errSmall_eps.const_mul (by norm_num)).const_mul (by norm_num))
  unfold deltaS deltaSep
  exact ((hP.sqrt.const_mul (by norm_num)).add (errSmall_const_div_q (by norm_num))).add
    (hP.const_mul (by norm_num))

/-- **`δ_S` of the chain**: the error of the `MirrorSimul` that `exists_mirrorSimul` builds. -/
theorem errSmall_deltaS : ErrSmall fun ε m d q => deltaS q (deltaLD q m d ε) ε :=
  errSmall_deltaLD.deltaS_comp

/-- The constant of `lem:qld-pauli-selfcons`, at any small `MirrorSimul` error. -/
theorem ErrSmall.deltaSelfCons_comp {g : ℝ → ℕ → ℕ → ℕ → ℝ} (hg : ErrSmall g) :
    ErrSmall fun ε m d q => deltaSelfCons (g ε m d q) ε m d q := by
  unfold deltaSelfCons
  exact ((((hg.const_mul (by norm_num)).add (errSmall_eps.const_mul (by norm_num))).add
    ((errSmall_eps.const_mul (by norm_num)).sqrt.const_mul (by norm_num))).add
      errSmall_md_div_q).const_mul (by norm_num)

/-- **The constant of `lem:qld-pauli-selfcons` along the chain.** -/
theorem errSmall_deltaSelfCons :
    ErrSmall fun ε m d q => deltaSelfCons (deltaS q (deltaLD q m d ε) ε) ε m d q :=
  errSmall_deltaS.deltaSelfCons_comp

/-! ## Item 1 of `lem:qld-swap` -/

/-- **`2 - 2 √(1 - η) ≤ 2 η` for every `η ≥ 0`**, and it is nonnegative. For `η ≤ 1` because
`√t ≥ t` on `[0, 1]`; for `η > 1` because `Real.sqrt` of a negative number is `0`. -/
theorem two_sub_two_sqrt_one_sub {η : ℝ} (hη : 0 ≤ η) :
    0 ≤ 2 - 2 * Real.sqrt (1 - η) ∧ 2 - 2 * Real.sqrt (1 - η) ≤ 2 * η := by
  have h1 : Real.sqrt (1 - η) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by rw [Real.sqrt_one]; linarith)
  have h2 : 1 - η ≤ Real.sqrt (1 - η) := by
    rcases le_or_gt (1 - η) 0 with h | h
    · exact h.trans (Real.sqrt_nonneg _)
    · have hs := Real.sq_sqrt h.le
      have hs0 := Real.sqrt_nonneg (1 - η)
      nlinarith
  constructor <;> linarith

/-- **Item 1's bound, at any small constant.** -/
theorem ErrSmall.itemOne_comp {g : ℝ → ℕ → ℕ → ℕ → ℝ} (hg : ErrSmall g) :
    ErrSmall fun ε m d q =>
      2 - 2 * Real.sqrt (1 - (2 * Real.sqrt (g ε m d q) + 2 * g ε m d q)) := by
  have hη : ErrSmall fun ε m d q => 2 * Real.sqrt (g ε m d q) + 2 * g ε m d q :=
    (hg.sqrt.const_mul (by norm_num)).add (hg.const_mul (by norm_num))
  exact (hη.const_mul (c := 2) (by norm_num)).mono fun ε m d q hε0 hε1 hm hd hq =>
    two_sub_two_sqrt_one_sub (hη.nonneg hε0 hε1 hm hd hq)

/-- **The quantity `η = 2 √X + 2 X` item 1 asks to be below one**, at the chain's `X`. -/
theorem errSmall_itemOneEta :
    ErrSmall fun ε m d q =>
      2 * Real.sqrt (deltaSelfCons (deltaS q (deltaLD q m d ε) ε) ε m d q)
        + 2 * deltaSelfCons (deltaS q (deltaLD q m d ε) ε) ε m d q :=
  (errSmall_deltaSelfCons.sqrt.const_mul (by norm_num)).add
    (errSmall_deltaSelfCons.const_mul (by norm_num))

/-- **Item 1 of `lem:qld-swap` has the error shape of `thm:qld`.** The bound
`MirrorSimul.exists_aux_close` gives on `‖endState - aux ⊗ EPR‖²`, at the `MirrorSimul` that
`exists_mirrorSimul` builds, is at most `a (md)^a (ε^b + q^{-b} + 2^{-bmd})` for universal
constants `a ≥ 1` and `0 < b < 1`. -/
theorem errSmall_swapItemOne :
    ErrSmall fun ε m d q =>
      2 - 2 * Real.sqrt (1 - (2 * Real.sqrt (deltaSelfCons (deltaS q (deltaLD q m d ε) ε) ε m d q)
        + 2 * deltaSelfCons (deltaS q (deltaLD q m d ε) ε) ε m d q)) :=
  errSmall_deltaSelfCons.itemOne_comp

/-- **The same for the distance itself**, rather than its square. -/
theorem errSmall_swapItemOne_sqrt :
    ErrSmall fun ε m d q =>
      Real.sqrt (2 - 2 * Real.sqrt (1 - (2 * Real.sqrt
        (deltaSelfCons (deltaS q (deltaLD q m d ε) ε) ε m d q)
          + 2 * deltaSelfCons (deltaS q (deltaLD q m d ε) ε) ε m d q))) :=
  errSmall_swapItemOne.sqrt

/-! ## Trivial bounds outside a regime

Two moves the proof of `thm:qld` makes on top of the chain: outside the regime where the chain
applies it takes the trivial bound, and it reads a failure probability `ε > 1` as `ε = 1`. -/

namespace ErrSmall

variable {f g h : ℝ → ℕ → ℕ → ℕ → ℝ}

/-- **A bounded error that is small wherever a small quantity is below one is small.** Where
`g ≥ 1` the trivial bound `C ≤ C g` is itself small. -/
theorem of_cases (hh : ErrSmall h) (hg : ErrSmall g) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ (ε : ℝ) (m d q : ℕ), 0 ≤ ε → ε ≤ 1 → 1 ≤ m → 1 ≤ d → 2 ≤ q →
      0 ≤ f ε m d q ∧ f ε m d q ≤ C ∧ (g ε m d q < 1 → f ε m d q ≤ h ε m d q)) :
    ErrSmall f := by
  refine (hh.add (hg.const_mul hC)).mono fun ε m d q hε0 hε1 hm hd hq => ?_
  obtain ⟨hf0, hfC, hfh⟩ := hf ε m d q hε0 hε1 hm hd hq
  have hh0 := hh.nonneg hε0 hε1 hm hd hq
  have hg0 := hg.nonneg hε0 hε1 hm hd hq
  refine ⟨hf0, ?_⟩
  rcases lt_or_ge (g ε m d q) 1 with hlt | hge
  · have := hfh hlt
    have : 0 ≤ C * g ε m d q := mul_nonneg hC hg0
    linarith
  · have : C ≤ C * g ε m d q := le_mul_of_one_le_right hC hge
    linarith

/-- **The regime `k m d ≤ q`.** A bounded error that is small wherever `k m d ≤ q` is small:
outside the regime `1 < k m d / q`, which is small. -/
theorem of_regime (hh : ErrSmall h) (k : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ (ε : ℝ) (m d q : ℕ), 0 ≤ ε → ε ≤ 1 → 1 ≤ m → 1 ≤ d → 2 ≤ q →
      0 ≤ f ε m d q ∧ f ε m d q ≤ C ∧ (k * m * d ≤ q → f ε m d q ≤ h ε m d q)) :
    ErrSmall f := by
  refine hh.of_cases (errSmall_md_div_q.const_mul (c := (k : ℝ)) (Nat.cast_nonneg _)) hC
    fun ε m d q hε0 hε1 hm hd hq => ?_
  obtain ⟨hf0, hfC, hfh⟩ := hf ε m d q hε0 hε1 hm hd hq
  refine ⟨hf0, hfC, fun hlt => hfh ?_⟩
  have hq0 : (0 : ℝ) < q := by linarith [one_le_q_real hq]
  rw [← mul_div_assoc, div_lt_one hq0] at hlt
  have : ((k * m * d : ℕ) : ℝ) < q := by push_cast; linarith
  exact_mod_cast this.le

end ErrSmall

/-- **The shape is monotone in `ε`**, so a bound at `min ε 1` is a bound at `ε`. -/
theorem errShape_mono_eps {a b ε ε' : ℝ} {m d q : ℕ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (hεε : ε ≤ ε') : errShape a b ε m d q ≤ errShape a b ε' m d q := by
  rw [errShape_eq, errShape_eq]
  have : ε ^ b ≤ ε' ^ b := Real.rpow_le_rpow hε hεε hb
  have hX : 0 ≤ a * ((m : ℝ) * d) ^ a := by positivity
  unfold errSum
  gcongr

/-- **The bound at every `ε ≥ 0`**: a small error, evaluated at `min ε 1`, is below the shape at
`ε`. A strategy's failure probability is at most one, so `min ε 1` is as good a failure bound as
`ε`. -/
theorem ErrSmall.exists_le_min_one {f : ℝ → ℕ → ℕ → ℕ → ℝ} (hf : ErrSmall f) :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧ ∀ (ε : ℝ) (m d q : ℕ), 0 ≤ ε → 1 ≤ m → 1 ≤ d → 2 ≤ q →
      0 ≤ f (min ε 1) m d q ∧ f (min ε 1) m d q ≤ errShape a b ε m d q := by
  obtain ⟨a, b, ha, hb0, hb1, hf⟩ := hf
  refine ⟨a, b, ha, hb0, hb1, fun ε m d q hε hm hd hq => ?_⟩
  obtain ⟨h0, h1⟩ := hf (min ε 1) m d q (le_min hε zero_le_one) (min_le_right _ _) hm hd hq
  exact ⟨h0, h1.trans (errShape_mono_eps (by linarith) hb0.le (le_min hε zero_le_one)
    (min_le_left _ _))⟩

end MIPRE.QLD
