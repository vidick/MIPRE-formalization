/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Tracial/Density/GVec.lean
-/
/-
# The faithful near-vector state of a separable strategy (stage E7.1)

`VN/StandardFormOf.lean` builds the standard form of `(N, φ)` from a *sequence*
`g : ℕ → H` with `∑ ‖gₖ‖² < ∞` and `φ(T) = ∑ₖ ⟪gₖ, T gₖ⟫`. This file produces such
a sequence for the perturbed state of PLAN-density.md §1.3,

    φ = ((1−ε)·ω_ψ + ε·∑ₖ 2^{-k-1} ω_{nv uₖ}) / Z ,

directly in the `∑ₖ ⟪gₖ, · gₖ⟫` shape: `gₖ := √(wₖ/Z) • vₖ` where `w` is the
probability weight `w₀ = 1−ε`, `w_{k+1} = ε 2^{-k-1}`, `v₀ = ψ`, `v_{k+1} = nv uₖ`
and `Z = ∑ₖ wₖ‖vₖ‖²`. Then `∑ₖ ‖gₖ‖² = 1`, the state is faithful as soon as `u`
is dense (`gvecState_faithful`), and it is `2ε/(1−ε)`-close to the vector state of
`ψ` on the unit ball (`norm_gvecState_sub_le`). Proof-side.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Tracial.Density.FaithfulState

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace Density

open scoped InnerProductSpace ComplexOrder

set_option linter.unusedSectionVars false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## The weights -/

/-- The probability weight `w₀ = 1 − ε`, `w_{k+1} = ε·2^{-(k+1)}`. -/
noncomputable def wgt (ε : ℝ) : ℕ → ℝ
  | 0 => 1 - ε
  | (k + 1) => ε * (1 / 2) ^ (k + 1)

theorem wgt_zero (ε : ℝ) : wgt ε 0 = 1 - ε := rfl

theorem wgt_succ (ε : ℝ) (k : ℕ) : wgt ε (k + 1) = ε * (1 / 2) ^ (k + 1) := rfl

theorem wgt_pos {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (k : ℕ) : 0 < wgt ε k := by
  cases k with
  | zero => rw [wgt_zero]; linarith
  | succ k => rw [wgt_succ]; positivity

theorem summable_wgt_succ {ε : ℝ} : Summable fun k : ℕ => wgt ε (k + 1) := by
  have h : Summable fun k : ℕ => ε * (1 / 2 : ℝ) ^ (k + 1) := by
    refine Summable.mul_left ε ?_
    exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective
      (add_left_injective 1)
  exact h

theorem tsum_wgt_succ {ε : ℝ} : ∑' k : ℕ, wgt ε (k + 1) = ε := by
  have h : ∀ k : ℕ, wgt ε (k + 1) = ε * ((1 / 2 : ℝ) * (1 / 2) ^ k) := fun k => by
    rw [wgt_succ, pow_succ]; ring
  rw [tsum_congr h, tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num)
    (by norm_num)]
  norm_num

theorem summable_wgt {ε : ℝ} : Summable (wgt ε) :=
  (summable_nat_add_iff 1).mp summable_wgt_succ

/-! ## The sequence -/

variable (ψ : H) (u : ℕ → H)

/-- The unit-ball sequence `v₀ = ψ`, `v_{k+1} = nv uₖ`. -/
noncomputable def vseq : ℕ → H
  | 0 => ψ
  | (k + 1) => nv u k

theorem vseq_zero : vseq ψ u 0 = ψ := rfl

theorem vseq_succ (k : ℕ) : vseq ψ u (k + 1) = nv u k := rfl

theorem norm_vseq_le (hψ : ‖ψ‖ = 1) (k : ℕ) : ‖vseq ψ u k‖ ≤ 1 := by
  cases k with
  | zero => rw [vseq_zero, hψ]
  | succ k => rw [vseq_succ]; exact norm_nv_le u k

/-- The normalizing constant `Z = ∑ₖ wₖ ‖vₖ‖²`. -/
noncomputable def Zc (ε : ℝ) : ℝ := ∑' k : ℕ, wgt ε k * ‖vseq ψ u k‖ ^ 2

theorem wgt_mul_norm_sq_le (hψ : ‖ψ‖ = 1) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (k : ℕ) :
    wgt ε k * ‖vseq ψ u k‖ ^ 2 ≤ wgt ε k := by
  have h1 : ‖vseq ψ u k‖ ^ 2 ≤ 1 := by
    nlinarith [norm_vseq_le ψ u hψ k, norm_nonneg (vseq ψ u k)]
  nlinarith [(wgt_pos hε0 hε1 k).le, h1]

theorem wgt_mul_norm_sq_nonneg {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (k : ℕ) :
    0 ≤ wgt ε k * ‖vseq ψ u k‖ ^ 2 :=
  mul_nonneg (wgt_pos hε0 hε1 k).le (sq_nonneg _)

theorem summable_wgt_mul_norm_sq (hψ : ‖ψ‖ = 1) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    Summable fun k : ℕ => wgt ε k * ‖vseq ψ u k‖ ^ 2 :=
  Summable.of_nonneg_of_le (wgt_mul_norm_sq_nonneg ψ u hε0 hε1)
    (wgt_mul_norm_sq_le ψ u hψ hε0 hε1) (summable_wgt (ε := ε))

theorem tsum_wgt (ε : ℝ) : ∑' k : ℕ, wgt ε k = 1 := by
  rw [(summable_wgt (ε := ε)).tsum_eq_zero_add, tsum_wgt_succ, wgt_zero]
  ring

theorem Zc_le_one (hψ : ‖ψ‖ = 1) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) : Zc ψ u ε ≤ 1 := by
  have h := Summable.tsum_le_tsum (f := fun k : ℕ => wgt ε k * ‖vseq ψ u k‖ ^ 2)
    (g := fun k : ℕ => wgt ε k) (wgt_mul_norm_sq_le ψ u hψ hε0 hε1)
    (summable_wgt_mul_norm_sq ψ u hψ hε0 hε1) (summable_wgt (ε := ε))
  rw [tsum_wgt ε] at h
  rw [Zc]
  exact h

theorem Zc_ge (hψ : ‖ψ‖ = 1) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) : 1 - ε ≤ Zc ψ u ε := by
  have hsum := summable_wgt_mul_norm_sq ψ u hψ hε0 hε1
  rw [Zc, hsum.tsum_eq_zero_add, wgt_zero, vseq_zero, hψ]
  have h2 : (0 : ℝ) ≤ ∑' k : ℕ, wgt ε (k + 1) * ‖vseq ψ u (k + 1)‖ ^ 2 :=
    tsum_nonneg fun k => wgt_mul_norm_sq_nonneg ψ u hε0 hε1 (k + 1)
  simp only [one_pow, mul_one]
  linarith

theorem Zc_pos (hψ : ‖ψ‖ = 1) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) : 0 < Zc ψ u ε := by
  have := Zc_ge ψ u hψ hε0 hε1
  linarith

/-- The sequence `gₖ = √(wₖ/Z) • vₖ` realizing the perturbed state. -/
noncomputable def gvec (ε : ℝ) (k : ℕ) : H :=
  ((Real.sqrt (wgt ε k / Zc ψ u ε) : ℝ) : ℂ) • vseq ψ u k

theorem norm_gvec_sq (hψ : ‖ψ‖ = 1) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (k : ℕ) :
    ‖gvec ψ u ε k‖ ^ 2 = wgt ε k / Zc ψ u ε * ‖vseq ψ u k‖ ^ 2 := by
  have hq : 0 ≤ wgt ε k / Zc ψ u ε :=
    div_nonneg (wgt_pos hε0 hε1 k).le (Zc_pos ψ u hψ hε0 hε1).le
  rw [gvec, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt hq]

theorem summable_norm_gvec_sq (hψ : ‖ψ‖ = 1) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    Summable fun k : ℕ => ‖gvec ψ u ε k‖ ^ 2 := by
  have h : (fun k : ℕ => ‖gvec ψ u ε k‖ ^ 2)
      = fun k : ℕ => (Zc ψ u ε)⁻¹ * (wgt ε k * ‖vseq ψ u k‖ ^ 2) := by
    funext k
    rw [norm_gvec_sq ψ u hψ hε0 hε1 k]
    field_simp
  rw [h]
  exact (summable_wgt_mul_norm_sq ψ u hψ hε0 hε1).mul_left _

theorem tsum_norm_gvec_sq (hψ : ‖ψ‖ = 1) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∑' k : ℕ, ‖gvec ψ u ε k‖ ^ 2 = 1 := by
  have hZ := Zc_pos ψ u hψ hε0 hε1
  have h : (fun k : ℕ => ‖gvec ψ u ε k‖ ^ 2)
      = fun k : ℕ => (Zc ψ u ε)⁻¹ * (wgt ε k * ‖vseq ψ u k‖ ^ 2) := by
    funext k
    rw [norm_gvec_sq ψ u hψ hε0 hε1 k]
    field_simp
  rw [h, tsum_mul_left, ← Zc]
  field_simp


/-! ## The perturbed state -/

/-- The state `φ(T) = ∑ₖ ⟪gₖ, T gₖ⟫`. -/
noncomputable def gvecState (ε : ℝ) (T : H →L[ℂ] H) : ℂ :=
  ∑' k : ℕ, ⟪gvec ψ u ε k, T (gvec ψ u ε k)⟫_ℂ

theorem norm_inner_gvec_le (ε : ℝ) (T : H →L[ℂ] H) (k : ℕ) :
    ‖⟪gvec ψ u ε k, T (gvec ψ u ε k)⟫_ℂ‖ ≤ ‖T‖ * ‖gvec ψ u ε k‖ ^ 2 := by
  calc ‖⟪gvec ψ u ε k, T (gvec ψ u ε k)⟫_ℂ‖
      ≤ ‖gvec ψ u ε k‖ * ‖T (gvec ψ u ε k)‖ := norm_inner_le_norm _ _
    _ ≤ ‖gvec ψ u ε k‖ * (‖T‖ * ‖gvec ψ u ε k‖) :=
        mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
    _ = ‖T‖ * ‖gvec ψ u ε k‖ ^ 2 := by ring

theorem summable_inner_gvec (hψ : ‖ψ‖ = 1) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (T : H →L[ℂ] H) : Summable fun k : ℕ => ⟪gvec ψ u ε k, T (gvec ψ u ε k)⟫_ℂ := by
  refine Summable.of_norm_bounded (g := fun k => ‖T‖ * ‖gvec ψ u ε k‖ ^ 2)
    ((summable_norm_gvec_sq ψ u hψ hε0 hε1).mul_left _) fun k => ?_
  exact norm_inner_gvec_le ψ u ε T k

theorem inner_gvec_self (ε : ℝ) (k : ℕ) :
    ⟪gvec ψ u ε k, (1 : H →L[ℂ] H) (gvec ψ u ε k)⟫_ℂ = ((‖gvec ψ u ε k‖ ^ 2 : ℝ) : ℂ) := by
  rw [one_apply_eq_self, inner_self_eq_norm_sq_to_K]
  norm_cast

theorem gvecState_one (hψ : ‖ψ‖ = 1) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    gvecState ψ u ε 1 = 1 := by
  rw [gvecState, tsum_congr fun k => inner_gvec_self ψ u ε k, ← Complex.ofReal_tsum,
    tsum_norm_gvec_sq ψ u hψ hε0 hε1, Complex.ofReal_one]

/-! ### Faithfulness -/

theorem inner_gvec_star_mul_self (ε : ℝ) (T : H →L[ℂ] H) (k : ℕ) :
    ⟪gvec ψ u ε k, (star T * T) (gvec ψ u ε k)⟫_ℂ = ((‖T (gvec ψ u ε k)‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast

theorem gvec_ne_zero_smul {ε : ℝ} (hψ : ‖ψ‖ = 1) (hε0 : 0 < ε) (hε1 : ε < 1) (k : ℕ)
    (T : H →L[ℂ] H) (h : T (gvec ψ u ε k) = 0) : T (vseq ψ u k) = 0 := by
  have hq : 0 < wgt ε k / Zc ψ u ε :=
    div_pos (wgt_pos hε0 hε1 k) (Zc_pos ψ u hψ hε0 hε1)
  have hs : Real.sqrt (wgt ε k / Zc ψ u ε) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.mpr hq)
  rw [gvec, map_smul, smul_eq_zero] at h
  rcases h with h | h
  · exact absurd (Complex.ofReal_eq_zero.mp h) hs
  · exact h

theorem gvecState_faithful (hψ : ‖ψ‖ = 1) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hu : DenseRange u) (T : H →L[ℂ] H) (h : gvecState ψ u ε (star T * T) = 0) : T = 0 := by
  have hsummR : Summable fun k : ℕ => ‖T (gvec ψ u ε k)‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      ((summable_norm_gvec_sq ψ u hψ hε0 hε1).mul_left (‖T‖ ^ 2))
    calc ‖T (gvec ψ u ε k)‖ ^ 2 ≤ (‖T‖ * ‖gvec ψ u ε k‖) ^ 2 := by
          refine pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm _) 2
      _ = ‖T‖ ^ 2 * ‖gvec ψ u ε k‖ ^ 2 := by ring
  have h0 : ∑' k : ℕ, ‖T (gvec ψ u ε k)‖ ^ 2 = 0 := by
    have he : gvecState ψ u ε (star T * T)
        = ((∑' k : ℕ, ‖T (gvec ψ u ε k)‖ ^ 2 : ℝ) : ℂ) := by
      rw [gvecState, tsum_congr fun k => inner_gvec_star_mul_self ψ u ε T k,
        ← Complex.ofReal_tsum]
    rw [he] at h
    exact Complex.ofReal_eq_zero.mp h
  have hzero : ∀ k, T (gvec ψ u ε k) = 0 := by
    intro k
    have hle := hsummR.le_tsum k fun j _ => sq_nonneg _
    rw [h0] at hle
    have : ‖T (gvec ψ u ε k)‖ ^ 2 = 0 := le_antisymm hle (sq_nonneg _)
    rw [pow_eq_zero_iff two_ne_zero, norm_eq_zero] at this
    exact this
  have hvz : ∀ k, T (vseq ψ u k) = 0 := fun k =>
    gvec_ne_zero_smul ψ u hψ hε0 hε1 k T (hzero k)
  have huz : ∀ k, T (u k) = 0 := fun k => by
    have := hvz (k + 1)
    rw [vseq_succ] at this
    exact (map_nv_eq_zero_iff u T k).mp this
  have hc : (T : H → H) = (0 : H →L[ℂ] H) :=
    hu.equalizer T.continuous (0 : H →L[ℂ] H).continuous (funext fun k => by simp [huz k])
  exact DFunLike.coe_injective hc

/-! ### Closeness to the vector state of `ψ` -/

theorem tsum_norm_gvec_sq_succ (hψ : ‖ψ‖ = 1) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∑' k : ℕ, ‖gvec ψ u ε (k + 1)‖ ^ 2 = 1 - (1 - ε) / Zc ψ u ε := by
  have hsum := summable_norm_gvec_sq ψ u hψ hε0 hε1
  have h0 : ‖gvec ψ u ε 0‖ ^ 2 = (1 - ε) / Zc ψ u ε := by
    rw [norm_gvec_sq ψ u hψ hε0 hε1 0, wgt_zero, vseq_zero, hψ]
    ring
  have := hsum.tsum_eq_zero_add
  rw [tsum_norm_gvec_sq ψ u hψ hε0 hε1, h0] at this
  linarith [this]

theorem tsum_norm_gvec_sq_succ_le (hψ : ‖ψ‖ = 1) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∑' k : ℕ, ‖gvec ψ u ε (k + 1)‖ ^ 2 ≤ ε / (1 - ε) := by
  have hZ := Zc_pos ψ u hψ hε0 hε1
  have hZ1 := Zc_le_one ψ u hψ hε0 hε1
  have hε' : (0 : ℝ) < 1 - ε := by linarith
  rw [tsum_norm_gvec_sq_succ ψ u hψ hε0 hε1]
  have h1 : (1 - ε) ≤ (1 - ε) / Zc ψ u ε := by
    rw [le_div_iff₀ hZ]; nlinarith
  have h2 : ε ≤ ε / (1 - ε) := by
    rw [le_div_iff₀ hε']; nlinarith
  linarith

/-- **The perturbed state is `2ε/(1−ε)`-close to the vector state of `ψ`** on the unit
ball of `B(H)`. -/
theorem norm_gvecState_sub_le (hψ : ‖ψ‖ = 1) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (T : H →L[ℂ] H) :
    ‖gvecState ψ u ε T - ⟪ψ, T ψ⟫_ℂ‖ ≤ 2 * ε * ‖T‖ / (1 - ε) := by
  have hZ := Zc_pos ψ u hψ hε0 hε1
  have hZ2 := Zc_ge ψ u hψ hε0 hε1
  have hε' : (0 : ℝ) < 1 - ε := by linarith
  have hsumI := summable_inner_gvec ψ u hψ hε0 hε1 T
  have hsumN := summable_norm_gvec_sq ψ u hψ hε0 hε1
  have hq : (1 - ε) / Zc ψ u ε ≤ 1 := by
    rw [div_le_one hZ]; linarith
  have hq0 : 0 ≤ (1 - ε) / Zc ψ u ε := div_nonneg hε'.le hZ.le
  -- the head term
  have hhead : ⟪gvec ψ u ε 0, T (gvec ψ u ε 0)⟫_ℂ
      = (((1 - ε) / Zc ψ u ε : ℝ) : ℂ) * ⟪ψ, T ψ⟫_ℂ := by
    rw [gvec, vseq_zero, wgt_zero, map_smul, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt hq0]
  -- the split
  have hsplit : gvecState ψ u ε T - ⟪ψ, T ψ⟫_ℂ
      = ((((1 - ε) / Zc ψ u ε - 1 : ℝ)) : ℂ) * ⟪ψ, T ψ⟫_ℂ
        + ∑' k : ℕ, ⟪gvec ψ u ε (k + 1), T (gvec ψ u ε (k + 1))⟫_ℂ := by
    rw [gvecState, hsumI.tsum_eq_zero_add, hhead]
    push_cast
    ring
  -- the two bounds
  have h2 : ‖⟪ψ, T ψ⟫_ℂ‖ ≤ ‖T‖ := by
    have hb := norm_inner_le_norm (𝕜 := ℂ) ψ (T ψ)
    have hc : ‖T ψ‖ ≤ ‖T‖ := by simpa [hψ] using T.le_opNorm ψ
    rw [hψ, one_mul] at hb
    exact hb.trans hc
  have h3 : 1 - (1 - ε) / Zc ψ u ε ≤ ε / (1 - ε) := by
    rw [← tsum_norm_gvec_sq_succ ψ u hψ hε0 hε1]
    exact tsum_norm_gvec_sq_succ_le ψ u hψ hε0 hε1
  have hb1 : ‖((((1 - ε) / Zc ψ u ε - 1 : ℝ)) : ℂ) * ⟪ψ, T ψ⟫_ℂ‖ ≤ ε / (1 - ε) * ‖T‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |(1 - ε) / Zc ψ u ε - 1| = 1 - (1 - ε) / Zc ψ u ε := by
      rw [abs_of_nonpos (by linarith)]; ring
    rw [h1]
    exact mul_le_mul h3 h2 (norm_nonneg _) (div_nonneg hε0.le hε'.le)
  have hb2 : ‖∑' k : ℕ, ⟪gvec ψ u ε (k + 1), T (gvec ψ u ε (k + 1))⟫_ℂ‖
      ≤ ‖T‖ * (ε / (1 - ε)) := by
    have hs2 : Summable fun k : ℕ => ‖T‖ * ‖gvec ψ u ε (k + 1)‖ ^ 2 :=
      ((summable_nat_add_iff 1).mpr hsumN).mul_left _
    have hbd : ‖∑' k : ℕ, ⟪gvec ψ u ε (k + 1), T (gvec ψ u ε (k + 1))⟫_ℂ‖
        ≤ ∑' k : ℕ, ‖T‖ * ‖gvec ψ u ε (k + 1)‖ ^ 2 :=
      tsum_of_norm_bounded hs2.hasSum fun k => norm_inner_gvec_le ψ u ε T (k + 1)
    refine hbd.trans ?_
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (tsum_norm_gvec_sq_succ_le ψ u hψ hε0 hε1) (norm_nonneg _)
  rw [hsplit]
  have hfin : ε / (1 - ε) * ‖T‖ + ‖T‖ * (ε / (1 - ε)) = 2 * ε * ‖T‖ / (1 - ε) := by
    field_simp
    ring
  refine (norm_add_le _ _).trans ?_
  rw [← hfin]
  exact add_le_add hb1 hb2

end Density

end CommutingRepetition
