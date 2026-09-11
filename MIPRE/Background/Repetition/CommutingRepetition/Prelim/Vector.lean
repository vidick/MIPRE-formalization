/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Prelim/Vector.lean
-/
/-
# Abstract vector inequalities (A1 toolkit)

Normed-space inequalities consumed by the prerounding and sampling
sections. This file is infrastructure: the statements are in-proof
displays of the manuscript, not audit nodes.

- `norm_normalize_sub_normalize_sq_le` — 05_prerounding.tex, eq
  prerounding-normalization-inequality: for nonzero vectors,
  `‖v/‖v‖ − w/‖w‖‖² ≤ 4‖v−w‖²/‖v‖²`. Stated with the `ℂ`-coerced
  real scalars used by the candidate layer (`ResolverArena.candidate`).
-/
import Mathlib

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped InnerProductSpace

/-- Difference of normalizations against difference of vectors
(05_prerounding.tex, eq prerounding-normalization-inequality,
linear form): `‖v/‖v‖ − w/‖w‖‖ ≤ 2‖v−w‖/‖v‖`. -/
theorem norm_normalize_sub_normalize_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (v w : E)
    (hv : v ≠ 0) (hw : w ≠ 0) :
    ‖((‖v‖⁻¹ : ℝ) : ℂ) • v - ((‖w‖⁻¹ : ℝ) : ℂ) • w‖
      ≤ 2 * ‖v - w‖ / ‖v‖ := by
  have hv0 : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv
  have hw0 : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  have tri : ‖((‖v‖⁻¹ : ℝ) : ℂ) • v - ((‖w‖⁻¹ : ℝ) : ℂ) • w‖
      ≤ ‖((‖v‖⁻¹ : ℝ) : ℂ) • v - ((‖v‖⁻¹ : ℝ) : ℂ) • w‖ +
        ‖((‖v‖⁻¹ : ℝ) : ℂ) • w - ((‖w‖⁻¹ : ℝ) : ℂ) • w‖ :=
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  have h1 : ‖((‖v‖⁻¹ : ℝ) : ℂ) • v - ((‖v‖⁻¹ : ℝ) : ℂ) • w‖
      = ‖v - w‖ / ‖v‖ := by
    rw [← smul_sub, norm_smul, Complex.norm_real, norm_inv,
      Real.norm_eq_abs, abs_of_pos hv0, inv_mul_eq_div]
  have h2 : ‖((‖v‖⁻¹ : ℝ) : ℂ) • w - ((‖w‖⁻¹ : ℝ) : ℂ) • w‖
      ≤ ‖v - w‖ / ‖v‖ := by
    have hcombine : ((‖v‖⁻¹ : ℝ) : ℂ) • w - ((‖w‖⁻¹ : ℝ) : ℂ) • w
        = (((‖v‖⁻¹ - ‖w‖⁻¹ : ℝ)) : ℂ) • w := by
      rw [Complex.ofReal_sub, sub_smul]
    rw [hcombine, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    have habs : |‖v‖⁻¹ - ‖w‖⁻¹| * ‖w‖ = |‖w‖ - ‖v‖| / ‖v‖ := by
      rw [show ‖v‖⁻¹ - ‖w‖⁻¹ = (‖w‖ - ‖v‖) / (‖v‖ * ‖w‖) by
        field_simp]
      rw [abs_div, abs_of_pos (mul_pos hv0 hw0), div_mul_eq_mul_div,
        mul_comm ‖v‖ ‖w‖, ← div_div,
        mul_div_assoc, div_self (ne_of_gt hw0), mul_one]
    rw [habs]
    have hnn : |‖w‖ - ‖v‖| ≤ ‖v - w‖ := by
      rw [norm_sub_rev]
      exact abs_norm_sub_norm_le w v
    exact div_le_div_of_nonneg_right hnn hv0.le
  calc ‖((‖v‖⁻¹ : ℝ) : ℂ) • v - ((‖w‖⁻¹ : ℝ) : ℂ) • w‖
      ≤ ‖v - w‖ / ‖v‖ + ‖v - w‖ / ‖v‖ := by
        rw [← h1] at *
        exact tri.trans (add_le_add le_rfl h2)
    _ = 2 * ‖v - w‖ / ‖v‖ := by ring

/-- **Normalization inequality** (05_prerounding.tex, eq
prerounding-normalization-inequality): for nonzero vectors,
`‖v/‖v‖ − w/‖w‖‖² ≤ 4·‖v−w‖²/‖v‖²`. -/
theorem norm_normalize_sub_normalize_sq_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (v w : E)
    (hv : v ≠ 0) (hw : w ≠ 0) :
    ‖((‖v‖⁻¹ : ℝ) : ℂ) • v - ((‖w‖⁻¹ : ℝ) : ℂ) • w‖ ^ 2
      ≤ 4 * ‖v - w‖ ^ 2 / ‖v‖ ^ 2 := by
  have hv0 : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv
  have h := norm_normalize_sub_normalize_le v w hv hw
  have hsq : ‖((‖v‖⁻¹ : ℝ) : ℂ) • v - ((‖w‖⁻¹ : ℝ) : ℂ) • w‖ ^ 2
      ≤ (2 * ‖v - w‖ / ‖v‖) ^ 2 := by
    have hnn : (0 : ℝ) ≤ ‖((‖v‖⁻¹ : ℝ) : ℂ) • v - ((‖w‖⁻¹ : ℝ) : ℂ) • w‖ :=
      norm_nonneg _
    exact pow_le_pow_left₀ hnn h 2
  calc ‖((‖v‖⁻¹ : ℝ) : ℂ) • v - ((‖w‖⁻¹ : ℝ) : ℂ) • w‖ ^ 2
      ≤ (2 * ‖v - w‖ / ‖v‖) ^ 2 := hsq
    _ = 4 * ‖v - w‖ ^ 2 / ‖v‖ ^ 2 := by
        rw [div_pow, mul_pow]
        norm_num

/-- **Effect-evaluation Lipschitz bound** (02_preliminaries.tex: "If
`v, w` are unit vectors and `0 ≤ T ≤ 1`, then
`|⟨v,Tv⟩ − ⟨w,Tw⟩| ≤ 2‖v−w‖`"). Stated for the Loewner order on
bounded operators; consumed by the section-6 assembly. -/
theorem abs_re_inner_effect_sub_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (h0 : 0 ≤ T) (h1 : T ≤ 1) (v w : H)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    |(⟪v, T v⟫_ℂ).re - (⟪w, T w⟫_ℂ).re| ≤ 2 * ‖v - w‖ := by
  have hT1 : ‖T‖ ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg T h0).mpr h1
  have hsplit : ⟪v, T v⟫_ℂ - ⟪w, T w⟫_ℂ
      = ⟪v - w, T v⟫_ℂ + ⟪w, T (v - w)⟫_ℂ := by
    rw [inner_sub_left, map_sub, inner_sub_right]
    ring
  have h1' : ‖⟪v - w, T v⟫_ℂ‖ ≤ ‖v - w‖ := by
    calc ‖⟪v - w, T v⟫_ℂ‖ ≤ ‖v - w‖ * ‖T v‖ := norm_inner_le_norm _ _
      _ ≤ ‖v - w‖ * (‖T‖ * ‖v‖) :=
          mul_le_mul_of_nonneg_left (T.le_opNorm v) (norm_nonneg _)
      _ ≤ ‖v - w‖ * 1 := by
          rw [hv, mul_one]
          exact mul_le_mul_of_nonneg_left hT1 (norm_nonneg _)
      _ = ‖v - w‖ := mul_one _
  have h2' : ‖⟪w, T (v - w)⟫_ℂ‖ ≤ ‖v - w‖ := by
    calc ‖⟪w, T (v - w)⟫_ℂ‖ ≤ ‖w‖ * ‖T (v - w)‖ := norm_inner_le_norm _ _
      _ = ‖T (v - w)‖ := by rw [hw, one_mul]
      _ ≤ ‖T‖ * ‖v - w‖ := T.le_opNorm _
      _ ≤ 1 * ‖v - w‖ :=
          mul_le_mul_of_nonneg_right hT1 (norm_nonneg _)
      _ = ‖v - w‖ := one_mul _
  calc |(⟪v, T v⟫_ℂ).re - (⟪w, T w⟫_ℂ).re|
      = |(⟪v, T v⟫_ℂ - ⟪w, T w⟫_ℂ).re| := by rw [Complex.sub_re]
    _ ≤ ‖⟪v, T v⟫_ℂ - ⟪w, T w⟫_ℂ‖ := Complex.abs_re_le_norm _
    _ = ‖⟪v - w, T v⟫_ℂ + ⟪w, T (v - w)⟫_ℂ‖ := by rw [hsplit]
    _ ≤ ‖⟪v - w, T v⟫_ℂ‖ + ‖⟪w, T (v - w)⟫_ℂ‖ := norm_add_le _ _
    _ ≤ ‖v - w‖ + ‖v - w‖ := add_le_add h1' h2'
    _ = 2 * ‖v - w‖ := by ring

/-! ### Cauchy–Schwarz for positive semidefinite forms and the
POVM-output ℓ¹ estimate (06_otqcs.tex, eq vector-to-l1) -/

/-- **Cauchy–Schwarz for the semidefinite form of a positive
self-adjoint operator**: `‖⟪x, T y⟫‖² ≤ re ⟪x, T x⟫ · re ⟪y, T y⟫`.
Proved through `PreInnerProductSpace.Core` (no definiteness needed). -/
theorem abs_inner_positive_form_sq_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (T : H →L[ℂ] H)
    (hsa : ∀ x y : H, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ)
    (hpos : ∀ x : H, 0 ≤ (⟪x, T x⟫_ℂ).re) (x y : H) :
    ‖⟪x, T y⟫_ℂ‖ ^ 2 ≤ (⟪x, T x⟫_ℂ).re * (⟪y, T y⟫_ℂ).re := by
  let c : PreInnerProductSpace.Core ℂ H :=
    { inner := fun u v => ⟪u, T v⟫_ℂ
      conj_inner_symm := fun u v => by
        show (starRingEnd ℂ) ⟪v, T u⟫_ℂ = ⟪u, T v⟫_ℂ
        rw [inner_conj_symm, hsa]
      re_inner_nonneg := hpos
      add_left := fun u v w => by
        show ⟪u + v, T w⟫_ℂ = ⟪u, T w⟫_ℂ + ⟪v, T w⟫_ℂ
        rw [inner_add_left]
      smul_left := fun u v r => by
        show ⟪r • u, T v⟫_ℂ = (starRingEnd ℂ) r * ⟪u, T v⟫_ℂ
        rw [inner_smul_left] }
  have h := InnerProductSpace.Core.inner_mul_inner_self_le
    (c := c) x y
  have hsymm : ‖(c.inner y x : ℂ)‖ = ‖(c.inner x y : ℂ)‖ := by
    rw [← c.conj_inner_symm y x]
    exact RCLike.norm_conj _
  show ‖(c.inner x y : ℂ)‖ ^ 2 ≤ RCLike.re (c.inner x x : ℂ) *
    RCLike.re (c.inner y y : ℂ)
  calc ‖(c.inner x y : ℂ)‖ ^ 2
      = ‖(c.inner x y : ℂ)‖ * ‖(c.inner y x : ℂ)‖ := by
        rw [hsymm, sq]
    _ ≤ _ := h


/-- Square-root form of the positive-form Cauchy–Schwarz. -/
theorem abs_inner_positive_form_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (T : H →L[ℂ] H)
    (hsa : ∀ x y : H, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ)
    (hpos : ∀ x : H, 0 ≤ (⟪x, T x⟫_ℂ).re) (x y : H) :
    ‖⟪x, T y⟫_ℂ‖ ≤
      Real.sqrt (⟪x, T x⟫_ℂ).re * Real.sqrt (⟪y, T y⟫_ℂ).re := by
  have h := abs_inner_positive_form_sq_le T hsa hpos x y
  have h1 : ‖⟪x, T y⟫_ℂ‖ = Real.sqrt (‖⟪x, T y⟫_ℂ‖ ^ 2) := by
    rw [Real.sqrt_sq (norm_nonneg _)]
  rw [h1, ← Real.sqrt_mul (hpos x)]
  exact Real.sqrt_le_sqrt h

/-- **POVM-output ℓ¹ estimate** (06_otqcs.tex, eq vector-to-l1,
consumed form): for a finite family of positive self-adjoint operators
summing to the identity and two unit vectors, the ℓ¹ distance of the
two output laws is at most `2 ‖z − u‖`. -/
theorem sum_abs_re_inner_effect_sub_le {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ι : Type*}
    [Fintype ι] (T : ι → H →L[ℂ] H)
    (hsa : ∀ i, ∀ x y : H, ⟪(T i) x, y⟫_ℂ = ⟪x, (T i) y⟫_ℂ)
    (hpos : ∀ i, ∀ x : H, 0 ≤ (⟪x, (T i) x⟫_ℂ).re)
    (hsum : (∑ i, T i) = 1) (z u : H) (hz : ‖z‖ = 1) (hu : ‖u‖ = 1) :
    (∑ i, |(⟪z, (T i) z⟫_ℂ).re - (⟪u, (T i) u⟫_ℂ).re|) ≤
      2 * ‖z - u‖ := by
  classical
  -- total masses through the completeness of the family
  have htotal : ∀ w : H, (∑ i, (⟪w, (T i) w⟫_ℂ).re) = ‖w‖ ^ 2 := by
    intro w
    have h1 : (∑ i, ⟪w, (T i) w⟫_ℂ) = ⟪w, w⟫_ℂ := by
      rw [← inner_sum]
      congr 1
      rw [← ContinuousLinearMap.sum_apply, hsum,
        ContinuousLinearMap.one_apply]
    calc (∑ i, (⟪w, (T i) w⟫_ℂ).re) = (∑ i, ⟪w, (T i) w⟫_ℂ).re := by
          rw [Complex.re_sum]
      _ = (⟪w, w⟫_ℂ).re := by rw [h1]
      _ = ‖w‖ ^ 2 := by
          rw [inner_self_eq_norm_sq_to_K]
          norm_cast
  -- pointwise split and Cauchy–Schwarz
  have hpoint : ∀ i,
      |(⟪z, (T i) z⟫_ℂ).re - (⟪u, (T i) u⟫_ℂ).re| ≤
        Real.sqrt (⟪z - u, (T i) (z - u)⟫_ℂ).re *
            Real.sqrt (⟪z, (T i) z⟫_ℂ).re +
          Real.sqrt (⟪u, (T i) u⟫_ℂ).re *
            Real.sqrt (⟪z - u, (T i) (z - u)⟫_ℂ).re := by
    intro i
    have hsplit : ⟪z, (T i) z⟫_ℂ - ⟪u, (T i) u⟫_ℂ =
        ⟪z - u, (T i) z⟫_ℂ + ⟪u, (T i) (z - u)⟫_ℂ := by
      rw [inner_sub_left, map_sub, inner_sub_right]
      ring
    have h1 : |(⟪z, (T i) z⟫_ℂ).re - (⟪u, (T i) u⟫_ℂ).re| ≤
        ‖⟪z - u, (T i) z⟫_ℂ‖ + ‖⟪u, (T i) (z - u)⟫_ℂ‖ := by
      have : (⟪z, (T i) z⟫_ℂ).re - (⟪u, (T i) u⟫_ℂ).re =
          (⟪z - u, (T i) z⟫_ℂ + ⟪u, (T i) (z - u)⟫_ℂ).re := by
        rw [← hsplit, Complex.sub_re]
      rw [this]
      calc |(⟪z - u, (T i) z⟫_ℂ + ⟪u, (T i) (z - u)⟫_ℂ).re| ≤
            ‖⟪z - u, (T i) z⟫_ℂ + ⟪u, (T i) (z - u)⟫_ℂ‖ :=
          Complex.abs_re_le_norm _
        _ ≤ _ := norm_add_le _ _
    refine h1.trans (add_le_add ?_ ?_)
    · exact abs_inner_positive_form_le (T i) (hsa i) (hpos i) (z - u) z
    · calc ‖⟪u, (T i) (z - u)⟫_ℂ‖ ≤
            Real.sqrt (⟪u, (T i) u⟫_ℂ).re *
              Real.sqrt (⟪z - u, (T i) (z - u)⟫_ℂ).re :=
          abs_inner_positive_form_le (T i) (hsa i) (hpos i) u (z - u)
        _ = _ := rfl
  -- sum the two Cauchy–Schwarz families
  have hCS : ∀ (a b : ι → ℝ), (∀ i, 0 ≤ a i) → (∀ i, 0 ≤ b i) →
      (∑ i, Real.sqrt (a i) * Real.sqrt (b i)) ≤
        Real.sqrt (∑ i, a i) * Real.sqrt (∑ i, b i) := by
    intro a b ha hb
    have h2 : (∑ i, Real.sqrt (a i) * Real.sqrt (b i)) ^ 2 ≤
        (∑ i, a i) * (∑ i, b i) := by
      calc (∑ i, Real.sqrt (a i) * Real.sqrt (b i)) ^ 2 ≤
            (∑ i, Real.sqrt (a i) ^ 2) * (∑ i, Real.sqrt (b i) ^ 2) :=
          Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
        _ = (∑ i, a i) * (∑ i, b i) := by
            congr 1 <;> exact Finset.sum_congr rfl fun i _ =>
              Real.sq_sqrt (by first | exact ha i | exact hb i)
    have hs : 0 ≤ ∑ i, Real.sqrt (a i) * Real.sqrt (b i) :=
      Finset.sum_nonneg fun i _ =>
        mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    calc (∑ i, Real.sqrt (a i) * Real.sqrt (b i)) =
          Real.sqrt ((∑ i, Real.sqrt (a i) * Real.sqrt (b i)) ^ 2) := by
          rw [Real.sqrt_sq hs]
      _ ≤ Real.sqrt ((∑ i, a i) * (∑ i, b i)) := Real.sqrt_le_sqrt h2
      _ = _ := Real.sqrt_mul (Finset.sum_nonneg fun i _ => ha i) _
  calc (∑ i, |(⟪z, (T i) z⟫_ℂ).re - (⟪u, (T i) u⟫_ℂ).re|) ≤
        (∑ i, (Real.sqrt (⟪z - u, (T i) (z - u)⟫_ℂ).re *
            Real.sqrt (⟪z, (T i) z⟫_ℂ).re +
          Real.sqrt (⟪u, (T i) u⟫_ℂ).re *
            Real.sqrt (⟪z - u, (T i) (z - u)⟫_ℂ).re)) :=
      Finset.sum_le_sum fun i _ => hpoint i
    _ = (∑ i, Real.sqrt (⟪z - u, (T i) (z - u)⟫_ℂ).re *
            Real.sqrt (⟪z, (T i) z⟫_ℂ).re) +
        (∑ i, Real.sqrt (⟪u, (T i) u⟫_ℂ).re *
            Real.sqrt (⟪z - u, (T i) (z - u)⟫_ℂ).re) := by
      rw [Finset.sum_add_distrib]
    _ ≤ Real.sqrt (∑ i, (⟪z - u, (T i) (z - u)⟫_ℂ).re) *
          Real.sqrt (∑ i, (⟪z, (T i) z⟫_ℂ).re) +
        Real.sqrt (∑ i, (⟪u, (T i) u⟫_ℂ).re) *
          Real.sqrt (∑ i, (⟪z - u, (T i) (z - u)⟫_ℂ).re) :=
      add_le_add
        (hCS _ _ (fun i => hpos i (z - u)) (fun i => hpos i z))
        (hCS _ _ (fun i => hpos i u) (fun i => hpos i (z - u)))
    _ = 2 * ‖z - u‖ := by
      rw [htotal (z - u), htotal z, htotal u, hz, hu]
      simp only [one_pow, Real.sqrt_one, mul_one, one_mul]
      rw [Real.sqrt_sq (norm_nonneg _)]
      ring

end CommutingRepetition
