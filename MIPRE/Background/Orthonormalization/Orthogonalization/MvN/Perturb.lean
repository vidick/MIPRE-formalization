/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/MvN/Perturb.lean
-/
/-
# Tier T3, Lemma 3.1: the type II₁ perturbation step (proof side)

The "latter case is easier" paragraph of the proof of Lemma 3.1 of M. de la
Salle, *Orthogonalization of Positive Operator Valued Measures*
(arXiv:2103.14126v2, Section 3): in a finite corner `p M p` whose central
summand `c M c` is of type II₁ (no nonzero abelian projection), an element
`0 ≤ e ≤ 1` of `c M c` commuting with `a` which is *not* a projection admits a
nonzero self-adjoint perturbation direction `b ∈ c M c` commuting with `a`,
killed by the center-valued trace `E`, along which `e + t b` stays in `[0, 1]`
for all small real `t`. This is the ingredient of the paper's extremality
argument for the set `C_i`; the paper's `p`, `b`, `z`, `b'` are the `r`, `b₂`,
`z`, `b₂ - z r` below.

The steps: (1) since `e` is not a projection, some spectral projection
`r = χ_{[δ, 1-δ]}(e)` is nonzero (`exists_spectral_middle`, through the Borel
functional calculus of `CommutingRepetition.VN`), and `δ r ≤ e r ≤ (1 - δ) r`;
(2) `r M r` is not abelian, so it contains a self-adjoint element commuting
with `a` and not of the form `z r` with `z ∈ Z(p M p)`
(`exists_selfAdjoint_not_central`); (3) it is normalized to `0 ≤ b₂ ≤ r`
(`exists_normalized`); (4) the division property of `E` centers it:
`b = b₂ - z r` with `E b = 0`; (5) the spectral bounds and `‖b‖ ≤ 2` keep
`e + t b` in `[0, 1]` for `|t| ≤ δ / 2` (`perturb_mem_Icc`).

Proof-side only: no statement of the paper is made here.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.SpectralProjection
import MIPRE.Background.Repetition.CommutingRepetition.VN.JointSpectral
import MIPRE.Background.Repetition.CommutingRepetition.VN.Generated
import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.Defs
import MIPRE.Background.Orthonormalization.Orthogonalization.Positivity
import MIPRE.Background.Orthonormalization.Orthogonalization.Blocks.StateOnM

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace Orthogonalization.MvN

open scoped BigOperators ComplexOrder
open CommutingRepetition.BorelCalc CommutingRepetition.VN Blocks

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Real scalars and the Loewner order -/

/-- Multiplication by a nonnegative real scalar preserves positivity (it is the
conjugation by `√δ • 1`). -/
theorem smul_nonneg_real {x : H →L[ℂ] H} {δ : ℝ} (hδ : 0 ≤ δ) (hx : 0 ≤ x) :
    0 ≤ (δ : ℂ) • x := by
  have h : (δ : ℂ) • x = star (((Real.sqrt δ : ℝ) : ℂ) • (1 : H →L[ℂ] H)) * x *
      (((Real.sqrt δ : ℝ) : ℂ) • 1) := by
    rw [star_smul, star_one, smul_mul_assoc, one_mul, mul_smul_comm, mul_one, smul_smul,
      Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hδ]
  rw [h]
  exact conj_nonneg hx _

/-- Multiplication by a nonnegative real scalar is monotone. -/
theorem smul_le_smul_real {x y : H →L[ℂ] H} (h : x ≤ y) {δ : ℝ} (hδ : 0 ≤ δ) :
    (δ : ℂ) • x ≤ (δ : ℂ) • y := by
  refine le_of_nonneg_sub ?_
  rw [← smul_sub]
  exact smul_nonneg_real hδ (nonneg_sub_of_le h)

/-- For `0 ≤ x` and real `α ≤ β`, `α • x ≤ β • x`. -/
theorem smul_le_smul_scalar {x : H →L[ℂ] H} {α β : ℝ} (h : α ≤ β) (hx : 0 ≤ x) :
    (α : ℂ) • x ≤ (β : ℂ) • x := by
  refine le_of_nonneg_sub ?_
  rw [← sub_smul, ← Complex.ofReal_sub]
  exact smul_nonneg_real (sub_nonneg.mpr h) hx

/-- A real number is a self-adjoint complex number. -/
theorem isSelfAdjoint_ofReal (x : ℝ) : IsSelfAdjoint (x : ℂ) := by
  show star (x : ℂ) = x
  rw [Complex.star_def, Complex.conj_ofReal]

/-! ### Corners -/

/-- An element of the corner `r M r` is fixed by left multiplication by `r`. -/
theorem corner_mul_left {r y : H →L[ℂ] H} (hr : IsStarProjection r) (hy : r * y * r = y) :
    r * y = y := by
  conv_lhs => rw [← hy]
  rw [← mul_assoc, ← mul_assoc, hr.isIdempotentElem.eq]
  exact hy

/-- An element of the corner `r M r` is fixed by right multiplication by `r`. -/
theorem corner_mul_right {r y : H →L[ℂ] H} (hr : IsStarProjection r) (hy : r * y * r = y) :
    y * r = y := by
  conv_lhs => rw [← hy]
  rw [mul_assoc, hr.isIdempotentElem.eq]
  exact hy

/-- `r y r` lies in the corner of `r`. -/
theorem corner_conj {r : H →L[ℂ] H} (hr : IsStarProjection r) (x : H →L[ℂ] H) :
    r * (r * x * r) * r = r * x * r := by
  rw [← mul_assoc, ← mul_assoc, hr.isIdempotentElem.eq, mul_assoc, hr.isIdempotentElem.eq]

omit [CompleteSpace H] in
/-- If `r ≤ c` (`c r = r = r c`) then the corner of `r` is contained in the corner of `c`. -/
theorem corner_of_corner {c r y : H →L[ℂ] H} (hcr : c * r = r) (hrc : r * c = r)
    (hy : r * y * r = y) : c * y * c = y := by
  conv_lhs => rw [← hy]
  rw [← mul_assoc, ← mul_assoc, hcr, mul_assoc, hrc]
  exact hy

/-- The adjoint of an element of the corner `r M r` lies in the corner. -/
theorem corner_star {r y : H →L[ℂ] H} (hr : IsStarProjection r) (hy : r * y * r = y) :
    r * star y * r = star y := by
  have h : star y = r * star y * r := by
    conv_lhs => rw [← hy]
    rw [star_mul, star_mul, hr.isSelfAdjoint.star_eq, mul_assoc]
  exact h.symm

/-! ### The center of the corner `p M p` -/

theorem isCentralIn_zero (M : VonNeumannAlgebra H) (p : H →L[ℂ] H) : IsCentralIn M p 0 :=
  ⟨zero_mem _, by rw [mul_zero, zero_mul], fun y _ _ => Commute.zero_left y⟩

theorem isCentralIn_proj (M : VonNeumannAlgebra H) {p : H →L[ℂ] H} (hp : IsStarProjection p)
    (hpM : p ∈ M) : IsCentralIn M p p :=
  ⟨hpM, by rw [hp.isIdempotentElem.eq, hp.isIdempotentElem.eq], fun y _ hy => by
    show p * y = y * p
    rw [corner_mul_left hp hy, corner_mul_right hp hy]⟩

theorem IsCentralIn.smul {M : VonNeumannAlgebra H} {p z : H →L[ℂ] H} (hz : IsCentralIn M p z)
    (α : ℂ) : IsCentralIn M p (α • z) :=
  ⟨smul_mem_vn M α hz.1, by rw [mul_smul_comm, smul_mul_assoc, hz.2.1],
    fun y hyM hy => (hz.2.2 y hyM hy).smul_left α⟩

theorem IsCentralIn.sub {M : VonNeumannAlgebra H} {p z w : H →L[ℂ] H} (hz : IsCentralIn M p z)
    (hw : IsCentralIn M p w) : IsCentralIn M p (z - w) :=
  ⟨sub_mem hz.1 hw.1, by rw [mul_sub, sub_mul, hz.2.1, hw.2.1],
    fun y hyM hy => (hz.2.2 y hyM hy).sub_left (hw.2.2 y hyM hy)⟩

/-- An element `z r` with `z ∈ Z(p M p)` and `r ≤ p` commutes with every element of
`r M r`. -/
theorem commute_central_mul_proj {M : VonNeumannAlgebra H} {p r z y : H →L[ℂ] H}
    (hr : IsStarProjection r) (hpr : p * r = r) (hrp : r * p = r) (hz : IsCentralIn M p z)
    (hyM : y ∈ M) (hy : r * y * r = y) : Commute (z * r) y := by
  have hzy : Commute z y := hz.2.2 y hyM (corner_of_corner hpr hrp hy)
  show z * r * y = y * (z * r)
  rw [mul_assoc, corner_mul_left hr hy, ← mul_assoc, ← hzy.eq, mul_assoc, corner_mul_right hr hy]

/-! ### Step 1: the spectral projection `χ_{[δ, 1-δ]}(e)` -/

/-- The clip `t ↦ max 0 (min t 1)` of the real line onto `[0, 1]`. -/
noncomputable def clip (t : ℝ) : ℝ := max 0 (min t 1)

theorem clip_nonneg (t : ℝ) : 0 ≤ clip t := le_max_left _ _

theorem clip_le_one (t : ℝ) : clip t ≤ 1 := max_le zero_le_one (min_le_right _ _)

theorem clip_continuous : Continuous clip := by
  unfold clip; fun_prop

theorem bdd_clip : Bdd clip := Bdd.of_unit clip_continuous.measurable clip_nonneg clip_le_one

theorem clip_of_mem {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : clip t = t := by
  unfold clip; rw [min_eq_left h1, max_eq_right h0]

theorem clip_le_of_le {t δ : ℝ} (hδ : 0 ≤ δ) (h : t ≤ δ) : clip t ≤ δ :=
  max_le hδ ((min_le_left _ _).trans h)

theorem le_clip_of_le {t δ : ℝ} (hδ : δ ≤ 1) (h : δ ≤ t) : δ ≤ clip t :=
  (le_min h hδ).trans (le_max_right _ _)

/-- `t ↦ clip t (1 - clip t)`: bounded, continuous, equal to `t (1 - t)` on `[0, 1]`. -/
noncomputable def bump (t : ℝ) : ℝ := clip t * (1 - clip t)

theorem bump_nonneg (t : ℝ) : 0 ≤ bump t :=
  mul_nonneg (clip_nonneg t) (sub_nonneg.mpr (clip_le_one t))

theorem bump_le_one (t : ℝ) : bump t ≤ 1 := by
  unfold bump
  calc clip t * (1 - clip t) ≤ 1 * 1 :=
        mul_le_mul (clip_le_one t) (by linarith [clip_nonneg t]) (by linarith [clip_le_one t])
          zero_le_one
    _ = 1 := one_mul 1

theorem bump_continuous : Continuous bump := by
  unfold bump; exact clip_continuous.mul (continuous_const.sub clip_continuous)

theorem bdd_bump : Bdd bump := Bdd.of_unit bump_continuous.measurable bump_nonneg bump_le_one

/-- Outside `[δ, 1 - δ]` the bump is at most `δ`. -/
theorem bump_le_of_notMem {t δ : ℝ} (hδ0 : 0 < δ) (ht : t ∉ Set.Icc δ (1 - δ)) :
    bump t ≤ δ := by
  unfold bump
  rw [Set.mem_Icc, not_and_or] at ht
  rcases ht with h | h
  · have hc : clip t ≤ δ := clip_le_of_le hδ0.le (not_le.mp h).le
    calc clip t * (1 - clip t) ≤ clip t * 1 :=
          mul_le_mul_of_nonneg_left (by linarith [clip_nonneg t]) (clip_nonneg t)
      _ ≤ δ := by rw [mul_one]; exact hc
  · have hc : 1 - δ ≤ clip t := le_clip_of_le (by linarith) (not_le.mp h).le
    calc clip t * (1 - clip t) ≤ 1 * (1 - clip t) :=
          mul_le_mul_of_nonneg_right (clip_le_one t) (by linarith [clip_le_one t])
      _ ≤ δ := by rw [one_mul]; linarith

/-- The spectrum of `0 ≤ e ≤ 1` lies in `[0, 1]`. -/
theorem spectrum_subset_Icc {e : H →L[ℂ] H} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    spectrum ℝ e ⊆ Set.Icc 0 1 := by
  intro x hx
  refine ⟨spectrum_nonneg_of_nonneg he0 hx, ?_⟩
  have h := (le_algebraMap_iff_spectrum_le (R := ℝ) (r := (1 : ℝ)) (a := e)
    (IsSelfAdjoint.of_nonneg he0)).mp (by rwa [map_one])
  exact h x hx

/-- `clip(e) = e` when the spectrum of `e` lies in `[0, 1]`. -/
theorem bfc_clip {e : H →L[ℂ] H} (he : IsSelfAdjoint e) (hs : spectrum ℝ e ⊆ Set.Icc 0 1) :
    bfc e he clip = e := by
  rw [bfc_cfc e he bdd_clip clip_continuous]
  conv_rhs => rw [← cfc_id' ℝ e]
  exact cfc_congr fun t ht => clip_of_mem (hs ht).1 (hs ht).2

/-- `bump(e) = e (1 - e)` when the spectrum of `e` lies in `[0, 1]`. -/
theorem bfc_bump {e : H →L[ℂ] H} (he : IsSelfAdjoint e) (hs : spectrum ℝ e ⊆ Set.Icc 0 1) :
    bfc e he bump = e * (1 - e) := by
  rw [bfc_cfc e he bdd_bump bump_continuous]
  have h : cfc bump e = cfc (fun t : ℝ => t * (1 - t)) e :=
    cfc_congr fun t ht => by simp only [bump, clip_of_mem (hs ht).1 (hs ht).2]
  rw [h, cfc_mul (fun t : ℝ => t) (fun t : ℝ => 1 - t) e, cfc_id' ℝ e,
    cfc_sub (fun _ : ℝ => (1 : ℝ)) (fun t : ℝ => t) e, cfc_const_one ℝ e, cfc_id' ℝ e]

/-- A self-adjoint contraction `0 ≤ e ≤ 1` which is not a projection has a nonzero
spectral projection `χ_{[δ, 1-δ]}(e)` for some `0 < δ < 1/2`: otherwise
`‖e (1 - e)‖ ≤ δ` for every such `δ`, so `e² = e`. -/
theorem exists_spectral_middle {e : H →L[ℂ] H} (he : IsSelfAdjoint e) (he0 : 0 ≤ e)
    (he1 : e ≤ 1) (hne : ¬ IsStarProjection e) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ P e he (Set.Icc δ (1 - δ)) ≠ 0 := by
  have hs := spectrum_subset_Icc he0 he1
  by_contra hcon
  have hzero : ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → P e he (Set.Icc δ (1 - δ)) = 0 := by
    intro δ hδ0 hδ1
    by_contra h
    exact hcon ⟨δ, hδ0, hδ1, h⟩
  have key : ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ‖e * (1 - e)‖ ≤ δ := by
    intro δ hδ0 hδ1
    have hIm : MeasurableSet (Set.Icc δ (1 - δ)) := measurableSet_Icc
    have hind := Bdd.indicator (I := Set.Icc δ (1 - δ)) hIm
    have hindc := Bdd.indicator (I := (Set.Icc δ (1 - δ))ᶜ) hIm.compl
    have h1 : bump = bump * (Set.Icc δ (1 - δ)).indicator 1 +
        bump * (Set.Icc δ (1 - δ))ᶜ.indicator 1 := by
      rw [← mul_add, Set.indicator_self_add_compl, mul_one]
    have h2 : bfc e he (bump * (Set.Icc δ (1 - δ)).indicator 1) = 0 := by
      rw [bfc_mul e he bdd_bump hind]
      change bfc e he bump * P e he (Set.Icc δ (1 - δ)) = 0
      rw [hzero δ hδ0 hδ1, mul_zero]
    have h3 : ‖bfc e he (bump * (Set.Icc δ (1 - δ))ᶜ.indicator 1)‖ ≤ δ := by
      refine norm_bfc_le e he (bdd_bump.mul hindc) fun t => ?_
      rw [Pi.mul_apply]
      by_cases ht : t ∈ Set.Icc δ (1 - δ)
      · rw [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr ht), mul_zero, abs_zero]
        exact hδ0.le
      · rw [Set.indicator_of_mem (Set.mem_compl ht), Pi.one_apply, mul_one,
          abs_of_nonneg (bump_nonneg t)]
        exact bump_le_of_notMem hδ0 ht
    rw [← bfc_bump he hs, h1, bfc_add e he (bdd_bump.mul hind) (bdd_bump.mul hindc), h2,
      zero_add]
    exact h3
  have h0 : e * (1 - e) = 0 := by
    by_contra hx
    have hpos : 0 < ‖e * (1 - e)‖ := norm_pos_iff.mpr hx
    have h := key (min (‖e * (1 - e)‖ / 2) (1 / 4)) (lt_min (by linarith) (by norm_num))
      (lt_of_le_of_lt (min_le_right _ _) (by norm_num))
    have := min_le_left (‖e * (1 - e)‖ / 2) (1 / 4)
    linarith
  apply hne
  refine ⟨?_, he⟩
  show e * e = e
  rw [mul_sub, mul_one, sub_eq_zero] at h0
  exact h0.symm

/-- `e χ_I(e) = (clip · 1_I)(e)`. -/
theorem mul_P_eq_bfc {e : H →L[ℂ] H} (he : IsSelfAdjoint e) (hs : spectrum ℝ e ⊆ Set.Icc 0 1)
    {I : Set ℝ} (hI : MeasurableSet I) :
    e * P e he I = bfc e he (clip * I.indicator 1) := by
  rw [bfc_mul e he bdd_clip (Bdd.indicator hI), bfc_clip he hs, P]

/-- `δ r ≤ e r` for `r = χ_{[δ, 1-δ]}(e)`. -/
theorem smul_P_le_mul_P {e : H →L[ℂ] H} (he : IsSelfAdjoint e)
    (hs : spectrum ℝ e ⊆ Set.Icc 0 1) (δ : ℝ) :
    (δ : ℂ) • P e he (Set.Icc δ (1 - δ)) ≤ e * P e he (Set.Icc δ (1 - δ)) := by
  have hIm : MeasurableSet (Set.Icc δ (1 - δ)) := measurableSet_Icc
  have hind := Bdd.indicator (I := Set.Icc δ (1 - δ)) hIm
  rw [mul_P_eq_bfc he hs hIm, P, ← bfc_const_mul e he δ hind]
  refine bfc_mono e he (hind.const_mul δ) (bdd_clip.mul hind) fun t => ?_
  dsimp only [Pi.mul_apply]
  by_cases ht : t ∈ Set.Icc δ (1 - δ)
  · rw [Set.indicator_of_mem ht, Pi.one_apply, mul_one, mul_one]
    exact le_clip_of_le (by linarith [ht.1, ht.2]) ht.1
  · rw [Set.indicator_of_notMem ht, mul_zero, mul_zero]

/-- `e r ≤ (1 - δ) r` for `r = χ_{[δ, 1-δ]}(e)`. -/
theorem mul_P_le_smul_P {e : H →L[ℂ] H} (he : IsSelfAdjoint e)
    (hs : spectrum ℝ e ⊆ Set.Icc 0 1) (δ : ℝ) :
    e * P e he (Set.Icc δ (1 - δ)) ≤ ((1 - δ : ℝ) : ℂ) • P e he (Set.Icc δ (1 - δ)) := by
  have hIm : MeasurableSet (Set.Icc δ (1 - δ)) := measurableSet_Icc
  have hind := Bdd.indicator (I := Set.Icc δ (1 - δ)) hIm
  rw [mul_P_eq_bfc he hs hIm, P, ← bfc_const_mul e he (1 - δ) hind]
  refine bfc_mono e he (bdd_clip.mul hind) (hind.const_mul (1 - δ)) fun t => ?_
  dsimp only [Pi.mul_apply]
  by_cases ht : t ∈ Set.Icc δ (1 - δ)
  · rw [Set.indicator_of_mem ht, Pi.one_apply, mul_one, mul_one]
    exact clip_le_of_le (by linarith [ht.1, ht.2]) ht.2
  · rw [Set.indicator_of_notMem ht, mul_zero, mul_zero]

/-- `r ≤ δ⁻¹ e r` for `r = χ_{[δ, 1-δ]}(e)`. -/
theorem P_le_smul_mul_P {e : H →L[ℂ] H} (he : IsSelfAdjoint e)
    (hs : spectrum ℝ e ⊆ Set.Icc 0 1) {δ : ℝ} (hδ0 : 0 < δ) :
    P e he (Set.Icc δ (1 - δ)) ≤ ((δ⁻¹ : ℝ) : ℂ) • (e * P e he (Set.Icc δ (1 - δ))) := by
  have hIm : MeasurableSet (Set.Icc δ (1 - δ)) := measurableSet_Icc
  have hind := Bdd.indicator (I := Set.Icc δ (1 - δ)) hIm
  rw [mul_P_eq_bfc he hs hIm, ← bfc_const_mul e he δ⁻¹ (bdd_clip.mul hind), P]
  refine bfc_mono e he hind ((bdd_clip.mul hind).const_mul δ⁻¹) fun t => ?_
  dsimp only [Pi.mul_apply]
  by_cases ht : t ∈ Set.Icc δ (1 - δ)
  · rw [Set.indicator_of_mem ht, Pi.one_apply, mul_one]
    calc (1 : ℝ) = δ⁻¹ * δ := (inv_mul_cancel₀ hδ0.ne').symm
      _ ≤ δ⁻¹ * clip t :=
          mul_le_mul_of_nonneg_left (le_clip_of_le (by linarith [ht.1, ht.2]) ht.1)
            (inv_nonneg.mpr hδ0.le)
  · rw [Set.indicator_of_notMem ht, mul_zero, mul_zero]

/-- A projection `r ≤ s • (e r)` (as `r = χ_{[δ, 1-δ]}(e)` with `s = δ⁻¹`) lies below every
projection `c` commuting with it such that `c e = e`. -/
theorem proj_mul_eq_self_of_le_smul {r e c : H →L[ℂ] H} (hr : IsStarProjection r)
    (hc : IsStarProjection c) (hrc : Commute r c) (hce : c * e = e) {s : ℂ}
    (hle : r ≤ s • (e * r)) : r * c = r := by
  have hq : IsStarProjection (1 - c) := hc.one_sub
  have hqe : (1 - c) * e = 0 := by rw [sub_mul, one_mul, hce, sub_self]
  have hrq : Commute r (1 - c) := (Commute.one_right r).sub_right hrc
  have h := conj_le_conj hle (1 - c)
  rw [hq.isSelfAdjoint.star_eq, mul_smul_comm, smul_mul_assoc, ← mul_assoc, hqe, zero_mul,
    zero_mul, smul_zero, ← hrq.eq, mul_assoc, hq.isIdempotentElem.eq] at h
  have h0 : r * (1 - c) = 0 := le_antisymm h (hr.mul hq hrq).nonneg
  rw [mul_sub, mul_one, sub_eq_zero] at h0
  exact h0.symm

/-- **Step 1.** For `0 ≤ e ≤ 1` in `c M c` (`c` a projection), commuting with `a` and not a
projection, some spectral projection `r = χ_{[δ, 1-δ]}(e)` (`0 < δ < 1/2`) is nonzero;
it lies in `M`, below `c`, commutes with `a` and `e`, and `δ r ≤ e r ≤ (1 - δ) r`. -/
theorem exists_middle_projection (M : VonNeumannAlgebra H) {e c a : H →L[ℂ] H}
    (heM : e ∈ M) (he0 : 0 ≤ e) (he1 : e ≤ 1) (hne : ¬ IsStarProjection e)
    (hc : IsStarProjection c) (hce : c * e = e) (hec : e * c = e) (hea : Commute e a) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ ∃ r : H →L[ℂ] H, r ≠ 0 ∧ IsStarProjection r ∧ r ∈ M ∧
      Commute r a ∧ Commute r e ∧ r * c = r ∧ c * r = r ∧
      (δ : ℂ) • r ≤ e * r ∧ e * r ≤ ((1 - δ : ℝ) : ℂ) • r := by
  have he : IsSelfAdjoint e := IsSelfAdjoint.of_nonneg he0
  have hs := spectrum_subset_Icc he0 he1
  obtain ⟨δ, hδ0, hδ1, hr0⟩ := exists_spectral_middle he he0 he1 hne
  have hIm : MeasurableSet (Set.Icc δ (1 - δ)) := measurableSet_Icc
  have hind := Bdd.indicator (I := Set.Icc δ (1 - δ)) hIm
  have hr : IsStarProjection (P e he (Set.Icc δ (1 - δ))) :=
    ⟨P_idem e he hIm, P_isSelfAdjoint e he _⟩
  have hrc : Commute (P e he (Set.Icc δ (1 - δ))) c :=
    commute_bfc e he (show Commute e c by rw [Commute, SemiconjBy, hec, hce]) hind
  have hrc' : P e he (Set.Icc δ (1 - δ)) * c = P e he (Set.Icc δ (1 - δ)) :=
    proj_mul_eq_self_of_le_smul hr hc hrc hce (P_le_smul_mul_P he hs hδ0)
  refine ⟨δ, hδ0, hδ1, P e he (Set.Icc δ (1 - δ)), hr0, hr, bfc_mem M he heM hind,
    commute_bfc e he hea hind, commute_bfc e he (Commute.refl e) hind, hrc', ?_,
    smul_P_le_mul_P he hs δ, mul_P_le_smul_P he hs δ⟩
  rw [← hrc.eq]
  exact hrc'

/-! ### Step 2: a self-adjoint element of `r M r` commuting with `a`, not in `Z(p M p) r` -/

/-- Real and imaginary parts: `x = ½ ((x + x*) + (-i) (i (x - x*)))`. -/
theorem eq_smul_add_smul_selfAdjoint (x : H →L[ℂ] H) :
    x = (1 / 2 : ℂ) • ((x + star x) + (-Complex.I) • (Complex.I • (x - star x))) := by
  rw [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
  have : x + star x + (x - star x) = (2 : ℂ) • x := by rw [two_smul]; abel
  rw [this, smul_smul]; norm_num

/-- `i (x - x*)` is self-adjoint. -/
theorem isSelfAdjoint_I_smul_sub_star (x : H →L[ℂ] H) :
    IsSelfAdjoint (Complex.I • (x - star x)) := by
  rw [IsSelfAdjoint, star_smul, star_sub, star_star, Complex.star_def, Complex.conj_I, neg_smul,
    ← smul_neg, neg_sub]

/-- If every self-adjoint element of `r M r` is of the form `z r` with `z ∈ Z(p M p)`
(`r ≤ p`), then `r M r` is commutative. -/
theorem commute_of_forall_selfAdjoint (M : VonNeumannAlgebra H) {p r : H →L[ℂ] H}
    (hr : IsStarProjection r) (hpr : p * r = r) (hrp : r * p = r)
    (hall : ∀ b : H →L[ℂ] H, b ∈ M → r * b * r = b → IsSelfAdjoint b →
      ∃ z, IsCentralIn M p z ∧ b = z * r)
    {x y : H →L[ℂ] H} (hxM : x ∈ M) (hrx : r * x * r = x) (hyM : y ∈ M)
    (hry : r * y * r = y) : Commute x y := by
  have hsx : r * star x * r = star x := corner_star hr hrx
  obtain ⟨zu, hzu, hu⟩ := hall (x + star x) (add_mem hxM (star_mem hxM))
    (by rw [mul_add, add_mul, hrx, hsx]) (IsSelfAdjoint.add_star_self x)
  obtain ⟨zv, hzv, hv⟩ := hall (Complex.I • (x - star x))
    (smul_mem_vn M _ (sub_mem hxM (star_mem hxM)))
    (by rw [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, hrx, hsx])
    (isSelfAdjoint_I_smul_sub_star x)
  have hu' : Commute (x + star x) y := by
    rw [hu]; exact commute_central_mul_proj hr hpr hrp hzu hyM hry
  have hv' : Commute (Complex.I • (x - star x)) y := by
    rw [hv]; exact commute_central_mul_proj hr hpr hrp hzv hyM hry
  rw [eq_smul_add_smul_selfAdjoint x]
  exact (hu'.add_left (hv'.smul_left _)).smul_left _

/-- **Step 2.** If `r M r` is not abelian (`r ≤ p` a projection of `M`) and `r` commutes with
the self-adjoint `a ∈ M`, there is a self-adjoint `b ∈ r M r` commuting with `a` which is not
of the form `z r` with `z ∈ Z(p M p)`: `r a` if `r a` is not of that form, and otherwise any
self-adjoint element of `r M r` not of that form (all of `r M r` then commutes with `a`). -/
theorem exists_selfAdjoint_not_central (M : VonNeumannAlgebra H) {p r a : H →L[ℂ] H}
    (hr : IsStarProjection r) (hrM : r ∈ M) (hpr : p * r = r) (hrp : r * p = r)
    (hnab : ¬ IsAbelianProj M r) (haM : a ∈ M) (hasa : IsSelfAdjoint a) (hra : Commute r a) :
    ∃ b : H →L[ℂ] H, b ∈ M ∧ r * b * r = b ∧ IsSelfAdjoint b ∧ Commute b a ∧
      ∀ z, IsCentralIn M p z → b ≠ z * r := by
  classical
  -- a noncommuting pair in `r M r`
  have hpair : ∃ x ∈ M, ∃ y ∈ M, (r * x * r) * (r * y * r) ≠ (r * y * r) * (r * x * r) := by
    by_contra h
    exact hnab ⟨hr, hrM, fun x hx y hy => by_contra fun hne => h ⟨x, hx, y, hy, hne⟩⟩
  -- a self-adjoint element of `r M r` not of the form `z r`
  have hS : ∃ b : H →L[ℂ] H, b ∈ M ∧ r * b * r = b ∧ IsSelfAdjoint b ∧
      ∀ z, IsCentralIn M p z → b ≠ z * r := by
    by_contra hall
    have hall' : ∀ b : H →L[ℂ] H, b ∈ M → r * b * r = b → IsSelfAdjoint b →
        ∃ z, IsCentralIn M p z ∧ b = z * r := by
      intro b hbM hrb hbsa
      by_contra h
      exact hall ⟨b, hbM, hrb, hbsa, fun z hz hb => h ⟨z, hz, hb⟩⟩
    obtain ⟨x, hxM, y, hyM, hne⟩ := hpair
    exact hne (commute_of_forall_selfAdjoint M hr hpr hrp hall' (mul_mem (mul_mem hrM hxM) hrM)
      (corner_conj hr x) (mul_mem (mul_mem hrM hyM) hrM) (corner_conj hr y)).eq
  obtain ⟨b, hbM, hrb, hbsa, hbQ⟩ := hS
  by_cases hex : ∃ z₀, IsCentralIn M p z₀ ∧ r * a = z₀ * r
  · -- `r a = z₀ r`: every element of `r M r` commutes with `a`
    obtain ⟨z₀, hz₀, hra'⟩ := hex
    refine ⟨b, hbM, hrb, hbsa, ?_, hbQ⟩
    have hzb : Commute z₀ b := hz₀.2.2 b hbM (corner_of_corner hpr hrp hrb)
    show b * a = a * b
    calc b * a = b * (r * a) := by rw [← mul_assoc, corner_mul_right hr hrb]
      _ = b * (z₀ * r) := by rw [hra']
      _ = z₀ * b * r := by rw [← mul_assoc, ← hzb.eq]
      _ = z₀ * b := by rw [mul_assoc, corner_mul_right hr hrb]
      _ = z₀ * (r * b) := by rw [corner_mul_left hr hrb]
      _ = z₀ * r * b := by rw [mul_assoc]
      _ = r * a * b := by rw [hra']
      _ = a * r * b := by rw [hra.eq]
      _ = a * b := by rw [mul_assoc, corner_mul_left hr hrb]
  · -- otherwise `r a` itself works
    refine ⟨r * a, mul_mem hrM haM, ?_, ?_, hra.mul_left (Commute.refl a),
      fun z hz h => hex ⟨z, hz, h⟩⟩
    · rw [← mul_assoc, hr.isIdempotentElem.eq, mul_assoc, ← hra.eq, ← mul_assoc,
        hr.isIdempotentElem.eq]
    · rw [IsSelfAdjoint, star_mul, hasa.star_eq, hr.isSelfAdjoint.star_eq]
      exact hra.symm.eq

/-! ### Step 3: normalization to `0 ≤ b ≤ r` -/

/-- A self-adjoint `b = r b r` satisfies `b ≤ ‖b‖ r`. -/
theorem le_norm_smul_proj {b r : H →L[ℂ] H} (hr : IsStarProjection r) (hb : IsSelfAdjoint b)
    (hrb : r * b * r = b) : b ≤ (‖b‖ : ℂ) • r := by
  have h := conj_le_conj (IsSelfAdjoint.le_algebraMap_norm_self hb) r
  rwa [hr.isSelfAdjoint.star_eq, hrb, Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul,
    mul_smul_comm, smul_mul_assoc, mul_one, hr.isIdempotentElem.eq] at h

/-- A self-adjoint `b = r b r` satisfies `-‖b‖ r ≤ b`. -/
theorem neg_norm_smul_proj_le {b r : H →L[ℂ] H} (hr : IsStarProjection r) (hb : IsSelfAdjoint b)
    (hrb : r * b * r = b) : -((‖b‖ : ℂ) • r) ≤ b := by
  have h := le_norm_smul_proj hr hb.neg (by rw [mul_neg, neg_mul, hrb])
  rw [norm_neg] at h
  exact neg_le.mp h

/-- **Step 3.** A self-adjoint `b₁ ∈ r M r` commuting with `a` and not of the form `z r`
(`z ∈ Z(p M p)`) is renormalized to `b₂ = (2 ‖b₁‖)⁻¹ (b₁ + ‖b₁‖ r)`, which satisfies
`0 ≤ b₂ ≤ r` and keeps the other properties. -/
theorem exists_normalized (M : VonNeumannAlgebra H) {p r a : H →L[ℂ] H} (hp : IsStarProjection p)
    (hpM : p ∈ M) (hr : IsStarProjection r) (hrM : r ∈ M) (hpr : p * r = r) (hra : Commute r a)
    {b₁ : H →L[ℂ] H} (hb₁M : b₁ ∈ M) (hrb₁ : r * b₁ * r = b₁) (hb₁sa : IsSelfAdjoint b₁)
    (hb₁a : Commute b₁ a) (hb₁Q : ∀ z, IsCentralIn M p z → b₁ ≠ z * r) :
    ∃ b : H →L[ℂ] H, b ∈ M ∧ r * b * r = b ∧ 0 ≤ b ∧ b ≤ r ∧ Commute b a ∧
      ∀ z, IsCentralIn M p z → b ≠ z * r := by
  have hb₁0 : b₁ ≠ 0 := fun h => hb₁Q 0 (isCentralIn_zero M p) (by rw [h, zero_mul])
  have hn : 0 < ‖b₁‖ := norm_pos_iff.mpr hb₁0
  have hn2 : (2 * ‖b₁‖ : ℝ) ≠ 0 := (mul_pos two_pos hn).ne'
  have hup : b₁ ≤ (‖b₁‖ : ℂ) • r := le_norm_smul_proj hr hb₁sa hrb₁
  have hlow : -((‖b₁‖ : ℂ) • r) ≤ b₁ := neg_norm_smul_proj_le hr hb₁sa hrb₁
  have hsum : b₁ + (‖b₁‖ : ℂ) • r ≤ ((2 * ‖b₁‖ : ℝ) : ℂ) • r := by
    refine le_of_nonneg_sub ?_
    have : ((2 * ‖b₁‖ : ℝ) : ℂ) • r - (b₁ + (‖b₁‖ : ℂ) • r) = (‖b₁‖ : ℂ) • r - b₁ := by
      push_cast; rw [two_mul, add_smul]; abel
    rw [this]; exact nonneg_sub_of_le hup
  have hkey : ((2 * ‖b₁‖ : ℝ) : ℂ) • ((((2 * ‖b₁‖)⁻¹ : ℝ) : ℂ) • (b₁ + (‖b₁‖ : ℂ) • r)) =
      b₁ + (‖b₁‖ : ℂ) • r := by
    rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn2, Complex.ofReal_one, one_smul]
  refine ⟨(((2 * ‖b₁‖)⁻¹ : ℝ) : ℂ) • (b₁ + (‖b₁‖ : ℂ) • r), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smul_mem_vn M _ (add_mem hb₁M (smul_mem_vn M _ hrM))
  · rw [mul_smul_comm, smul_mul_assoc, mul_add, add_mul, hrb₁, mul_smul_comm, smul_mul_assoc,
      hr.isIdempotentElem.eq, hr.isIdempotentElem.eq]
  · refine smul_nonneg_real (by positivity) ?_
    have h := nonneg_sub_of_le hlow
    rwa [sub_neg_eq_add] at h
  · have h := smul_le_smul_real hsum (δ := (2 * ‖b₁‖)⁻¹) (by positivity)
    rwa [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hn2, Complex.ofReal_one,
      one_smul] at h
  · exact (hb₁a.add_left (hra.smul_left _)).smul_left _
  · intro z hz h
    apply hb₁Q (((2 * ‖b₁‖ : ℝ) : ℂ) • z - (‖b₁‖ : ℂ) • p)
      ((hz.smul _).sub ((isCentralIn_proj M hp hpM).smul _))
    rw [sub_mul, smul_mul_assoc, smul_mul_assoc, hpr, ← h, hkey, add_sub_cancel_right]

/-! ### Step 5: the perturbation stays in `[0, 1]` -/

/-- **Step 5.** If `r` is a projection commuting with `0 ≤ e ≤ 1` with
`δ r ≤ e r ≤ (1 - δ) r`, and `b = r b r` is self-adjoint of norm `≤ 2`, then
`e + t b ∈ [0, 1]` for `|t| ≤ δ / 2`: decompose `e = e (1 - r) + e r` with
`0 ≤ e (1 - r) ≤ 1 - r`, and `-δ r ≤ t b ≤ δ r`. -/
theorem perturb_mem_Icc {e r b : H →L[ℂ] H} (hr : IsStarProjection r) (he0 : 0 ≤ e)
    (he1 : e ≤ 1) (hre : Commute r e) {δ : ℝ} (hlow : (δ : ℂ) • r ≤ e * r)
    (hupp : e * r ≤ ((1 - δ : ℝ) : ℂ) • r) (hbsa : IsSelfAdjoint b) (hrb : r * b * r = b)
    (hbn : ‖b‖ ≤ 2) {t : ℝ} (ht : |t| ≤ δ / 2) :
    0 ≤ e + (t : ℂ) • b ∧ e + (t : ℂ) • b ≤ 1 := by
  have htb_sa : IsSelfAdjoint ((t : ℂ) • b) := (isSelfAdjoint_ofReal t).smul hbsa
  have htb_r : r * ((t : ℂ) • b) * r = (t : ℂ) • b := by
    rw [mul_smul_comm, smul_mul_assoc, hrb]
  have htb_norm : ‖(t : ℂ) • b‖ ≤ δ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    calc |t| * ‖b‖ ≤ (δ / 2) * 2 := mul_le_mul ht hbn (norm_nonneg _) ((abs_nonneg t).trans ht)
      _ = δ := by ring
  have h1 : (t : ℂ) • b ≤ (δ : ℂ) • r :=
    (le_norm_smul_proj hr htb_sa htb_r).trans (smul_le_smul_scalar htb_norm hr.nonneg)
  have h2 : -((δ : ℂ) • r) ≤ (t : ℂ) • b :=
    (neg_le_neg (smul_le_smul_scalar htb_norm hr.nonneg)).trans
      (neg_norm_smul_proj_le hr htb_sa htb_r)
  have hsplit : e = e * (1 - r) + e * r := by rw [mul_sub, mul_one, sub_add_cancel]
  have hq : IsStarProjection (1 - r) := hr.one_sub
  have hqe : Commute (1 - r) e := (Commute.one_left e).sub_left hre
  have h3 : 0 ≤ e * (1 - r) := by
    have h := Orthogonalization.IsStarProjection.mul_nonneg_of_commute hq he0 hqe
    rwa [hqe.eq] at h
  have h4 : e * (1 - r) ≤ 1 - r := by
    have h := mul_nonneg_of_commute (sub_nonneg.mpr he1) hq.nonneg
      ((Commute.one_left (1 - r)).sub_left hqe.symm)
    rw [sub_mul, one_mul] at h
    exact le_of_nonneg_sub h
  constructor
  · have h : e + (t : ℂ) • b =
        e * (1 - r) + (e * r - (δ : ℂ) • r) + ((t : ℂ) • b - -((δ : ℂ) • r)) := by
      conv_lhs => rw [hsplit]
      abel
    rw [h]
    exact add_nonneg (add_nonneg h3 (nonneg_sub_of_le hlow)) (nonneg_sub_of_le h2)
  · refine le_of_nonneg_sub ?_
    have hr' : ((1 - δ : ℝ) : ℂ) • r + (δ : ℂ) • r = r := by
      rw [← add_smul, ← Complex.ofReal_add, sub_add_cancel, Complex.ofReal_one, one_smul]
    have h : ((1 - r) - e * (1 - r)) + (((1 - δ : ℝ) : ℂ) • r - e * r) +
        ((δ : ℂ) • r - (t : ℂ) • b) =
        (1 - (e + (t : ℂ) • b)) + (((1 - δ : ℝ) : ℂ) • r + (δ : ℂ) • r - r) := by
      conv_rhs => rw [hsplit]
      abel
    rw [hr', sub_self, add_zero] at h
    rw [← h]
    exact add_nonneg (add_nonneg (nonneg_sub_of_le h4) (nonneg_sub_of_le hupp))
      (nonneg_sub_of_le h1)

/-! ### The perturbation step of Lemma 3.1 -/

/-- **The type II₁ perturbation of Lemma 3.1** (paper, Section 3, "The latter case is easier"):
if `e ∈ c M c`, `0 ≤ e ≤ 1`, commutes with `a` and is not a projection, then there is a nonzero
self-adjoint `b ∈ c M c` commuting with `a` with `E b = 0` such that `e + t b ∈ [0, 1]` for all
small real `t`. Here `c` is a central projection of the finite corner `p M p` whose corner
`c M c` has no nonzero abelian projection (type II₁), and `E` is the center-valued trace of
`p M p`. -/
theorem exists_perturbation (M : VonNeumannAlgebra H) {p : H →L[ℂ] H}
    (hp : IsStarProjection p) (hpM : p ∈ M)
    {c : H →L[ℂ] H} (hc : IsStarProjection c) (hcc : IsCentralIn M p c)
    (hII : ∀ r, IsAbelianProj M r → r * c = r → r = 0)
    (E : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)) (hE : IsCenterValuedTrace M p E)
    {a e : H →L[ℂ] H} (haM : a ∈ M) (hac : c * a * c = a) (ha0 : 0 ≤ a)
    (heM : e ∈ M) (hec : c * e * c = e) (he0 : 0 ≤ e) (he1 : e ≤ 1) (hea : Commute e a)
    (hne : ¬ IsStarProjection e) :
    ∃ b : H →L[ℂ] H, b ≠ 0 ∧ b ∈ M ∧ c * b * c = b ∧ IsSelfAdjoint b ∧ Commute b a ∧ E b = 0 ∧
      ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, |t| ≤ t₀ → 0 ≤ e + (t : ℂ) • b ∧ e + (t : ℂ) • b ≤ 1 := by
  classical
  -- `c ≤ p`, and `e, a ∈ c M c ⊆ p M p`
  have hpc : p * c = c := corner_mul_left hp hcc.2.1
  have hcp : c * p = c := corner_mul_right hp hcc.2.1
  have hce : c * e = e := corner_mul_left hc hec
  have hec' : e * c = e := corner_mul_right hc hec
  have hpa : p * a * p = a := corner_of_corner hpc hcp hac
  -- Step 1: the spectral projection `r = χ_{[δ, 1-δ]}(e)`
  obtain ⟨δ, hδ0, hδ1, r, hr0, hr, hrM, hra, hre, hrc, hcr, hlow, hupp⟩ :=
    exists_middle_projection M heM he0 he1 hne hc hce hec' hea
  have hpr : p * r = r := by rw [← hcr, ← mul_assoc, hpc]
  have hrp : r * p = r := by rw [← hrc, mul_assoc, hcp]
  have hprp : p * r * p = r := by rw [hpr, hrp]
  -- Step 2: `r M r` is not abelian (type II₁)
  have hnab : ¬ IsAbelianProj M r := fun h => hr0 (hII r h hrc)
  obtain ⟨b₁, hb₁M, hrb₁, hb₁sa, hb₁a, hb₁Q⟩ :=
    exists_selfAdjoint_not_central M hr hrM hpr hrp hnab haM (IsSelfAdjoint.of_nonneg ha0) hra
  -- Step 3: normalization
  obtain ⟨b₂, hb₂M, hrb₂, hb₂0, hb₂r, hb₂a, hb₂Q⟩ :=
    exists_normalized M hp hpM hr hrM hpr hra hb₁M hrb₁ hb₁sa hb₁a hb₁Q
  -- Step 4: centering by the division property of `E`
  obtain ⟨z, hz, hz0, hzp, hEz⟩ := hE.div r hr hrM hrp b₂ hb₂M hb₂0 hb₂r
  have hzr : Commute z r := hz.2.2 r hrM hprp
  have hza : Commute z a := hz.2.2 a haM hpa
  have hzsa : IsSelfAdjoint z := IsSelfAdjoint.of_nonneg hz0
  have hrzr : r * (z * r) * r = z * r := by
    rw [← mul_assoc, ← hzr.eq, mul_assoc, hr.isIdempotentElem.eq, mul_assoc,
      hr.isIdempotentElem.eq]
  have hrb : r * (b₂ - z * r) * r = b₂ - z * r := by rw [mul_sub, sub_mul, hrb₂, hrzr]
  have hbsa : IsSelfAdjoint (b₂ - z * r) := by
    refine (IsSelfAdjoint.of_nonneg hb₂0).sub ?_
    rw [IsSelfAdjoint, star_mul, hr.isSelfAdjoint.star_eq, hzsa.star_eq]
    exact hzr.symm.eq
  have hbn : ‖b₂ - z * r‖ ≤ 2 := by
    have h1 : ‖b₂‖ ≤ 1 :=
      (CStarAlgebra.norm_le_one_iff_of_nonneg b₂ hb₂0).mpr (hb₂r.trans hr.le_one)
    have h2 : ‖z‖ ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg z hz0).mpr (hzp.trans hp.le_one)
    have h3 : ‖r‖ ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg r hr.nonneg).mpr hr.le_one
    calc ‖b₂ - z * r‖ ≤ ‖b₂‖ + ‖z * r‖ := norm_sub_le _ _
      _ ≤ ‖b₂‖ + ‖z‖ * ‖r‖ := add_le_add le_rfl (norm_mul_le _ _)
      _ ≤ 1 + 1 * 1 := add_le_add h1 (mul_le_mul h2 h3 (norm_nonneg _) zero_le_one)
      _ = 2 := by norm_num
  -- Step 5: assemble
  refine ⟨b₂ - z * r, sub_ne_zero.mpr (hb₂Q z hz), sub_mem hb₂M (mul_mem hz.1 hrM),
    corner_of_corner hcr hrc hrb, hbsa, hb₂a.sub_left (hza.mul_left hra), ?_, δ / 2,
    by positivity, fun t ht => perturb_mem_Icc hr he0 he1 hre hlow hupp hbsa hrb hbn ht⟩
  rw [map_sub, hEz, hE.center_mul z hz r hrM hprp, sub_self]

end Orthogonalization.MvN
