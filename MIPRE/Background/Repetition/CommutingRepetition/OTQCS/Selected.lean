/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/OTQCS/Selected.lean
-/
/-
# OTQCS: the selected state (node 1.3.7)

Anchors: 06_otqcs.tex, eqs wst, w-norm, zst, c-zero, rounded-y,
z-rounded-y, rounding-tails, normalization-inequality, rounded-y-y.

The selected-trial conditional state `z_{st}` and its comparison with
the rounded polar vector `ỹ_t`: everything happens back in the base
algebra (the normalized `e_{★★}`-corner identification of the trial
factor), over one pair of spectral packages and their joint coupling,
with an abstract band family (OTQCS/Trial.lean) standing for the
retained shifted bins. The zero-common-mass default for `z_{st}` is
the trace vector `ι(1)` — "a fixed unit vector" (eq zst); eq c-zero
makes the uniform constant `4` work for both branches of eq
z-rounded-y. The composition into eq rounded-y-y and eq
selected-state-preopt (via the proved normalization inequality of
Prelim/Vector.lean, eq normalization-inequality) is proof-layer of
node 1.3.9.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.OTQCS.Trial

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open MeasureTheory
open scoped BigOperators InnerProductSpace

universe u

variable {N : StdTracialAlgebra.{u}} {x y : N.H}

section Selected

variable (dA : SpectralData N x) (dB : SpectralData N y)
variable (Jd : JointSpectralData dA dB)
variable {m : ℕ} (B : Fin m → Set ℝ) (t : Fin m → ℝ)

/-- Alice's band mass `a = ∑_j t_j² μ_A(B_j)` for one pair of packages
(the `bandMassA` of OTQCS/Trial.lean, without the family wrapper). -/
noncomputable def pairMassA : ℝ := ∑ j, t j ^ 2 * (dA.μ (B j)).toReal

/-- Bob's band mass `b = ∑_j t_j² μ_B(B_j)`. -/
noncomputable def pairMassB : ℝ := ∑ j, t j ^ 2 * (dB.μ (B j)).toReal

/-- The joint band mass `c = ∑_j t_j² ν(B_j × B_j)`. -/
noncomputable def pairCross : ℝ := ∑ j, t j ^ 2 * (Jd.ν (B j ×ˢ B j)).toReal

/-- The unnormalized selected word
`w_{st} = ∑_j t_j p_j(h_s) p_j(k_t) v_t` — an algebra element
(06_otqcs.tex, eq wst). -/
noncomputable def selWord : N.A :=
  ∑ j, (t j : ℂ) • (dA.proj (B j) * dB.proj (B j) * dB.v)

/-- The selected vector `ι(w_{st}) ∈ L²` (06_otqcs.tex, eq wst). -/
noncomputable def selVec : N.H := N.ι (selWord dA dB B t)

open Classical in
/-- The selected state `z_{st}`: the normalized selected vector when
the common mass is positive, the trace vector (a fixed unit default)
when it vanishes (06_otqcs.tex, eqs zst + c-zero; the default is never
passed to a physical branch — eq common-index-mass gives such branches
zero mass). -/
noncomputable def selState : N.H :=
  if pairCross dA dB Jd B t = 0 then N.ι 1
  else ((‖selVec dA dB B t‖⁻¹ : ℝ) : ℂ) • selVec dA dB B t

/-- The rounded modulus `k_t^♯ = ∑_j t_j p_j(k_t)` — a bounded algebra
element (06_otqcs.tex, eq rounded-y). -/
noncomputable def selSharp : N.A := ∑ j, (t j : ℂ) • dB.proj (B j)

/-- The rounded polar vector `ỹ_t = b_t^{−1/2} k_t^♯ v_t`
(06_otqcs.tex, eq rounded-y). -/
noncomputable def selYTilde : N.H :=
  (((Real.sqrt (pairMassB dB B t))⁻¹ : ℝ) : ℂ) •
    N.ι (selSharp dB B t * dB.v)

/-- The cut modulus `k_t^{cut} = k_t 1_{∪_j B_j}(k_t)` as an L² vector
(06_otqcs.tex, above eq rounding-tails, with the retained window
realized by the band union). -/
noncomputable def selCutVec : N.H :=
  N.Rop (dB.proj (⋃ j, B j)) dB.hvec

/-- `‖w_{st}‖₂² = c_{st}` (06_otqcs.tex, eq w-norm): orthogonality of
the spectral projections, tracial cyclicity, and `p_j(k_t) ≤ v_t v_t*`. -/
theorem selVec_normSq (hB : IsBandFamily B t) :
    ‖selVec dA dB B t‖ ^ 2 = pairCross dA dB Jd B t := by
  rw [selVec, ← inner_self_eq_norm_sq (𝕜 := ℂ) (N.ι (selWord dA dB B t)),
    N.ι_inner (selWord dA dB B t) (selWord dA dB B t), selWord,
    wnorm_core dA dB Jd B t hB, RCLike.re_to_complex, Complex.ofReal_re,
    pairCross]

/-- `‖z_{st} − ỹ_t‖₂² ≤ 4 Γ_{st}` (06_otqcs.tex, eqs z-rounded-y +
c-zero): at positive common mass via `2 − 2√(c/b) ≤ 2(b−c)/b ≤
4(b−c) ≤ 4Γ`, and at zero common mass via `Γ = a + b ≥ 1` against the
crude bound `‖z − ỹ‖² ≤ 4`; the constant `4` covers both branches. -/
theorem selState_sub_yTilde (hB : IsBandFamily B t)
    (ha : 1 / 2 ≤ pairMassA dA B t) (hb : 1 / 2 ≤ pairMassB dB B t) :
    ‖selState dA dB Jd B t - selYTilde dB B t‖ ^ 2 ≤
      4 * (pairMassA dA B t + pairMassB dB B t -
        2 * pairCross dA dB Jd B t) := by
  classical
  have hprobB : IsProbabilityMeasure dB.μ := dB.μ_prob
  have hprobA : IsProbabilityMeasure dA.μ := dA.μ_prob
  have hprobJ : IsProbabilityMeasure Jd.ν := Jd.ν_prob
  set a := pairMassA dA B t with ha_def
  set b := pairMassB dB B t with hb_def
  set c := pairCross dA dB Jd B t with hc_def
  have hb0 : 0 < b := by linarith
  have ha0 : 0 < a := by linarith
  have hbne : b ≠ 0 := ne_of_gt hb0
  have hc0 : 0 ≤ c := by
    rw [hc_def, pairCross]
    exact Finset.sum_nonneg fun j _ => by positivity
  -- marginal bounds: c ≤ b, c ≤ a
  have hcle_b : c ≤ b := by
    rw [hc_def, hb_def, pairCross, pairMassB]
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg (t j))
    apply ENNReal.toReal_mono (measure_ne_top dB.μ (B j))
    rw [← Jd.margB, Measure.map_apply measurable_snd (hB.meas j)]
    exact measure_mono fun p hp => Set.mem_preimage.mpr hp.2
  have hcle_a : c ≤ a := by
    rw [hc_def, ha_def, pairCross, pairMassA]
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg (t j))
    apply ENNReal.toReal_mono (measure_ne_top dA.μ (B j))
    rw [← Jd.margA, Measure.map_apply measurable_fst (hB.meas j)]
    exact measure_mono fun p hp => Set.mem_preimage.mpr hp.1
  -- ‖selVec‖ = √c
  have hsvnorm : ‖selVec dA dB B t‖ = Real.sqrt c := by
    rw [← Real.sqrt_sq (norm_nonneg (selVec dA dB B t)), selVec_normSq dA dB Jd B t hB]
  -- projection facts
  set pA : Fin m → N.A := fun j => dA.proj (B j) with hpA
  set pB : Fin m → N.A := fun j => dB.proj (B j) with hpB
  have hidemB : ∀ j, pB j * pB j = pB j := by
    intro j; simp only [hpB]
    rw [dB.proj_inter (B j) (B j) (hB.meas j) (hB.meas j), Set.inter_self]
  have horthB : ∀ i j : Fin m, i ≠ j → pB i * pB j = 0 := by
    intro i j hij; simp only [hpB]
    rw [dB.proj_inter (B i) (B j) (hB.meas i) (hB.meas j),
      Set.disjoint_iff_inter_eq_empty.mp (hB.disj hij), dB.proj_empty]
  have hstarB : ∀ j, star (pB j) = pB j := by
    intro j; simp only [hpB]; exact dB.proj_star (B j)
  have hrab : ∀ j, pB j * (dB.v * star dB.v) = pB j := by
    intro j; simp only [hpB]
    have h := dB.absorb (B j) (hB.meas j) (hB.pos j)
    have hs := congrArg star h
    rw [star_mul, star_mul, star_star, dB.proj_star] at hs
    exact hs
  -- Key inner product: ⟪selVec, ι(selSharp * v)⟫ = c
  have hZY : ⟪selVec dA dB B t, N.ι (selSharp dB B t * dB.v)⟫_ℂ = ((c : ℝ) : ℂ) := by
    rw [hc_def, pairCross, selVec, N.ι_inner]
    have hstarA : ∀ j, star (pA j) = pA j := by
      intro j; simp only [hpA]; exact dA.proj_star (B j)
    set aw : Fin m → N.A := fun i => star dB.v * pB i * pA i with haw
    set as : Fin m → N.A := fun j => pB j * dB.v with has
    have hstarword : star (selWord dA dB B t) = ∑ i, (t i : ℂ) • aw i := by
      rw [selWord, star_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [star_smul, Complex.star_def, Complex.conj_ofReal, haw]
      simp only [hpA, hpB]
      rw [star_mul, star_mul, dA.proj_star, dB.proj_star, mul_assoc]
    have hsharpv : selSharp dB B t * dB.v = ∑ j, (t j : ℂ) • as j := by
      rw [selSharp, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_mul_assoc, has]
    rw [hstarword, hsharpv, Fintype.sum_mul_sum, map_sum]
    have hterm : ∀ i, N.τ (∑ j, ((t i : ℂ) • aw i) * ((t j : ℂ) • as j))
        = ((t i ^ 2 * (Jd.ν (B i ×ˢ B i)).toReal : ℝ) : ℂ) := by
      intro i
      rw [map_sum, Finset.sum_eq_single i]
      · rw [smul_mul_smul_comm, map_smul, smul_eq_mul, haw, has]
        have hτ : N.τ (star dB.v * pB i * pA i * (pB i * dB.v))
            = ((Jd.ν (B i ×ˢ B i)).toReal : ℂ) := by
          rw [show star dB.v * pB i * pA i * (pB i * dB.v)
              = star dB.v * (pB i * pA i * pB i * dB.v) by noncomm_ring,
            N.τ_mul_comm (star dB.v) (pB i * pA i * pB i * dB.v),
            show pB i * pA i * pB i * dB.v * star dB.v
              = pB i * pA i * (pB i * (dB.v * star dB.v)) by noncomm_ring, hrab i,
            N.τ_mul_comm (pB i * pA i) (pB i),
            show pB i * (pB i * pA i) = (pB i * pB i) * pA i by noncomm_ring,
            hidemB i, N.τ_mul_comm (pB i) (pA i)]
          simp only [hpA, hpB]
          rw [Jd.cross (B i) (B i) (hB.meas i) (hB.meas i)]
        rw [hτ]; push_cast; ring
      · intro j _ hji
        rw [smul_mul_smul_comm, map_smul, smul_eq_mul, haw, has]
        rw [show star dB.v * pB i * pA i * (pB j * dB.v)
            = star dB.v * (pB i * pA i * pB j * dB.v) by noncomm_ring,
          N.τ_mul_comm (star dB.v) (pB i * pA i * pB j * dB.v),
          show pB i * pA i * pB j * dB.v * star dB.v
            = pB i * pA i * (pB j * (dB.v * star dB.v)) by noncomm_ring, hrab j,
          N.τ_mul_comm (pB i * pA i) (pB j),
          show pB j * (pB i * pA i) = (pB j * pB i) * pA i by noncomm_ring,
          horthB j i hji]
        simp
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [Finset.sum_congr rfl fun i _ => hterm i, ← Complex.ofReal_sum]
  -- ‖ι(selSharp * v)‖² = b
  have hsv_c : ⟪N.ι (selSharp dB B t * dB.v), N.ι (selSharp dB B t * dB.v)⟫_ℂ
      = ((b : ℝ) : ℂ) := by
    rw [hb_def, pairMassB, N.ι_inner]
    set as : Fin m → N.A := fun j => pB j * dB.v with has
    have hsharpv : selSharp dB B t * dB.v = ∑ j, (t j : ℂ) • as j := by
      rw [selSharp, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_mul_assoc, has]
    have hstar : star (selSharp dB B t * dB.v) = ∑ i, (t i : ℂ) • (star dB.v * pB i) := by
      rw [hsharpv, star_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [star_smul, Complex.star_def, Complex.conj_ofReal, has, star_mul, hstarB i]
    rw [hstar, hsharpv, Fintype.sum_mul_sum, map_sum]
    have hterm : ∀ i, N.τ (∑ j, ((t i : ℂ) • (star dB.v * pB i)) * ((t j : ℂ) • as j))
        = ((t i ^ 2 * (dB.μ (B i)).toReal : ℝ) : ℂ) := by
      intro i
      rw [map_sum, Finset.sum_eq_single i]
      · rw [smul_mul_smul_comm, map_smul, smul_eq_mul, has]
        have hτ : N.τ (star dB.v * pB i * (pB i * dB.v)) = ((dB.μ (B i)).toReal : ℂ) := by
          rw [show star dB.v * pB i * (pB i * dB.v)
              = star dB.v * ((pB i * pB i) * dB.v) by noncomm_ring, hidemB i,
            N.τ_mul_comm (star dB.v) (pB i * dB.v),
            show pB i * dB.v * star dB.v = pB i * (dB.v * star dB.v) by noncomm_ring,
            hrab i]
          simp only [hpB]
          rw [dB.proj_trace (B i) (hB.meas i)]
        rw [hτ]; push_cast; ring
      · intro j _ hji
        rw [smul_mul_smul_comm, map_smul, smul_eq_mul, has]
        rw [show star dB.v * pB i * (pB j * dB.v)
            = star dB.v * ((pB i * pB j) * dB.v) by noncomm_ring, horthB i j (Ne.symm hji)]
        simp
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [Finset.sum_congr rfl fun i _ => hterm i, ← Complex.ofReal_sum]
  have hsvn2 : ‖N.ι (selSharp dB B t * dB.v)‖ ^ 2 = b := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (N.ι (selSharp dB B t * dB.v)), hsv_c,
      RCLike.re_to_complex, Complex.ofReal_re]
  have hsvn : ‖N.ι (selSharp dB B t * dB.v)‖ = Real.sqrt b := by
    rw [← Real.sqrt_sq (norm_nonneg (N.ι (selSharp dB B t * dB.v))), hsvn2]
  -- ‖selYTilde‖ = 1
  have hyt_norm : ‖selYTilde dB B t‖ = 1 := by
    rw [selYTilde, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), ← hb_def, hsvn,
      inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hb0))]
  -- branch on common mass
  by_cases hc : c = 0
  · -- zero common mass: selState = ι 1
    have hz_norm : ‖selState dA dB Jd B t‖ = 1 := by
      have hz1 : ‖N.ι (1 : N.A)‖ ^ 2 = 1 := by
        rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (N.ι (1 : N.A)), N.ι_inner, star_one, one_mul,
          N.τ_one, RCLike.re_to_complex, Complex.one_re]
      rw [selState, if_pos hc, ← Real.sqrt_sq (norm_nonneg (N.ι (1 : N.A))), hz1, Real.sqrt_one]
    have htri : ‖selState dA dB Jd B t - selYTilde dB B t‖ ≤ 2 := by
      calc ‖selState dA dB Jd B t - selYTilde dB B t‖
          ≤ ‖selState dA dB Jd B t‖ + ‖selYTilde dB B t‖ := norm_sub_le _ _
        _ = 2 := by rw [hz_norm, hyt_norm]; norm_num
    have h4 : ‖selState dA dB Jd B t - selYTilde dB B t‖ ^ 2 ≤ 4 := by
      nlinarith [norm_nonneg (selState dA dB Jd B t - selYTilde dB B t), htri]
    have hΓ : (1 : ℝ) ≤ a + b - 2 * c := by rw [hc]; linarith
    linarith [h4, hΓ]
  · -- positive common mass
    have hc0' : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hc)
    have hcne : c ≠ 0 := hc
    have hsvpos : 0 < ‖selVec dA dB B t‖ := by
      rw [hsvnorm]; exact Real.sqrt_pos.mpr hc0'
    have hz_norm_pos : ‖selState dA dB Jd B t‖ = 1 := by
      rw [selState, if_neg hc, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity), inv_mul_cancel₀ (ne_of_gt hsvpos)]
    -- re⟪selState, selYTilde⟫ = √(c/b)
    have hsc : Real.sqrt c ^ 2 = c := Real.sq_sqrt (le_of_lt hc0')
    have hscpos : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc0'
    have hkeysq : (‖selVec dA dB B t‖⁻¹ * (Real.sqrt b)⁻¹ * c) ^ 2 = c / b := by
      rw [hsvnorm, mul_pow, mul_pow, inv_pow, inv_pow, Real.sq_sqrt (le_of_lt hc0'),
        Real.sq_sqrt (le_of_lt hb0)]
      field_simp
    have hkeynn : 0 ≤ ‖selVec dA dB B t‖⁻¹ * (Real.sqrt b)⁻¹ * c := by
      rw [hsvnorm]; positivity
    have hkey : ‖selVec dA dB B t‖⁻¹ * (Real.sqrt b)⁻¹ * c = Real.sqrt (c / b) := by
      rw [← Real.sqrt_sq hkeynn, hkeysq]
    have hzy_re : RCLike.re ⟪selState dA dB Jd B t, selYTilde dB B t⟫_ℂ = Real.sqrt (c / b) := by
      rw [selState, if_neg hc, selYTilde, ← hb_def, inner_smul_left, inner_smul_right, hZY,
        Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
        RCLike.re_to_complex, Complex.ofReal_re]
      rw [← hkey]; ring
    have hnormsub : ‖selState dA dB Jd B t - selYTilde dB B t‖ ^ 2
        = 2 - 2 * Real.sqrt (c / b) := by
      rw [norm_sub_sq (𝕜 := ℂ), hz_norm_pos, hyt_norm, hzy_re]; ring
    rw [hnormsub]
    -- 2 - 2√(c/b) ≤ 4(a+b-2c)
    set s := Real.sqrt (c / b) with hs_def
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hub1 : c / b ≤ 1 := (div_le_one hb0).mpr hcle_b
    have hs1 : s ≤ 1 := by
      rw [hs_def, show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt hub1
    have hssq : s ^ 2 = c / b := Real.sq_sqrt (div_nonneg hc0 (le_of_lt hb0))
    have hsu : c / b ≤ s := by nlinarith [hssq, hs0, hs1]
    have hstep2 : 2 - 2 * (c / b) = 2 * (b - c) / b := by field_simp
    have hstep3 : 2 * (b - c) / b ≤ 4 * (b - c) := by
      rw [div_le_iff₀ hb0]
      nlinarith [mul_nonneg (show (0:ℝ) ≤ b - c by linarith) (show (0:ℝ) ≤ 2*b - 1 by linarith)]
    linarith [hsu, hstep2, hstep3, hcle_a]

/-- Omitted-tail identity (06_otqcs.tex, eq rounding-tails, second
bound, in exact form): the cut loss is the off-window second moment,
`‖k_t − k_t^{cut}‖₂² = ∫ b² dμ − ∫_{∪_j B_j} b² dμ` (bounded by
`ρ + L²` at consumption, where the omitted region is the union of the
low window and the high tail). -/
theorem selCutVec_sub (hB : IsBandFamily B t) :
    ‖dB.hvec - selCutVec dB B‖ ^ 2 =
      (∫ b, b ^ 2 ∂dB.μ) - ∫ b in ⋃ j, B j, b ^ 2 ∂dB.μ := by
  classical
  set U : Set ℝ := ⋃ j, B j with hU
  have hUmeas : MeasurableSet U := MeasurableSet.iUnion hB.meas
  set P : N.A := dB.proj U with hP
  set h : N.H := dB.hvec with hh
  set T : N.H →L[ℂ] N.H := N.Rop P with hT
  -- P self-adjoint
  have hPstar : star P = P := dB.proj_star U
  -- P idempotent
  have hPidem : P * P = P := by
    rw [hP, dB.proj_inter U U hUmeas hUmeas, Set.inter_self]
  -- T self-adjoint (adjoint = T)
  have hTadj : ContinuousLinearMap.adjoint T = T := by
    rw [hT, ← ContinuousLinearMap.star_eq_adjoint]
    show star (N.R (MulOpposite.op P)) = N.R (MulOpposite.op P)
    rw [← map_star, ← MulOpposite.op_star, hPstar]
  -- T idempotent
  have hTT : T * T = T := by
    rw [hT]
    show N.R (MulOpposite.op P) * N.R (MulOpposite.op P) = N.R (MulOpposite.op P)
    rw [← map_mul, ← MulOpposite.op_mul, hPidem]
  have hTidem : T (T h) = T h := by
    rw [← ContinuousLinearMap.mul_apply, hTT]
  -- self-adjointness identity
  have hsa : ∀ a b : N.H, ⟪T a, b⟫_ℂ = ⟪a, T b⟫_ℂ := by
    intro a b
    conv_lhs => rw [← hTadj]
    rw [ContinuousLinearMap.adjoint_inner_left]
  have e1 : ⟪T h, h⟫_ℂ = ⟪h, T h⟫_ℂ := hsa h h
  have e2 : ⟪T h, T h⟫_ℂ = ⟪h, T h⟫_ℂ := by rw [hsa h (T h), hTidem]
  have hinner : ⟪h - T h, h - T h⟫_ℂ = ⟪h, h⟫_ℂ - ⟪h, T h⟫_ℂ := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, e1, e2]
    ring
  have hnormsq : ‖h - T h‖ ^ 2 = (⟪h, h⟫_ℂ).re - (⟪h, T h⟫_ℂ).re := by
    have hz := inner_self_eq_norm_sq (𝕜 := ℂ) (h - T h)
    rw [← hz, hinner, RCLike.re_to_complex, Complex.sub_re]
  -- evaluate the two inner products
  have hhh : (⟪h, h⟫_ℂ).re = ∫ b, b ^ 2 ∂dB.μ := by
    have hz := inner_self_eq_norm_sq (𝕜 := ℂ) h
    rw [RCLike.re_to_complex] at hz
    rw [hz, hh, dB.hvec_norm, dB.moment2]
  have hht : (⟪h, T h⟫_ℂ).re = ∫ b in U, b ^ 2 ∂dB.μ := by
    have hp2 : ⟪h, T h⟫_ℂ = ((∫ b in U, b ^ 2 ∂dB.μ : ℝ) : ℂ) :=
      dB.pairing2 U hUmeas
    rw [hp2, Complex.ofReal_re]
  -- assemble
  show ‖h - T h‖ ^ 2 = (∫ b, b ^ 2 ∂dB.μ) - ∫ b in U, b ^ 2 ∂dB.μ
  rw [hnormsq, hhh, hht]

/-- Upward-rounding cost (06_otqcs.tex, eq rounding-tails, first
bound): when every band sits inside `[t_j / r, t_j]` — the shifted-bin
geometry at ratio `r` — the rounded modulus is `(r−1)`-close to the
cut modulus in L², relative to the second moment:
`‖k^♯ − k^{cut}‖₂² ≤ (r − 1)² ‖y‖₂²` (at `r = 1 + α` this is `≤ α²`). -/
theorem selSharp_round (hB : IsBandFamily B t) (r : ℝ) (hr : 1 ≤ r)
    (hband : ∀ j, B j ⊆ Set.Icc (t j / r) (t j)) :
    ‖N.ι (selSharp dB B t) - selCutVec dB B‖ ^ 2 ≤
      (r - 1) ^ 2 * ‖y‖ ^ 2 := by
  classical
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  have hprob : IsProbabilityMeasure dB.μ := dB.μ_prob
  have hUmeas : MeasurableSet (⋃ j, B j) := MeasurableSet.iUnion hB.meas
  -- finite additivity of proj
  have hprojU : dB.proj (⋃ j, B j) = ∑ j, dB.proj (B j) := by
    have key : ∀ s : Finset (Fin m),
        dB.proj (⋃ j ∈ s, B j) = ∑ j ∈ s, dB.proj (B j) := by
      intro s
      induction s using Finset.induction with
      | empty =>
        simp only [Set.iUnion_of_empty, Set.iUnion_empty, Finset.sum_empty,
          Finset.notMem_empty]
        exact dB.proj_empty
      | insert a s ha ih =>
        rw [Finset.set_biUnion_insert, Finset.sum_insert ha, ← ih]
        have hmeas_s : MeasurableSet (⋃ j ∈ s, B j) :=
          Finset.measurableSet_biUnion s (fun j _ => hB.meas j)
        have hdisj : Disjoint (B a) (⋃ j ∈ s, B j) := by
          simp only [Set.disjoint_iUnion_right]
          intro j hjs
          exact hB.disj (fun h => ha (h.symm ▸ hjs))
        exact dB.proj_union (B a) (⋃ j ∈ s, B j) (hB.meas a) hmeas_s hdisj
    have h := key Finset.univ
    simpa only [Finset.mem_univ, Set.iUnion_true] using h
  -- Rop of a sum
  have hRopSum : N.Rop (∑ j, dB.proj (B j)) = ∑ j, N.Rop (dB.proj (B j)) := by
    simp only [StdTracialAlgebra.Rop]
    rw [← map_sum]
    congr 1
    rw [Finset.op_sum]
  -- pairwise inner products
  have hpp : ∀ i j : Fin m, ⟪N.ι (dB.proj (B i)), N.ι (dB.proj (B j))⟫_ℂ
      = if i = j then ((dB.μ (B i)).toReal : ℂ) else 0 := by
    intro i j
    rw [N.ι_inner, dB.proj_star]
    by_cases hij : i = j
    · subst hij
      rw [dB.proj_inter (B i) (B i) (hB.meas i) (hB.meas i), Set.inter_self,
        dB.proj_trace (B i) (hB.meas i), if_pos rfl]
    · rw [dB.proj_inter (B i) (B j) (hB.meas i) (hB.meas j),
        Set.disjoint_iff_inter_eq_empty.mp (hB.disj hij), dB.proj_empty,
        map_zero, if_neg hij]
  -- self-adjointness of Rop(proj (⋃))
  have hPUsa : ∀ a w : N.H,
      ⟪N.Rop (dB.proj (⋃ j, B j)) a, w⟫_ℂ
        = ⟪a, N.Rop (dB.proj (⋃ j, B j)) w⟫_ℂ := by
    intro a w
    have hadj : ContinuousLinearMap.adjoint (N.Rop (dB.proj (⋃ j, B j)))
        = N.Rop (dB.proj (⋃ j, B j)) := by
      rw [← ContinuousLinearMap.star_eq_adjoint]
      show star (N.R (MulOpposite.op (dB.proj (⋃ j, B j))))
          = N.R (MulOpposite.op (dB.proj (⋃ j, B j)))
      rw [← map_star, ← MulOpposite.op_star, dB.proj_star]
    conv_lhs => rw [← hadj]
    rw [ContinuousLinearMap.adjoint_inner_left]
  -- S as an explicit sum
  have hS_sum : N.ι (selSharp dB B t) = ∑ j, (t j : ℂ) • N.ι (dB.proj (B j)) := by
    rw [selSharp, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul]
  -- ‖S‖²
  have hSS_c : ⟪N.ι (selSharp dB B t), N.ι (selSharp dB B t)⟫_ℂ
      = ((∑ j, t j ^ 2 * (dB.μ (B j)).toReal : ℝ) : ℂ) := by
    rw [hS_sum, sum_inner, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum, Finset.sum_eq_single i]
    · rw [inner_smul_left, inner_smul_right, hpp i i, if_pos rfl, Complex.conj_ofReal]
      push_cast; ring
    · intro j _ hji
      rw [inner_smul_left, inner_smul_right, hpp i j, if_neg (Ne.symm hji),
        mul_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hSS : ‖N.ι (selSharp dB B t)‖ ^ 2 = ∑ j, t j ^ 2 * (dB.μ (B j)).toReal := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (N.ι (selSharp dB B t)), hSS_c,
      RCLike.re_to_complex, Complex.ofReal_re]
  -- ⟪ι(proj B i), C⟫ = ∫_{B i} b dμ
  have hiC : ∀ i, ⟪N.ι (dB.proj (B i)), selCutVec dB B⟫_ℂ
      = ((∫ b in B i, b ∂dB.μ : ℝ) : ℂ) := by
    intro i
    have hCU : selCutVec dB B = N.Rop (dB.proj (⋃ j, B j)) dB.hvec := rfl
    rw [hCU, ← hPUsa (N.ι (dB.proj (B i))) dB.hvec]
    have hRi : N.Rop (dB.proj (⋃ j, B j)) (N.ι (dB.proj (B i)))
        = N.ι (dB.proj (B i) * dB.proj (⋃ j, B j)) :=
      N.R_apply (dB.proj (⋃ j, B j)) (dB.proj (B i))
    rw [hRi]
    have hBiU : dB.proj (B i) * dB.proj (⋃ j, B j) = dB.proj (B i) := by
      rw [dB.proj_inter (B i) (⋃ j, B j) (hB.meas i) hUmeas,
        Set.inter_eq_left.mpr (Set.subset_iUnion B i)]
    rw [hBiU]
    exact dB.pairing1 (B i) (hB.meas i)
  -- ⟪S, C⟫
  have hSC_c : ⟪N.ι (selSharp dB B t), selCutVec dB B⟫_ℂ
      = ((∑ j, t j * (∫ b in B j, b ∂dB.μ) : ℝ) : ℂ) := by
    rw [hS_sum, sum_inner, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_left, hiC i, Complex.conj_ofReal, ← Complex.ofReal_mul]
  have hSC_re : RCLike.re ⟪N.ι (selSharp dB B t), selCutVec dB B⟫_ℂ
      = ∑ j, t j * (∫ b in B j, b ∂dB.μ) := by
    rw [hSC_c, RCLike.re_to_complex, Complex.ofReal_re]
  -- Rop(proj U) idempotent
  have hPUidem : N.Rop (dB.proj (⋃ j, B j)) (N.Rop (dB.proj (⋃ j, B j)) dB.hvec)
      = N.Rop (dB.proj (⋃ j, B j)) dB.hvec := by
    rw [← ContinuousLinearMap.mul_apply]
    congr 1
    show N.R (MulOpposite.op (dB.proj (⋃ j, B j)))
        * N.R (MulOpposite.op (dB.proj (⋃ j, B j)))
        = N.R (MulOpposite.op (dB.proj (⋃ j, B j)))
    rw [← map_mul, ← MulOpposite.op_mul,
      dB.proj_inter (⋃ j, B j) (⋃ j, B j) hUmeas hUmeas, Set.inter_self]
  -- ‖C‖²
  have hCC : ‖selCutVec dB B‖ ^ 2 = ∫ b in ⋃ j, B j, b ^ 2 ∂dB.μ := by
    have hC_c : ⟪selCutVec dB B, selCutVec dB B⟫_ℂ
        = ((∫ b in ⋃ j, B j, b ^ 2 ∂dB.μ : ℝ) : ℂ) := by
      show ⟪N.Rop (dB.proj (⋃ j, B j)) dB.hvec,
          N.Rop (dB.proj (⋃ j, B j)) dB.hvec⟫_ℂ = _
      rw [hPUsa dB.hvec (N.Rop (dB.proj (⋃ j, B j)) dB.hvec), hPUidem]
      exact dB.pairing2 (⋃ j, B j) hUmeas
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (selCutVec dB B), hC_c,
      RCLike.re_to_complex, Complex.ofReal_re]
  -- ‖S - C‖²
  have hnorm : ‖N.ι (selSharp dB B t) - selCutVec dB B‖ ^ 2
      = (∑ j, t j ^ 2 * (dB.μ (B j)).toReal)
        - 2 * (∑ j, t j * (∫ b in B j, b ∂dB.μ))
        + (∫ b in ⋃ j, B j, b ^ 2 ∂dB.μ) := by
    rw [norm_sub_sq (𝕜 := ℂ), hSS, hCC, hSC_re]
  -- E = ∑ m2
  have hE_eq : (∫ b in ⋃ j, B j, b ^ 2 ∂dB.μ) = ∑ j, ∫ b in B j, b ^ 2 ∂dB.μ := by
    have hc : ((∫ b in ⋃ j, B j, b ^ 2 ∂dB.μ : ℝ) : ℂ)
        = ((∑ j, ∫ b in B j, b ^ 2 ∂dB.μ : ℝ) : ℂ) := by
      rw [← dB.pairing2 (⋃ j, B j) hUmeas]
      have hsplit : N.Rop (dB.proj (⋃ j, B j)) dB.hvec
          = ∑ j, N.Rop (dB.proj (B j)) dB.hvec := by
        rw [hprojU, hRopSum, ContinuousLinearMap.sum_apply]
      rw [hsplit, inner_sum, Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun j _ => (dB.pairing2 (B j) (hB.meas j))
    exact_mod_cast hc
  -- E ≤ ‖y‖²  (via selCutVec_sub which is now already proved above in the file)
  have hEbound : (∫ b in ⋃ j, B j, b ^ 2 ∂dB.μ) ≤ ‖y‖ ^ 2 := by
    have hcv := selCutVec_sub dB B t hB
    rw [dB.moment2] at hcv
    have hnn : (0 : ℝ) ≤ ‖dB.hvec - selCutVec dB B‖ ^ 2 := sq_nonneg _
    linarith
  -- per-band bound
  have hbb : ∀ j : Fin m,
      t j ^ 2 * (dB.μ (B j)).toReal - 2 * (t j) * (∫ b in B j, b ∂dB.μ)
          + (∫ b in B j, b ^ 2 ∂dB.μ)
        ≤ (r - 1) ^ 2 * (∫ b in B j, b ^ 2 ∂dB.μ) := by
    intro j
    have hmeasB := hB.meas j
    have hbd_b : ∀ᵐ b ∂(dB.μ.restrict (B j)), ‖b‖ ≤ t j := by
      filter_upwards [ae_restrict_mem hmeasB] with b hb
      have hbj := hband j hb
      rw [Real.norm_eq_abs, abs_le]
      refine ⟨?_, hbj.2⟩
      have : (0 : ℝ) < t j / r := div_pos (hB.tpos j) hr0
      linarith [hbj.1, hB.tpos j]
    have hbd_b2 : ∀ᵐ b ∂(dB.μ.restrict (B j)), ‖b ^ 2‖ ≤ t j ^ 2 := by
      filter_upwards [ae_restrict_mem hmeasB] with b hb
      have hbj := hband j hb
      have hb0 : 0 ≤ b := le_trans (le_of_lt (div_pos (hB.tpos j) hr0)) hbj.1
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg b)]
      nlinarith [hbj.2, hb0]
    have hInt_b : IntegrableOn (fun b => b) (B j) dB.μ :=
      Measure.integrableOn_of_bounded (measure_ne_top dB.μ (B j))
        measurable_id.aestronglyMeasurable hbd_b
    have hInt_b2 : IntegrableOn (fun b => b ^ 2) (B j) dB.μ :=
      Measure.integrableOn_of_bounded (measure_ne_top dB.μ (B j))
        ((measurable_id.pow_const 2).aestronglyMeasurable) hbd_b2
    have hIconst : IntegrableOn (fun _ => (t j) ^ 2) (B j) dB.μ :=
      integrableOn_const (measure_ne_top dB.μ (B j))
    -- expansion identity
    have hid : (∫ b in B j, ((t j) ^ 2 - 2 * (t j) * b + b ^ 2) ∂dB.μ)
        = t j ^ 2 * (dB.μ (B j)).toReal - 2 * (t j) * (∫ b in B j, b ∂dB.μ)
          + (∫ b in B j, b ^ 2 ∂dB.μ) := by
      have hIsub : IntegrableOn (fun b => (t j) ^ 2 - 2 * (t j) * b) (B j) dB.μ :=
        hIconst.sub (hInt_b.const_mul (2 * (t j)))
      rw [integral_add hIsub hInt_b2,
        integral_sub hIconst (hInt_b.const_mul (2 * (t j))),
        integral_const_mul, setIntegral_const, measureReal_def, smul_eq_mul]
      ring
    -- pointwise bound
    have hpt : ∀ b ∈ B j, (t j) ^ 2 - 2 * (t j) * b + b ^ 2 ≤ (r - 1) ^ 2 * b ^ 2 := by
      intro b hb
      have hbj := hband j hb
      have hb0 : 0 < b := lt_of_lt_of_le (div_pos (hB.tpos j) hr0) hbj.1
      have htrb : t j ≤ r * b := by
        nlinarith [(div_le_iff₀ hr0).mp hbj.1]
      have hub : t j - b ≤ (r - 1) * b := by nlinarith [htrb]
      have hlb : 0 ≤ t j - b := by linarith [hbj.2]
      have hrb : 0 ≤ (r - 1) * b :=
        mul_nonneg (by linarith) (le_of_lt hb0)
      nlinarith [mul_nonneg (show (0:ℝ) ≤ (r - 1) * b - (t j - b) by linarith)
        (show (0:ℝ) ≤ (r - 1) * b + (t j - b) by linarith)]
    have hmono : (∫ b in B j, ((t j) ^ 2 - 2 * (t j) * b + b ^ 2) ∂dB.μ)
        ≤ (∫ b in B j, (r - 1) ^ 2 * b ^ 2 ∂dB.μ) := by
      apply setIntegral_mono_on _ (hInt_b2.const_mul ((r - 1) ^ 2)) hmeasB hpt
      exact ((integrableOn_const (measure_ne_top dB.μ (B j))).sub
        (hInt_b.const_mul (2 * (t j)))).add hInt_b2
    rw [integral_const_mul] at hmono
    rw [hid] at hmono
    exact hmono
  -- assembly
  have hLHS : (∑ j, t j ^ 2 * (dB.μ (B j)).toReal)
      - 2 * (∑ j, t j * (∫ b in B j, b ∂dB.μ))
      + (∑ j, ∫ b in B j, b ^ 2 ∂dB.μ)
      = ∑ j, (t j ^ 2 * (dB.μ (B j)).toReal - 2 * (t j) * (∫ b in B j, b ∂dB.μ)
          + (∫ b in B j, b ^ 2 ∂dB.μ)) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    congr 1
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hbb_sum : (∑ j, t j ^ 2 * (dB.μ (B j)).toReal)
      - 2 * (∑ j, t j * (∫ b in B j, b ∂dB.μ))
      + (∑ j, ∫ b in B j, b ^ 2 ∂dB.μ)
      ≤ (r - 1) ^ 2 * (∑ j, ∫ b in B j, b ^ 2 ∂dB.μ) := by
    rw [hLHS, Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => hbb j)
  -- conclude
  have hMbound : (∑ j, ∫ b in B j, b ^ 2 ∂dB.μ) ≤ ‖y‖ ^ 2 := by
    rw [← hE_eq]; exact hEbound
  have hr2 : (0 : ℝ) ≤ (r - 1) ^ 2 := sq_nonneg _
  calc ‖N.ι (selSharp dB B t) - selCutVec dB B‖ ^ 2
      = (∑ j, t j ^ 2 * (dB.μ (B j)).toReal)
        - 2 * (∑ j, t j * (∫ b in B j, b ∂dB.μ))
        + (∑ j, ∫ b in B j, b ^ 2 ∂dB.μ) := by rw [hnorm, hE_eq]
    _ ≤ (r - 1) ^ 2 * (∑ j, ∫ b in B j, b ^ 2 ∂dB.μ) := hbb_sum
    _ ≤ (r - 1) ^ 2 * ‖y‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_left hMbound hr2

/-- Right multiplication by the polar isometry preserves the norms of
the rounded and exact moduli and their combinations (06_otqcs.tex,
display below eq normalization-inequality: "right multiplication by
`v_t` preserves the norms needed here"): the supports of `k_t` and
`k_t^♯` lie below `s(k_t) = v_t v_t*`. -/
theorem Rop_v_norm (hB : IsBandFamily B t) (c₁ c₂ : ℂ) :
    ‖N.Rop dB.v (c₁ • N.ι (selSharp dB B t) + c₂ • dB.hvec)‖ =
      ‖c₁ • N.ι (selSharp dB B t) + c₂ • dB.hvec‖ := by
  classical
  set T : N.H →L[ℂ] N.H := N.Rop dB.v with hT
  set ξ : N.H := c₁ • N.ι (selSharp dB B t) + c₂ • dB.hvec with hξ
  -- right-support absorption per band: proj (B j) * (v * star v) = proj (B j)
  have hrab : ∀ j, dB.proj (B j) * (dB.v * star dB.v) = dB.proj (B j) := by
    intro j
    have h := dB.absorb (B j) (hB.meas j) (hB.pos j)
    have hs := congrArg star h
    rw [star_mul, star_mul, star_star, dB.proj_star] at hs
    exact hs
  -- selSharp * (v * star v) = selSharp
  have hsharp : selSharp dB B t * (dB.v * star dB.v) = selSharp dB B t := by
    simp only [selSharp, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_assoc, hrab j]
  -- adjoint T = Rop (star v)
  have hTadj : ContinuousLinearMap.adjoint T = N.Rop (star dB.v) := by
    rw [hT, ← ContinuousLinearMap.star_eq_adjoint]
    show star (N.R (MulOpposite.op dB.v)) = N.Rop (star dB.v)
    rw [← map_star, ← MulOpposite.op_star]
    rfl
  -- (adjoint T) (T ξ) = Rop(v * star v) ξ
  have hcomp : (ContinuousLinearMap.adjoint T) (T ξ) = N.Rop (dB.v * star dB.v) ξ := by
    rw [hTadj, hT, ← ContinuousLinearMap.mul_apply]
    congr 1
    show N.R (MulOpposite.op (star dB.v)) * N.R (MulOpposite.op dB.v)
        = N.R (MulOpposite.op (dB.v * star dB.v))
    rw [← map_mul, ← MulOpposite.op_mul]
  -- Rop (v*star v) fixes ι(selSharp)
  have hfixS : N.Rop (dB.v * star dB.v) (N.ι (selSharp dB B t))
      = N.ι (selSharp dB B t) := by
    show N.R (MulOpposite.op (dB.v * star dB.v)) (N.ι (selSharp dB B t))
        = N.ι (selSharp dB B t)
    rw [N.R_apply, hsharp]
  -- Rop (v*star v) fixes ξ
  have hfix : N.Rop (dB.v * star dB.v) ξ = ξ := by
    rw [hξ, map_add, map_smul, map_smul, hfixS, dB.supp_vec]
  -- inner products equal
  have hii : ⟪T ξ, T ξ⟫_ℂ = ⟪ξ, ξ⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, hcomp, hfix]
  -- norms squared equal
  have hnsq : ‖T ξ‖ ^ 2 = ‖ξ‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (T ξ),
      ← inner_self_eq_norm_sq (𝕜 := ℂ) ξ, hii]
  -- conclude
  rw [← Real.sqrt_sq (norm_nonneg (T ξ)), ← Real.sqrt_sq (norm_nonneg ξ), hnsq]

/-! ### Proof-side helpers (not manuscript statements) -/

/-- The selected state is a unit vector in both branches of its definition:
the trace vector at zero common mass, the normalized selected vector otherwise
(using `‖w_{st}‖² = c_{st} ≠ 0`). Consumed by the `∑ r` conjunct of
`compile_decomposition` (OTQCS/Compile). -/
theorem selState_norm (hB : IsBandFamily B t) : ‖selState dA dB Jd B t‖ = 1 := by
  classical
  by_cases hc : pairCross dA dB Jd B t = 0
  · have hz1 : ‖N.ι (1 : N.A)‖ ^ 2 = 1 := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (N.ι (1 : N.A)), N.ι_inner, star_one, one_mul,
        N.τ_one, RCLike.re_to_complex, Complex.one_re]
    rw [selState, if_pos hc, ← Real.sqrt_sq (norm_nonneg (N.ι (1 : N.A))), hz1, Real.sqrt_one]
  · have hsq := selVec_normSq dA dB Jd B t hB
    have hne : ‖selVec dA dB B t‖ ≠ 0 := by
      intro h0
      apply hc
      rw [← hsq, h0]
      norm_num
    rw [selState, if_neg hc, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), inv_mul_cancel₀ hne]

/-- Proof-side helper: `c_{st} · ⟪z_{st}, L(A) R(B) z_{st}⟫ = τ(w_{st}* A w_{st} B)` in both
branches of `z_{st}` (at zero common mass both sides vanish, since `‖ι w‖² = c = 0`). -/
theorem selState_pairing (hB : IsBandFamily B t) (A B' : N.A) :
    pairCross dA dB Jd B t *
        (⟪selState dA dB Jd B t, N.L A (N.Rop B' (selState dA dB Jd B t))⟫_ℂ).re
      = (N.τ (star (selWord dA dB B t) * (A * selWord dA dB B t * B'))).re := by
  classical
  have hsq := selVec_normSq dA dB Jd B t hB
  have hLR : ⟪selVec dA dB B t, N.L A (N.Rop B' (selVec dA dB B t))⟫_ℂ
      = N.τ (star (selWord dA dB B t) * (A * selWord dA dB B t * B')) :=
    N.inner_L_R _ _ _ _
  by_cases hc : pairCross dA dB Jd B t = 0
  · have hv0 : selVec dA dB B t = 0 := by
      have h2 : ‖selVec dA dB B t‖ ^ 2 = 0 := by rw [hsq, hc]
      exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h2)
    rw [hc, zero_mul, ← hLR, hv0, inner_zero_left, Complex.zero_re]
  · have hne : ‖selVec dA dB B t‖ ≠ 0 := by
      intro h0; apply hc; rw [← hsq, h0]; norm_num
    have hz : selState dA dB Jd B t
        = ((‖selVec dA dB B t‖⁻¹ : ℝ) : ℂ) • selVec dA dB B t := by
      rw [selState, if_neg hc]
    rw [hz, map_smul, map_smul, inner_smul_left, inner_smul_right, hLR, Complex.conj_ofReal,
      ← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul, ← mul_assoc]
    have hcoef : pairCross dA dB Jd B t *
        (‖selVec dA dB B t‖⁻¹ * ‖selVec dA dB B t‖⁻¹) = 1 := by
      rw [← hsq]; field_simp
    rw [hcoef, one_mul]

end Selected

end CommutingRepetition
