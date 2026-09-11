/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/Modular/UnitaryLog.lean
-/
/-
# The logarithm of a unitary (density stage E6.3)

For a unitary `u` in a von Neumann algebra `N` we build a self-adjoint `b ∈ N` with
`0 ≤ b ≤ 2π` and `e^{ib} = u`.

The branch of the argument is discontinuous on the circle, so a *single* joint Borel symbol in
`(Re u, Im u)` cannot be continuous — and the composition rule `cbfc_jbfc` needs a continuous
inner symbol. The fix is to encode the angle in two commuting operators: its absolute value
`X = arccos(Re u)` (spectrum in `[0, π]`) and the sign of `Im u`, i.e. the spectral projection
`E = 1_{[0,∞)}(Im u)` (spectrum in `[0,1]`). The required symbol
`F(x, q) = 2π + x(2q − 1) − 2πq` is then a polynomial in the clamped variables, hence
continuous, and equals the angle on the joint spectrum (where `q ∈ {0,1}`).
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.Modular.CentralExp

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace VN

namespace Modular

open scoped InnerProductSpace ComplexConjugate Real
open Filter Topology MeasureTheory BorelCalc

set_option linter.unusedSectionVars false

/-! ## The scalar symbols -/

/-- Clamp to `[0, π]`. -/
noncomputable def clP (x : ℝ) : ℝ := max 0 (min x π)

/-- Clamp to `[0, 1]`. -/
noncomputable def clU (q : ℝ) : ℝ := max 0 (min q 1)

theorem clP_nonneg (x : ℝ) : 0 ≤ clP x := le_max_left _ _

theorem clP_le_pi (x : ℝ) : clP x ≤ π := max_le Real.pi_nonneg (min_le_right _ _)

theorem continuous_clP : Continuous clP := by unfold clP; fun_prop

theorem bdd_clP : Bdd clP :=
  Bdd.of_continuous continuous_clP (C := π) fun x => by
    rw [abs_le]
    exact ⟨by linarith [clP_nonneg x, Real.pi_nonneg], clP_le_pi x⟩

theorem clP_eq_self {x : ℝ} (h : x ∈ Set.Icc (0 : ℝ) π) : clP x = x := by
  unfold clP
  rw [min_eq_left h.2, max_eq_right h.1]

theorem clU_nonneg (q : ℝ) : 0 ≤ clU q := le_max_left _ _

theorem clU_le_one (q : ℝ) : clU q ≤ 1 := max_le zero_le_one (min_le_right _ _)

theorem continuous_clU : Continuous clU := by unfold clU; fun_prop

theorem bdd_clU : Bdd clU :=
  Bdd.of_continuous continuous_clU (C := 1) fun q => by
    rw [abs_le]
    exact ⟨by linarith [clU_nonneg q], clU_le_one q⟩

theorem clU_eq_self {q : ℝ} (h : q ∈ Set.Icc (0 : ℝ) 1) : clU q = q := by
  unfold clU
  rw [min_eq_left h.2, max_eq_right h.1]

/-- The symbol of the logarithm: `2π + x(2q − 1) − 2πq`, which is `x` at `q = 1` and
`2π − x` at `q = 0`. -/
noncomputable def logSym (p : ℝ × ℝ) : ℝ :=
  2 * π + clP p.1 * (2 * clU p.2 - 1) - 2 * π * clU p.2

theorem continuous_logSym : Continuous logSym := by
  unfold logSym
  exact ((continuous_const.add ((continuous_clP.comp continuous_fst).mul
    ((continuous_const.mul (continuous_clU.comp continuous_snd)).sub continuous_const))).sub
      (continuous_const.mul (continuous_clU.comp continuous_snd)))

theorem logSym_nonneg (p : ℝ × ℝ) : 0 ≤ logSym p := by
  have h1 : 0 ≤ clP p.1 := clP_nonneg _
  have h2 : clP p.1 ≤ π := clP_le_pi _
  have h3 : 0 ≤ clU p.2 := clU_nonneg _
  have h4 : clU p.2 ≤ 1 := clU_le_one _
  have hπ : 0 < π := Real.pi_pos
  unfold logSym
  rcases le_total (1 / 2 : ℝ) (clU p.2) with h | h
  · nlinarith
  · nlinarith

theorem logSym_le (p : ℝ × ℝ) : logSym p ≤ 2 * π := by
  have h1 : 0 ≤ clP p.1 := clP_nonneg _
  have h2 : clP p.1 ≤ π := clP_le_pi _
  have h3 : 0 ≤ clU p.2 := clU_nonneg _
  have h4 : clU p.2 ≤ 1 := clU_le_one _
  have hπ : 0 < π := Real.pi_pos
  unfold logSym
  rcases le_total (1 / 2 : ℝ) (clU p.2) with h | h
  · nlinarith
  · nlinarith

theorem bdd2_logSym : Bdd2 logSym :=
  Bdd2.of_continuous continuous_logSym (C := 2 * π) fun p => by
    rw [abs_le]
    exact ⟨by linarith [logSym_nonneg p, Real.pi_pos], logSym_le p⟩

/-- `e^{i·arg} = cos + i sin` for a real argument. -/
theorem exp_I_ofReal (x : ℝ) :
    Complex.exp (Complex.I * (x : ℂ)) = (Real.cos x : ℂ) + Complex.I * (Real.sin x : ℂ) := by
  rw [mul_comm, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  ring

/-- The key pointwise identity, valid where the sign variable is `0` or `1`. -/
theorem exp_I_logSym {p : ℝ × ℝ} (hq : clU p.2 = 0 ∨ clU p.2 = 1) :
    Complex.exp (Complex.I * (logSym p : ℂ)) =
      (Real.cos (clP p.1) : ℂ) +
        Complex.I * (((2 * clU p.2 - 1) * Real.sin (clP p.1) : ℝ) : ℂ) := by
  rcases hq with h | h
  · have hs : logSym p = 2 * π - clP p.1 := by rw [logSym, h]; ring
    rw [hs, h]
    have e : ((2 * π - clP p.1 : ℝ) : ℂ) = 2 * π - (clP p.1 : ℂ) := by push_cast; ring
    rw [e, mul_sub, Complex.exp_sub]
    have h2 : Complex.exp (Complex.I * (2 * π)) = 1 := by
      rw [mul_comm]
      exact Complex.exp_two_pi_mul_I
    rw [h2, one_div, ← Complex.exp_neg, ← mul_neg]
    have e2 : -(clP p.1 : ℂ) = ((-clP p.1 : ℝ) : ℂ) := by push_cast; ring
    rw [e2, exp_I_ofReal, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  · have hs : logSym p = clP p.1 := by rw [logSym, h]; ring
    rw [hs, h, exp_I_ofReal]
    push_cast
    ring

/-! ## The real and imaginary parts of a unitary -/

section Unitary

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (u : K →L[ℂ] K)

/-- `Re u = (u + u*)/2`. -/
noncomputable def reU : K →L[ℂ] K := (1 / 2 : ℂ) • (u + star u)

/-- `Im u = i(u* − u)/2`. -/
noncomputable def imU : K →L[ℂ] K := (-(1 / 2 : ℂ) * Complex.I) • (u - star u)

theorem isSelfAdjoint_reU : IsSelfAdjoint (reU u) := isSelfAdjoint_half_add_star u

theorem isSelfAdjoint_imU : IsSelfAdjoint (imU u) := isSelfAdjoint_half_I_sub_star u

theorem u_eq_reU_add_imU : u = reU u + Complex.I • imU u := eq_sa_add_I_smul_sa u

theorem norm_apply_eq_of_star_mul (hu1 : star u * u = 1) (x : K) : ‖u x‖ = ‖x‖ := by
  have h : ⟪u x, u x⟫_ℂ = ⟪x, x⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
      ← mul_apply_eq_comp, hu1, one_apply_eq_self]
  have h2 : ‖u x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), h]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

theorem norm_le_one_of_star_mul (hu1 : star u * u = 1) : ‖u‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [norm_apply_eq_of_star_mul u hu1, one_mul]

theorem norm_star_le_one (hu2 : u * star u = 1) : ‖star u‖ ≤ 1 :=
  norm_le_one_of_star_mul (star u) (by rw [star_star]; exact hu2)

theorem norm_reU_le_one (hu1 : star u * u = 1) (hu2 : u * star u = 1) : ‖reU u‖ ≤ 1 := by
  have h := norm_add_le u (star u)
  have h1 := norm_le_one_of_star_mul u hu1
  have h2 := norm_star_le_one u hu2
  rw [reU, norm_smul]
  have hc : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [hc]
  nlinarith

theorem norm_imU_le_one (hu1 : star u * u = 1) (hu2 : u * star u = 1) : ‖imU u‖ ≤ 1 := by
  have h := norm_sub_le u (star u)
  have h1 := norm_le_one_of_star_mul u hu1
  have h2 := norm_star_le_one u hu2
  rw [imU, norm_smul]
  have hc : ‖(-(1 / 2 : ℂ) * Complex.I)‖ = 1 / 2 := by
    rw [norm_mul, Complex.norm_I, mul_one, norm_neg]
    norm_num
  rw [hc]
  nlinarith

theorem commute_self_star (hu1 : star u * u = 1) (hu2 : u * star u = 1) :
    Commute u (star u) := by rw [Commute, SemiconjBy, hu1, hu2]

theorem commute_reU_imU (hu1 : star u * u = 1) (hu2 : u * star u = 1) :
    Commute (reU u) (imU u) := by
  have h := commute_self_star u hu1 hu2
  have h1 : Commute (u + star u) (u - star u) :=
    Commute.add_left ((Commute.refl u).sub_right h) (h.symm.sub_right (Commute.refl (star u)))
  exact (h1.smul_left _).smul_right _

theorem reU_sq_add_imU_sq (hu1 : star u * u = 1) (hu2 : u * star u = 1) :
    reU u * reU u + imU u * imU u = 1 := by
  have hsq : ∀ (c : ℂ) (x : K →L[ℂ] K), (c • x) * (c • x) = (c * c) • (x * x) := fun c x => by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  have h2A : (2 : K →L[ℂ] K) = ((2 : ℂ)) • 1 := by rw [two_smul, one_add_one_eq_two]
  have hp : (u + star u) * (u + star u) = u * u + star u * star u + 2 := by
    rw [mul_add, add_mul, add_mul, hu1, hu2, ← one_add_one_eq_two]
    abel
  have hm : (u - star u) * (u - star u) = u * u + star u * star u - 2 := by
    rw [mul_sub, sub_mul, sub_mul, hu1, hu2, ← one_add_one_eq_two]
    abel
  rw [reU, imU, hsq, hsq, hp, hm, h2A]
  have e1 : (1 / 2 : ℂ) * (1 / 2 : ℂ) = 1 / 4 := by norm_num
  have e2 : (-(1 / 2 : ℂ) * Complex.I) * (-(1 / 2 : ℂ) * Complex.I) = -(1 / 4) := by
    rw [mul_mul_mul_comm, Complex.I_mul_I]
    norm_num
  rw [e1, e2]
  module

/-! ## The angle and the sign -/

/-- `|arg u| = arccos (Re u)`, with spectrum in `[0, π]`. -/
noncomputable def angU : K →L[ℂ] K := cfc Real.arccos (reU u)

/-- The sign of the imaginary part: the spectral projection `1_{[0,∞)}(Im u)`. -/
noncomputable def sgnU : K →L[ℂ] K := P (imU u) (isSelfAdjoint_imU u) (Set.Ici 0)

theorem isSelfAdjoint_angU : IsSelfAdjoint (angU u) := cfc_predicate _ _

theorem isSelfAdjoint_sgnU : IsSelfAdjoint (sgnU u) := P_isSelfAdjoint _ _ _

theorem bdd_arccos_clamp : Bdd fun y => Real.arccos (clamp 1 y) :=
  Bdd.of_continuous (Real.continuous_arccos.comp (continuous_clamp 1)) (C := π) fun y => by
    rw [abs_le]
    exact ⟨by linarith [Real.arccos_nonneg (clamp 1 y), Real.pi_nonneg],
      Real.arccos_le_pi (clamp 1 y)⟩

theorem angU_eq_bfc (hu1 : star u * u = 1) (hu2 : u * star u = 1) :
    angU u = bfc (reU u) (isSelfAdjoint_reU u) (fun y => Real.arccos (clamp 1 y)) := by
  rw [bfc_cfc (reU u) (isSelfAdjoint_reU u) bdd_arccos_clamp
    (Real.continuous_arccos.comp (continuous_clamp 1))]
  refine (cfc_congr fun y hy => ?_).symm
  rw [clamp_eq_of_abs_le ((abs_le_of_mem_spectrum hy).trans (norm_reU_le_one u hu1 hu2))]

theorem angU_nonneg (hu1 : star u * u = 1) (hu2 : u * star u = 1) : 0 ≤ angU u := by
  rw [angU_eq_bfc u hu1 hu2]
  exact bfc_nonneg _ _ bdd_arccos_clamp fun y => Real.arccos_nonneg _

theorem norm_angU_le (hu1 : star u * u = 1) (hu2 : u * star u = 1) : ‖angU u‖ ≤ π := by
  rw [angU_eq_bfc u hu1 hu2]
  refine norm_bfc_le _ _ bdd_arccos_clamp fun y => ?_
  rw [abs_le]
  exact ⟨by linarith [Real.arccos_nonneg (clamp 1 y), Real.pi_nonneg],
    Real.arccos_le_pi (clamp 1 y)⟩

theorem spectrum_angU (hu1 : star u * u = 1) (hu2 : u * star u = 1) :
    spectrum ℝ (angU u) ⊆ Set.Icc 0 π := fun _ hl =>
  ⟨spectrum_nonneg_of_nonneg (angU_nonneg u hu1 hu2) hl,
    (abs_le.mp (abs_le_of_mem_spectrum hl)).2.trans (norm_angU_le u hu1 hu2)⟩

theorem spectrum_sgnU : spectrum ℝ (sgnU u) ⊆ Set.Icc 0 1 := fun _ hl =>
  ⟨spectrum_nonneg_of_nonneg (P_nonneg _ _ _) hl,
    (abs_le.mp (abs_le_of_mem_spectrum hl)).2.trans (P_norm_le_one _ _ _)⟩

theorem commute_angU_sgnU (hu1 : star u * u = 1) (hu2 : u * star u = 1) :
    Commute (angU u) (sgnU u) := by
  rw [angU_eq_bfc u hu1 hu2, sgnU, P]
  exact commute_bfc_bfc (reU u) (imU u) (isSelfAdjoint_reU u) (isSelfAdjoint_imU u)
    (commute_reU_imU u hu1 hu2) bdd_arccos_clamp (Bdd.indicator measurableSet_Ici)

end Unitary

/-! ## A vanishing joint symbol is a.e. zero -/

section AeZero

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {E₁ E₂ : K →L[ℂ] K} (h₁ : IsSelfAdjoint E₁) (h₂ : IsSelfAdjoint E₂) (hcm : Commute E₁ E₂)

include h₁ h₂ hcm in
theorem ae_eq_zero_of_jbfc_eq_zero {F : ℝ × ℝ → ℝ} (hF : Bdd2 F)
    (h : jbfc E₁ E₂ h₁ h₂ hcm F = 0) (ζ : K) :
    ∀ᵐ p ∂(νP E₁ E₂ h₁ h₂ hcm ζ), F p = 0 := by
  have hFsq : Bdd2 fun p => F p ^ 2 := by
    have e : (fun p => F p ^ 2) = F * F := by funext p; rw [pow_two]; rfl
    rw [e]; exact hF.mul hF
  have h1 : ∫ p, F p ^ 2 ∂(νP E₁ E₂ h₁ h₂ hcm ζ) = 0 := by
    rw [← norm_sq_jbfc E₁ E₂ h₁ h₂ hcm hF ζ, h, zero_apply, norm_zero,
      zero_pow (two_ne_zero : (2 : ℕ) ≠ 0)]
  have h2 := (integral_eq_zero_iff_of_nonneg (fun p => sq_nonneg (F p))
    (hFsq.integrable _)).mp h1
  filter_upwards [h2] with p hp
  exact pow_eq_zero_iff (two_ne_zero : (2 : ℕ) ≠ 0) |>.mp hp

end AeZero

/-! ## The logarithm -/

section Log

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (u : K →L[ℂ] K) (hu1 : star u * u = 1) (hu2 : u * star u = 1)

/-- **The logarithm of a unitary**: `-i log u`, with `0 ≤ · ≤ 2π` and `e^{i·} = u`. -/
noncomputable def ulog : K →L[ℂ] K :=
  jbfc (angU u) (sgnU u) (isSelfAdjoint_angU u) (isSelfAdjoint_sgnU u)
    (commute_angU_sgnU u hu1 hu2) logSym

theorem isSelfAdjoint_ulog : IsSelfAdjoint (ulog u hu1 hu2) :=
  jbfc_isSelfAdjoint _ _ _ _ _ bdd2_logSym

theorem ulog_nonneg : 0 ≤ ulog u hu1 hu2 :=
  jbfc_nonneg _ _ _ _ _ bdd2_logSym logSym_nonneg

theorem ulog_le : ulog u hu1 hu2 ≤ ((2 * π : ℝ) : ℂ) • 1 := by
  rw [← jbfc_const (angU u) (sgnU u) (isSelfAdjoint_angU u) (isSelfAdjoint_sgnU u)
    (commute_angU_sgnU u hu1 hu2) (2 * π)]
  exact jbfc_mono _ _ _ _ _ bdd2_logSym (Bdd2.const _) logSym_le

theorem reU_mem {N : VonNeumannAlgebra K} (hu : u ∈ N) : reU u ∈ N :=
  VN.smul_mem_vn N _ (add_mem hu (star_mem hu))

theorem imU_mem {N : VonNeumannAlgebra K} (hu : u ∈ N) : imU u ∈ N :=
  VN.smul_mem_vn N _ (sub_mem hu (star_mem hu))

theorem angU_mem {N : VonNeumannAlgebra K} (hu : u ∈ N) : angU u ∈ N :=
  VN.cfc_real_mem N (reU_mem u hu) _

theorem sgnU_mem {N : VonNeumannAlgebra K} (hu : u ∈ N) : sgnU u ∈ N :=
  VN.bfc_mem N (isSelfAdjoint_imU u) (imU_mem u hu) (Bdd.indicator measurableSet_Ici)

theorem ulog_mem {N : VonNeumannAlgebra K} (hu : u ∈ N) : ulog u hu1 hu2 ∈ N :=
  jbfc_mem _ _ _ _ _ N (angU_mem u hu) (sgnU_mem u hu) bdd2_logSym

theorem commute_ulog {T : K →L[ℂ] K} (h1 : Commute u T) (h2 : Commute (star u) T) :
    Commute (ulog u hu1 hu2) T := by
  have hre : Commute (reU u) T := (h1.add_left h2).smul_left _
  have him : Commute (imU u) T := (h1.sub_left h2).smul_left _
  refine commute_jbfc _ _ _ _ _ ?_ ?_ bdd2_logSym
  · exact hre.cfc_real _
  · exact commute_bfc _ _ him (Bdd.indicator measurableSet_Ici)

/-! ### Identifying the symbols -/

theorem bdd_cos_clP : Bdd fun x => Real.cos (clP x) :=
  Bdd.of_continuous (Real.continuous_cos.comp continuous_clP) (C := 1) fun _ =>
    Real.abs_cos_le_one _

theorem bdd_sin_clP : Bdd fun x => Real.sin (clP x) :=
  Bdd.of_continuous (Real.continuous_sin.comp continuous_clP) (C := 1) fun _ =>
    Real.abs_sin_le_one _

theorem bdd_sign_clU : Bdd fun q => 2 * clU q - 1 :=
  Bdd.of_continuous ((continuous_const.mul continuous_clU).sub continuous_const) (C := 1)
    fun q => by
      rw [abs_le]
      exact ⟨by linarith [clU_nonneg q], by linarith [clU_le_one q]⟩

theorem bfc_clU : bfc (sgnU u) (isSelfAdjoint_sgnU u) clU = sgnU u := by
  have hs := isSelfAdjoint_sgnU u
  rw [bfc_cfc _ _ bdd_clU continuous_clU,
    cfc_congr (f := clU) (g := id)
      fun q hq => show clU q = id q from clU_eq_self (spectrum_sgnU u hq),
    cfc_id ℝ (sgnU u) hs]

theorem jbfc_cos_clP :
    jbfc (angU u) (sgnU u) (isSelfAdjoint_angU u) (isSelfAdjoint_sgnU u)
      (commute_angU_sgnU u hu1 hu2) (fun p => Real.cos (clP p.1)) = reU u := by
  have hsre := isSelfAdjoint_reU u
  have hsang := isSelfAdjoint_angU u
  rw [jbfc_fst _ _ _ _ _ bdd_cos_clP,
    bfc_cfc _ _ bdd_cos_clP (Real.continuous_cos.comp continuous_clP),
    cfc_congr (f := fun x => Real.cos (clP x)) (g := Real.cos)
      fun x hx => show Real.cos (clP x) = Real.cos x by
        rw [clP_eq_self (spectrum_angU u hu1 hu2 hx)], angU,
    ← cfc_comp' Real.cos Real.arccos (reU u) Real.continuous_cos.continuousOn
      Real.continuous_arccos.continuousOn,
    cfc_congr (f := fun y => Real.cos (Real.arccos y)) (g := id)
      fun y hy => show Real.cos (Real.arccos y) = id y from
        have h := abs_le.mp ((abs_le_of_mem_spectrum hy).trans (norm_reU_le_one u hu1 hu2))
        Real.cos_arccos h.1 h.2, cfc_id ℝ (reU u) hsre]

theorem jbfc_sin_clP :
    jbfc (angU u) (sgnU u) (isSelfAdjoint_angU u) (isSelfAdjoint_sgnU u)
      (commute_angU_sgnU u hu1 hu2) (fun p => Real.sin (clP p.1)) =
      cfc (fun s : ℝ => |s|) (imU u) := by
  have hsre := isSelfAdjoint_reU u
  have hsim := isSelfAdjoint_imU u
  have hsang := isSelfAdjoint_angU u
  have hcont : Continuous fun y : ℝ => 1 - y ^ 2 := by fun_prop
  have hsq : cfc (fun y : ℝ => 1 - y ^ 2) (reU u) = 1 - reU u * reU u := by
    rw [cfc_sub (fun _ : ℝ => (1 : ℝ)) (fun y : ℝ => y ^ 2) (reU u),
      cfc_const_one ℝ (a := reU u), cfc_pow (fun y : ℝ => y) 2 (reU u),
      cfc_id' ℝ (a := reU u), pow_two]
  have hsq2 : cfc (fun s : ℝ => s ^ 2) (imU u) = imU u * imU u := by
    rw [cfc_pow (fun s : ℝ => s) 2 (imU u), cfc_id' ℝ (a := imU u), pow_two]
  have hkey : 1 - reU u * reU u = imU u * imU u := by
    rw [← reU_sq_add_imU_sq u hu1 hu2]
    abel
  rw [jbfc_fst _ _ _ _ _ bdd_sin_clP,
    bfc_cfc _ _ bdd_sin_clP (Real.continuous_sin.comp continuous_clP),
    cfc_congr (f := fun x => Real.sin (clP x)) (g := Real.sin)
      fun x hx => show Real.sin (clP x) = Real.sin x by
        rw [clP_eq_self (spectrum_angU u hu1 hu2 hx)], angU,
    ← cfc_comp' Real.sin Real.arccos (reU u) Real.continuous_sin.continuousOn
      Real.continuous_arccos.continuousOn,
    cfc_congr (f := fun y => Real.sin (Real.arccos y)) (g := fun y => Real.sqrt (1 - y ^ 2))
      fun y _ => show Real.sin (Real.arccos y) = Real.sqrt (1 - y ^ 2) from Real.sin_arccos y,
    cfc_comp' Real.sqrt (fun y : ℝ => 1 - y ^ 2) (reU u) Real.continuous_sqrt.continuousOn
      hcont.continuousOn,
    hsq, hkey, ← hsq2,
    ← cfc_comp' Real.sqrt (fun s : ℝ => s ^ 2) (imU u) Real.continuous_sqrt.continuousOn
      (by fun_prop : Continuous fun s : ℝ => s ^ 2).continuousOn]
  exact cfc_congr fun s _ => show Real.sqrt (s ^ 2) = |s| from Real.sqrt_sq_eq_abs s

theorem jbfc_sign_clU :
    jbfc (angU u) (sgnU u) (isSelfAdjoint_angU u) (isSelfAdjoint_sgnU u)
      (commute_angU_sgnU u hu1 hu2) (fun p => 2 * clU p.2 - 1) =
      ((2 : ℝ) : ℂ) • sgnU u - 1 := by
  have e : (fun q : ℝ => 2 * clU q - 1) = (fun q : ℝ => 2 * clU q) - (1 : ℝ → ℝ) := rfl
  rw [jbfc_snd _ _ _ _ _ bdd_sign_clU, e,
    bfc_sub (sgnU u) (isSelfAdjoint_sgnU u) (Bdd.const_mul 2 bdd_clU) Bdd.one,
    bfc_const_mul (sgnU u) (isSelfAdjoint_sgnU u) 2 bdd_clU, bfc_one, bfc_clU]

include hu1 hu2 in
/-- The polar decomposition of `Im u`: `(2·1_{[0,∞)}(Im u) − 1)|Im u| = Im u`. -/
theorem sign_mul_abs_imU : (((2 : ℝ) : ℂ) • sgnU u - 1) * cfc (fun s : ℝ => |s|) (imU u) = imU u := by
  have habs : Bdd fun s : ℝ => |clamp 1 s| := by
    refine Bdd.of_continuous (continuous_abs.comp (continuous_clamp 1)) (C := 1) fun s => ?_
    rw [abs_abs]
    exact abs_clamp_le zero_le_one s
  have hind : Bdd fun s : ℝ => 2 * (Set.Ici (0 : ℝ)).indicator (1 : ℝ → ℝ) s - 1 :=
    (Bdd.const_mul 2 (Bdd.indicator measurableSet_Ici)).sub Bdd.one
  have h1 : ((2 : ℝ) : ℂ) • sgnU u - 1 =
      bfc (imU u) (isSelfAdjoint_imU u)
        (fun s => 2 * (Set.Ici (0 : ℝ)).indicator (1 : ℝ → ℝ) s - 1) := by
    have e : (fun s : ℝ => 2 * (Set.Ici (0 : ℝ)).indicator (1 : ℝ → ℝ) s - 1) =
        (fun s : ℝ => 2 * (Set.Ici (0 : ℝ)).indicator (1 : ℝ → ℝ) s) - (1 : ℝ → ℝ) := rfl
    rw [e, bfc_sub (imU u) (isSelfAdjoint_imU u)
        (Bdd.const_mul 2 (Bdd.indicator measurableSet_Ici)) Bdd.one,
      bfc_const_mul (imU u) (isSelfAdjoint_imU u) 2 (Bdd.indicator measurableSet_Ici), bfc_one,
      sgnU, P]
  have hsim := isSelfAdjoint_imU u
  have h2 : cfc (fun s : ℝ => |s|) (imU u) = bfc (imU u) (isSelfAdjoint_imU u)
      (fun s => |clamp 1 s|) := by
    rw [bfc_cfc _ _ habs (continuous_abs.comp (continuous_clamp 1))]
    refine (cfc_congr fun s hs => show |clamp 1 s| = |s| from ?_).symm
    rw [clamp_eq_of_abs_le ((abs_le_of_mem_spectrum hs).trans (norm_imU_le_one u hu1 hu2))]
  rw [h1, h2, ← bfc_mul (imU u) (isSelfAdjoint_imU u) hind habs]
  have hfun : ((fun s : ℝ => 2 * (Set.Ici (0 : ℝ)).indicator (1 : ℝ → ℝ) s - 1) *
      fun s : ℝ => |clamp 1 s|) = clamp 1 := by
    funext s
    by_cases hs : (0 : ℝ) ≤ s
    · have hcl : 0 ≤ clamp 1 s := le_max_of_le_right (le_min hs zero_le_one)
      simp only [Pi.mul_apply, Set.indicator_of_mem (Set.mem_Ici.mpr hs), Pi.one_apply,
        abs_of_nonneg hcl]
      ring
    · have hcl : clamp 1 s ≤ 0 :=
        max_le (by norm_num) ((min_le_left s 1).trans (not_le.mp hs).le)
      simp only [Pi.mul_apply,
        Set.indicator_of_notMem (fun hmem => hs (Set.mem_Ici.mp hmem)), abs_of_nonpos hcl]
      ring
  rw [hfun, bfc_clamp (isSelfAdjoint_imU u) (norm_imU_le_one u hu1 hu2)]

/-! ### `e^{i log u} = u` -/

theorem ae_clU_snd (ζ : K) :
    ∀ᵐ p ∂(νP (angU u) (sgnU u) (isSelfAdjoint_angU u) (isSelfAdjoint_sgnU u)
      (commute_angU_sgnU u hu1 hu2) ζ), clU p.2 = 0 ∨ clU p.2 = 1 := by
  have hG : Bdd2 fun p : ℝ × ℝ => clU p.2 ^ 2 - clU p.2 := by
    have e : (fun p : ℝ × ℝ => clU p.2 ^ 2 - clU p.2) =
        ((fun p : ℝ × ℝ => clU p.2) * fun p : ℝ × ℝ => clU p.2) - fun p : ℝ × ℝ => clU p.2 := by
      funext p; simp only [Pi.sub_apply, Pi.mul_apply]; rw [pow_two]
    rw [e]
    exact ((Bdd2.comp_snd bdd_clU).mul (Bdd2.comp_snd bdd_clU)).sub (Bdd2.comp_snd bdd_clU)
  have h0 : jbfc (angU u) (sgnU u) (isSelfAdjoint_angU u) (isSelfAdjoint_sgnU u)
      (commute_angU_sgnU u hu1 hu2) (fun p => clU p.2 ^ 2 - clU p.2) = 0 := by
    have e : (fun p : ℝ × ℝ => clU p.2 ^ 2 - clU p.2) =
        ((fun p : ℝ × ℝ => clU p.2) * fun p : ℝ × ℝ => clU p.2) - fun p : ℝ × ℝ => clU p.2 := by
      funext p; simp only [Pi.sub_apply, Pi.mul_apply]; rw [pow_two]
    rw [e, jbfc_sub _ _ _ _ _ ((Bdd2.comp_snd bdd_clU).mul (Bdd2.comp_snd bdd_clU))
      (Bdd2.comp_snd bdd_clU), jbfc_mul _ _ _ _ _ (Bdd2.comp_snd bdd_clU) (Bdd2.comp_snd bdd_clU),
      jbfc_snd _ _ _ _ _ bdd_clU, bfc_clU, sub_eq_zero]
    exact (P_idem (imU u) (isSelfAdjoint_imU u) measurableSet_Ici).symm ▸ rfl
  filter_upwards [ae_eq_zero_of_jbfc_eq_zero (isSelfAdjoint_angU u) (isSelfAdjoint_sgnU u)
    (commute_angU_sgnU u hu1 hu2) hG h0 ζ] with p hp
  have h : clU p.2 * (clU p.2 - 1) = 0 := by nlinarith [hp]
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

/-- **`e^{i log u} = u`**. -/
theorem eit_ulog : eit (ulog u hu1 hu2) (isSelfAdjoint_ulog u hu1 hu2) 1 = u := by
  have hF1 : CBdd2 fun p : ℝ × ℝ => eitf 1 (logSym p) :=
    CBdd2.comp (cbdd_eitf 1) bdd2_logSym.1
  have hF2 : CBdd2 fun p : ℝ × ℝ => ((Real.cos (clP p.1) : ℝ) : ℂ) +
      Complex.I * (((2 * clU p.2 - 1) * Real.sin (clP p.1) : ℝ) : ℂ) := by
    refine (CBdd2.ofReal (Bdd2.comp_fst bdd_cos_clP)).add ((CBdd2.const Complex.I).mul
      (CBdd2.ofReal ((Bdd2.comp_snd bdd_sign_clU).mul (Bdd2.comp_fst bdd_sin_clP))))
  unfold eit ulog
  rw [cbfc_jbfc _ _ _ _ _ bdd2_logSym continuous_logSym (cbdd_eitf 1),
    cjbfc_congr_ae _ _ _ _ _ hF1 hF2 fun ζ => ?_]
  · rw [cjbfc]
    have hre : (fun p : ℝ × ℝ => (((Real.cos (clP p.1) : ℝ) : ℂ) +
        Complex.I * (((2 * clU p.2 - 1) * Real.sin (clP p.1) : ℝ) : ℂ)).re) =
        fun p => Real.cos (clP p.1) := by
      funext p
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
    have him : (fun p : ℝ × ℝ => (((Real.cos (clP p.1) : ℝ) : ℂ) +
        Complex.I * (((2 * clU p.2 - 1) * Real.sin (clP p.1) : ℝ) : ℂ)).im) =
        ((fun p : ℝ × ℝ => 2 * clU p.2 - 1) * fun p : ℝ × ℝ => Real.sin (clP p.1)) := by
      funext p
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, zero_mul, one_mul, zero_add, Pi.mul_apply]
    rw [hre, him, jbfc_cos_clP u hu1 hu2,
      jbfc_mul _ _ _ _ _ (Bdd2.comp_snd bdd_sign_clU) (Bdd2.comp_fst bdd_sin_clP),
      jbfc_sign_clU u hu1 hu2, jbfc_sin_clP u hu1 hu2, sign_mul_abs_imU u hu1 hu2,
      ← u_eq_reU_add_imU]
  · filter_upwards [ae_clU_snd u hu1 hu2 ζ] with p hp
    have e : eitf 1 (logSym p) = Complex.exp (Complex.I * (logSym p : ℂ)) := by
      unfold eitf
      rw [one_mul, mul_comm]
    rw [e, exp_I_logSym hp]

/-- Scaling: `e^{it(c·log u)} = e^{i(tc) log u}`. -/
theorem eit_ulog_smul (c t : ℝ) (hcb : IsSelfAdjoint ((c : ℂ) • ulog u hu1 hu2)) :
    eit ((c : ℂ) • ulog u hu1 hu2) hcb t =
      eit (ulog u hu1 hu2) (isSelfAdjoint_ulog u hu1 hu2) (t * c) := by
  have hsm : (c : ℂ) • ulog u hu1 hu2 =
      jbfc (angU u) (sgnU u) (isSelfAdjoint_angU u) (isSelfAdjoint_sgnU u)
        (commute_angU_sgnU u hu1 hu2) (fun p => c * logSym p) :=
    (jbfc_const_mul _ _ _ _ _ c bdd2_logSym).symm
  have h1 : eit ((c : ℂ) • ulog u hu1 hu2) hcb t =
      cjbfc (angU u) (sgnU u) (isSelfAdjoint_angU u) (isSelfAdjoint_sgnU u)
        (commute_angU_sgnU u hu1 hu2) (fun p => eitf t (c * logSym p)) := by
    unfold eit
    rw [BorelCalc.cbfc_congr_op hsm hcb (jbfc_isSelfAdjoint _ _ _ _ _ (bdd2_logSym.const_mul c)),
      cbfc_jbfc _ _ _ _ _ (bdd2_logSym.const_mul c)
        (continuous_const.mul continuous_logSym) (cbdd_eitf t)]
  have h2 : eit (ulog u hu1 hu2) (isSelfAdjoint_ulog u hu1 hu2) (t * c) =
      cjbfc (angU u) (sgnU u) (isSelfAdjoint_angU u) (isSelfAdjoint_sgnU u)
        (commute_angU_sgnU u hu1 hu2) (fun p => eitf (t * c) (logSym p)) :=
    cbfc_jbfc _ _ _ _ _ bdd2_logSym continuous_logSym (cbdd_eitf (t * c))
  rw [h1, h2]
  congr 1
  funext p
  unfold eitf
  congr 2
  push_cast
  ring

end Log

end Modular

end VN

end CommutingRepetition
