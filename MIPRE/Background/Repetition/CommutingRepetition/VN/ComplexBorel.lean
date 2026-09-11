/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/ComplexBorel.lean
-/
/-
# Complex-valued bounded Borel calculus of a self-adjoint operator (stage E4 infrastructure)

`cbfc E hE G := bfc (Re G) + i · bfc (Im G)` for bounded measurable
`G : ℝ → ℂ`, on top of the real Borel calculus `bfc` of
`VN/BorelCalculus.lean`.  Multiplicative, unital, `*`-compatible,
`⟪ξ, G(E) ξ⟫ = ∫ G dν_ξ`, `‖G(E) ξ‖² = ∫ |G|² dν_ξ`, eigenvectors
(`E ξ = c ξ ⇒ G(E) ξ = G(c) ξ`), dominated convergence, commutation and
membership in a von Neumann algebra containing `E`.  Used for the modular
group `Δ^{it} = ((2−R)/R)^{it}` of Rieffel–van Daele (`VN/Modular/ModularGroup.lean`).
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.JointSpectral
import MIPRE.Background.Repetition.CommutingRepetition.VN.Generated
import MIPRE.Background.Repetition.CommutingRepetition.VN.Cutdown

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace BorelCalc

open scoped InnerProductSpace ComplexConjugate
open Filter Topology MeasureTheory

set_option linter.unusedSectionVars false

variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [CompleteSpace 𝓗]

/-! ## Bounded measurable complex functions -/

/-- Bounded measurable complex-valued functions on `ℝ`. -/
def CBdd (G : ℝ → ℂ) : Prop := Measurable G ∧ ∃ C, ∀ t, ‖G t‖ ≤ C

namespace CBdd

variable {G H : ℝ → ℂ}

theorem measurable (hG : CBdd G) : Measurable G := hG.1

theorem re (hG : CBdd G) : Bdd fun t => (G t).re := by
  obtain ⟨hm, C, hC⟩ := hG
  exact ⟨Complex.measurable_re.comp hm, C, fun t => (Complex.abs_re_le_norm _).trans (hC t)⟩

theorem im (hG : CBdd G) : Bdd fun t => (G t).im := by
  obtain ⟨hm, C, hC⟩ := hG
  exact ⟨Complex.measurable_im.comp hm, C, fun t => (Complex.abs_im_le_norm _).trans (hC t)⟩

theorem const (z : ℂ) : CBdd fun _ => z := ⟨measurable_const, ‖z‖, fun _ => le_rfl⟩

theorem one : CBdd fun _ : ℝ => (1 : ℂ) := const 1

theorem ofReal {g : ℝ → ℝ} (hg : Bdd g) : CBdd fun t => (g t : ℂ) := by
  obtain ⟨hm, C, hC⟩ := hg
  exact ⟨Complex.measurable_ofReal.comp hm, C, fun t => by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hC t⟩

theorem add (hG : CBdd G) (hH : CBdd H) : CBdd (G + H) := by
  obtain ⟨hm, C, hC⟩ := hG
  obtain ⟨hm', C', hC'⟩ := hH
  exact ⟨hm.add hm', C + C', fun t => (norm_add_le _ _).trans (add_le_add (hC t) (hC' t))⟩

theorem sub (hG : CBdd G) (hH : CBdd H) : CBdd (G - H) := by
  obtain ⟨hm, C, hC⟩ := hG
  obtain ⟨hm', C', hC'⟩ := hH
  exact ⟨hm.sub hm', C + C', fun t => (norm_sub_le _ _).trans (add_le_add (hC t) (hC' t))⟩

theorem mul (hG : CBdd G) (hH : CBdd H) : CBdd (G * H) := by
  obtain ⟨hm, C, hC⟩ := hG
  obtain ⟨hm', C', hC'⟩ := hH
  refine ⟨hm.mul hm', C * C', fun t => ?_⟩
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_mul (hC t) (hC' t) (norm_nonneg _) ((norm_nonneg _).trans (hC t))

theorem conjugate (hG : CBdd G) : CBdd fun t => conj (G t) := by
  obtain ⟨hm, C, hC⟩ := hG
  exact ⟨Complex.continuous_conj.measurable.comp hm, C, fun t => by
    rw [Complex.norm_conj]; exact hC t⟩

theorem smul (c : ℂ) (hG : CBdd G) : CBdd fun t => c * G t := by
  obtain ⟨hm, C, hC⟩ := hG
  exact ⟨measurable_const.mul hm, ‖c‖ * C, fun t => by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC t) (norm_nonneg _)⟩

theorem norm_sq (hG : CBdd G) : Bdd fun t => ‖G t‖ ^ 2 := by
  obtain ⟨hm, C, hC⟩ := hG
  refine ⟨(hm.norm.pow_const 2), C ^ 2, fun t => ?_⟩
  rw [abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hC t) 2

theorem integrable (hG : CBdd G) (μ : Measure ℝ) [IsFiniteMeasure μ] : Integrable G μ := by
  obtain ⟨hm, C, hC⟩ := hG
  exact Integrable.of_bound hm.aestronglyMeasurable C (Eventually.of_forall hC)

end CBdd

/-! ## The complex Borel calculus -/

variable (E : 𝓗 →L[ℂ] 𝓗) (hE : IsSelfAdjoint E)

/-- `G(E) := (Re G)(E) + i (Im G)(E)`. -/
noncomputable def cbfc (G : ℝ → ℂ) : 𝓗 →L[ℂ] 𝓗 :=
  bfc E hE (fun t => (G t).re) + Complex.I • bfc E hE (fun t => (G t).im)

theorem cbfc_ofReal (g : ℝ → ℝ) : cbfc E hE (fun t => (g t : ℂ)) = bfc E hE g := by
  unfold cbfc
  have h1 : (fun t => ((g t : ℂ)).re) = g := by funext t; exact Complex.ofReal_re _
  have h2 : (fun t => ((g t : ℂ)).im) = 0 := by funext t; exact Complex.ofReal_im _
  rw [h1, h2, bfc_zero, smul_zero, add_zero]

/-- Rewriting the operator inside `cbfc` (the self-adjointness proof is transported). -/
theorem cbfc_congr_op {E E' : 𝓗 →L[ℂ] 𝓗} (h : E = E') (hE : IsSelfAdjoint E)
    (hE' : IsSelfAdjoint E') (G : ℝ → ℂ) : cbfc E hE G = cbfc E' hE' G := by
  subst h; rfl

theorem cbfc_const (z : ℂ) : cbfc E hE (fun _ => z) = z • 1 := by
  unfold cbfc
  rw [bfc_const, bfc_const, smul_smul]
  conv_rhs => rw [← Complex.re_add_im z, add_smul, mul_comm]

theorem cbfc_one : cbfc E hE (fun _ => (1 : ℂ)) = 1 := by
  rw [cbfc_const, one_smul]

theorem cbfc_add {G H : ℝ → ℂ} (hG : CBdd G) (hH : CBdd H) :
    cbfc E hE (G + H) = cbfc E hE G + cbfc E hE H := by
  unfold cbfc
  have h1 : (fun t => ((G + H) t).re) = (fun t => (G t).re) + fun t => (H t).re := by
    funext t; simp
  have h2 : (fun t => ((G + H) t).im) = (fun t => (G t).im) + fun t => (H t).im := by
    funext t; simp
  rw [h1, h2, bfc_add E hE hG.re hH.re, bfc_add E hE hG.im hH.im, smul_add]
  abel

theorem cbfc_sub {G H : ℝ → ℂ} (hG : CBdd G) (hH : CBdd H) :
    cbfc E hE (G - H) = cbfc E hE G - cbfc E hE H := by
  unfold cbfc
  have h1 : (fun t => ((G - H) t).re) = (fun t => (G t).re) - fun t => (H t).re := by
    funext t; simp
  have h2 : (fun t => ((G - H) t).im) = (fun t => (G t).im) - fun t => (H t).im := by
    funext t; simp
  rw [h1, h2, bfc_sub E hE hG.re hH.re, bfc_sub E hE hG.im hH.im, smul_sub]
  abel

theorem cbfc_mul {G H : ℝ → ℂ} (hG : CBdd G) (hH : CBdd H) :
    cbfc E hE (G * H) = cbfc E hE G * cbfc E hE H := by
  unfold cbfc
  have h1 : (fun t => ((G * H) t).re) =
      (fun t => (G t).re) * (fun t => (H t).re) - (fun t => (G t).im) * fun t => (H t).im := by
    funext t; simp [Complex.mul_re]
  have h2 : (fun t => ((G * H) t).im) =
      (fun t => (G t).re) * (fun t => (H t).im) + (fun t => (G t).im) * fun t => (H t).re := by
    funext t; simp [Complex.mul_im]
  rw [h1, h2, bfc_sub E hE (hG.re.mul hH.re) (hG.im.mul hH.im),
    bfc_add E hE (hG.re.mul hH.im) (hG.im.mul hH.re), bfc_mul E hE hG.re hH.re,
    bfc_mul E hE hG.im hH.im, bfc_mul E hE hG.re hH.im, bfc_mul E hE hG.im hH.re]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, Complex.I_mul_I,
    neg_one_smul, smul_add]
  abel

theorem cbfc_star {G : ℝ → ℂ} (hG : CBdd G) :
    star (cbfc E hE G) = cbfc E hE fun t => conj (G t) := by
  unfold cbfc
  have h1 : (fun t => (conj (G t)).re) = fun t => (G t).re := by funext t; simp
  have h2 : (fun t => (conj (G t)).im) = fun t => (-1 : ℝ) * (G t).im := by funext t; simp
  rw [h1, h2, bfc_const_mul E hE (-1) hG.im, star_add, star_smul,
    (bfc_isSelfAdjoint E hE hG.re).star_eq, (bfc_isSelfAdjoint E hE hG.im).star_eq,
    Complex.star_def, Complex.conj_I, Complex.ofReal_neg, Complex.ofReal_one, neg_one_smul,
    neg_smul, smul_neg]

theorem cbfc_comm {G H : ℝ → ℂ} (hG : CBdd G) (hH : CBdd H) :
    cbfc E hE G * cbfc E hE H = cbfc E hE H * cbfc E hE G := by
  rw [← cbfc_mul E hE hG hH, ← cbfc_mul E hE hH hG, mul_comm]

/-- `⟪ξ, G(E) ξ⟫ = ∫ G dν_ξ`. -/
theorem inner_cbfc_self {G : ℝ → ℂ} (hG : CBdd G) (ξ : 𝓗) :
    ⟪ξ, cbfc E hE G ξ⟫_ℂ = ∫ t, G t ∂(ν E hE ξ) := by
  have h := integral_coe_re_add_coe_im (𝕜 := ℂ) (hG.integrable (ν E hE ξ))
  rw [integral_ofReal, integral_ofReal] at h
  unfold cbfc
  rw [_root_.add_apply, _root_.smul_apply, inner_add_right, inner_smul_right,
    inner_bfc_self E hE hG.re, inner_bfc_self E hE hG.im, Q, Q, ← h, mul_comm]
  rfl

/-- `‖G(E) ξ‖² = ∫ |G|² dν_ξ`. -/
theorem norm_sq_cbfc {G : ℝ → ℂ} (hG : CBdd G) (ξ : 𝓗) :
    ‖cbfc E hE G ξ‖ ^ 2 = ∫ t, ‖G t‖ ^ 2 ∂(ν E hE ξ) := by
  have h1 : ⟪cbfc E hE G ξ, cbfc E hE G ξ⟫_ℂ =
      ⟪ξ, cbfc E hE (fun t => conj (G t) * G t) ξ⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
      cbfc_star E hE hG, ← mul_apply_eq_comp, ← cbfc_mul E hE hG.conjugate hG]
    rfl
  have h2 : (fun t => conj (G t) * G t) = fun t => ((‖G t‖ ^ 2 : ℝ) : ℂ) := by
    funext t
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), h1, h2, inner_cbfc_self E hE (CBdd.ofReal hG.norm_sq),
    ← integral_re ((CBdd.ofReal hG.norm_sq).integrable _)]
  congr 1

/-- Norm bound: `‖G(E)‖ ≤ sup |G|`. -/
theorem norm_cbfc_le {G : ℝ → ℂ} (hG : CBdd G) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ t, ‖G t‖ ≤ C) :
    ‖cbfc E hE G‖ ≤ C := by
  refine ContinuousLinearMap.opNorm_le_bound _ hC0 fun ξ => ?_
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
  rw [norm_sq_cbfc E hE hG, mul_pow]
  have : ∫ t, ‖G t‖ ^ 2 ∂(ν E hE ξ) ≤ ∫ _, C ^ 2 ∂(ν E hE ξ) :=
    integral_mono (integrable_of_bdd hG.norm_sq.measurable (fun t => by
      rw [abs_of_nonneg (by positivity)]; exact pow_le_pow_left₀ (norm_nonneg _) (hC t) 2))
      (integrable_const _) fun t => pow_le_pow_left₀ (norm_nonneg _) (hC t) 2
  rw [integral_const, smul_eq_mul, ν_univ_real] at this
  linarith

/-! ## Eigenvectors -/

/-- The spectral measure is concentrated on `[-‖E‖, ‖E‖]`. -/
theorem ae_norm_le (ξ : 𝓗) : ∀ᵐ t ∂(ν E hE ξ), |t| ≤ ‖E‖ := by
  rw [ae_iff]
  refine measure_mono_null (fun t ht => ?_) (ν_compl_spectrum E hE ξ)
  intro hs
  refine ht ?_
  have h1 := spectrum.norm_le_norm_mul_of_mem hs
  have h2 : ‖(1 : 𝓗 →L[ℂ] 𝓗)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  rw [Real.norm_eq_abs] at h1
  calc |t| ≤ ‖E‖ * ‖(1 : 𝓗 →L[ℂ] 𝓗)‖ := h1
    _ ≤ ‖E‖ * 1 := by gcongr
    _ = ‖E‖ := mul_one _

/-- The spectral measure of an eigenvector is concentrated at the eigenvalue. -/
theorem ae_eq_of_eigen {ξ : 𝓗} {c : ℝ} (hξ : E ξ = (c : ℂ) • ξ) :
    ∀ᵐ t ∂(ν E hE ξ), t = c := by
  have h0 : ∫ t, (t - c) ^ 2 ∂(ν E hE ξ) = 0 := by
    rw [integral_ν E hE ξ (by fun_prop)]
    have : cfc (fun t : ℝ => (t - c) ^ 2) E = (E - algebraMap ℝ _ c) ^ 2 := by
      rw [cfc_pow (fun t : ℝ => t - c) 2 E, cfc_sub (fun t : ℝ => t) (fun _ => c) E, cfc_id' ℝ E,
        cfc_const c E]
    have hz : (E - algebraMap ℝ (𝓗 →L[ℂ] 𝓗) c) ξ = 0 := by
      have hc : c • ξ = (c : ℂ) • ξ := RCLike.real_smul_eq_coe_smul (K := ℂ) c ξ
      rw [_root_.sub_apply, Algebra.algebraMap_eq_smul_one, _root_.smul_apply, one_apply_eq_self,
        hξ, hc, sub_self]
    rw [this, pow_two, mul_apply_eq_comp, hz, map_zero, inner_zero_right, Complex.zero_re]
  have hnn : 0 ≤ fun t : ℝ => (t - c) ^ 2 := fun t => sq_nonneg _
  have hint : Integrable (fun t : ℝ => (t - c) ^ 2) (ν E hE ξ) := by
    refine Integrable.of_bound (by fun_prop) ((‖E‖ + |c|) ^ 2) ?_
    filter_upwards [ae_norm_le E hE ξ] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs (t - c)]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    calc |t - c| ≤ |t| + |c| := abs_sub _ _
      _ ≤ ‖E‖ + |c| := add_le_add ht le_rfl
  have := (integral_eq_zero_iff_of_nonneg hnn hint).mp h0
  filter_upwards [this] with t ht
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp ht)

/-- `E ξ = c ξ` implies `G(E) ξ = G(c) ξ`. -/
theorem cbfc_eigen {G : ℝ → ℂ} (hG : CBdd G) {ξ : 𝓗} {c : ℝ} (hξ : E ξ = (c : ℂ) • ξ) :
    cbfc E hE G ξ = G c • ξ := by
  have h : cbfc E hE G ξ - G c • ξ = cbfc E hE (G - fun _ => G c) ξ := by
    rw [cbfc_sub E hE hG (CBdd.const _), cbfc_const, _root_.sub_apply, _root_.smul_apply,
      one_apply_eq_self]
  rw [← sub_eq_zero, h, ← norm_eq_zero, ← pow_eq_zero_iff two_ne_zero,
    norm_sq_cbfc E hE (hG.sub (CBdd.const _))]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [ae_eq_of_eigen E hE hξ] with t ht
  simp [ht]

theorem bfc_eigen {g : ℝ → ℝ} (hg : Bdd g) {ξ : 𝓗} {c : ℝ} (hξ : E ξ = (c : ℂ) • ξ) :
    bfc E hE g ξ = (g c : ℂ) • ξ := by
  rw [← cbfc_ofReal E hE g]
  exact cbfc_eigen E hE (CBdd.ofReal hg) hξ

/-! ## Commutation, membership, dominated convergence -/

theorem commute_cbfc {T : 𝓗 →L[ℂ] 𝓗} (hT : Commute E T) {G : ℝ → ℂ} (hG : CBdd G) :
    Commute (cbfc E hE G) T := by
  unfold cbfc
  exact (commute_bfc E hE hT hG.re).add_left ((commute_bfc E hE hT hG.im).smul_left _)

theorem cbfc_mem (N : VonNeumannAlgebra 𝓗) (hEN : E ∈ N) {G : ℝ → ℂ} (hG : CBdd G) :
    cbfc E hE G ∈ N := by
  unfold cbfc
  exact add_mem (VN.bfc_mem N hE hEN hG.re) (VN.smul_mem_vn N _ (VN.bfc_mem N hE hEN hG.im))

/-- Dominated convergence: uniformly bounded `G i → Ginf` pointwise gives `G i (E) ξ → Ginf(E) ξ`. -/
theorem tendsto_cbfc {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {G : ι → ℝ → ℂ}
    {Ginf : ℝ → ℂ} (hG : ∀ i, CBdd (G i)) (hGinf : CBdd Ginf) {C : ℝ} (hC : ∀ i t, ‖G i t‖ ≤ C)
    (hCinf : ∀ t, ‖Ginf t‖ ≤ C) (hlim : ∀ t, Tendsto (fun i => G i t) l (𝓝 (Ginf t))) (ξ : 𝓗) :
    Tendsto (fun i => cbfc E hE (G i) ξ) l (𝓝 (cbfc E hE Ginf ξ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : Tendsto (fun i => ‖cbfc E hE (G i) ξ - cbfc E hE Ginf ξ‖ ^ 2) l (𝓝 0) := by
    have heq : ∀ i, ‖cbfc E hE (G i) ξ - cbfc E hE Ginf ξ‖ ^ 2 =
        ∫ t, ‖G i t - Ginf t‖ ^ 2 ∂(ν E hE ξ) := fun i => by
      rw [← _root_.sub_apply, ← cbfc_sub E hE (hG i) hGinf, norm_sq_cbfc E hE ((hG i).sub hGinf)]
      rfl
    simp only [heq]
    have h0 : (0 : ℝ) = ∫ _t, (0 : ℝ) ∂(ν E hE ξ) := by simp
    rw [h0]
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (2 * C) ^ 2)
      (Eventually.of_forall fun i => ((hG i).sub hGinf).norm_sq.measurable.aestronglyMeasurable)
      (Eventually.of_forall fun i => Eventually.of_forall fun t => ?_) (integrable_const _)
      (Eventually.of_forall fun t => ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      calc ‖G i t - Ginf t‖ ≤ ‖G i t‖ + ‖Ginf t‖ := norm_sub_le _ _
        _ ≤ C + C := add_le_add (hC i t) (hCinf t)
        _ = 2 * C := by ring
    · have : Tendsto (fun i => G i t - Ginf t) l (𝓝 0) := by
        simpa using (hlim t).sub_const (Ginf t)
      simpa using (this.norm).pow 2
  have := hsq.sqrt
  simpa only [Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] using this

end BorelCalc

end CommutingRepetition
