/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/OTQCS/Assembly.lean
-/
/-
# OTQCS: assembly lemmas for the root theorem (proof layer of node 1.3.9)

Everything the proof of `otqcs_sampling` (OTQCS/Main.lean) needs beyond the
node statements of slabs α–δ, following the proof of thm otqcs in
06_otqcs.tex, §"Parameter choice and output error":

* transport of vectors, POVMs, the pair law and the alignment defect `Δ` along
  the tracial extension delivered by `exists_modulusFamily`;
* the pure ℓ¹ toolkit — the trivial bound `‖p − q‖₁ ≤ 2` for two laws, the
  branch-decomposition conversion `‖q̂ − q‖₁ ≤ ‖q_z − q‖₁ + 2(1 − cm)`
  (eq otqcs-main from eq common-index-mass), and the vector-to-ℓ¹ step
  `‖p_z − p_u‖₁ ≤ 2‖z − u‖₂` (eq vector-to-l1) for pair laws;
* the selected-state chain `‖z_{st} − u_{st}‖₂ ≤ ‖z − ỹ‖ + ‖ỹ − y‖ + ‖y − u‖`
  (eq selected-state-preopt) with `‖ỹ − y‖ ≤ 2‖k♯ − k‖₂` (normalization
  inequality), `‖k♯ − k^{cut}‖ ≤ α` (eq rounded-y) and
  `‖k^{cut} − k‖² ≤ ρ + L²` (eq rounding-tails);
* the finite bad bound at the trial count `R = ⌈2Z log(2/ξ²)⌉` (eq R-choice);
* the measure-theoretic hypotheses of `grid_disagreement` /
  `exists_common_shift` read off a `JointSpectralData`;
* Jensen for the square root and the final constant bookkeeping in `δ = Δ^{1/6}`
  (eqs cutoff-choice, alpha-choice, Dbar-Delta);
* the trivial resource used in the degenerate range.

All declarations here are proof-side helpers; none is a manuscript statement.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.OTQCS.Compile
import MIPRE.Background.Repetition.CommutingRepetition.OTQCS.Bands
import MIPRE.Background.Repetition.CommutingRepetition.OTQCS.PairLaw
import MIPRE.Background.Repetition.CommutingRepetition.Prelim.Vector

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open MeasureTheory Set
open scoped BigOperators InnerProductSpace

universe u v w

/-! ### Transport along a tracial extension -/

namespace TracialExtension

variable {N : StdTracialAlgebra.{0}} (ext : TracialExtension N)

/-- The pair law is invariant under the spatial extension: `U` intertwines the
left and right actions and preserves inner products. -/
theorem tracialPairLaw_map {S T A B : Type} (u : S → T → N.H) (E : S → A → N.A)
    (F : T → B → N.A) (s : S) (t : T) (a : A) (b : B) :
    tracialPairLaw ext.N' (fun s t => ext.U (u s t)) (fun s a => ext.emb (E s a))
        (fun t b => ext.emb (F t b)) s t a b
      = tracialPairLaw N u E F s t a b := by
  simp only [tracialPairLaw]
  rw [ext.R_emb, ext.L_emb, LinearIsometryEquiv.inner_map_map]

/-- The alignment defect is invariant under the isometry `U`. -/
theorem piAlignment_map {S T : Type} [Fintype S] [Fintype T] (π : S → T → ℝ)
    (u : S → T → N.H) (xv : S → N.H) (yv : T → N.H) :
    piAlignment π (fun s t => ext.U (u s t)) (fun s => ext.U (xv s)) (fun t => ext.U (yv t))
      = piAlignment π u xv yv := by
  simp only [piAlignment, ← map_sub, LinearIsometryEquiv.norm_map]

theorem emb_isPosElem {a : N.A} (ha : IsPosElem a) : IsPosElem (ext.emb a) :=
  ha.starAlgHom_map ext.emb

theorem emb_sum_eq_one {A : Type*} [Fintype A] (E : A → N.A) (hE : (∑ a, E a) = 1) :
    (∑ a, ext.emb (E a)) = 1 := by
  rw [← map_sum, hE, map_one]

end TracialExtension

/-! ### ℓ¹ toolkit -/

/-- Two probability laws on a finite product are at unhalved ℓ¹ distance at most 2. -/
theorem l1_le_two {A B : Type*} [Fintype A] [Fintype B] (p q : A → B → ℝ)
    (hp : ∀ a b, 0 ≤ p a b) (hq : ∀ a b, 0 ≤ q a b)
    (hpsum : (∑ a, ∑ b, p a b) = 1) (hqsum : (∑ a, ∑ b, q a b) = 1) :
    (∑ a, ∑ b, |p a b - q a b|) ≤ 2 := by
  calc (∑ a, ∑ b, |p a b - q a b|) ≤ ∑ a, ∑ b, (p a b + q a b) := by
        apply Finset.sum_le_sum; intro a _; apply Finset.sum_le_sum; intro b _
        exact abs_le.mpr ⟨by linarith [hp a b, hq a b], by linarith [hp a b, hq a b]⟩
    _ = 2 := by simp only [Finset.sum_add_distrib]; rw [hpsum, hqsum]; norm_num

/-- ℓ¹ conversion of a branch decomposition `q̂ = cm · q_z + r` with nonnegative
remainder of mass `1 − cm` against a probability law `q`:
`‖q̂ − q‖₁ ≤ ‖q_z − q‖₁ + 2(1 − cm)` (06_otqcs.tex, the display deriving eq
otqcs-main: "on a bad branch the unhalved ℓ¹ cost is at most 2"). -/
theorem l1_le_of_decomposition {A B : Type*} [Fintype A] [Fintype B]
    (qhat qz q r : A → B → ℝ) (cm : ℝ) (hcm0 : 0 ≤ cm)
    (hr : ∀ a b, 0 ≤ r a b) (hrsum : (∑ a, ∑ b, r a b) = 1 - cm)
    (hq : ∀ a b, 0 ≤ q a b) (hqsum : (∑ a, ∑ b, q a b) = 1)
    (hdec : ∀ a b, qhat a b = cm * qz a b + r a b) :
    (∑ a, ∑ b, |qhat a b - q a b|) ≤ (∑ a, ∑ b, |qz a b - q a b|) + 2 * (1 - cm) := by
  have hcm1 : cm ≤ 1 := by
    have : 0 ≤ ∑ a, ∑ b, r a b :=
      Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hr a b
    linarith
  have hpt : ∀ a b, |qhat a b - q a b| ≤ |qz a b - q a b| + r a b + (1 - cm) * q a b := by
    intro a b
    rw [hdec a b]
    have h1 : cm * qz a b + r a b - q a b
        = cm * (qz a b - q a b) + r a b + (-(1 - cm) * q a b) := by ring
    rw [h1]
    calc |cm * (qz a b - q a b) + r a b + (-(1 - cm) * q a b)|
        ≤ |cm * (qz a b - q a b)| + |r a b| + |-(1 - cm) * q a b| := abs_add_three _ _ _
      _ = cm * |qz a b - q a b| + r a b + (1 - cm) * q a b := by
          rw [abs_mul, abs_of_nonneg hcm0, abs_of_nonneg (hr a b), abs_mul, abs_neg,
            abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - cm), abs_of_nonneg (hq a b)]
      _ ≤ |qz a b - q a b| + r a b + (1 - cm) * q a b := by
          have := mul_le_of_le_one_left (abs_nonneg (qz a b - q a b)) hcm1
          linarith
  calc (∑ a, ∑ b, |qhat a b - q a b|)
      ≤ ∑ a, ∑ b, (|qz a b - q a b| + r a b + (1 - cm) * q a b) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hpt a b
    _ = (∑ a, ∑ b, |qz a b - q a b|) + (∑ a, ∑ b, r a b)
          + (1 - cm) * ∑ a, ∑ b, q a b := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ = (∑ a, ∑ b, |qz a b - q a b|) + 2 * (1 - cm) := by rw [hrsum, hqsum]; ring

/-- **Vector-to-ℓ¹** for pair laws (06_otqcs.tex, eq vector-to-l1): two unit
vectors' pair laws under one pair of full POVMs differ in unhalved ℓ¹ by at most
`2‖z − w‖₂` — the ℓ¹-POVM estimate `sum_abs_re_inner_effect_sub_le` applied to
the commuting product effects `L(A_s^a) R(B_t^b)`. -/
theorem sum_abs_tracialPairLaw_sub_le (N : StdTracialAlgebra.{0}) {S T A B : Type}
    [Fintype A] [Fintype B] (E : S → A → N.A) (F : T → B → N.A)
    (hE : ∀ s a, IsPosElem (E s a)) (hF : ∀ t b, IsPosElem (F t b))
    (hEs : ∀ s, (∑ a, E s a) = 1) (hFs : ∀ t, (∑ b, F t b) = 1) (s : S) (t : T)
    {z w : N.H} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) :
    (∑ a, ∑ b, |tracialPairLaw N (fun _ _ => z) E F s t a b
        - tracialPairLaw N (fun _ _ => w) E F s t a b|) ≤ 2 * ‖z - w‖ := by
  classical
  let Tm : A × B → N.H →L[ℂ] N.H := fun p => N.L (E s p.1) * N.Rop (F t p.2)
  have hposT : ∀ p, (Tm p).IsPositive := by
    intro p
    have hL : (0 : N.H →L[ℂ] N.H) ≤ N.L (E s p.1) := by
      rw [ContinuousLinearMap.le_def]; simpa using N.L_isPositive (hE s p.1)
    have hR : (0 : N.H →L[ℂ] N.H) ≤ N.Rop (F t p.2) := by
      rw [ContinuousLinearMap.le_def]; simpa using N.Rop_isPositive (hF t p.2)
    have hmul := Commute.mul_nonneg hL hR (N.LR_commute (E s p.1) (F t p.2))
    rw [ContinuousLinearMap.le_def, sub_zero] at hmul
    exact hmul
  have hsa : ∀ p, ∀ x y : N.H, ⟪Tm p x, y⟫_ℂ = ⟪x, Tm p y⟫_ℂ :=
    fun p x y => (hposT p).1 x y
  have hpos : ∀ p, ∀ x : N.H, 0 ≤ (⟪x, Tm p x⟫_ℂ).re :=
    fun p x => tracialPairLaw_nonneg N (fun _ _ => x) E F hE hF s t p.1 p.2
  have hsum : (∑ p, Tm p) = 1 := by
    rw [Fintype.sum_prod_type]
    have hL : (∑ a, N.L (E s a)) = 1 := by rw [← map_sum, hEs s, map_one]
    have hR : (∑ b, N.Rop (F t b)) = 1 := by
      simp only [StdTracialAlgebra.Rop]
      rw [← map_sum, ← Finset.op_sum, hFs t, MulOpposite.op_one, map_one]
    calc (∑ a, ∑ b, Tm (a, b)) = (∑ a, N.L (E s a)) * (∑ b, N.Rop (F t b)) := by
          rw [Finset.sum_mul_sum]
      _ = 1 := by rw [hL, hR, one_mul]
  have h := sum_abs_re_inner_effect_sub_le Tm hsa hpos hsum z w hz hw
  rw [Fintype.sum_prod_type] at h
  exact h

/-! ### The finite bad bound at the chosen trial count -/

theorem commonMass_nonneg (a b c Z : ℝ) (R : ℕ) (hZ : 0 < Z) (hc : 0 ≤ c)
    (hle : a + b - c ≤ Z) : 0 ≤ commonMass a b c Z R := by
  unfold commonMass
  refine Finset.sum_nonneg fun j _ => mul_nonneg (pow_nonneg ?_ j) (div_nonneg hc hZ.le)
  rw [sub_nonneg, div_le_one hZ]; exact hle

/-- The trial count `R = ⌈2 Z log(2/ξ²)⌉` makes the exhaustion tail
`2 e^{−R/(2Z)} ≤ ξ²` (06_otqcs.tex, eq R-choice). -/
theorem two_exp_ceil_le (Z ξ : ℝ) (hZ : 0 < Z) (hξ : 0 < ξ) :
    2 * Real.exp (-((⌈2 * Z * Real.log (2 / ξ ^ 2)⌉₊ : ℕ) : ℝ) / (2 * Z)) ≤ ξ ^ 2 := by
  have hpos : 0 < 2 / ξ ^ 2 := by positivity
  have hR : 2 * Z * Real.log (2 / ξ ^ 2) ≤ ((⌈2 * Z * Real.log (2 / ξ ^ 2)⌉₊ : ℕ) : ℝ) :=
    Nat.le_ceil _
  have h1 : -((⌈2 * Z * Real.log (2 / ξ ^ 2)⌉₊ : ℕ) : ℝ) / (2 * Z) ≤ -Real.log (2 / ξ ^ 2) := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  calc 2 * Real.exp (-((⌈2 * Z * Real.log (2 / ξ ^ 2)⌉₊ : ℕ) : ℝ) / (2 * Z))
      ≤ 2 * Real.exp (-Real.log (2 / ξ ^ 2)) := by
        have := Real.exp_le_exp.mpr h1; linarith
    _ = ξ ^ 2 := by
        rw [Real.exp_neg, Real.exp_log hpos]
        field_simp

/-- `1 − cm ≤ 2Γ + ξ²` at `R = ⌈2 Z log(2/ξ²)⌉` (eq finite-bad + eq R-choice). -/
theorem one_sub_commonMass_le (a b c Z ξ : ℝ) (hZ : 0 < Z) (hξ : 0 < ξ)
    (ha : 1 / 2 ≤ a) (hb : 1 / 2 ≤ b) (hc : 0 ≤ c) (hca : c ≤ a) (hcb : c ≤ b)
    (hle : a + b - c ≤ Z) :
    1 - commonMass a b c Z ⌈2 * Z * Real.log (2 / ξ ^ 2)⌉₊ ≤ 2 * (a + b - 2 * c) + ξ ^ 2 := by
  have h := finite_bad_bound a b c Z ⌈2 * Z * Real.log (2 / ξ ^ 2)⌉₊ hZ ha hb hc hca hcb hle
  have h2 := two_exp_ceil_le Z ξ hZ hξ
  linarith

/-! ### The selected-state chain (eq selected-state-preopt) -/

section SelectedChain

variable {N : StdTracialAlgebra.{u}} {x y : N.H}
variable (dA : SpectralData N x) (dB : SpectralData N y) (Jd : JointSpectralData dA dB)
variable {m : ℕ} (B : Fin m → Set ℝ) (t : Fin m → ℝ)

/-- `‖k♯‖₂² = b` (06_otqcs.tex, eq rounded-y: the normalization of `ỹ`). -/
theorem selSharp_normSq (hB : IsBandFamily B t) :
    ‖N.ι (selSharp dB B t)‖ ^ 2 = pairMassB dB B t := by
  have hpp : ∀ i j : Fin m, ⟪N.ι (dB.proj (B i)), N.ι (dB.proj (B j))⟫_ℂ
      = if i = j then ((dB.μ (B i)).toReal : ℂ) else 0 := by
    intro i j
    rw [N.ι_inner, dB.proj_star]
    by_cases hij : i = j
    · subst hij
      rw [dB.proj_inter (B i) (B i) (hB.meas i) (hB.meas i), Set.inter_self,
        dB.proj_trace (B i) (hB.meas i), if_pos rfl]
    · rw [dB.proj_inter (B i) (B j) (hB.meas i) (hB.meas j),
        Set.disjoint_iff_inter_eq_empty.mp (hB.disj hij), dB.proj_empty, map_zero, if_neg hij]
  have hS_sum : N.ι (selSharp dB B t) = ∑ j, (t j : ℂ) • N.ι (dB.proj (B j)) := by
    rw [selSharp, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul]
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
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (N.ι (selSharp dB B t)), hSS_c,
    RCLike.re_to_complex, Complex.ofReal_re]
  rfl

theorem selSharp_norm (hB : IsBandFamily B t) :
    ‖N.ι (selSharp dB B t)‖ = Real.sqrt (pairMassB dB B t) := by
  rw [← selSharp_normSq dB B t hB, Real.sqrt_sq (norm_nonneg _)]

/-- The normalization inequality for the rounded polar vector:
`‖ỹ_t − y_t‖₂ ≤ 2 ‖k_t^♯ − k_t‖₂` (06_otqcs.tex, eq normalization-inequality
applied to `ỹ = b^{−1/2} k♯ v`, `y = k v`, with `v` a right isometry on the
relevant vectors — `Rop_v_norm`). -/
theorem selYTilde_sub_le (hB : IsBandFamily B t) (hy : ‖y‖ = 1) (hb : 0 < pairMassB dB B t) :
    ‖selYTilde dB B t - y‖ ≤ 2 * ‖N.ι (selSharp dB B t) - dB.hvec‖ := by
  set S : N.H := N.ι (selSharp dB B t) with hS
  have hSnorm : ‖S‖ = Real.sqrt (pairMassB dB B t) := selSharp_norm dB B t hB
  have hSne : S ≠ 0 := by
    intro h
    rw [h, norm_zero] at hSnorm
    exact absurd hSnorm.symm (ne_of_gt (Real.sqrt_pos.mpr hb))
  have hhnorm : ‖dB.hvec‖ = 1 := by rw [dB.hvec_norm, hy]
  have hhne : dB.hvec ≠ 0 := by
    intro h; rw [h, norm_zero] at hhnorm; exact zero_ne_one hhnorm
  set c : ℂ := (((Real.sqrt (pairMassB dB B t))⁻¹ : ℝ) : ℂ) with hc
  have hdiff : selYTilde dB B t - y = N.Rop dB.v (c • S + (-1 : ℂ) • dB.hvec) := by
    rw [map_add, map_smul, map_smul, neg_one_smul, ← sub_eq_add_neg, dB.polar]
    congr 1
    rw [selYTilde, hc]
    congr 1
    exact (N.R_apply dB.v (selSharp dB B t)).symm
  have key : ‖dB.hvec - c • S‖ ≤ 2 * ‖S - dB.hvec‖ := by
    have h := norm_normalize_sub_normalize_le dB.hvec S hhne hSne
    rw [hhnorm, inv_one, Complex.ofReal_one, one_smul, div_one, hSnorm,
      norm_sub_rev dB.hvec S] at h
    exact h
  calc ‖selYTilde dB B t - y‖
      = ‖N.Rop dB.v (c • S + (-1 : ℂ) • dB.hvec)‖ := by rw [hdiff]
    _ = ‖c • S + (-1 : ℂ) • dB.hvec‖ := Rop_v_norm dB B t hB c (-1)
    _ = ‖dB.hvec - c • S‖ := by rw [neg_one_smul, ← sub_eq_add_neg, norm_sub_rev]
    _ ≤ 2 * ‖S - dB.hvec‖ := key

/-- `‖k − k^{cut}‖₂ ≤ √(ρ + L²)` when the bands cover `[L, H]` and the high tail
beyond `H` is at most `ρ` (06_otqcs.tex, eq rounding-tails). -/
theorem hvec_sub_selCutVec_le (hB : IsBandFamily B t) (hy : ‖y‖ = 1) {L H ρ : ℝ}
    (hL : 0 < L) (hLH : L < H) (hU : (⋃ j, B j) = Set.Icc L H)
    (htail : (∫ b in Set.Ioi H, b ^ 2 ∂dB.μ) ≤ ρ) :
    ‖dB.hvec - selCutVec dB B‖ ≤ Real.sqrt (ρ + L ^ 2) := by
  have hprob : IsProbabilityMeasure dB.μ := dB.μ_prob
  have h1 : (∫ b, b ^ 2 ∂dB.μ) = 1 := by rw [dB.moment2, hy, one_pow]
  have hwin := setIntegral_sq_Icc_ge dB.μ dB.μ_nonneg h1 hL hLH htail
  have hsq : ‖dB.hvec - selCutVec dB B‖ ^ 2 ≤ ρ + L ^ 2 := by
    rw [selCutVec_sub dB B t hB, hU, h1]; linarith
  calc ‖dB.hvec - selCutVec dB B‖
      = Real.sqrt (‖dB.hvec - selCutVec dB B‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (ρ + L ^ 2) := Real.sqrt_le_sqrt hsq

/-- **The selected-state chain** (06_otqcs.tex, eq selected-state-preopt):
`‖z_{st} − u_{st}‖₂ ≤ 2√Γ_{st} + 2((r − 1) + κ) + ‖y_t − u_{st}‖₂`, where
`r − 1 = α` bounds the rounding `‖k♯ − k^{cut}‖` and `κ` the cut `‖k^{cut} − k‖`. -/
theorem selState_sub_le (hB : IsBandFamily B t) (hy : ‖y‖ = 1)
    (ha : 1 / 2 ≤ pairMassA dA B t) (hb : 1 / 2 ≤ pairMassB dB B t)
    (r : ℝ) (hr : 1 ≤ r) (hband : ∀ j, B j ⊆ Set.Icc (t j / r) (t j))
    (κ : ℝ) (hcut : ‖dB.hvec - selCutVec dB B‖ ≤ κ) (u : N.H) :
    ‖selState dA dB Jd B t - u‖ ≤
      2 * Real.sqrt (pairMassA dA B t + pairMassB dB B t - 2 * pairCross dA dB Jd B t)
        + 2 * ((r - 1) + κ) + ‖y - u‖ := by
  have hb0 : 0 < pairMassB dB B t := by linarith
  have hsqrt4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  -- ‖z − ỹ‖ ≤ 2√Γ
  have h1 : ‖selState dA dB Jd B t - selYTilde dB B t‖ ≤
      2 * Real.sqrt (pairMassA dA B t + pairMassB dB B t - 2 * pairCross dA dB Jd B t) := by
    have h := selState_sub_yTilde dA dB Jd B t hB ha hb
    calc ‖selState dA dB Jd B t - selYTilde dB B t‖
        = Real.sqrt (‖selState dA dB Jd B t - selYTilde dB B t‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (4 * (pairMassA dA B t + pairMassB dB B t
            - 2 * pairCross dA dB Jd B t)) := Real.sqrt_le_sqrt h
      _ = 2 * Real.sqrt (pairMassA dA B t + pairMassB dB B t
            - 2 * pairCross dA dB Jd B t) := by
          rw [Real.sqrt_mul (by norm_num), hsqrt4]
  -- ‖k♯ − k^{cut}‖ ≤ r − 1
  have h2 : ‖N.ι (selSharp dB B t) - selCutVec dB B‖ ≤ r - 1 := by
    have h := selSharp_round dB B t hB r hr hband
    rw [hy, one_pow, mul_one] at h
    calc ‖N.ι (selSharp dB B t) - selCutVec dB B‖
        = Real.sqrt (‖N.ι (selSharp dB B t) - selCutVec dB B‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((r - 1) ^ 2) := Real.sqrt_le_sqrt h
      _ = r - 1 := Real.sqrt_sq (by linarith)
  -- ‖ỹ − y‖ ≤ 2((r − 1) + κ)
  have h3 : ‖selYTilde dB B t - y‖ ≤ 2 * ((r - 1) + κ) := by
    have h := selYTilde_sub_le dB B t hB hy hb0
    have htri : ‖N.ι (selSharp dB B t) - dB.hvec‖ ≤
        ‖N.ι (selSharp dB B t) - selCutVec dB B‖ + ‖selCutVec dB B - dB.hvec‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    rw [norm_sub_rev (selCutVec dB B)] at htri
    linarith
  have htri1 := norm_sub_le_norm_sub_add_norm_sub (selState dA dB Jd B t) (selYTilde dB B t) u
  have htri2 := norm_sub_le_norm_sub_add_norm_sub (selYTilde dB B t) y u
  linarith

end SelectedChain

/-! ### Hypotheses of the grid slab read off a joint spectral package -/

section JointTransport

variable {N : StdTracialAlgebra.{u}} {x y : N.H} {dA : SpectralData N x} {dB : SpectralData N y}
variable (Jd : JointSpectralData dA dB)

theorem JointSpectralData.ae_nonneg : ∀ᵐ p ∂Jd.ν, 0 ≤ p.1 ∧ 0 ≤ p.2 := by
  have hA : ∀ᵐ p ∂Jd.ν, 0 ≤ p.1 := by
    rw [ae_iff]
    have hs : {p : ℝ × ℝ | ¬ 0 ≤ p.1} = Prod.fst ⁻¹' Set.Iio 0 := by ext p; simp [not_le]
    rw [hs, ← Measure.map_apply measurable_fst measurableSet_Iio, Jd.margA, dA.μ_nonneg]
  have hB : ∀ᵐ p ∂Jd.ν, 0 ≤ p.2 := by
    rw [ae_iff]
    have hs : {p : ℝ × ℝ | ¬ 0 ≤ p.2} = Prod.snd ⁻¹' Set.Iio 0 := by ext p; simp [not_le]
    rw [hs, ← Measure.map_apply measurable_snd measurableSet_Iio, Jd.margB, dB.μ_nonneg]
  exact hA.and hB

theorem JointSpectralData.integral_fst_sq : (∫ p : ℝ × ℝ, p.1 ^ 2 ∂Jd.ν) = ‖x‖ ^ 2 := by
  have h := integral_map (μ := Jd.ν) (φ := Prod.fst) measurable_fst.aemeasurable
    (f := fun b : ℝ => b ^ 2) (measurable_id.pow_const 2).aestronglyMeasurable
  rw [Jd.margA, dA.moment2] at h
  exact h.symm

theorem JointSpectralData.integral_snd_sq : (∫ p : ℝ × ℝ, p.2 ^ 2 ∂Jd.ν) = ‖y‖ ^ 2 := by
  have h := integral_map (μ := Jd.ν) (φ := Prod.snd) measurable_snd.aemeasurable
    (f := fun b : ℝ => b ^ 2) (measurable_id.pow_const 2).aestronglyMeasurable
  rw [Jd.margB, dB.moment2] at h
  exact h.symm

theorem JointSpectralData.setIntegral_fst_sq_tail (H : ℝ) :
    (∫ p in {q : ℝ × ℝ | H < q.1}, p.1 ^ 2 ∂Jd.ν) = ∫ b in Set.Ioi H, b ^ 2 ∂dA.μ := by
  have h := setIntegral_map (μ := Jd.ν) (g := Prod.fst) (f := fun b : ℝ => b ^ 2)
    (s := Set.Ioi H) measurableSet_Ioi (measurable_id.pow_const 2).aestronglyMeasurable
    measurable_fst.aemeasurable
  rw [Jd.margA] at h
  have hs : {q : ℝ × ℝ | H < q.1} = Prod.fst ⁻¹' Set.Ioi H := rfl
  rw [hs]
  exact h.symm

theorem JointSpectralData.setIntegral_snd_sq_tail (H : ℝ) :
    (∫ p in {q : ℝ × ℝ | H < q.2}, p.2 ^ 2 ∂Jd.ν) = ∫ b in Set.Ioi H, b ^ 2 ∂dB.μ := by
  have h := setIntegral_map (μ := Jd.ν) (g := Prod.snd) (f := fun b : ℝ => b ^ 2)
    (s := Set.Ioi H) measurableSet_Ioi (measurable_id.pow_const 2).aestronglyMeasurable
    measurable_snd.aemeasurable
  rw [Jd.margB] at h
  have hs : {q : ℝ × ℝ | H < q.2} = Prod.snd ⁻¹' Set.Ioi H := rfl
  rw [hs]
  exact h.symm

end JointTransport

/-! ### Averaging and the parameter arithmetic -/

/-- Jensen for the square root under a probability weight:
`∑ πᵢ √gᵢ ≤ √(∑ πᵢ gᵢ)` ("this is the sole square-root conversion in the proof"). -/
theorem sum_mul_sqrt_le_sqrt {ι : Type*} [Fintype ι] (π g : ι → ℝ)
    (hπ : ∀ i, 0 ≤ π i) (hπ1 : (∑ i, π i) = 1) (hg : ∀ i, 0 ≤ g i) :
    (∑ i, π i * Real.sqrt (g i)) ≤ Real.sqrt (∑ i, π i * g i) := by
  have hnn : 0 ≤ ∑ i, π i * Real.sqrt (g i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hπ i) (Real.sqrt_nonneg _)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => Real.sqrt (π i))
    (fun i => Real.sqrt (π i) * Real.sqrt (g i))
  have h1 : ∀ i, Real.sqrt (π i) * (Real.sqrt (π i) * Real.sqrt (g i))
      = π i * Real.sqrt (g i) := by
    intro i; rw [← mul_assoc, Real.mul_self_sqrt (hπ i)]
  have h2 : ∀ i, Real.sqrt (π i) ^ 2 = π i := fun i => Real.sq_sqrt (hπ i)
  have h3 : ∀ i, (Real.sqrt (π i) * Real.sqrt (g i)) ^ 2 = π i * g i := by
    intro i; rw [mul_pow, Real.sq_sqrt (hπ i), Real.sq_sqrt (hg i)]
  simp only [h1, h2, h3, hπ1, one_mul] at hcs
  calc (∑ i, π i * Real.sqrt (g i))
      = Real.sqrt ((∑ i, π i * Real.sqrt (g i)) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt (∑ i, π i * g i) := Real.sqrt_le_sqrt hcs

/-- `‖x − y‖² ≤ 2‖u − x‖² + 2‖u − y‖²` (the step behind eq Dbar-Delta). -/
theorem norm_sub_sq_le_two_mul {E : Type*} [SeminormedAddCommGroup E] (x y u : E) :
    ‖x - y‖ ^ 2 ≤ 2 * ‖u - x‖ ^ 2 + 2 * ‖u - y‖ ^ 2 := by
  have h : ‖x - y‖ ≤ ‖u - x‖ + ‖u - y‖ := by
    calc ‖x - y‖ = ‖(u - y) - (u - x)‖ := by congr 1; abel
      _ ≤ ‖u - y‖ + ‖u - x‖ := norm_sub_le _ _
      _ = ‖u - x‖ + ‖u - y‖ := add_comm _ _
  have h0 : 0 ≤ ‖x - y‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖u - x‖ - ‖u - y‖), norm_nonneg (u - x), norm_nonneg (u - y)]

/-- `(Δ^{1/6})^6 = Δ`. -/
theorem rpow_sixth_pow (Δ : ℝ) (hΔ : 0 ≤ Δ) : (Δ ^ ((1 : ℝ) / 6)) ^ 6 = Δ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hΔ]
  norm_num

/-- The final constant bookkeeping in the nontrivial range `δ + ξ ≤ 1/2`, with
`δ = Δ^{1/6}`, `ρ = ξ²/32`, `L = ξ/8`, `α = δ + ξ` (06_otqcs.tex, eqs cutoff-choice,
alpha-choice, alpha-optimization, Dbar-Delta): the averaged per-pair bound is at
most a universal multiple of `δ + ξ`. -/
theorem final_arith (C₀ δ ξ Γbar Ybar Dbar : ℝ) (hC₀ : 0 < C₀) (hδ : 0 ≤ δ) (hξ : 0 < ξ)
    (hα : δ + ξ ≤ 1 / 2)
    (hΓ : Γbar ≤ C₀ * (Dbar + Real.sqrt Dbar / (δ + ξ) + ξ ^ 2 / 32 + (ξ / 8) ^ 2))
    (hD : Dbar ≤ 4 * δ ^ 6) (hY : Ybar ≤ δ ^ 6) :
    4 * Real.sqrt Γbar + 4 * (δ + ξ) + 4 * Real.sqrt (ξ ^ 2 / 32 + (ξ / 8) ^ 2)
        + 2 * Real.sqrt Ybar + 4 * Γbar + 2 * ξ ^ 2
      ≤ (4 * Real.sqrt (6 * C₀) + 24 * C₀ + 8) * (δ + ξ) := by
  have hξ1 : ξ ≤ 1 / 2 := by linarith
  have hδ1 : δ ≤ 1 / 2 := by linarith
  have hα0 : 0 < δ + ξ := by linarith
  have hδ2 : δ ^ 2 ≤ δ := by nlinarith
  have hδ3 : δ ^ 3 ≤ δ ^ 2 := by nlinarith [pow_nonneg hδ 2]
  have hδ6 : δ ^ 6 ≤ δ ^ 2 :=
    pow_le_pow_of_le_one hδ (by linarith : δ ≤ 1) (by norm_num : 2 ≤ 6)
  have hsqD : Real.sqrt Dbar ≤ 2 * δ ^ 3 := by
    calc Real.sqrt Dbar ≤ Real.sqrt ((2 * δ ^ 3) ^ 2) := by
          apply Real.sqrt_le_sqrt; nlinarith
      _ = 2 * δ ^ 3 := Real.sqrt_sq (by positivity)
  have hsqDα : Real.sqrt Dbar / (δ + ξ) ≤ 2 * δ ^ 2 := by
    rw [div_le_iff₀ hα0]
    nlinarith [pow_nonneg hδ 2]
  have hΓ2 : Γbar ≤ 6 * C₀ * (δ + ξ) ^ 2 := by
    have hinner : Dbar + Real.sqrt Dbar / (δ + ξ) + ξ ^ 2 / 32 + (ξ / 8) ^ 2
        ≤ 6 * (δ + ξ) ^ 2 := by nlinarith [mul_nonneg hδ hξ.le]
    calc Γbar ≤ C₀ * (Dbar + Real.sqrt Dbar / (δ + ξ) + ξ ^ 2 / 32 + (ξ / 8) ^ 2) := hΓ
      _ ≤ C₀ * (6 * (δ + ξ) ^ 2) := mul_le_mul_of_nonneg_left hinner hC₀.le
      _ = 6 * C₀ * (δ + ξ) ^ 2 := by ring
  have hsqΓ : Real.sqrt Γbar ≤ Real.sqrt (6 * C₀) * (δ + ξ) := by
    calc Real.sqrt Γbar ≤ Real.sqrt (6 * C₀ * (δ + ξ) ^ 2) := Real.sqrt_le_sqrt hΓ2
      _ = Real.sqrt (6 * C₀) * (δ + ξ) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hα0.le]
  have hΓ3 : 4 * Γbar ≤ 24 * C₀ * (δ + ξ) := by
    have : (δ + ξ) ^ 2 ≤ δ + ξ := by nlinarith
    nlinarith
  have hκ : Real.sqrt (ξ ^ 2 / 32 + (ξ / 8) ^ 2) ≤ ξ / 4 := by
    calc Real.sqrt (ξ ^ 2 / 32 + (ξ / 8) ^ 2) ≤ Real.sqrt ((ξ / 4) ^ 2) := by
          apply Real.sqrt_le_sqrt; nlinarith
      _ = ξ / 4 := Real.sqrt_sq (by positivity)
  have hsqY : Real.sqrt Ybar ≤ δ := by
    calc Real.sqrt Ybar ≤ Real.sqrt ((δ ^ 3) ^ 2) := by
          apply Real.sqrt_le_sqrt; nlinarith
      _ = δ ^ 3 := Real.sqrt_sq (by positivity)
      _ ≤ δ := by nlinarith
  have hξsq : 2 * ξ ^ 2 ≤ ξ := by nlinarith
  have hsC : 0 ≤ Real.sqrt (6 * C₀) := Real.sqrt_nonneg _
  nlinarith [mul_nonneg hsC hα0.le]

/-- **Averaging the per-pair bound** (06_otqcs.tex, the final display of the proof
of thm otqcs): if every pair obeys the selected-state/bad-branch bound in terms of
its grid disagreement `Γᵢ` and its alignment `Yᵢ = ‖y − u‖²`, and the `π`-averages
obey eqs common-shift and Dbar-Delta, then the `π`-average of the ℓ¹ errors is at
most a universal multiple of `δ + ξ`, `δ = Δ^{1/6}`. -/
theorem average_bound {ι : Type*} [Fintype ι] (π Γ Y ℓ : ι → ℝ) (C₀ δ ξ Dbar : ℝ)
    (hπ : ∀ i, 0 ≤ π i) (hπ1 : (∑ i, π i) = 1)
    (hΓ : ∀ i, 0 ≤ Γ i) (hY : ∀ i, 0 ≤ Y i)
    (hℓ : ∀ i, ℓ i ≤ 4 * Real.sqrt (Γ i) + 4 * (δ + ξ)
      + 4 * Real.sqrt (ξ ^ 2 / 32 + (ξ / 8) ^ 2) + 2 * Real.sqrt (Y i) + 4 * Γ i + 2 * ξ ^ 2)
    (hC₀ : 0 < C₀) (hδ : 0 ≤ δ) (hξ : 0 < ξ) (hα : δ + ξ ≤ 1 / 2)
    (hΓavg : (∑ i, π i * Γ i) ≤
      C₀ * (Dbar + Real.sqrt Dbar / (δ + ξ) + ξ ^ 2 / 32 + (ξ / 8) ^ 2))
    (hD : Dbar ≤ 4 * δ ^ 6) (hYavg : (∑ i, π i * Y i) ≤ δ ^ 6) :
    (∑ i, π i * ℓ i) ≤ (4 * Real.sqrt (6 * C₀) + 24 * C₀ + 8) * (δ + ξ) := by
  set κ := 4 * (δ + ξ) + 4 * Real.sqrt (ξ ^ 2 / 32 + (ξ / 8) ^ 2) + 2 * ξ ^ 2 with hκ
  have h1 : (∑ i, π i * ℓ i) ≤
      ∑ i, π i * (4 * Real.sqrt (Γ i) + κ + 2 * Real.sqrt (Y i) + 4 * Γ i) := by
    apply Finset.sum_le_sum; intro i _
    apply mul_le_mul_of_nonneg_left _ (hπ i)
    linarith [hℓ i]
  have hexp : ∀ i, π i * (4 * Real.sqrt (Γ i) + κ + 2 * Real.sqrt (Y i) + 4 * Γ i)
      = 4 * (π i * Real.sqrt (Γ i)) + κ * π i + 2 * (π i * Real.sqrt (Y i))
        + 4 * (π i * Γ i) := fun i => by ring
  have h2 : (∑ i, π i * (4 * Real.sqrt (Γ i) + κ + 2 * Real.sqrt (Y i) + 4 * Γ i))
      = 4 * (∑ i, π i * Real.sqrt (Γ i)) + κ + 2 * (∑ i, π i * Real.sqrt (Y i))
        + 4 * (∑ i, π i * Γ i) := by
    simp only [hexp, Finset.sum_add_distrib, ← Finset.mul_sum, hπ1, mul_one]
  have hJ1 := sum_mul_sqrt_le_sqrt π Γ hπ hπ1 hΓ
  have hJ2 := sum_mul_sqrt_le_sqrt π Y hπ hπ1 hY
  have hfin := final_arith C₀ δ ξ (∑ i, π i * Γ i) (∑ i, π i * Y i) Dbar hC₀ hδ hξ hα
    hΓavg hD hYavg
  calc (∑ i, π i * ℓ i)
      ≤ ∑ i, π i * (4 * Real.sqrt (Γ i) + κ + 2 * Real.sqrt (Y i) + 4 * Γ i) := h1
    _ = 4 * (∑ i, π i * Real.sqrt (Γ i)) + κ + 2 * (∑ i, π i * Real.sqrt (Y i))
        + 4 * (∑ i, π i * Γ i) := h2
    _ ≤ 4 * Real.sqrt (∑ i, π i * Γ i) + κ + 2 * Real.sqrt (∑ i, π i * Y i)
        + 4 * (∑ i, π i * Γ i) := by linarith
    _ ≤ (4 * Real.sqrt (6 * C₀) + 24 * C₀ + 8) * (δ + ξ) := by rw [hκ]; linarith

/-! ### The trivial resource (degenerate range) -/

open Classical in
/-- The trivial sampling resource of the degenerate range `α₀ > 1/2`
(06_otqcs.tex, proof of thm otqcs: "take explicitly `N̂ = N`, `Ω = 1`,
`Â_s^{a₀} = B̂_t^{b₀} = 1` and set all other output effects to zero"). -/
noncomputable def trivialResource (S T A B : Type) [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (N : StdTracialAlgebra.{0}) : SamplingResource S T A B where
  N := N
  Ω := N.ι 1
  Ω_norm := by
    have h : ‖N.ι (1 : N.A)‖ ^ 2 = 1 := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (N.ι (1 : N.A)), N.ι_inner, star_one, one_mul,
        N.τ_one, RCLike.re_to_complex, Complex.one_re]
    calc ‖N.ι (1 : N.A)‖ = Real.sqrt (‖N.ι (1 : N.A)‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ = 1 := by rw [h, Real.sqrt_one]
  E := fun _ a => if a = Classical.arbitrary A then 1 else 0
  F := fun _ b => if b = Classical.arbitrary B then 1 else 0
  E_pos := by
    intro s a
    split_ifs
    · simpa using isPosElem_star_mul_self (1 : N.A)
    · exact isPosElem_zero
  F_pos := by
    intro t b
    split_ifs
    · simpa using isPosElem_star_mul_self (1 : N.A)
    · exact isPosElem_zero
  E_sum := by intro s; simp [Finset.sum_ite_eq']
  F_sum := by intro t; simp [Finset.sum_ite_eq']

end CommutingRepetition
