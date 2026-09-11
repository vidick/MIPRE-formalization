/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Tracial/Density/FaithfulState.lean
-/
/-
# A faithful normal state on `B(K)` for separable `K` (stage E1)

From a dense sequence `u` in a separable Hilbert space, the functional
`T ↦ Z⁻¹ ∑ₖ 2⁻ᵏ ⟪vₖ, T vₖ⟫` with `vₖ = uₖ/(1 + ‖uₖ‖)` is a state on `B(K)` that
is faithful (`φ(T*T) = 0 ⇒ T = 0`) and of trace-class form
`∑ ⟪aₖ, T bₖ⟫` with `∑ ‖aₖ‖‖bₖ‖ < ∞` (the normal functionals). It is the
ingredient of the faithful perturbation of PLAN-density.md §1.3. Proof-side.
-/
import Mathlib

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace Density

open scoped InnerProductSpace ComplexOrder
open TopologicalSpace

set_option linter.unusedSectionVars false

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A functional on `B(K)` of trace-class form `∑ ⟪vₖ, T wₖ⟫` with `∑ ‖vₖ‖‖wₖ‖ < ∞` (these are
exactly the normal functionals). -/
def IsTraceClassFunctional (φ : (K →L[ℂ] K) →ₗ[ℂ] ℂ) : Prop :=
  ∃ v w : ℕ → K, Summable (fun i => ‖v i‖ * ‖w i‖) ∧ ∀ T, φ T = ∑' i, ⟪v i, T (w i)⟫_ℂ

theorem IsTraceClassFunctional.smul {φ : (K →L[ℂ] K) →ₗ[ℂ] ℂ} (hφ : IsTraceClassFunctional φ)
    (c : ℂ) : IsTraceClassFunctional (c • φ) := by
  obtain ⟨v, w, hs, h⟩ := hφ
  refine ⟨v, fun i => c • w i, ?_, fun T => ?_⟩
  · simpa [norm_smul, mul_left_comm] using hs.mul_left ‖c‖
  · simp only [LinearMap.smul_apply, smul_eq_mul, h, map_smul, inner_smul_right]
    exact (tsum_mul_left).symm

section Faithful

variable (u : ℕ → K)

/-- The normalized sequence `uₖ / (1 + ‖uₖ‖)`. -/
noncomputable def nv (k : ℕ) : K := (((1 + ‖u k‖)⁻¹ : ℝ) : ℂ) • u k

theorem norm_nv_le (k : ℕ) : ‖nv u k‖ ≤ 1 := by
  rw [nv, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [inv_mul_le_iff₀ (by positivity), mul_one]
  linarith

theorem map_nv_eq_zero_iff (T : K →L[ℂ] K) (k : ℕ) : T (nv u k) = 0 ↔ T (u k) = 0 := by
  rw [nv, map_smul, smul_eq_zero, Complex.ofReal_eq_zero, inv_eq_zero]
  have : (1 + ‖u k‖) ≠ 0 := by positivity
  simp [this]

/-- The weights `2⁻ᵏ`. -/
noncomputable def wt (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ k

theorem wt_nonneg (k : ℕ) : 0 ≤ wt k := by unfold wt; positivity

theorem wt_pos (k : ℕ) : 0 < wt k := by unfold wt; positivity

theorem summable_wt : Summable wt := summable_geometric_two

theorem norm_inner_nv_le (T : K →L[ℂ] K) (k : ℕ) : ‖⟪nv u k, T (nv u k)⟫_ℂ‖ ≤ ‖T‖ :=
  calc ‖⟪nv u k, T (nv u k)⟫_ℂ‖ ≤ ‖nv u k‖ * ‖T (nv u k)‖ := norm_inner_le_norm _ _
    _ ≤ 1 * (‖T‖ * 1) := by
        refine mul_le_mul (norm_nv_le u k) ((T.le_opNorm _).trans ?_) (norm_nonneg _) zero_le_one
        exact mul_le_mul_of_nonneg_left (norm_nv_le u k) (norm_nonneg _)
    _ = ‖T‖ := by ring

theorem summable_term (T : K →L[ℂ] K) :
    Summable fun k => ((wt k : ℝ) : ℂ) * ⟪nv u k, T (nv u k)⟫_ℂ :=
  Summable.of_norm_bounded (summable_wt.mul_right ‖T‖) fun k => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (wt_nonneg k)]
    exact mul_le_mul_of_nonneg_left (norm_inner_nv_le u T k) (wt_nonneg k)

/-- The unnormalized functional `T ↦ ∑ₖ 2⁻ᵏ ⟪vₖ, T vₖ⟫`. -/
noncomputable def preState : (K →L[ℂ] K) →ₗ[ℂ] ℂ where
  toFun T := ∑' k, ((wt k : ℝ) : ℂ) * ⟪nv u k, T (nv u k)⟫_ℂ
  map_add' T U := by
    simp only [_root_.add_apply, inner_add_right, mul_add]
    exact (summable_term u T).tsum_add (summable_term u U)
  map_smul' c T := by
    simp only [_root_.smul_apply, inner_smul_right, RingHom.id_apply, smul_eq_mul]
    rw [← tsum_mul_left]
    congr 1
    funext k
    ring

theorem preState_apply (T : K →L[ℂ] K) :
    preState u T = ∑' k, ((wt k : ℝ) : ℂ) * ⟪nv u k, T (nv u k)⟫_ℂ := rfl

theorem summable_sq (T : K →L[ℂ] K) : Summable fun k => wt k * ‖T (nv u k)‖ ^ 2 :=
  Summable.of_nonneg_of_le (fun k => mul_nonneg (wt_nonneg k) (sq_nonneg _))
    (fun k => by
      refine mul_le_mul_of_nonneg_left ?_ (wt_nonneg k)
      calc ‖T (nv u k)‖ ^ 2 ≤ (‖T‖ * 1) ^ 2 := by
            gcongr
            exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_nv_le u k) (norm_nonneg _))
        _ = ‖T‖ ^ 2 := by ring)
    (summable_wt.mul_right (‖T‖ ^ 2))

theorem preState_star_mul_self (T : K →L[ℂ] K) :
    preState u (star T * T) = ((∑' k, wt k * ‖T (nv u k)‖ ^ 2 : ℝ) : ℂ) := by
  rw [preState_apply, Complex.ofReal_tsum]
  congr 1
  funext k
  rw [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K, Complex.ofReal_mul, Complex.ofReal_pow]
  rfl

/-- The normalization constant `Z = ∑ₖ 2⁻ᵏ ‖vₖ‖²`. -/
noncomputable def Z : ℝ := ∑' k, wt k * ‖nv u k‖ ^ 2

theorem Z_nonneg : 0 ≤ Z u := tsum_nonneg fun k => mul_nonneg (wt_nonneg k) (sq_nonneg _)

theorem Z_pos (hne : ∃ k, u k ≠ 0) : 0 < Z u := by
  obtain ⟨k, hk⟩ := hne
  have h1 : ∀ k, wt k * ‖(1 : K →L[ℂ] K) (nv u k)‖ ^ 2 = wt k * ‖nv u k‖ ^ 2 := fun k => by
    rw [one_apply_eq_self]
  refine (summable_sq u 1).tsum_pos (fun k => mul_nonneg (wt_nonneg k) (sq_nonneg _)) k ?_ |>.trans_eq
    (tsum_congr h1)
  rw [h1]
  have : nv u k ≠ 0 := by
    intro h
    have := (map_nv_eq_zero_iff u 1 k).mp (by rw [h, map_zero])
    exact hk (by simpa using this)
  have hn : 0 < ‖nv u k‖ := norm_pos_iff.mpr this
  exact mul_pos (wt_pos k) (by positivity)

theorem preState_one : preState u 1 = ((Z u : ℝ) : ℂ) := by
  have := preState_star_mul_self u 1
  rwa [star_one, one_mul] at this

/-- **The faithful state** `Z⁻¹ · preState`. -/
noncomputable def faithfulState : (K →L[ℂ] K) →ₗ[ℂ] ℂ := (((Z u)⁻¹ : ℝ) : ℂ) • preState u

theorem faithfulState_apply (T : K →L[ℂ] K) :
    faithfulState u T = (((Z u)⁻¹ : ℝ) : ℂ) * preState u T := rfl

theorem faithfulState_one (hne : ∃ k, u k ≠ 0) : faithfulState u 1 = 1 := by
  rw [faithfulState_apply, preState_one, ← Complex.ofReal_mul, inv_mul_cancel₀ (Z_pos u hne).ne',
    Complex.ofReal_one]

theorem faithfulState_star_mul_self (T : K →L[ℂ] K) :
    faithfulState u (star T * T) = (((Z u)⁻¹ * ∑' k, wt k * ‖T (nv u k)‖ ^ 2 : ℝ) : ℂ) := by
  rw [faithfulState_apply, preState_star_mul_self, Complex.ofReal_mul]

theorem faithfulState_nonneg (T : K →L[ℂ] K) : 0 ≤ faithfulState u (star T * T) := by
  rw [faithfulState_star_mul_self]
  exact Complex.zero_le_real.mpr
    (mul_nonneg (inv_nonneg.mpr (Z_nonneg u))
      (tsum_nonneg fun k => mul_nonneg (wt_nonneg k) (sq_nonneg _)))

/-- Faithfulness: `φ(T*T) = 0` forces `T = 0`, since `u` is dense. -/
theorem faithfulState_faithful (hu : DenseRange u) (hne : ∃ k, u k ≠ 0) (T : K →L[ℂ] K)
    (h : faithfulState u (star T * T) = 0) : T = 0 := by
  rw [faithfulState_star_mul_self, Complex.ofReal_eq_zero,
    mul_eq_zero, inv_eq_zero] at h
  rcases h with h | h
  · exact absurd h (Z_pos u hne).ne'
  have hterm : ∀ k, wt k * ‖T (nv u k)‖ ^ 2 = 0 := fun k => by
    have hle := (summable_sq u T).le_tsum k fun j _ => mul_nonneg (wt_nonneg j) (sq_nonneg _)
    rw [h] at hle
    exact le_antisymm hle (mul_nonneg (wt_nonneg k) (sq_nonneg _))
  have hT : ∀ k, T (u k) = 0 := fun k => by
    have := hterm k
    rw [mul_eq_zero, pow_eq_zero_iff two_ne_zero, norm_eq_zero] at this
    rcases this with h0 | h0
    · exact absurd h0 (wt_pos k).ne'
    · exact (map_nv_eq_zero_iff u T k).mp h0
  have : (T : K → K) = (0 : K →L[ℂ] K) :=
    hu.equalizer T.continuous (0 : K →L[ℂ] K).continuous (funext fun k => by simp [hT k])
  exact DFunLike.coe_injective this

theorem faithfulState_traceClass : IsTraceClassFunctional (faithfulState u) := by
  refine ⟨fun k => (((Z u)⁻¹ * wt k : ℝ) : ℂ) • nv u k, nv u, ?_, fun T => ?_⟩
  · refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) (summable_wt.mul_left (Z u)⁻¹)
    · positivity
    · rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg
        (mul_nonneg (inv_nonneg.mpr (Z_nonneg u)) (wt_nonneg k)), mul_assoc]
      refine (mul_le_mul_of_nonneg_left ?_
        (mul_nonneg (inv_nonneg.mpr (Z_nonneg u)) (wt_nonneg k))).trans_eq (mul_one _)
      exact (mul_le_mul (norm_nv_le u k) (norm_nv_le u k) (norm_nonneg _) zero_le_one).trans_eq
        (one_mul _)
  · rw [faithfulState_apply, preState_apply, ← tsum_mul_left]
    congr 1
    funext k
    rw [inner_smul_left, Complex.conj_ofReal, Complex.ofReal_mul]
    ring

/-- `|φ(T)| ≤ ‖T‖`. -/
theorem norm_faithfulState_le (hne : ∃ k, u k ≠ 0) (T : K →L[ℂ] K) :
    ‖faithfulState u T‖ ≤ ‖T‖ := by
  rw [faithfulState_apply, preState_apply, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.mpr (Z_nonneg u))]
  have h1 : ‖∑' k, ((wt k : ℝ) : ℂ) * ⟪nv u k, T (nv u k)⟫_ℂ‖ ≤
      ∑' k, wt k * ‖nv u k‖ ^ 2 * ‖T‖ := by
    refine (norm_tsum_le_tsum_norm ?_).trans (Summable.tsum_le_tsum (fun k => ?_) ?_ ?_)
    · exact (summable_term u T).norm
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (wt_nonneg k), mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (wt_nonneg k)
      calc ‖⟪nv u k, T (nv u k)⟫_ℂ‖ ≤ ‖nv u k‖ * ‖T (nv u k)‖ := norm_inner_le_norm _ _
        _ ≤ ‖nv u k‖ * (‖T‖ * ‖nv u k‖) :=
            mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
        _ = ‖nv u k‖ ^ 2 * ‖T‖ := by ring
    · exact (summable_term u T).norm
    · exact (summable_sq u 1).mul_right ‖T‖ |>.congr fun k => by rw [one_apply_eq_self]
  calc (Z u)⁻¹ * ‖∑' k, ((wt k : ℝ) : ℂ) * ⟪nv u k, T (nv u k)⟫_ℂ‖
      ≤ (Z u)⁻¹ * (∑' k, wt k * ‖nv u k‖ ^ 2 * ‖T‖) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr (Z_nonneg u))
    _ = (Z u)⁻¹ * (Z u * ‖T‖) := by rw [Z, ← tsum_mul_right]
    _ = ‖T‖ := by rw [← mul_assoc, inv_mul_cancel₀ (Z_pos u hne).ne', one_mul]

end Faithful

end Density

end CommutingRepetition
