/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/Normal.lean
-/
/-
# Normality as bounded strong continuity (density stage E3.2)

We render "normal" concretely: a functional on `B(H)` is *normal* if it is
continuous along bounded strongly convergent nets, and a map `B(H) → B(K)` is
normal if it preserves bounded strong convergence.  (For positive functionals
and positive maps between von Neumann algebras this is equivalent to the usual
definition; only this direction is ever used, and it is exactly the property
that the Haagerup expectations `Φ_n(x) → x` are fed into.)  Functionals of
trace-class form (`Density.IsTraceClassFunctional`, stage E1) are normal by
dominated convergence.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Tracial.Density.FaithfulState

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace VN

open scoped InnerProductSpace
open Filter Topology

set_option linter.unusedSectionVars false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ## Bounded strong convergence -/

/-- `T i → L` strongly (pointwise) along `l`, with `‖T i‖` uniformly bounded. -/
def TendstoStrongBdd {ι : Type*} (l : Filter ι) (T : ι → H →L[ℂ] H) (L : H →L[ℂ] H) : Prop :=
  (∃ C, ∀ i, ‖T i‖ ≤ C) ∧ ∀ ξ, Tendsto (fun i => T i ξ) l (𝓝 (L ξ))

namespace TendstoStrongBdd

variable {ι : Type*} {l : Filter ι} {T S : ι → H →L[ℂ] H} {L M : H →L[ℂ] H}

theorem bdd (h : TendstoStrongBdd l T L) : ∃ C, ∀ i, ‖T i‖ ≤ C := h.1

theorem tendsto (h : TendstoStrongBdd l T L) (ξ : H) :
    Tendsto (fun i => T i ξ) l (𝓝 (L ξ)) := h.2 ξ

theorem const (L : H →L[ℂ] H) : TendstoStrongBdd l (fun _ => L) L :=
  ⟨⟨‖L‖, fun _ => le_rfl⟩, fun _ => tendsto_const_nhds⟩

theorem mul_left (h : TendstoStrongBdd l T L) (A : H →L[ℂ] H) :
    TendstoStrongBdd l (fun i => A * T i) (A * L) := by
  obtain ⟨⟨C, hC⟩, ht⟩ := h
  refine ⟨⟨‖A‖ * C, fun i => (norm_mul_le _ _).trans (by gcongr; exact hC i)⟩, fun ξ => ?_⟩
  simp only [mul_apply_eq_comp]
  exact (A.continuous.tendsto _).comp (ht ξ)

theorem mul_right (h : TendstoStrongBdd l T L) (A : H →L[ℂ] H) :
    TendstoStrongBdd l (fun i => T i * A) (L * A) := by
  obtain ⟨⟨C, hC⟩, ht⟩ := h
  refine ⟨⟨C * ‖A‖, fun i => (norm_mul_le _ _).trans (by gcongr; exact hC i)⟩, fun ξ => ?_⟩
  simp only [mul_apply_eq_comp]
  exact ht (A ξ)

theorem add (h : TendstoStrongBdd l T L) (h' : TendstoStrongBdd l S M) :
    TendstoStrongBdd l (fun i => T i + S i) (L + M) := by
  obtain ⟨⟨C, hC⟩, ht⟩ := h
  obtain ⟨⟨C', hC'⟩, ht'⟩ := h'
  refine ⟨⟨C + C', fun i => (norm_add_le _ _).trans (add_le_add (hC i) (hC' i))⟩, fun ξ => ?_⟩
  simp only [_root_.add_apply]
  exact (ht ξ).add (ht' ξ)

theorem smul (h : TendstoStrongBdd l T L) (c : ℂ) :
    TendstoStrongBdd l (fun i => c • T i) (c • L) := by
  obtain ⟨⟨C, hC⟩, ht⟩ := h
  refine ⟨⟨‖c‖ * C, fun i => by rw [norm_smul]; gcongr; exact hC i⟩, fun ξ => ?_⟩
  simp only [_root_.smul_apply]
  exact (ht ξ).const_smul c

/-- Multiplication is jointly continuous along bounded strongly convergent nets. -/
theorem mul (h : TendstoStrongBdd l T L) (h' : TendstoStrongBdd l S M) :
    TendstoStrongBdd l (fun i => T i * S i) (L * M) := by
  obtain ⟨⟨C, hC⟩, ht⟩ := h
  obtain ⟨⟨C', hC'⟩, ht'⟩ := h'
  refine ⟨⟨C * C', fun i => (norm_mul_le _ _).trans (mul_le_mul (hC i) (hC' i) (norm_nonneg _)
    ((norm_nonneg _).trans (hC i)))⟩, fun ξ => ?_⟩
  simp only [mul_apply_eq_comp]
  -- `T i (S i ξ) - L (M ξ) = T i (S i ξ - M ξ) + (T i (M ξ) - L (M ξ))`
  have h1 : Tendsto (fun i => T i (S i ξ - M ξ)) l (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (g := fun i => C * ‖S i ξ - M ξ‖) (fun _ => norm_nonneg _)
      (fun i => ?_) ?_
    · exact (T i).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_right (hC i) (norm_nonneg _))
    · have : Tendsto (fun i => S i ξ - M ξ) l (𝓝 0) := by
        simpa using (ht' ξ).sub_const (M ξ)
      simpa using (tendsto_zero_iff_norm_tendsto_zero.mp this).const_mul C
  have h2 : Tendsto (fun i => T i (M ξ)) l (𝓝 (L (M ξ))) := ht (M ξ)
  have := h1.add h2
  simp only [zero_add] at this
  refine this.congr fun i => ?_
  rw [map_sub, sub_add_cancel]

end TendstoStrongBdd

/-! ## Normal functionals and maps -/

/-- A functional on `B(H)` is normal if it is continuous along bounded strongly convergent
nets (indexed by a `Type`). -/
def IsNormalFun (φ : (H →L[ℂ] H) → ℂ) : Prop :=
  ∀ {ι : Type} (l : Filter ι) (T : ι → H →L[ℂ] H) (L : H →L[ℂ] H),
    TendstoStrongBdd l T L → Tendsto (fun i => φ (T i)) l (𝓝 (φ L))

/-- A map `B(H) → B(K)` is normal if it preserves bounded strong convergence. -/
def IsNormalMap (Φ : (H →L[ℂ] H) → (K →L[ℂ] K)) : Prop :=
  ∀ {ι : Type} (l : Filter ι) (T : ι → H →L[ℂ] H) (L : H →L[ℂ] H),
    TendstoStrongBdd l T L → TendstoStrongBdd l (fun i => Φ (T i)) (Φ L)

namespace IsNormalFun

variable {φ ψ : (H →L[ℂ] H) → ℂ}

theorem add (hφ : IsNormalFun φ) (hψ : IsNormalFun ψ) : IsNormalFun (fun T => φ T + ψ T) :=
  fun l T L h => (hφ l T L h).add (hψ l T L h)

theorem smul (hφ : IsNormalFun φ) (c : ℂ) : IsNormalFun (fun T => c * φ T) :=
  fun l T L h => (hφ l T L h).const_mul c

theorem const (c : ℂ) : IsNormalFun (fun _ : H →L[ℂ] H => c) :=
  fun _ _ _ _ => tendsto_const_nhds

theorem comp (hφ : IsNormalFun φ) {Φ : (K →L[ℂ] K) → (H →L[ℂ] H)} (hΦ : IsNormalMap Φ) :
    IsNormalFun (fun T => φ (Φ T)) :=
  fun l T L h => hφ l _ _ (hΦ l T L h)

/-- The vector functionals `T ↦ ⟪ξ, T η⟫` are normal. -/
theorem inner (ξ η : H) : IsNormalFun (fun T : H →L[ℂ] H => ⟪ξ, T η⟫_ℂ) :=
  fun _ _ _ h => ((continuous_const.inner continuous_id).tendsto _).comp (h.tendsto η)

end IsNormalFun

namespace IsNormalMap

variable {Φ : (H →L[ℂ] H) → (K →L[ℂ] K)}

theorem id : IsNormalMap (fun T : H →L[ℂ] H => T) := fun _ _ _ h => h

theorem comp {K' : Type*} [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']
    {Ψ : (K →L[ℂ] K) → (K' →L[ℂ] K')} (hΨ : IsNormalMap Ψ) (hΦ : IsNormalMap Φ) :
    IsNormalMap (fun T => Ψ (Φ T)) :=
  fun l T L h => hΨ l _ _ (hΦ l T L h)

end IsNormalMap

/-! ## Trace-class functionals are normal -/

theorem isNormalFun_of_traceClass {φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ}
    (hφ : Density.IsTraceClassFunctional φ) : IsNormalFun φ := by
  obtain ⟨v, w, hs, h⟩ := hφ
  intro ι l T L ⟨⟨C, hC⟩, ht⟩
  simp only [h]
  refine tendsto_tsum_of_dominated_convergence (bound := fun k => max C 0 * (‖v k‖ * ‖w k‖))
    (hs.mul_left _) (fun k => ?_) (Eventually.of_forall fun i k => ?_)
  · exact ((continuous_const.inner continuous_id).tendsto _).comp (ht (w k))
  · calc ‖⟪v k, T i (w k)⟫_ℂ‖ ≤ ‖v k‖ * ‖T i (w k)‖ := norm_inner_le_norm _ _
      _ ≤ ‖v k‖ * (‖T i‖ * ‖w k‖) := by gcongr; exact (T i).le_opNorm _
      _ ≤ ‖v k‖ * (max C 0 * ‖w k‖) := by gcongr; exact (hC i).trans (le_max_left _ _)
      _ = max C 0 * (‖v k‖ * ‖w k‖) := by ring

end VN

end CommutingRepetition
