/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Game/Mixture.lean
-/
/-
# Classical mixtures of commuting strategies

Aux layer for nodes 1.4.1 and 1.6.1: a strategy that first samples a
finite classical seed (shared randomness) and then plays a seed-indexed
commuting strategy on a common state is itself a legal commuting strategy,
realized block-diagonally on the finite ℓ²-power `⊕_ω H`. Its correlation
is the ν-mixture of the component correlations.

[07_main_theorem.tex sec 7.2 "Tensor this resource with the finite
classical flag"; sec 7.4 "Presample the other n−1 question pairs using
shared classical randomness"]
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Game.Strategy

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped BigOperators InnerProductSpace

variable {Seed : Type} [Fintype Seed]
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Blockwise (diagonal) operator on the finite ℓ²-power `⊕_ω H`. -/
noncomputable def diagCLM (T : Seed → H →L[ℂ] H) :
    PiLp 2 (fun _ : Seed => H) →L[ℂ] PiLp 2 (fun _ : Seed => H) :=
  ((PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : Seed => H)).symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.pi fun ω =>
      (T ω).comp (PiLp.proj 2 (fun _ : Seed => H) ω))

@[simp] theorem diagCLM_apply (T : Seed → H →L[ℂ] H)
    (v : PiLp 2 (fun _ : Seed => H)) (ω : Seed) :
    diagCLM T v ω = T ω (v ω) := rfl

theorem diagCLM_sum {κ : Type*} (s : Finset κ)
    (T : κ → Seed → H →L[ℂ] H) :
    (∑ k ∈ s, diagCLM (T k)) = diagCLM (fun ω => ∑ k ∈ s, T k ω) := by
  ext v ω
  simp

theorem diagCLM_one :
    diagCLM (fun _ : Seed => (1 : H →L[ℂ] H)) = 1 := by
  ext v ω
  simp

theorem diagCLM_mul (T S : Seed → H →L[ℂ] H) :
    diagCLM T * diagCLM S = diagCLM (fun ω => T ω * S ω) := by
  ext v ω
  simp [ContinuousLinearMap.mul_apply]

theorem diagCLM_commute {T S : Seed → H →L[ℂ] H}
    (h : ∀ ω, Commute (T ω) (S ω)) :
    Commute (diagCLM T) (diagCLM S) := by
  unfold Commute SemiconjBy
  rw [diagCLM_mul, diagCLM_mul]
  congr 1
  funext ω
  exact h ω

theorem diagCLM_isPositive {T : Seed → H →L[ℂ] H}
    (h : ∀ ω, (T ω).IsPositive) :
    (diagCLM T).IsPositive := by
  constructor
  · intro u v
    have hsym : ∀ ω, ∀ x y : H, ⟪T ω x, y⟫_ℂ = ⟪x, T ω y⟫_ℂ := fun ω =>
      (h ω).1
    calc ⟪diagCLM T u, v⟫_ℂ
        = ∑ ω : Seed, ⟪T ω (u ω), v ω⟫_ℂ := PiLp.inner_apply _ _
      _ = ∑ ω : Seed, ⟪u ω, T ω (v ω)⟫_ℂ :=
          Finset.sum_congr rfl fun ω _ => hsym ω (u ω) (v ω)
      _ = ⟪u, diagCLM T v⟫_ℂ := (PiLp.inner_apply u (diagCLM T v)).symm
  · intro v
    have hterm : ∀ ω : Seed, 0 ≤ (⟪T ω (v ω), v ω⟫_ℂ).re := fun ω => by
      have := (h ω).2 (v ω)
      simpa [ContinuousLinearMap.reApplyInnerSelf] using this
    have hcalc : (diagCLM T).reApplyInnerSelf v
        = ∑ ω : Seed, (⟪T ω (v ω), v ω⟫_ℂ).re := by
      rw [ContinuousLinearMap.reApplyInnerSelf]
      rw [show (⟪diagCLM T v, v⟫_ℂ) = ∑ ω : Seed, ⟪T ω (v ω), v ω⟫_ℂ from
        PiLp.inner_apply _ _]
      exact Complex.re_sum _ _
    rw [hcalc]
    exact Finset.sum_nonneg fun ω _ => hterm ω

/-- A finite sum of positive operators is positive. -/
theorem isPositive_sum {κ : Type*} (s : Finset κ) (T : κ → H →L[ℂ] H)
    (h : ∀ k ∈ s, (T k).IsPositive) : (∑ k ∈ s, T k).IsPositive := by
  constructor
  · intro u v
    show ⟪(∑ k ∈ s, T k) u, v⟫_ℂ = ⟪u, (∑ k ∈ s, T k) v⟫_ℂ
    have hu : (∑ k ∈ s, T k) u = ∑ k ∈ s, T k u := by simp
    have hv : (∑ k ∈ s, T k) v = ∑ k ∈ s, T k v := by simp
    calc ⟪(∑ k ∈ s, T k) u, v⟫_ℂ
        = ∑ k ∈ s, ⟪T k u, v⟫_ℂ := by rw [hu, sum_inner]
      _ = ∑ k ∈ s, ⟪u, T k v⟫_ℂ :=
          Finset.sum_congr rfl fun k hk => (h k hk).1 u v
      _ = ⟪u, (∑ k ∈ s, T k) v⟫_ℂ := by rw [hv, inner_sum]
  · intro v
    have hcalc : (∑ k ∈ s, T k).reApplyInnerSelf v
        = ∑ k ∈ s, (T k).reApplyInnerSelf v := by
      simp only [ContinuousLinearMap.reApplyInnerSelf,
        ContinuousLinearMap.sum_apply, sum_inner, map_sum]
    rw [hcalc]
    exact Finset.sum_nonneg fun k hk => (h k hk).2 v

/-- An if-then-else between a positive operator and zero is positive. -/
theorem isPositive_ite (c : Prop) [Decidable c] {T : H →L[ℂ] H}
    (h : c → T.IsPositive) :
    (if c then T else 0).IsPositive := by
  split
  · exact h ‹c›
  · exact ContinuousLinearMap.isPositive_zero

/-- The mixed state `⊕_ω √(ν ω) • ψ`. -/
noncomputable def mixState (ν : Seed → ℝ) (ψ : H) :
    PiLp 2 (fun _ : Seed => H) :=
  WithLp.toLp 2 (fun ω => Real.sqrt (ν ω) • ψ)

@[simp] theorem mixState_apply (ν : Seed → ℝ) (ψ : H) (ω : Seed) :
    mixState ν ψ ω = Real.sqrt (ν ω) • ψ := rfl

theorem mixState_norm (ν : Seed → ℝ) (hν0 : ∀ ω, 0 ≤ ν ω)
    (hν1 : (∑ ω : Seed, ν ω) = 1) (ψ : H) (hψ : ‖ψ‖ = 1) :
    ‖mixState ν ψ‖ = 1 := by
  have hsq : ‖mixState ν ψ‖ ^ 2 = 1 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc (∑ ω : Seed, ‖mixState ν ψ ω‖ ^ 2)
        = ∑ ω : Seed, ν ω := by
          refine Finset.sum_congr rfl fun ω _ => ?_
          rw [mixState_apply, norm_smul, hψ, mul_one, Real.norm_eq_abs,
            abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hν0 ω)]
      _ = 1 := hν1
  nlinarith [norm_nonneg (mixState ν ψ), hsq]

/-- **Seed mixture of commuting strategies** (shared classical
randomness): sampling `ω ∼ ν` and playing the `ω`-th effect families on a
common unit state `ψ` is a legal commuting strategy on `⊕_ω H`. -/
noncomputable def CommutingStrategy.seedMixture
    {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (ν : Seed → ℝ) (hν0 : ∀ ω, 0 ≤ ν ω) (hν1 : (∑ ω : Seed, ν ω) = 1)
    (ψ : H) (hψ : ‖ψ‖ = 1)
    (E : Seed → X → A → H →L[ℂ] H) (F : Seed → Y → B → H →L[ℂ] H)
    (hE_pos : ∀ ω x a, (E ω x a).IsPositive)
    (hF_pos : ∀ ω y b, (F ω y b).IsPositive)
    (hE_sum : ∀ ω x, (∑ a : A, E ω x a) = 1)
    (hF_sum : ∀ ω y, (∑ b : B, F ω y b) = 1)
    (hcomm : ∀ ω x y a b, Commute (E ω x a) (F ω y b)) :
    CommutingStrategy.{0} X Y A B where
  H := PiLp 2 (fun _ : Seed => H)
  ψ := mixState ν ψ
  ψ_norm := mixState_norm ν hν0 hν1 ψ hψ
  E x a := diagCLM (fun ω => E ω x a)
  F y b := diagCLM (fun ω => F ω y b)
  E_pos x a := diagCLM_isPositive fun ω => hE_pos ω x a
  F_pos y b := diagCLM_isPositive fun ω => hF_pos ω y b
  E_sum x := by
    rw [diagCLM_sum]
    rw [show (fun ω => ∑ a : A, E ω x a) = fun _ => (1 : H →L[ℂ] H) by
      funext ω; exact hE_sum ω x]
    exact diagCLM_one
  F_sum y := by
    rw [diagCLM_sum]
    rw [show (fun ω => ∑ b : B, F ω y b) = fun _ => (1 : H →L[ℂ] H) by
      funext ω; exact hF_sum ω y]
    exact diagCLM_one
  commutes x y a b := diagCLM_commute fun ω => hcomm ω x y a b

/-- The mixture's correlation is the `ν`-average of the component
correlations. -/
theorem CommutingStrategy.seedMixture_correlation
    {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (ν : Seed → ℝ) (hν0 : ∀ ω, 0 ≤ ν ω) (hν1 : (∑ ω : Seed, ν ω) = 1)
    (ψ : H) (hψ : ‖ψ‖ = 1)
    (E : Seed → X → A → H →L[ℂ] H) (F : Seed → Y → B → H →L[ℂ] H)
    (hE_pos : ∀ ω x a, (E ω x a).IsPositive)
    (hF_pos : ∀ ω y b, (F ω y b).IsPositive)
    (hE_sum : ∀ ω x, (∑ a : A, E ω x a) = 1)
    (hF_sum : ∀ ω y, (∑ b : B, F ω y b) = 1)
    (hcomm : ∀ ω x y a b, Commute (E ω x a) (F ω y b))
    (x : X) (y : Y) (a : A) (b : B) :
    (CommutingStrategy.seedMixture ν hν0 hν1 ψ hψ E F hE_pos hF_pos
        hE_sum hF_sum hcomm).correlation x y a b
      = ∑ ω : Seed, ν ω * (⟪ψ, E ω x a (F ω y b ψ)⟫_ℂ).re := by
  show (⟪mixState ν ψ, diagCLM (fun ω => E ω x a)
      ((diagCLM fun ω => F ω y b) (mixState ν ψ))⟫_ℂ).re = _
  rw [show (⟪mixState ν ψ, diagCLM (fun ω => E ω x a)
      ((diagCLM fun ω => F ω y b) (mixState ν ψ))⟫_ℂ)
      = ∑ ω : Seed, ⟪mixState ν ψ ω,
          E ω x a (F ω y b (mixState ν ψ ω))⟫_ℂ from PiLp.inner_apply _ _]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [mixState_apply,
    RCLike.real_smul_eq_coe_smul (K := ℂ) (Real.sqrt (ν ω)),
    map_smul, map_smul, inner_smul_left, inner_smul_right,
    RCLike.conj_ofReal, ← mul_assoc, ← RCLike.ofReal_mul,
    Real.mul_self_sqrt (hν0 ω), ← RCLike.re_to_complex]
  exact RCLike.re_ofReal_mul _ _

end CommutingRepetition
