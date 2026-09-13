/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/MvN/PolarDecomp.lean
-/
/-
# Polar decomposition inside a von Neumann algebra

Proof-side discharge of field **H6** of the structure-theory interface
(`Orthogonalization/MvN/Interface.lean`; Anantharaman–Popa, Prop. 2.2.4): for
`x ∈ M` there is a partial isometry `u ∈ M` from the right support of `x` onto
its left support with `x = u |x|`, `|x| = √(x* x)`.

The partial isometry is the strong limit of the approximants
`wₙ = x (|x| + εₙ)⁻¹`, `εₙ = 1/(n+1)`, which lie in `M` (functional calculus of
`|x| ∈ M`) and are contractions because `‖x ξ‖ = ‖|x| ξ‖`:

* on the range of `|x|`, `wₙ (|x| ζ) = x (gₙ(|x|) ζ)` with `gₙ(t) = t/(t + εₙ)`,
  and `‖x (gₙ(|x|) ζ − ζ)‖ = ‖|x| (gₙ(|x|) − 1) ζ‖ ≤ εₙ ‖ζ‖`, so `wₙ (|x| ζ) → x ζ`;
* on the kernel of `|x|` (which is the kernel of `x`) every `wₙ` vanishes;
* `range |x| + ker |x|` is dense (`(range |x|)ᗮ = ker |x|` for the self-adjoint
  `|x|`), so the uniformly bounded sequence `wₙ ξ` is Cauchy for every `ξ`.

The limit `u` satisfies `u |x| = x`, vanishes on `ker x`, and takes its values in
the closure of the range of `x`. The identity `u* u = rightSupport x` follows
from `|x| (1 − u* u) |x| = x* x − x* x = 0` (hence `u* u |x| = |x|`, `x u* u = x`,
`R ≤ u* u`) and `u R = u` (`u* u ≤ R`); the identity `u u* = leftSupport x` from
`u u* x = x` (`L ≤ u u*`) and `L u = u` (`u u* ≤ L`).

No statement of the paper is made here.
-/
import Mathlib
import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.BlockCalc
import MIPRE.Background.Repetition.CommutingRepetition.VN.Generated
import MIPRE.Background.Repetition.CommutingRepetition.VN.MonotoneLimit

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace Orthogonalization.MvN

open scoped InnerProductSpace ComplexOrder
open Filter Topology CommutingRepetition.VN CommutingRepetition.StrongLimit

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### The norm identity `‖x ξ‖ = ‖s ξ‖` for `x* x = s* s` -/

theorem inner_apply_self_eq (x : H →L[ℂ] H) (ξ : H) :
    ⟪x ξ, x ξ⟫_ℂ = ⟪ξ, (star x * x) ξ⟫_ℂ := by
  rw [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

/-- Two operators with the same modulus, `x* x = s* s`, have the same "length": `‖x ξ‖ = ‖s ξ‖`.
In particular they have the same kernel. -/
theorem norm_apply_eq_of_star_mul_self_eq {x s : H →L[ℂ] H} (h : star x * x = star s * s)
    (ξ : H) : ‖x ξ‖ = ‖s ξ‖ := by
  have h1 : ⟪x ξ, x ξ⟫_ℂ = ⟪s ξ, s ξ⟫_ℂ := by rw [inner_apply_self_eq, inner_apply_self_eq, h]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h1
  have h2 : ‖x ξ‖ ^ 2 = ‖s ξ‖ ^ 2 := by exact_mod_cast h1
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

/-! ### Range and kernel of a self-adjoint operator -/

/-- For a self-adjoint operator, `(range s)ᗮ = ker s`. -/
theorem orthogonal_range_eq_ker {s : H →L[ℂ] H} (hs : IsSelfAdjoint s) :
    (LinearMap.range (s : H →ₗ[ℂ] H))ᗮ = LinearMap.ker (s : H →ₗ[ℂ] H) := by
  ext η
  rw [Submodule.mem_orthogonal, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  constructor
  · intro h
    refine ext_inner_left ℂ fun ζ => ?_
    rw [inner_zero_right, ← ContinuousLinearMap.adjoint_inner_left,
      ← ContinuousLinearMap.star_eq_adjoint, hs.star_eq]
    exact h (s ζ) ⟨ζ, rfl⟩
  · rintro h _ ⟨ζ, rfl⟩
    rw [ContinuousLinearMap.coe_coe, ← ContinuousLinearMap.adjoint_inner_right,
      ← ContinuousLinearMap.star_eq_adjoint, hs.star_eq, h, inner_zero_right]

/-- For a self-adjoint operator, `range s + ker s` is dense: its orthogonal complement is
`ker s ∩ (ker s)ᗮ = 0`. -/
theorem sup_range_ker_topologicalClosure {s : H →L[ℂ] H} (hs : IsSelfAdjoint s) :
    (LinearMap.range (s : H →ₗ[ℂ] H) ⊔ LinearMap.ker (s : H →ₗ[ℂ] H)).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, ← Submodule.inf_orthogonal,
    orthogonal_range_eq_ker hs, Submodule.inf_orthogonal_eq_bot]

/-! ### Uniformly bounded sequences converging on a dense set -/

omit [CompleteSpace H] in
/-- A uniformly bounded sequence of operators which converges pointwise on a set `D` has Cauchy
orbits on the closure of `D` (the `ε/3` argument). -/
theorem cauchySeq_apply_of_mem_closure {T : ℕ → H →L[ℂ] H} {C : ℝ} (hC : ∀ n, ‖T n‖ ≤ C)
    {D : Set H} (hD : ∀ η ∈ D, ∃ l, Tendsto (fun n => T n η) atTop (𝓝 l)) {ξ : H}
    (hξ : ξ ∈ closure D) : CauchySeq fun n => T n ξ := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hδ : 0 < ε / (3 * (C + 1)) := by positivity
  obtain ⟨η, hηD, hηξ⟩ := Metric.mem_closure_iff.mp hξ _ hδ
  obtain ⟨l, hl⟩ := hD η hηD
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hl.cauchySeq (ε / 3) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have h1 : ∀ k, ‖T k ξ - T k η‖ ≤ ε / 3 := fun k => by
    rw [← map_sub]
    calc ‖T k (ξ - η)‖ ≤ ‖T k‖ * ‖ξ - η‖ := (T k).le_opNorm _
      _ ≤ (C + 1) * (ε / (3 * (C + 1))) := by
        refine mul_le_mul ((hC k).trans (by linarith)) ?_ (norm_nonneg _) (by linarith)
        rw [dist_eq_norm] at hηξ
        exact hηξ.le
      _ = ε / 3 := by field_simp
  have h2 := hN m hm n hn
  rw [dist_eq_norm] at h2 ⊢
  calc ‖T m ξ - T n ξ‖ = ‖(T m ξ - T m η) + (T m η - T n η) + (T n η - T n ξ)‖ := by
        congr 1; abel
    _ ≤ ‖T m ξ - T m η‖ + ‖T m η - T n η‖ + ‖T n η - T n ξ‖ := norm_add₃_le
    _ < ε / 3 + ε / 3 + ε / 3 := by
        have h3 := h1 n
        rw [norm_sub_rev] at h3
        linarith [h1 m]
    _ = ε := by ring

/-! ### The resolvent approximants `s (s + ε)⁻¹` of a positive operator

For `s ≥ 0` and `ε > 0`, the functions `t ↦ (t + ε)⁻¹` and `t ↦ t/(t + ε)` are continuous on the
spectrum `σ(s) ⊆ [0, ∞)`, `‖s (s + ε)⁻¹‖ ≤ 1`, and `‖s · s (s + ε)⁻¹ − s‖ ≤ ε` because
`|t (t/(t + ε) − 1)| = ε t/(t + ε) ≤ ε` for `t ≥ 0`. -/

theorem continuousOn_inv_add {s : H →L[ℂ] H} (hs : 0 ≤ s) {ε : ℝ} (hε : 0 < ε) :
    ContinuousOn (fun t : ℝ => (t + ε)⁻¹) (spectrum ℝ s) := by
  refine ContinuousOn.inv₀ ((continuousOn_id' _).add continuousOn_const) fun t ht => ?_
  have := spectrum_nonneg_of_nonneg hs ht
  exact (by linarith : (0 : ℝ) < t + ε).ne'

theorem mul_cfc_inv_add {s : H →L[ℂ] H} (hs : 0 ≤ s) {ε : ℝ} (hε : 0 < ε) :
    s * cfc (fun t : ℝ => (t + ε)⁻¹) s = cfc (fun t : ℝ => t * (t + ε)⁻¹) s := by
  rw [cfc_mul (fun t : ℝ => t) (fun t : ℝ => (t + ε)⁻¹) s (continuousOn_id' _)
    (continuousOn_inv_add hs hε), cfc_id' ℝ s (IsSelfAdjoint.of_nonneg hs)]

theorem cfc_inv_add_mul {s : H →L[ℂ] H} (hs : 0 ≤ s) {ε : ℝ} (hε : 0 < ε) :
    cfc (fun t : ℝ => (t + ε)⁻¹) s * s = cfc (fun t : ℝ => t * (t + ε)⁻¹) s := by
  have h := cfc_mul (fun t : ℝ => (t + ε)⁻¹) (fun t : ℝ => t) s (continuousOn_inv_add hs hε)
    (continuousOn_id' _)
  rw [cfc_id' ℝ s (IsSelfAdjoint.of_nonneg hs)] at h
  rw [← h]
  exact cfc_congr fun t _ => mul_comm _ _

theorem norm_cfc_mul_inv_add_le {s : H →L[ℂ] H} (hs : 0 ≤ s) {ε : ℝ} (hε : 0 < ε) :
    ‖cfc (fun t : ℝ => t * (t + ε)⁻¹) s‖ ≤ 1 := by
  refine norm_cfc_le zero_le_one fun t ht => ?_
  have ht0 := spectrum_nonneg_of_nonneg hs ht
  rw [Real.norm_eq_abs, ← div_eq_mul_inv, abs_of_nonneg (by positivity)]
  exact (div_le_one (by positivity)).mpr (by linarith)

theorem mul_cfc_sub_self_eq {s : H →L[ℂ] H} (hs : 0 ≤ s) {ε : ℝ} (hε : 0 < ε) :
    s * cfc (fun t : ℝ => t * (t + ε)⁻¹) s - s =
      cfc (fun t : ℝ => t * (t * (t + ε)⁻¹) - t) s := by
  have hc : ContinuousOn (fun t : ℝ => t * (t + ε)⁻¹) (spectrum ℝ s) :=
    (continuousOn_id' _).mul (continuousOn_inv_add hs hε)
  rw [cfc_sub (fun t : ℝ => t * (t * (t + ε)⁻¹)) (fun t : ℝ => t) s ((continuousOn_id' _).mul hc)
    (continuousOn_id' _), cfc_mul (fun t : ℝ => t) (fun t : ℝ => t * (t + ε)⁻¹) s
    (continuousOn_id' _) hc, cfc_id' ℝ s (IsSelfAdjoint.of_nonneg hs)]

theorem norm_mul_cfc_sub_self_le {s : H →L[ℂ] H} (hs : 0 ≤ s) {ε : ℝ} (hε : 0 < ε) :
    ‖s * cfc (fun t : ℝ => t * (t + ε)⁻¹) s - s‖ ≤ ε := by
  rw [mul_cfc_sub_self_eq hs hε]
  refine norm_cfc_le hε.le fun t ht => ?_
  have ht0 := spectrum_nonneg_of_nonneg hs ht
  have hpos : 0 < t + ε := by linarith
  have : t * (t * (t + ε)⁻¹) - t = -(ε * t / (t + ε)) := by field_simp; ring
  rw [this, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity), div_le_iff₀ hpos]
  nlinarith

/-! ### A C⋆-algebraic cancellation -/

/-- If `a ≥ 0`, `s = s*` and `s a s = 0`, then `a s = 0`: `(√a s)* (√a s) = s a s = 0`. -/
theorem mul_eq_zero_of_conj_eq_zero {a s : H →L[ℂ] H} (ha : 0 ≤ a) (hs : IsSelfAdjoint s)
    (h : s * a * s = 0) : a * s = 0 := by
  have hT : CFC.sqrt a * CFC.sqrt a = a := CFC.sqrt_mul_sqrt_self a ha
  have hTsa : star (CFC.sqrt a) = CFC.sqrt a :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)).star_eq
  have h0 : star (CFC.sqrt a * s) * (CFC.sqrt a * s) = 0 := by
    calc star (CFC.sqrt a * s) * (CFC.sqrt a * s)
        = s * (CFC.sqrt a * CFC.sqrt a) * s := by
          rw [star_mul, hTsa, hs.star_eq]; simp only [mul_assoc]
      _ = 0 := by rw [hT, h]
  have h1 : CFC.sqrt a * s = 0 := (CStarRing.star_mul_self_eq_zero_iff _).mp h0
  rw [← hT, mul_assoc, h1, mul_zero]

/-! ### The strong limit of the approximants -/

/-- **The polar partial isometry as a strong limit.** For `x ∈ M` and `s ∈ M` with `s ≥ 0` and
`x* x = s²` (so `s = |x|`), the contractions `wₙ = x (s + εₙ)⁻¹ ∈ M` converge strongly to a
contraction `u ∈ M` with `u s = x`, `u = 0` on `ker x`, and `u ξ ∈ closure (range x)` for all
`ξ`. -/
theorem exists_strong_limit (M : VonNeumannAlgebra H) {x s : H →L[ℂ] H} (hx : x ∈ M)
    (hsM : s ∈ M) (hs : 0 ≤ s) (hxs : star x * x = s * s) :
    ∃ u ∈ M, ‖u‖ ≤ 1 ∧ u * s = x ∧ (∀ η, x η = 0 → u η = 0) ∧
      ∀ ξ, u ξ ∈ (LinearMap.range (x : H →ₗ[ℂ] H)).topologicalClosure := by
  have hssa : IsSelfAdjoint s := IsSelfAdjoint.of_nonneg hs
  have hnorm : ∀ ξ, ‖x ξ‖ = ‖s ξ‖ :=
    norm_apply_eq_of_star_mul_self_eq (by rw [hxs, hssa.star_eq])
  have hker : ∀ η, s η = 0 → x η = 0 := fun η hη => by
    rw [← norm_eq_zero, hnorm, hη, norm_zero]
  have hker' : ∀ η, x η = 0 → s η = 0 := fun η hη => by
    rw [← norm_eq_zero, ← hnorm, hη, norm_zero]
  /- The approximants `wₙ = x (s + εₙ)⁻¹`, contractions in `M`. -/
  obtain ⟨ε, hε⟩ : ∃ ε : ℕ → ℝ, ∀ n, ε n = 1 / ((n : ℝ) + 1) := ⟨_, fun _ => rfl⟩
  have hεpos : ∀ n, 0 < ε n := fun n => by rw [hε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).congr fun n => (hε n).symm
  obtain ⟨w, hw⟩ : ∃ w : ℕ → H →L[ℂ] H, ∀ n, w n = x * cfc (fun t : ℝ => (t + ε n)⁻¹) s :=
    ⟨_, fun _ => rfl⟩
  have hwM : ∀ n, w n ∈ M := fun n => by rw [hw n]; exact mul_mem hx (cfc_real_mem M hsM _)
  have hw1 : ∀ n, ‖w n‖ ≤ 1 := fun n => by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ξ => ?_
    rw [one_mul, hw n, mul_apply_eq_comp, hnorm, ← mul_apply_eq_comp, mul_cfc_inv_add hs (hεpos n)]
    calc ‖cfc (fun t : ℝ => t * (t + ε n)⁻¹) s ξ‖
        ≤ ‖cfc (fun t : ℝ => t * (t + ε n)⁻¹) s‖ * ‖ξ‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖ξ‖ :=
          mul_le_mul_of_nonneg_right (norm_cfc_mul_inv_add_le hs (hεpos n)) (norm_nonneg _)
      _ = ‖ξ‖ := one_mul _
  /- Convergence on the range of `s`: `wₙ (s ζ) = x (gₙ(s) ζ) → x ζ`. -/
  have hconv : ∀ ζ, Tendsto (fun n => w n (s ζ)) atTop (𝓝 (x ζ)) := fun ζ => by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun n => ε n * ‖ζ‖) atTop (𝓝 0) := by
      have := hεlim.mul_const ‖ζ‖
      rwa [zero_mul] at this
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
    have e : w n (s ζ) - x ζ = x ((cfc (fun t : ℝ => t * (t + ε n)⁻¹) s - 1) ζ) := by
      rw [hw n, mul_apply_eq_comp, ← cfc_inv_add_mul hs (hεpos n), sub_apply, one_apply_eq_self,
        map_sub, mul_apply_eq_comp]
    rw [e, hnorm, ← mul_apply_eq_comp, mul_sub, mul_one]
    calc ‖(s * cfc (fun t : ℝ => t * (t + ε n)⁻¹) s - s) ζ‖
        ≤ ‖s * cfc (fun t : ℝ => t * (t + ε n)⁻¹) s - s‖ * ‖ζ‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ε n * ‖ζ‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_cfc_sub_self_le hs (hεpos n)) (norm_nonneg _)
  /- Vanishing on the kernel of `s`. -/
  have hwker : ∀ n η, s η = 0 → w n η = 0 := fun n η hη => by
    rw [hw n, mul_apply_eq_comp]
    refine hker _ ?_
    rw [← mul_apply_eq_comp, mul_cfc_inv_add hs (hεpos n), ← cfc_inv_add_mul hs (hεpos n),
      mul_apply_eq_comp, hη, map_zero]
  /- Existence of the limits: convergence on the dense subspace `range s + ker s` and uniform
  boundedness. -/
  have hex : ∀ ξ, ∃ l, Tendsto (fun n => w n ξ) atTop (𝓝 l) := fun ξ => by
    refine cauchySeq_tendsto_of_complete (cauchySeq_apply_of_mem_closure hw1
      (D := ((LinearMap.range (s : H →ₗ[ℂ] H) ⊔ LinearMap.ker (s : H →ₗ[ℂ] H) :
        Submodule ℂ H) : Set H)) ?_ ?_)
    · intro η hη
      rw [SetLike.mem_coe, Submodule.mem_sup] at hη
      obtain ⟨_, ⟨ζ, rfl⟩, z, hz, rfl⟩ := hη
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hz
      refine ⟨x ζ, (hconv ζ).congr fun n => ?_⟩
      rw [ContinuousLinearMap.coe_coe, map_add, hwker n z hz, add_zero]
    · rw [← Submodule.topologicalClosure_coe, sup_range_ker_topologicalClosure hssa]
      exact Submodule.mem_top
  /- The strong limit `u`. -/
  obtain ⟨u, hu⟩ : ∃ u : H →L[ℂ] H, ∀ ξ, Tendsto (fun n => w n ξ) atTop (𝓝 (u ξ)) :=
    ⟨_, pointwiseLimit_tendsto w 1 hw1 hex⟩
  refine ⟨u, mem_of_tendsto_seq M hwM hu, ?_, ?_, ?_, ?_⟩
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ξ => ?_
    rw [one_mul]
    refine le_of_tendsto' (hu ξ).norm fun n => ?_
    calc ‖w n ξ‖ ≤ ‖w n‖ * ‖ξ‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖ξ‖ := mul_le_mul_of_nonneg_right (hw1 n) (norm_nonneg _)
      _ = ‖ξ‖ := one_mul _
  · refine ContinuousLinearMap.ext fun ζ => ?_
    rw [mul_apply_eq_comp]
    exact tendsto_nhds_unique (hu (s ζ)) (hconv ζ)
  · intro η hη
    refine tendsto_nhds_unique (hu η) ?_
    simp only [hwker _ η (hker' η hη)]
    exact tendsto_const_nhds
  · intro ξ
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    refine mem_closure_of_tendsto (hu ξ) (Eventually.of_forall fun n => ?_)
    rw [hw n, SetLike.mem_coe, LinearMap.mem_range]
    exact ⟨_, rfl⟩

/-! ### The polar decomposition -/

/-- **Polar decomposition inside a von Neumann algebra** (Anantharaman–Popa 2.2.4): for
`x ∈ M` there is `u ∈ M` with `u* u = rightSupport x`, `u u* = leftSupport x` and
`x = u √(x* x)`. Discharges interface field H6. -/
theorem exists_polar (M : VonNeumannAlgebra H) (x : H →L[ℂ] H) (hx : x ∈ M) :
    ∃ u ∈ M, star u * u = rightSupport x ∧ u * star u = leftSupport x ∧
      x = u * CFC.sqrt (star x * x) := by
  have hA : 0 ≤ star x * x := star_mul_self_nonneg x
  have hs : 0 ≤ CFC.sqrt (star x * x) := CFC.sqrt_nonneg _
  have hxs : star x * x = CFC.sqrt (star x * x) * CFC.sqrt (star x * x) :=
    (CFC.sqrt_mul_sqrt_self _ hA).symm
  have hsM : CFC.sqrt (star x * x) ∈ M := Blocks.sqrt_mem M (mul_mem (star_mem hx) hx) hA
  obtain ⟨u, huM, hu1, hus, huker, hucl⟩ := exists_strong_limit M hx hsM hs hxs
  generalize CFC.sqrt (star x * x) = s at hs hxs hus ⊢
  have hssa : IsSelfAdjoint s := IsSelfAdjoint.of_nonneg hs
  have hRproj : IsStarProjection (rightSupport x) := isStarProjection_rightSupport x
  /- `Q = u* u` is a positive contraction with `s Q s = s s`, hence `Q s = s`. -/
  have hQ0 : 0 ≤ star u * u := star_mul_self_nonneg u
  have hQ1 : star u * u ≤ 1 := by
    rw [← CStarAlgebra.norm_le_one_iff_of_nonneg _ hQ0, CStarRing.norm_star_mul_self]
    exact mul_le_one₀ hu1 (norm_nonneg _) hu1
  have hQsa : star (star u * u) = star u * u := (IsSelfAdjoint.star_mul_self u).star_eq
  have hsQs : s * (1 - star u * u) * s = 0 := by
    have h1 : star x * x = s * (star u * u) * s := by
      rw [← hus, star_mul, hssa.star_eq]
      simp only [mul_assoc]
    rw [mul_sub, mul_one, sub_mul, ← h1, hxs, sub_self]
  have hQs : star u * u * s = s := by
    have h := mul_eq_zero_of_conj_eq_zero (sub_nonneg.mpr hQ1) hssa hsQs
    rwa [sub_mul, one_mul, sub_eq_zero, eq_comm] at h
  have hsQ : s * (star u * u) = s := by
    have h := congrArg star hQs
    rwa [star_mul, hQsa, hssa.star_eq] at h
  /- `x Q = x`, so `R ≤ Q`; and `u R = u` because `u` vanishes on `ker x = range (1 − R)`, so
  `Q ≤ R`. -/
  have hxQ : x * (star u * u) = x := by rw [← hus, mul_assoc, hsQ]
  have hRQ : rightSupport x * (star u * u) = rightSupport x := rightSupport_mul_eq_self_of hxQ
  have huR : u * rightSupport x = u := by
    refine ContinuousLinearMap.ext fun ξ => ?_
    rw [mul_apply_eq_comp, ← sub_eq_zero, ← map_sub]
    refine huker _ ?_
    rw [map_sub, ← mul_apply_eq_comp, mul_rightSupport, sub_self]
  have hQR : star u * u * rightSupport x = star u * u := by rw [mul_assoc, huR]
  have huu : star u * u = rightSupport x := by
    have h := congrArg star hRQ
    rw [star_mul, hQsa, hRproj.isSelfAdjoint.star_eq] at h
    exact hQR.symm.trans h
  /- `P = u u*` is a projection with `P x = x`, so `L ≤ P`; and `L u = u` because `u` takes its
  values in the closure of the range of `x`, so `P ≤ L`. -/
  have hP : IsStarProjection (u * star u) := isStarProjection_mul_star_of (huu ▸ hRproj)
  have hPx : u * star u * x = x := by
    calc u * star u * x = u * (star u * u) * s := by rw [← hus]; simp only [mul_assoc]
      _ = x := by rw [huu, huR, hus]
  have hLP : leftSupport x * (u * star u) = leftSupport x := leftSupport_mul_eq_self_of hP hPx
  have hLu : leftSupport x * u = u := by
    refine ContinuousLinearMap.ext fun ξ => ?_
    rw [mul_apply_eq_comp]
    exact Submodule.starProjection_eq_self_iff.mpr (hucl ξ)
  have huu' : u * star u = leftSupport x := by
    calc u * star u = leftSupport x * u * star u := by rw [hLu]
      _ = leftSupport x := by rw [mul_assoc, hLP]
  exact ⟨u, huM, huu, huu', hus.symm⟩

end Orthogonalization.MvN
