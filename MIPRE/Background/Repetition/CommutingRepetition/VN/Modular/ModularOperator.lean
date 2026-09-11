/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/Modular/ModularOperator.lean
-/
/-
# The operators `P`, `Q`, `R = P + Q` of Rieffel–van Daele (stage E4.2a)

For the standard subspace `𝒦 = closure (M_s Ω)` of a cyclic separating vector
(`VN/Modular/RealSubspace.lean`), let `P, Q` be the real orthogonal
projections onto `𝒦` and `i𝒦`.  Then `Q = i P i⁻¹`, `R := P + Q` is
complex-linear, self-adjoint, `0 ≤ R ≤ 2`, and `R`, `2 − R` are injective
(Rieffel–van Daele Prop. 2.2(1) and Prop. 3.1); `P − Q` is conjugate-linear;
`R Ω = Ω`.  The modular operator is `Δ = (2 − R) R⁻¹`, and the modular group
`Δ^{it} = (2 − R)^{it} R^{-it}` is a bounded Borel function of `R`
(`VN/Modular/ModularGroup.lean`).  Source: `PLAN-tomita.md` §0.1.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.Modular.RealSubspace

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace VN

namespace Modular

open scoped InnerProductSpace ComplexOrder
open Filter Topology ClosedSubmodule

set_option linter.unusedSectionVars false

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ## Real-linear operators commuting with `i` are complex-linear -/

/-- A bounded real-linear operator commuting with multiplication by `i`, as a complex-linear
operator. -/
noncomputable def complexify (T : K →L[ℝ] K) (hT : ∀ x, T (Complex.I • x) = Complex.I • T x) :
    K →L[ℂ] K where
  toFun := T
  map_add' := map_add T
  map_smul' := fun c x => by
    show T (c • x) = c • T x
    have hre : ∀ (r : ℝ) (y : K), T ((r : ℂ) • y) = (r : ℂ) • T y := fun r y => by
      have e1 : ((r : ℂ) • y) = r • y := (RCLike.real_smul_eq_coe_smul (K := ℂ) r y).symm
      have e2 : ((r : ℂ) • T y) = r • T y := (RCLike.real_smul_eq_coe_smul (K := ℂ) r (T y)).symm
      rw [e1, e2, map_smul]
    have hc : c • x = (c.re : ℂ) • x + (c.im : ℂ) • (Complex.I • x) := by
      rw [smul_smul, ← add_smul, Complex.re_add_im]
    have hc' : c • T x = (c.re : ℂ) • T x + (c.im : ℂ) • (Complex.I • T x) := by
      rw [smul_smul, ← add_smul, Complex.re_add_im]
    rw [hc, map_add, hre, hre, hT, hc']
  cont := T.continuous

theorem complexify_apply (T : K →L[ℝ] K) (hT : ∀ x, T (Complex.I • x) = Complex.I • T x) (x : K) :
    complexify T hT x = T x := rfl

/-- A complex-linear operator whose real quadratic form is symmetric is symmetric. -/
theorem inner_eq_of_re_eq {A : K →L[ℂ] K} (h : ∀ x y, (⟪A x, y⟫_ℂ).re = (⟪x, A y⟫_ℂ).re)
    (x y : K) : ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ := by
  apply Complex.ext
  · exact h x y
  · have := h x (Complex.I • y)
    rw [inner_smul_right, map_smul, inner_smul_right, Complex.I_mul_re, Complex.I_mul_re] at this
    exact neg_inj.mp this

theorem inner_I_smul_I_smul (a b : K) : inner ℝ (Complex.I • a) (Complex.I • b) = inner ℝ a b := by
  rw [inner_real_eq_re_inner, inner_real_eq_re_inner, inner_smul_left, inner_smul_right,
    Complex.conj_I, ← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]

/-! ## The real projections `P` and `Q` -/

variable (M : VonNeumannAlgebra K) (Ω : K)

/-- The real orthogonal projection onto `𝒦`. -/
noncomputable def Pre : K →L[ℝ] K := (Kre M Ω).toSubmodule.starProjection

/-- The real orthogonal projection onto `i𝒦`. -/
noncomputable def Qre : K →L[ℝ] K := (Kre M Ω).mulI.toSubmodule.starProjection

theorem Pre_apply_mem (x : K) : Pre M Ω x ∈ Kre M Ω :=
  Submodule.starProjection_apply_mem _ x

theorem Qre_apply_mem (x : K) : Qre M Ω x ∈ (Kre M Ω).mulI :=
  Submodule.starProjection_apply_mem _ x

theorem Pre_eq_self {x : K} (hx : x ∈ Kre M Ω) : Pre M Ω x = x :=
  Submodule.starProjection_eq_self_iff.mpr hx

theorem Qre_eq_self {x : K} (hx : x ∈ (Kre M Ω).mulI) : Qre M Ω x = x :=
  Submodule.starProjection_eq_self_iff.mpr hx

theorem Pre_Pre (x : K) : Pre M Ω (Pre M Ω x) = Pre M Ω x := Pre_eq_self M Ω (Pre_apply_mem M Ω x)

theorem Qre_Qre (x : K) : Qre M Ω (Qre M Ω x) = Qre M Ω x := Qre_eq_self M Ω (Qre_apply_mem M Ω x)

theorem inner_Pre_left (x y : K) : inner ℝ (Pre M Ω x) y = inner ℝ x (Pre M Ω y) :=
  Submodule.inner_starProjection_left_eq_right _ x y

theorem inner_Qre_left (x y : K) : inner ℝ (Qre M Ω x) y = inner ℝ x (Qre M Ω y) :=
  Submodule.inner_starProjection_left_eq_right _ x y

theorem inner_Pre_self (x : K) : inner ℝ (Pre M Ω x) x = ‖Pre M Ω x‖ ^ 2 :=
  calc inner ℝ (Pre M Ω x) x = inner ℝ (Pre M Ω (Pre M Ω x)) x := by rw [Pre_Pre]
    _ = inner ℝ (Pre M Ω x) (Pre M Ω x) := inner_Pre_left M Ω _ x
    _ = ‖Pre M Ω x‖ ^ 2 := real_inner_self_eq_norm_sq _

theorem inner_Qre_self (x : K) : inner ℝ (Qre M Ω x) x = ‖Qre M Ω x‖ ^ 2 :=
  calc inner ℝ (Qre M Ω x) x = inner ℝ (Qre M Ω (Qre M Ω x)) x := by rw [Qre_Qre]
    _ = inner ℝ (Qre M Ω x) (Qre M Ω x) := inner_Qre_left M Ω _ x
    _ = ‖Qre M Ω x‖ ^ 2 := real_inner_self_eq_norm_sq _

theorem norm_Pre_le (x : K) : ‖Pre M Ω x‖ ≤ ‖x‖ := Submodule.norm_starProjection_apply_le _ x

theorem norm_Qre_le (x : K) : ‖Qre M Ω x‖ ≤ ‖x‖ := Submodule.norm_starProjection_apply_le _ x

theorem Pre_eq_zero_iff {x : K} : Pre M Ω x = 0 ↔ x ∈ ((Kre M Ω).toSubmodule)ᗮ :=
  Submodule.starProjection_apply_eq_zero_iff _

theorem Qre_eq_zero_iff {x : K} : Qre M Ω x = 0 ↔ x ∈ ((Kre M Ω).mulI.toSubmodule)ᗮ :=
  Submodule.starProjection_apply_eq_zero_iff _

theorem Pre_Ω : Pre M Ω Ω = Ω := Pre_eq_self M Ω (Ω_mem_Kre M Ω)

theorem Qre_Ω : Qre M Ω Ω = 0 :=
  (Qre_eq_zero_iff M Ω).mpr
    ((ClosedSubmodule.mem_orthogonal_toSubmodule_iff _ _).mpr (Ω_mem_symplComp M Ω))

/-- `Q = i P i⁻¹`. -/
theorem Qre_eq (x : K) : Qre M Ω x = Complex.I • Pre M Ω ((-Complex.I) • x) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · exact I_smul_mem_mulI_Kre M Ω (Pre_apply_mem M Ω _)
  · intro w hw
    have hw' : (-Complex.I) • w ∈ Kre M Ω := (mem_mulI_Kre_iff M Ω).mp hw
    have hw2 : w = Complex.I • ((-Complex.I) • w) := by
      rw [smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]
    have e : x - Complex.I • Pre M Ω ((-Complex.I) • x) =
        Complex.I • (((-Complex.I) • x) - Pre M Ω ((-Complex.I) • x)) := by
      rw [smul_sub, smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]
    rw [hw2, e, inner_I_smul_I_smul]
    exact Submodule.starProjection_inner_eq_zero _ _ hw'

theorem Pre_I_smul (x : K) : Pre M Ω (Complex.I • x) = Complex.I • Qre M Ω x := by
  rw [Qre_eq, smul_smul, Complex.I_mul_I, neg_one_smul, neg_smul, map_neg, neg_neg]

theorem Qre_I_smul (x : K) : Qre M Ω (Complex.I • x) = Complex.I • Pre M Ω x := by
  rw [Qre_eq, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]

/-- `P − Q` is conjugate-linear. -/
theorem Pre_sub_Qre_I_smul (x : K) :
    (Pre M Ω - Qre M Ω) (Complex.I • x) = (-Complex.I) • (Pre M Ω - Qre M Ω) x := by
  rw [_root_.sub_apply, _root_.sub_apply, Pre_I_smul, Qre_I_smul, smul_sub, neg_smul, neg_smul]
  abel

/-! ## The operator `R = P + Q` -/

theorem Pre_add_Qre_I_smul (x : K) :
    (Pre M Ω + Qre M Ω) (Complex.I • x) = Complex.I • (Pre M Ω + Qre M Ω) x := by
  rw [_root_.add_apply, _root_.add_apply, Pre_I_smul, Qre_I_smul, smul_add, add_comm]

/-- `R = P + Q`, complex-linear (RvD Prop. 3.1). -/
noncomputable def R : K →L[ℂ] K := complexify (Pre M Ω + Qre M Ω) (Pre_add_Qre_I_smul M Ω)

theorem R_apply (x : K) : R M Ω x = Pre M Ω x + Qre M Ω x := rfl

theorem re_inner_R_left (x y : K) : (⟪R M Ω x, y⟫_ℂ).re = (⟪x, R M Ω y⟫_ℂ).re := by
  rw [← inner_real_eq_re_inner, ← inner_real_eq_re_inner, R_apply, R_apply, inner_add_left,
    inner_add_right, inner_Pre_left, inner_Qre_left]

theorem inner_R_left (x y : K) : ⟪R M Ω x, y⟫_ℂ = ⟪x, R M Ω y⟫_ℂ :=
  inner_eq_of_re_eq (re_inner_R_left M Ω) x y

theorem R_isSelfAdjoint : IsSelfAdjoint (R M Ω) :=
  LinearMap.IsSymmetric.isSelfAdjoint (inner_R_left M Ω)

theorem re_inner_R_self (x : K) : (⟪R M Ω x, x⟫_ℂ).re = ‖Pre M Ω x‖ ^ 2 + ‖Qre M Ω x‖ ^ 2 := by
  rw [← inner_real_eq_re_inner, R_apply, inner_add_left, inner_Pre_self, inner_Qre_self]

theorem im_inner_R_self (x : K) : (⟪R M Ω x, x⟫_ℂ).im = 0 := by
  rw [← BorelCalc.inner_sa (R_isSelfAdjoint M Ω)]
  exact BorelCalc.inner_self_im (R_isSelfAdjoint M Ω) x

theorem inner_R_self (x : K) : ⟪R M Ω x, x⟫_ℂ = ((‖Pre M Ω x‖ ^ 2 + ‖Qre M Ω x‖ ^ 2 : ℝ) : ℂ) := by
  apply Complex.ext
  · rw [re_inner_R_self, Complex.ofReal_re]
  · rw [im_inner_R_self, Complex.ofReal_im]

/-- `0 ≤ R` (RvD Prop. 2.2(1)). -/
theorem R_nonneg : 0 ≤ R M Ω := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff']
  refine ⟨R_isSelfAdjoint M Ω, fun x => ?_⟩
  rw [inner_R_self]
  exact Complex.zero_le_real.mpr (by positivity)

theorem inner_two_sub_R_self (x : K) : ⟪(2 - R M Ω) x, x⟫_ℂ =
    ((2 * ‖x‖ ^ 2 - ‖Pre M Ω x‖ ^ 2 - ‖Qre M Ω x‖ ^ 2 : ℝ) : ℂ) := by
  have h2 : ((2 : K →L[ℂ] K) x) = (2 : ℂ) • x := by
    rw [show (2 : K →L[ℂ] K) = 1 + 1 from one_add_one_eq_two.symm, _root_.add_apply,
      one_apply_eq_self, two_smul]
  have hxx : ⟪x, x⟫_ℂ = ((‖x‖ ^ 2 : ℝ) : ℂ) :=
    Complex.ext (by rw [Complex.ofReal_re]; exact inner_self_eq_norm_sq (𝕜 := ℂ) x)
      (by rw [Complex.ofReal_im]; exact inner_self_im (𝕜 := ℂ) x)
  rw [_root_.sub_apply, inner_sub_left, inner_R_self, h2, inner_smul_left, map_ofNat, hxx]
  push_cast
  ring

/-- `R ≤ 2` (RvD Prop. 2.2(1)). -/
theorem R_le_two : R M Ω ≤ 2 := by
  rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff']
  refine ⟨?_, fun x => ?_⟩
  · have : IsSelfAdjoint (2 : K →L[ℂ] K) := by
      rw [show (2 : K →L[ℂ] K) = 1 + 1 by norm_num]
      exact (IsSelfAdjoint.one _).add (IsSelfAdjoint.one _)
    exact this.sub (R_isSelfAdjoint M Ω)
  · rw [inner_two_sub_R_self]
    refine Complex.zero_le_real.mpr ?_
    have h1 := norm_Pre_le M Ω x
    have h2 := norm_Qre_le M Ω x
    have h1' : ‖Pre M Ω x‖ ^ 2 ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h2' : ‖Qre M Ω x‖ ^ 2 ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    linarith

theorem R_Ω : R M Ω Ω = Ω := by
  rw [R_apply, Pre_Ω, Qre_Ω, add_zero]

/-! ## Injectivity of `R` and `2 − R` (RvD Prop. 2.2(1)) -/

variable (hs : IsSeparating (M : Set (K →L[ℂ] K)) Ω) (hc : IsCyclic (M : Set (K →L[ℂ] K)) Ω)

include hc in
/-- `R` is injective: `R x = 0` forces `x ⊥ 𝒦` and `x ⊥ i𝒦`, and `𝒦 + i𝒦` is dense. -/
theorem R_eq_zero_iff {x : K} : R M Ω x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have h0 : ‖Pre M Ω x‖ ^ 2 + ‖Qre M Ω x‖ ^ 2 = 0 := by
      have := re_inner_R_self M Ω x
      rwa [h, inner_zero_left, Complex.zero_re, eq_comm] at this
    have hP : Pre M Ω x = 0 := by
      rw [← norm_eq_zero, ← pow_eq_zero_iff two_ne_zero]
      nlinarith [sq_nonneg ‖Pre M Ω x‖, sq_nonneg ‖Qre M Ω x‖]
    have hQ : Qre M Ω x = 0 := by
      rw [← norm_eq_zero, ← pow_eq_zero_iff two_ne_zero]
      nlinarith [sq_nonneg ‖Pre M Ω x‖, sq_nonneg ‖Qre M Ω x‖]
    rw [Pre_eq_zero_iff] at hP
    rw [Qre_eq_zero_iff] at hQ
    have hx : x ∈ ((Kre M Ω).toSubmodule ⊔ (Kre M Ω).mulI.toSubmodule)ᗮ := by
      rw [← Submodule.inf_orthogonal]
      exact ⟨hP, hQ⟩
    have htop : ((Kre M Ω).toSubmodule ⊔ (Kre M Ω).mulI.toSubmodule).topologicalClosure = ⊤ := by
      have := congrArg ClosedSubmodule.toSubmodule (Kre_sup_mulI M Ω hc)
      rwa [ClosedSubmodule.toSubmodule_sup, ClosedSubmodule.toSubmodule_top] at this
    rw [← Submodule.orthogonal_closure, htop, Submodule.top_orthogonal_eq_bot] at hx
    exact (Submodule.mem_bot ℝ).mp hx
  · rintro rfl
    exact map_zero _

include hs in
/-- `2 − R` is injective: `(2 − R) x = 0` forces `x ∈ 𝒦 ∩ i𝒦 = 0`. -/
theorem two_sub_R_eq_zero_iff {x : K} : (2 - R M Ω) x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have h0 : 2 * ‖x‖ ^ 2 - ‖Pre M Ω x‖ ^ 2 - ‖Qre M Ω x‖ ^ 2 = 0 := by
      have := inner_two_sub_R_self M Ω x
      rw [h, inner_zero_left] at this
      exact_mod_cast this.symm
    have h1 : ‖Pre M Ω x‖ ^ 2 ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_Pre_le M Ω x) 2
    have h2 : ‖Qre M Ω x‖ ^ 2 ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_Qre_le M Ω x) 2
    have hP : ‖Pre M Ω x‖ ^ 2 = ‖x‖ ^ 2 := by linarith
    have hQ : ‖Qre M Ω x‖ ^ 2 = ‖x‖ ^ 2 := by linarith
    -- `‖x − P x‖² = ‖x‖² − ‖P x‖² = 0`
    have hPx : x = Pre M Ω x := by
      have : ‖x - Pre M Ω x‖ ^ 2 = 0 := by
        rw [norm_sub_sq_real, real_inner_comm, inner_Pre_self, hP]
        ring
      exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this |> norm_eq_zero.mp)
    have hQx : x = Qre M Ω x := by
      have : ‖x - Qre M Ω x‖ ^ 2 = 0 := by
        rw [norm_sub_sq_real, real_inner_comm, inner_Qre_self, hQ]
        ring
      exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this |> norm_eq_zero.mp)
    have hmem : x ∈ Kre M Ω ⊓ (Kre M Ω).mulI := by
      rw [ClosedSubmodule.mem_inf]
      exact ⟨hPx ▸ Pre_apply_mem M Ω x, hQx ▸ Qre_apply_mem M Ω x⟩
    rw [Kre_inf_mulI M Ω hs, ClosedSubmodule.mem_bot] at hmem
    exact hmem
  · rintro rfl
    exact map_zero _

end Modular

end VN

end CommutingRepetition
