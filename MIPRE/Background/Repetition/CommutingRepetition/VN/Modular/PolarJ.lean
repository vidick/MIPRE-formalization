/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/Modular/PolarJ.lean
-/
/-
# The operators `T = |P − Q|` and `J` (stage E4.2c; Rieffel–van Daele Prop. 2.2(2)–(5), 3.1, 3.3)

`T := (R(2−R))^{1/2}`, a function of `R`, and `A := P − Q` (conjugate-linear)
satisfy `A² = T²`, `A R = (2−R) A`, `A T = T A`; the antiunitary `J` is defined
on the dense range of `T` by `J (T x) = A x` and extended.  Then `J² = 1`,
`⟪Jξ, η⟫ = ⟪Jη, ξ⟫`, `JT = TJ = A`, `JR = (2−R)J`, `JΩ = Ω`,
`JΔ^{it} = Δ^{it}J`, `Δ^{it}𝒦 = 𝒦`, and the bounded identities
`TJxΩ = (2−R)x*Ω` (`x ∈ M`), `TJx′Ω = Rx′*Ω` (`x′ ∈ M′`) of RvD p. 203.
The functional-calculus intertwining `A f(S) = f(S′) A` for real-linear `A`
with `A S = S′ A` is proved by Weierstrass approximation.
Source: `PLAN-tomita.md` §0.1.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.Modular.ModularGroup

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace VN

namespace Modular

open scoped InnerProductSpace ComplexConjugate
open Filter Topology BorelCalc ClosedSubmodule Polynomial

set_option linter.unusedSectionVars false

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ## Intertwining the continuous functional calculus -/

section Intertwine

variable {A : K →L[ℝ] K} {S S' : K →L[ℂ] K}

theorem pow_intertwine (h : ∀ x, A (S x) = S' (A x)) (n : ℕ) (x : K) :
    A ((S ^ n) x) = (S' ^ n) (A x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, mul_apply_eq_comp, mul_apply_eq_comp, ih, h]

theorem aeval_intertwine (h : ∀ x, A (S x) = S' (A x)) (p : ℝ[X]) (x : K) :
    A (aeval S p x) = aeval S' p (A x) := by
  induction p using Polynomial.induction_on' generalizing x with
  | add p q hp hq => rw [map_add, map_add, _root_.add_apply, _root_.add_apply, map_add, hp, hq]
  | monomial n c =>
    rw [aeval_monomial, aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
      smul_mul_assoc, one_mul, one_mul, _root_.smul_apply, _root_.smul_apply, map_smul,
      pow_intertwine h]

theorem spectrum_subset_Icc_norm (S : K →L[ℂ] K) :
    spectrum ℝ S ⊆ Set.Icc (-‖S‖) ‖S‖ := by
  intro t ht
  have h1 := spectrum.norm_le_norm_mul_of_mem ht
  have h2 : ‖(1 : K →L[ℂ] K)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have : |t| ≤ ‖S‖ := by
    rw [Real.norm_eq_abs] at h1
    calc |t| ≤ ‖S‖ * ‖(1 : K →L[ℂ] K)‖ := h1
      _ ≤ ‖S‖ * 1 := by gcongr
      _ = ‖S‖ := mul_one _
  exact abs_le.mp this

/-- A real-linear operator intertwining two self-adjoint operators intertwines their continuous
functional calculi (Weierstrass approximation). -/
theorem cfc_intertwine (hS : IsSelfAdjoint S) (hS' : IsSelfAdjoint S')
    (h : ∀ x, A (S x) = S' (A x)) {f : ℝ → ℝ} (hf : Continuous f) (x : K) :
    A (cfc f S x) = cfc f S' (A x) := by
  set M : ℝ := max ‖S‖ ‖S'‖ with hM
  have hM0 : 0 ≤ M := le_max_of_le_left (norm_nonneg _)
  have hspec : spectrum ℝ S ⊆ Set.Icc (-M) M := fun t ht => by
    have := spectrum_subset_Icc_norm S ht
    exact ⟨by linarith [this.1, le_max_left ‖S‖ ‖S'‖], this.2.trans (le_max_left _ _)⟩
  have hspec' : spectrum ℝ S' ⊆ Set.Icc (-M) M := fun t ht => by
    have := spectrum_subset_Icc_norm S' ht
    exact ⟨by linarith [this.1, le_max_right ‖S‖ ‖S'‖], this.2.trans (le_max_right _ _)⟩
  rw [← sub_eq_zero, ← norm_eq_zero]
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) (norm_nonneg _)
  rw [zero_add]
  set C : ℝ := ‖A‖ * ‖x‖ + ‖A x‖ + 1 with hC
  have hC0 : 0 < C := by positivity
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-M) M f hf.continuousOn (ε / C)
    (by positivity)
  -- `‖cfc f S − aeval S p‖ ≤ ε / C` and likewise for `S'`
  have hb : ∀ (U : K →L[ℂ] K), IsSelfAdjoint U → spectrum ℝ U ⊆ Set.Icc (-M) M →
      ‖cfc f U - aeval U p‖ ≤ ε / C := fun U hU hUs => by
    rw [← cfc_polynomial p U, ← cfc_sub f p.eval U]
    refine norm_cfc_le (by positivity) fun t ht => ?_
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact (hp t (hUs ht)).le
  have h1 := hb S hS hspec
  have h2 := hb S' hS' hspec'
  calc ‖A (cfc f S x) - cfc f S' (A x)‖
      = ‖A ((cfc f S - aeval S p) x) + ((aeval S' p - cfc f S') (A x))‖ := by
        congr 1
        rw [_root_.sub_apply, map_sub, _root_.sub_apply, aeval_intertwine h]
        abel
    _ ≤ ‖A ((cfc f S - aeval S p) x)‖ + ‖(aeval S' p - cfc f S') (A x)‖ := norm_add_le _ _
    _ ≤ ‖A‖ * (ε / C * ‖x‖) + ε / C * ‖A x‖ := by
        gcongr
        · exact (A.le_opNorm _).trans (mul_le_mul_of_nonneg_left
            ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right h1
              (norm_nonneg _))) (norm_nonneg _))
        · rw [_root_.sub_apply, norm_sub_rev, ← _root_.sub_apply]
          exact (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
    _ = ε * ((‖A‖ * ‖x‖ + ‖A x‖) / C) := by ring
    _ ≤ ε * 1 := by
        gcongr
        rw [div_le_one hC0, hC]
        linarith
    _ = ε := mul_one _

end Intertwine

/-! ## `T = |P − Q| = (R(2−R))^{1/2}` and `A = P − Q` -/

variable (M : VonNeumannAlgebra K) (Ω : K)

/-- `√(λ(2−λ))`, bounded by `1`. -/
noncomputable def gT (l : ℝ) : ℝ := Real.sqrt (l * (2 - l))

theorem gT_nonneg (l : ℝ) : 0 ≤ gT l := Real.sqrt_nonneg _

theorem gT_le_one (l : ℝ) : gT l ≤ 1 := by
  unfold gT
  rw [← Real.sqrt_one]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (l - 1)])

theorem continuous_gT : Continuous gT := by
  unfold gT
  fun_prop

theorem bdd_gT : Bdd gT :=
  Bdd.of_continuous continuous_gT (C := 1) fun l => by
    rw [abs_of_nonneg (gT_nonneg l)]
    exact gT_le_one l

theorem gT_one : gT 1 = 1 := by norm_num [gT]

theorem gT_two_sub (l : ℝ) : gT (2 - l) = gT l := by
  unfold gT
  congr 1
  ring

theorem norm_R_le_two : ‖R M Ω‖ ≤ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun x => ?_
  rw [R_apply]
  calc ‖Pre M Ω x + Qre M Ω x‖ ≤ ‖Pre M Ω x‖ + ‖Qre M Ω x‖ := norm_add_le _ _
    _ ≤ ‖x‖ + ‖x‖ := add_le_add (norm_Pre_le M Ω x) (norm_Qre_le M Ω x)
    _ = 2 * ‖x‖ := by ring

theorem spectrum_R_subset : spectrum ℝ (R M Ω) ⊆ Set.Icc 0 2 := fun _ ht =>
  ⟨spectrum_nonneg_of_nonneg (R_nonneg M Ω) ht,
    (spectrum_subset_Icc_norm _ ht).2.trans (norm_R_le_two M Ω)⟩

/-- `T := (R(2−R))^{1/2}` (RvD's `T`, the modulus of `P − Q`). -/
noncomputable def Tm : K →L[ℂ] K := cfc gT (R M Ω)

theorem Tm_isSelfAdjoint : IsSelfAdjoint (Tm M Ω) := cfc_predicate _ _

theorem Tm_eq_bfc : Tm M Ω = bfc (R M Ω) (R_isSelfAdjoint M Ω) gT :=
  (bfc_cfc _ _ bdd_gT continuous_gT).symm

theorem cfc_two_sub : cfc (fun l : ℝ => 2 - l) (R M Ω) = 2 - R M Ω := by
  have hR := R_isSelfAdjoint M Ω
  rw [cfc_sub (fun _ : ℝ => (2 : ℝ)) (fun l : ℝ => l) (R M Ω), cfc_const (2 : ℝ) (R M Ω) hR,
    cfc_id' ℝ (R M Ω) hR, map_ofNat]

/-- `T² = R(2−R)` (RvD Prop. 2.2(2)). -/
theorem Tm_mul_Tm : Tm M Ω * Tm M Ω = R M Ω * (2 - R M Ω) := by
  have hR := R_isSelfAdjoint M Ω
  have hgc : ContinuousOn gT (spectrum ℝ (R M Ω)) := continuous_gT.continuousOn
  unfold Tm
  rw [← cfc_mul gT gT (R M Ω) hgc hgc]
  have h1 : cfc (fun l => gT l * gT l) (R M Ω) = cfc (fun l : ℝ => l * (2 - l)) (R M Ω) := by
    refine cfc_congr fun l hl => ?_
    have := spectrum_R_subset M Ω hl
    exact Real.mul_self_sqrt (by nlinarith [this.1, this.2])
  rw [h1, cfc_mul (fun l : ℝ => l) (fun l : ℝ => 2 - l) (R M Ω), cfc_id' ℝ (R M Ω) hR,
    cfc_two_sub]

theorem Tm_Ω : Tm M Ω Ω = Ω := by
  have hΩ : R M Ω Ω = ((1 : ℝ) : ℂ) • Ω := by rw [R_Ω]; simp
  rw [Tm_eq_bfc, bfc_eigen _ _ bdd_gT hΩ, gT_one]
  simp

theorem norm_Tm_le : ‖Tm M Ω‖ ≤ 1 :=
  norm_cfc_le zero_le_one fun l _ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (gT_nonneg l)]
    exact gT_le_one l

theorem R_commute_Tm : Commute (R M Ω) (Tm M Ω) := (Commute.cfc_real (Commute.refl _) gT).symm

theorem Δit_commute_Tm (t : ℝ) : Commute (Δit M Ω t) (Tm M Ω) :=
  commute_cbfc _ _ (R_commute_Tm M Ω) (cbdd_gDel t)

variable (hs : IsSeparating (M : Set (K →L[ℂ] K)) Ω) (hc : IsCyclic (M : Set (K →L[ℂ] K)) Ω)

include hs hc in
theorem Tm_eq_zero_iff {x : K} : Tm M Ω x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have h2 : (R M Ω * (2 - R M Ω)) x = 0 := by
      rw [← Tm_mul_Tm, mul_apply_eq_comp, h, map_zero]
    rw [mul_apply_eq_comp, R_eq_zero_iff M Ω hc, two_sub_R_eq_zero_iff M Ω hs] at h2
    exact h2
  · rintro rfl
    exact map_zero _

include hs hc in
theorem denseRange_Tm : DenseRange (Tm M Ω) := by
  have : (LinearMap.range (Tm M Ω : K →ₗ[ℂ] K)).topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro v hv
    rw [Submodule.mem_orthogonal] at hv
    have : Tm M Ω v = 0 := by
      have h := hv (Tm M Ω (Tm M Ω v)) (LinearMap.mem_range_self _ _)
      rw [← BorelCalc.inner_sa (Tm_isSelfAdjoint M Ω), inner_self_eq_zero] at h
      exact h
    exact (Tm_eq_zero_iff M Ω hs hc).mp this
  rw [DenseRange]
  have hr : Set.range (Tm M Ω) = (LinearMap.range (Tm M Ω : K →ₗ[ℂ] K) : Set K) := by
    ext v
    simp [LinearMap.mem_range]
  rw [hr, ← Submodule.dense_iff_topologicalClosure_eq_top] at *
  exact this

/-- `A := P − Q` (conjugate-linear). -/
noncomputable def Am : K →L[ℝ] K := Pre M Ω - Qre M Ω

theorem Am_apply (x : K) : Am M Ω x = Pre M Ω x - Qre M Ω x := rfl

theorem Am_I_smul (x : K) : Am M Ω (Complex.I • x) = (-Complex.I) • Am M Ω x :=
  Pre_sub_Qre_I_smul M Ω x

theorem inner_Am_left (x y : K) : inner ℝ (Am M Ω x) y = inner ℝ x (Am M Ω y) := by
  rw [Am_apply, Am_apply, inner_sub_left, inner_sub_right, inner_Pre_left, inner_Qre_left]

/-- `A² = R(2−R)` (RvD Prop. 2.2(2)). -/
theorem Am_Am (x : K) : Am M Ω (Am M Ω x) = (R M Ω * (2 - R M Ω)) x := by
  have h2 : ((2 : K →L[ℂ] K) x) = x + x := by
    rw [show (2 : K →L[ℂ] K) = 1 + 1 from one_add_one_eq_two.symm, _root_.add_apply,
      one_apply_eq_self]
  simp only [Am_apply, mul_apply_eq_comp, _root_.sub_apply, R_apply, map_add, map_sub, h2,
    Pre_Pre, Qre_Qre]
  abel

/-- `A R = (2 − R) A` (RvD Prop. 2.2(5) via the polar decomposition). -/
theorem Am_R (x : K) : Am M Ω (R M Ω x) = (2 - R M Ω) (Am M Ω x) := by
  have h2 : ∀ y : K, ((2 : K →L[ℂ] K) y) = y + y := fun y => by
    rw [show (2 : K →L[ℂ] K) = 1 + 1 from one_add_one_eq_two.symm, _root_.add_apply,
      one_apply_eq_self]
  simp only [Am_apply, _root_.sub_apply, R_apply, map_add, map_sub, h2, Pre_Pre, Qre_Qre]
  abel

theorem inner_sa_real {S : K →L[ℂ] K} (hS : IsSelfAdjoint S) (x y : K) :
    inner ℝ (S x) y = inner ℝ x (S y) := by
  rw [inner_real_eq_re_inner, inner_real_eq_re_inner, BorelCalc.inner_sa hS]

/-- `A T = T A` (RvD Prop. 2.2(4)). -/
theorem Am_Tm (x : K) : Am M Ω (Tm M Ω x) = Tm M Ω (Am M Ω x) := by
  have hR := R_isSelfAdjoint M Ω
  have h2sa : IsSelfAdjoint (2 - R M Ω) := by
    have : IsSelfAdjoint (2 : K →L[ℂ] K) := by
      rw [show (2 : K →L[ℂ] K) = 1 + 1 from one_add_one_eq_two.symm]
      exact (IsSelfAdjoint.one _).add (IsSelfAdjoint.one _)
    exact this.sub hR
  have h := cfc_intertwine (A := Am M Ω) hR h2sa (Am_R M Ω) continuous_gT x
  rw [Tm, h, ← cfc_two_sub, ← cfc_comp gT (fun l : ℝ => 2 - l) (R M Ω) hR
    continuous_gT.continuousOn (by fun_prop)]
  congr 2
  funext l
  exact gT_two_sub l

theorem norm_Am_apply (x : K) : ‖Am M Ω x‖ = ‖Tm M Ω x‖ := by
  refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_Am_left, Am_Am,
    ← Tm_mul_Tm, mul_apply_eq_comp, ← inner_sa_real (Tm_isSelfAdjoint M Ω)]

theorem Am_Ω : Am M Ω Ω = Ω := by
  rw [Am_apply, Pre_Ω, Qre_Ω, sub_zero]

/-! ## The antiunitary `J`: `J (T x) = A x` -/

section J

/-- The range of `T` as a (dense) subspace. -/
noncomputable abbrev TmRange : Submodule ℂ K := LinearMap.range (Tm M Ω : K →ₗ[ℂ] K)

theorem exists_rep_Tm (v : TmRange M Ω) : ∃ x, Tm M Ω x = v := LinearMap.mem_range.mp v.2

/-- A preimage under `T`. -/
noncomputable def repT (v : TmRange M Ω) : K := (exists_rep_Tm M Ω v).choose

theorem Tm_repT (v : TmRange M Ω) : Tm M Ω (repT M Ω v) = v := (exists_rep_Tm M Ω v).choose_spec

include hs hc in
theorem repT_Tm (x : K) : repT M Ω ⟨Tm M Ω x, LinearMap.mem_range_self _ x⟩ = x := by
  have h := Tm_repT M Ω ⟨Tm M Ω x, LinearMap.mem_range_self _ x⟩
  have h2 : Tm M Ω (repT M Ω ⟨Tm M Ω x, LinearMap.mem_range_self _ x⟩ - x) = 0 := by
    rw [map_sub, h, sub_self]
  exact sub_eq_zero.mp ((Tm_eq_zero_iff M Ω hs hc).mp h2)

theorem Am_eq_of_Tm_eq {x y : K} (h : Tm M Ω x = Tm M Ω y) : Am M Ω x = Am M Ω y := by
  have : ‖Am M Ω (x - y)‖ = 0 := by
    rw [norm_Am_apply, map_sub, h, sub_self, norm_zero]
  rw [map_sub] at this
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

/-- `J₀ : T x ↦ A x` on the range of `T`, conjugate-linear and isometric. -/
noncomputable def J₀ : TmRange M Ω →SL[starRingEnd ℂ] K :=
  LinearMap.mkContinuous
    { toFun := fun v => Am M Ω (repT M Ω v)
      map_add' := fun v w => by
        refine (Am_eq_of_Tm_eq M Ω ?_).trans (map_add _ _ _)
        rw [Tm_repT, map_add, Tm_repT, Tm_repT]
        rfl
      map_smul' := fun c v => by
        show Am M Ω (repT M Ω (c • v)) = (starRingEnd ℂ) c • Am M Ω (repT M Ω v)
        have h1 : Tm M Ω (repT M Ω (c • v)) = Tm M Ω (c • repT M Ω v) := by
          rw [Tm_repT, map_smul, Tm_repT]
          rfl
        rw [Am_eq_of_Tm_eq M Ω h1]
        -- `A (c • x) = conj c • A x` from real-linearity and `A (i x) = -i A x`
        have hre : ∀ (r : ℝ) (y : K), Am M Ω ((r : ℂ) • y) = (r : ℂ) • Am M Ω y := fun r y => by
          have e1 : ((r : ℂ) • y) = r • y := (RCLike.real_smul_eq_coe_smul (K := ℂ) r y).symm
          have e2 : ((r : ℂ) • Am M Ω y) = r • Am M Ω y :=
            (RCLike.real_smul_eq_coe_smul (K := ℂ) r (Am M Ω y)).symm
          rw [e1, e2, map_smul]
        set y := repT M Ω v
        have hc' : c • y = (c.re : ℂ) • y + (c.im : ℂ) • (Complex.I • y) := by
          rw [smul_smul, ← add_smul, Complex.re_add_im]
        rw [hc', map_add, hre, hre, Am_I_smul, smul_smul, ← add_smul]
        congr 1
        apply Complex.ext <;> simp } 1 fun v => by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
    rw [norm_Am_apply, Tm_repT]
    exact le_rfl

theorem J₀_apply (v : TmRange M Ω) : J₀ M Ω v = Am M Ω (repT M Ω v) := rfl

include hs hc in
theorem denseRange_subtypeL_TmRange : DenseRange (TmRange M Ω).subtypeL := by
  have h : Set.range (TmRange M Ω).subtypeL = Set.range (Tm M Ω) := by
    ext v
    constructor
    · rintro ⟨w, rfl⟩
      exact LinearMap.mem_range.mp w.2
    · rintro ⟨x, rfl⟩
      exact ⟨⟨Tm M Ω x, LinearMap.mem_range_self _ x⟩, rfl⟩
  rw [DenseRange, h]
  exact denseRange_Tm M Ω hs hc

theorem isUniformInducing_subtypeL_TmRange : IsUniformInducing (TmRange M Ω).subtypeL :=
  ((AddMonoidHomClass.isometry_iff_norm _).mpr fun _ => rfl).isUniformInducing

/-- The antiunitary `J`, the continuous extension of `T x ↦ A x` (RvD §2, the partial isometry of
the polar decomposition `P − Q = JT`). -/
noncomputable def Jm : K →SL[starRingEnd ℂ] K :=
  (J₀ M Ω).extend (TmRange M Ω).subtypeL

include hs hc in
theorem Jm_Tm (x : K) : Jm M Ω (Tm M Ω x) = Am M Ω x := by
  have hv : Tm M Ω x ∈ TmRange M Ω := LinearMap.mem_range_self _ x
  have h := ContinuousLinearMap.extend_eq (J₀ M Ω) (denseRange_subtypeL_TmRange M Ω hs hc)
    (isUniformInducing_subtypeL_TmRange M Ω) ⟨Tm M Ω x, hv⟩
  rw [show (TmRange M Ω).subtypeL ⟨Tm M Ω x, hv⟩ = Tm M Ω x from rfl] at h
  rw [Jm, h, J₀_apply, repT_Tm M Ω hs hc]

theorem Jm_smul (c : ℂ) (ξ : K) : Jm M Ω (c • ξ) = conj c • Jm M Ω ξ :=
  map_smulₛₗ _ c ξ

include hs hc in
/-- Two continuous maps agreeing on the range of `T` agree everywhere. -/
theorem ext_of_Tm {Y : Type*} [TopologicalSpace Y] [T2Space Y] {f g : K → Y} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x, f (Tm M Ω x) = g (Tm M Ω x)) : f = g :=
  Continuous.ext_on (denseRange_Tm M Ω hs hc) hf hg (by rintro _ ⟨x, rfl⟩; exact h x)

include hs hc in
theorem norm_Jm_apply (ξ : K) : ‖Jm M Ω ξ‖ = ‖ξ‖ := by
  have := congrFun (ext_of_Tm M Ω hs hc (f := fun ξ => ‖Jm M Ω ξ‖) (g := fun ξ => ‖ξ‖)
    (by fun_prop) (by fun_prop) fun x => by
      simp only [Jm_Tm M Ω hs hc, norm_Am_apply]) ξ
  exact this

include hs hc in
/-- `T J = A` (`J` commutes with `T`, RvD Prop. 2.2(4)). -/
theorem Tm_Jm (ξ : K) : Tm M Ω (Jm M Ω ξ) = Am M Ω ξ := by
  have := congrFun (ext_of_Tm M Ω hs hc (f := fun ξ => Tm M Ω (Jm M Ω ξ))
    (g := fun ξ => Am M Ω ξ) (by fun_prop) (by fun_prop) fun x => by
      simp only [Jm_Tm M Ω hs hc, Am_Tm]) ξ
  exact this

include hs hc in
theorem Jm_Tm_comm (ξ : K) : Jm M Ω (Tm M Ω ξ) = Tm M Ω (Jm M Ω ξ) := by
  rw [Jm_Tm M Ω hs hc, Tm_Jm M Ω hs hc]

include hs hc in
/-- Real symmetry `Re⟪Jξ, η⟫ = Re⟪ξ, Jη⟫`. -/
theorem inner_Jm_left_real (ξ η : K) :
    inner ℝ (Jm M Ω ξ) η = inner ℝ ξ (Jm M Ω η) := by
  -- both sides are continuous in `(ξ, η)` and agree on `range T × range T`
  have h1 : ∀ x y, inner ℝ (Jm M Ω (Tm M Ω x)) (Tm M Ω y) =
      inner ℝ (Tm M Ω x) (Jm M Ω (Tm M Ω y)) := fun x y => by
    rw [Jm_Tm M Ω hs hc, Jm_Tm M Ω hs hc, inner_Am_left, Am_Tm, ← inner_sa_real (Tm_isSelfAdjoint M Ω)]
  have h2 : ∀ x (η : K), inner ℝ (Jm M Ω (Tm M Ω x)) η =
      inner ℝ (Tm M Ω x) (Jm M Ω η) := fun x => by
    have := ext_of_Tm M Ω hs hc (f := fun η => inner ℝ (Jm M Ω (Tm M Ω x)) η)
      (g := fun η => inner ℝ (Tm M Ω x) (Jm M Ω η)) (by fun_prop) (by fun_prop) (h1 x)
    exact fun η => congrFun this η
  have := ext_of_Tm M Ω hs hc (f := fun ξ => inner ℝ (Jm M Ω ξ) η)
    (g := fun ξ => inner ℝ ξ (Jm M Ω η)) (by fun_prop) (by fun_prop) fun x => h2 x η
  exact congrFun this ξ

include hs hc in
/-- `⟪Jξ, η⟫ = ⟪Jη, ξ⟫` (RvD Prop. 3.1). -/
theorem inner_Jm_left (ξ η : K) : ⟪Jm M Ω ξ, η⟫_ℂ = ⟪Jm M Ω η, ξ⟫_ℂ := by
  apply Complex.ext
  · have h := inner_Jm_left_real M Ω hs hc ξ η
    rw [inner_real_eq_re_inner, inner_real_eq_re_inner, ← inner_conj_symm ξ (Jm M Ω η),
      Complex.conj_re] at h
    exact h
  · -- apply the real identity to `I • η`
    have h := inner_Jm_left_real M Ω hs hc ξ (Complex.I • η)
    rw [inner_real_eq_re_inner, inner_real_eq_re_inner, inner_smul_right, Jm_smul,
      inner_smul_right, Complex.conj_I, neg_mul, Complex.neg_re, Complex.I_mul_re,
      Complex.I_mul_re, neg_neg, ← inner_conj_symm ξ (Jm M Ω η), Complex.conj_im] at h
    exact neg_inj.mp h

include hs hc in
theorem inner_Jm_Jm (ξ η : K) : inner ℝ (Jm M Ω ξ) (Jm M Ω η) = inner ℝ ξ η := by
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two, ← map_add,
    norm_Jm_apply M Ω hs hc, norm_Jm_apply M Ω hs hc, norm_Jm_apply M Ω hs hc]

include hs hc in
/-- `J² = 1` (RvD Prop. 2.2(3)). -/
theorem Jm_Jm (ξ : K) : Jm M Ω (Jm M Ω ξ) = ξ := by
  have : ∀ ζ, inner ℝ (Jm M Ω (Jm M Ω ξ) - ξ) ζ = 0 := fun ζ => by
    rw [inner_sub_left, inner_Jm_left_real M Ω hs hc, inner_Jm_Jm M Ω hs hc, sub_self]
  have h := this (Jm M Ω (Jm M Ω ξ) - ξ)
  rw [real_inner_self_eq_norm_sq, pow_eq_zero_iff two_ne_zero, norm_eq_zero, sub_eq_zero] at h
  exact h

include hs hc in
theorem Jm_Ω : Jm M Ω Ω = Ω := by
  have := Jm_Tm M Ω hs hc Ω
  rwa [Tm_Ω, Am_Ω] at this

include hs hc in
/-- `J R = (2 − R) J` (RvD Prop. 2.2(5)). -/
theorem Jm_R (ξ : K) : Jm M Ω (R M Ω ξ) = (2 - R M Ω) (Jm M Ω ξ) := by
  have := congrFun (ext_of_Tm M Ω hs hc (f := fun ξ => Jm M Ω (R M Ω ξ))
    (g := fun ξ => (2 - R M Ω) (Jm M Ω ξ)) (by fun_prop) (by fun_prop) fun x => by
      show Jm M Ω (R M Ω (Tm M Ω x)) = (2 - R M Ω) (Jm M Ω (Tm M Ω x))
      rw [← mul_apply_eq_comp, (R_commute_Tm M Ω).eq, mul_apply_eq_comp, Jm_Tm M Ω hs hc, Am_R,
        Jm_Tm M Ω hs hc]) ξ
  exact this

end J

/-! ## `J` and the functional calculus of `R`

`J R = (2 − R) J` transports the spectral data of `R` under `λ ↦ 2 − λ`: `J g(R) = g(2 − R) J`
for every bounded Borel `g`. -/

section JCalc

theorem two_sub_R_isSelfAdjoint : IsSelfAdjoint (2 - R M Ω) :=
  cfc_two_sub M Ω ▸ cfc_predicate _ _

/-- `J` as a real-linear operator. -/
noncomputable def JmR : K →L[ℝ] K :=
  LinearMap.mkContinuous
    { toFun := Jm M Ω
      map_add' := map_add _
      map_smul' := fun r x => by
        simp only [RingHom.id_apply]
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ), Jm_smul,
          RCLike.conj_ofReal] }
    ‖Jm M Ω‖ fun x => (Jm M Ω).le_opNorm x

theorem JmR_apply (x : K) : JmR M Ω x = Jm M Ω x := rfl

include hs hc in
/-- `J f(R) = f(2 − R) J = (f ∘ (2 − ·))(R) J` for continuous `f`. -/
theorem Jm_cfc {f : ℝ → ℝ} (hf : Continuous f) (x : K) :
    Jm M Ω (cfc f (R M Ω) x) = cfc (fun l => f (2 - l)) (R M Ω) (Jm M Ω x) := by
  have h1 : JmR M Ω (cfc f (R M Ω) x) = cfc f (2 - R M Ω) (JmR M Ω x) :=
    cfc_intertwine (R_isSelfAdjoint M Ω) (two_sub_R_isSelfAdjoint M Ω) (Jm_R M Ω hs hc) hf x
  have h2 : cfc f (2 - R M Ω) = cfc (fun l => f (2 - l)) (R M Ω) := by
    rw [← cfc_two_sub M Ω]
    exact (cfc_comp f (fun l : ℝ => 2 - l) (R M Ω) (R_isSelfAdjoint M Ω) hf.continuousOn
      (by fun_prop)).symm
  rw [JmR_apply, JmR_apply] at h1
  rw [h1, h2]

include hs hc in
/-- The spectral measure of `R` at `J ξ` is the push-forward of the one at `ξ` under `λ ↦ 2 − λ`. -/
theorem ν_Jm (ξ : K) :
    ν (R M Ω) (R_isSelfAdjoint M Ω) (Jm M Ω ξ) =
      MeasureTheory.Measure.map (fun l : ℝ => 2 - l) (ν (R M Ω) (R_isSelfAdjoint M Ω) ξ) := by
  refine MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  have hφ : Measurable fun l : ℝ => 2 - l := by fun_prop
  have hf' : Continuous fun l : ℝ => f (2 - l) := f.continuous.comp (by fun_prop)
  rw [MeasureTheory.integral_map hφ.aemeasurable f.continuous.aestronglyMeasurable,
    integral_ν _ _ _ f.continuous,
    integral_ν _ _ _ hf', ← inner_real_eq_re_inner, ← inner_real_eq_re_inner,
    ← inner_Jm_Jm M Ω hs hc (Jm M Ω ξ), Jm_Jm M Ω hs hc, Jm_cfc M Ω hs hc f.continuous, Jm_Jm M Ω hs hc]

theorem _root_.CommutingRepetition.BorelCalc.Bdd.comp_two_sub {g : ℝ → ℝ} (hg : Bdd g) :
    Bdd fun l => g (2 - l) := by
  obtain ⟨hm, C, hC⟩ := hg
  exact ⟨hm.comp (by fun_prop), C, fun t => hC _⟩

/-- Conjugation `G ↦ J G J` by the antiunitary `J`, a (complex-linear) operator. -/
noncomputable def conjJm (G : K →L[ℂ] K) : K →L[ℂ] K := (Jm M Ω).comp (G.comp (Jm M Ω))

theorem conjJm_apply (G : K →L[ℂ] K) (ξ : K) : conjJm M Ω G ξ = Jm M Ω (G (Jm M Ω ξ)) := rfl

include hs hc in
/-- `J g(R) = (g ∘ (2 − ·))(R) J` for bounded Borel `g`. -/
theorem Jm_bfc (g : ℝ → ℝ) (ξ : K) :
    Jm M Ω (bfc (R M Ω) (R_isSelfAdjoint M Ω) g ξ) =
      bfc (R M Ω) (R_isSelfAdjoint M Ω) (fun l => g (2 - l)) (Jm M Ω ξ) := by
  by_cases hg : Bdd g
  · have hop : conjJm M Ω (bfc (R M Ω) (R_isSelfAdjoint M Ω) g) =
        bfc (R M Ω) (R_isSelfAdjoint M Ω) (fun l => g (2 - l)) := by
      refine ext_of_inner_self fun η => ?_
      have hφ : Measurable fun l : ℝ => 2 - l := by fun_prop
      rw [conjJm_apply, ← inner_conj_symm, ← inner_Jm_left M Ω hs hc, inner_bfc_self _ _ hg,
        inner_bfc_self _ _ hg.comp_two_sub, Q, Q, ν_Jm M Ω hs hc,
        MeasureTheory.integral_map hφ.aemeasurable (hg.1.aestronglyMeasurable),
        Complex.conj_ofReal]
    have := congrArg (fun S => S (Jm M Ω ξ)) hop
    simp only [conjJm_apply, Jm_Jm M Ω hs hc] at this
    exact this
  · have hg' : ¬ Bdd fun l => g (2 - l) := fun h => hg (by
      have := h.comp_two_sub
      simpa using this)
    rw [bfc_of_not _ _ hg, bfc_of_not _ _ hg', _root_.zero_apply, _root_.zero_apply,
      map_zero]

include hs hc in
theorem Jm_cbfc {G : ℝ → ℂ} (hG : CBdd G) (ξ : K) :
    Jm M Ω (cbfc (R M Ω) (R_isSelfAdjoint M Ω) G ξ) =
      cbfc (R M Ω) (R_isSelfAdjoint M Ω) (fun l => conj (G (2 - l))) (Jm M Ω ξ) := by
  unfold cbfc
  rw [_root_.add_apply, _root_.add_apply, map_add, _root_.smul_apply, _root_.smul_apply, Jm_smul,
    Complex.conj_I, Jm_bfc M Ω hs hc, Jm_bfc M Ω hs hc]
  simp only [Complex.conj_re, Complex.conj_im, neg_smul]
  have : (fun l : ℝ => -(G (2 - l)).im) = fun l => (-1 : ℝ) * (G (2 - l)).im := by
    funext l; ring
  rw [this, bfc_const_mul _ _ (-1) hG.im.comp_two_sub, _root_.smul_apply, smul_smul]
  congr 1
  simp

/-- `θ(2 − l) = −θ l`. -/
theorem θ_two_sub (l : ℝ) : θ (2 - l) = -θ l := by
  unfold θ
  have hmem : (2 - l) ∈ Set.Ioo (0 : ℝ) 2 ↔ l ∈ Set.Ioo (0 : ℝ) 2 := by
    simp only [Set.mem_Ioo]; constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  by_cases h : l ∈ Set.Ioo (0 : ℝ) 2
  · rw [if_pos (hmem.mpr h), if_pos h, sub_sub_cancel, ← Real.log_inv, inv_div]
  · rw [if_neg (mt hmem.mp h), if_neg h, neg_zero]

theorem gDel_two_sub (t l : ℝ) : gDel t (2 - l) = conj (gDel t l) := by
  unfold gDel
  rw [θ_two_sub, ← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal, mul_neg]

include hs hc in
/-- `J Δ^{it} = Δ^{it} J` (RvD Prop. 3.3). -/
theorem Jm_Δit (t : ℝ) (ξ : K) : Jm M Ω (Δit M Ω t ξ) = Δit M Ω t (Jm M Ω ξ) := by
  unfold Δit
  rw [Jm_cbfc M Ω hs hc (cbdd_gDel t)]
  have : (fun l => conj (gDel t (2 - l))) = gDel t := by
    funext l; rw [gDel_two_sub, Complex.conj_conj]
  rw [this]

include hs hc in
/-- `Δ^{it}` preserves `𝒦` (RvD Prop. 3.3): `P = (R + A)/2` commutes with `Δ^{it}`. -/
theorem Δit_Kre (t : ℝ) {x : K} (hx : x ∈ Kre M Ω) : Δit M Ω t x ∈ Kre M Ω := by
  -- `Pre y = (R y + Am y)/2` and both `R` and `Am = Tm ∘ Jm` commute with `Δ^{it}`
  have hP : ∀ y, Pre M Ω y = (1 / 2 : ℝ) • (R M Ω y + Am M Ω y) := fun y => by
    rw [R_apply, Am_apply, add_add_sub_cancel, ← two_smul ℝ, smul_smul]; norm_num
  have hcomm : Pre M Ω (Δit M Ω t x) = Δit M Ω t (Pre M Ω x) := by
    have h1 : R M Ω (Δit M Ω t x) = Δit M Ω t (R M Ω x) :=
      congrArg (fun S => S x) (Δit_commute_R M Ω t).symm.eq
    have h2 : Am M Ω (Δit M Ω t x) = Δit M Ω t (Am M Ω x) := by
      rw [← Tm_Jm M Ω hs hc, ← Tm_Jm M Ω hs hc, Jm_Δit M Ω hs hc]
      exact congrArg (fun S => S (Jm M Ω x)) (Δit_commute_Tm M Ω t).symm.eq
    rw [hP, hP, h1, h2, ContinuousLinearMap.map_smul_of_tower, map_add]
  have h : Pre M Ω (Δit M Ω t x) = Δit M Ω t x := by rw [hcomm, Pre_eq_self M Ω hx]
  rw [← h]
  exact Pre_apply_mem M Ω _

end JCalc

/-! ## The bounded identities `T J (x Ω) = (2 − R)(x* Ω)`, `T J (x' Ω) = R (x'* Ω)` (RvD Lemma 4.5) -/

section Bounded

/-- For self-adjoint `a' ∈ M'`, `Q (a' Ω) = 0`: `a' Ω ⊥ i𝒦`. -/
theorem Qre_commutant_sa {a' : K →L[ℂ] K} (ha' : a' ∈ M.commutant) (hsa' : IsSelfAdjoint a') :
    Qre M Ω (a' Ω) = 0 := by
  rw [Qre_eq_zero_iff, Submodule.mem_orthogonal]
  intro u hu
  have hu : u ∈ (Kre M Ω).mulI := hu
  rw [mem_mulI_Kre_iff] at hu
  have h := im_inner_commutant_sa M Ω hu ha' hsa'
  have hu' : u = Complex.I • ((-Complex.I) • u) := by
    rw [smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]
  rw [hu', inner_real_eq_re_inner, inner_smul_left, Complex.conj_I, neg_mul, Complex.neg_re,
    Complex.I_mul_re, neg_neg, h]

/-- For self-adjoint `a ∈ M`, `T J (a Ω) = (2 − R)(a Ω)`. -/
theorem Am_sa_mem {a : K →L[ℂ] K} (ha : a ∈ M) (hsa : IsSelfAdjoint a) :
    Am M Ω (a Ω) = (2 - R M Ω) (a Ω) := by
  have hP := Pre_eq_self M Ω (mem_Kre_of_sa M Ω ha hsa)
  have h2 : ((2 : K →L[ℂ] K) (a Ω)) = a Ω + a Ω := by
    rw [show (2 : K →L[ℂ] K) = 1 + 1 from one_add_one_eq_two.symm, _root_.add_apply,
      one_apply_eq_self]
  rw [Am_apply, _root_.sub_apply, R_apply, hP, h2]
  abel

/-- For self-adjoint `a' ∈ M'`, `A (a' Ω) = R (a' Ω)`. -/
theorem Am_commutant_sa {a' : K →L[ℂ] K} (ha' : a' ∈ M.commutant) (hsa' : IsSelfAdjoint a') :
    Am M Ω (a' Ω) = R M Ω (a' Ω) := by
  rw [Am_apply, R_apply, Qre_commutant_sa M Ω ha' hsa', sub_zero, add_zero]

/-- Conjugate-linearity of `A` in the form used for the decomposition `x = a + i b`. -/
theorem Am_add_I_smul (u v : K) :
    Am M Ω (u + Complex.I • v) = Am M Ω u - Complex.I • Am M Ω v := by
  rw [map_add, Am_I_smul, neg_smul, sub_eq_add_neg]

include hs hc in
/-- RvD Lemma 4.5 (first identity): `T J (x Ω) = (2 − R)(x* Ω)` for `x ∈ M`. -/
theorem Tm_Jm_apply_mem {x : K →L[ℂ] K} (hx : x ∈ M) :
    Tm M Ω (Jm M Ω (x Ω)) = (2 - R M Ω) (star x Ω) := by
  rw [Tm_Jm M Ω hs hc]
  obtain ⟨a, b, ha, hb, hsa, hsb, hab⟩ : ∃ a b : K →L[ℂ] K, a ∈ M ∧ b ∈ M ∧ IsSelfAdjoint a ∧
      IsSelfAdjoint b ∧ x = a + Complex.I • b :=
    ⟨(1 / 2 : ℂ) • (x + star x), (-(1 / 2 : ℂ) * Complex.I) • (x - star x),
      VN.smul_mem_vn M _ (add_mem hx (star_mem hx)), VN.smul_mem_vn M _ (sub_mem hx (star_mem hx)),
      isSelfAdjoint_half_add_star x, isSelfAdjoint_half_I_sub_star x, eq_sa_add_I_smul_sa x⟩
  have hstar : star x = a - Complex.I • b := by
    rw [hab, star_add, star_smul, Complex.star_def, Complex.conj_I, hsa.star_eq, hsb.star_eq,
      neg_smul, sub_eq_add_neg]
  rw [hstar, hab, _root_.add_apply, _root_.smul_apply, Am_add_I_smul, Am_sa_mem M Ω ha hsa,
    Am_sa_mem M Ω hb hsb]
  simp only [_root_.sub_apply, _root_.smul_apply, map_sub, map_smul, smul_sub]

include hs hc in
/-- RvD Lemma 4.5 (second identity): `T J (x' Ω) = R (x'* Ω)` for `x' ∈ M'`. -/
theorem Tm_Jm_apply_mem_commutant {x' : K →L[ℂ] K} (hx' : x' ∈ M.commutant) :
    Tm M Ω (Jm M Ω (x' Ω)) = R M Ω (star x' Ω) := by
  rw [Tm_Jm M Ω hs hc]
  obtain ⟨a, b, ha, hb, hsa, hsb, hab⟩ : ∃ a b : K →L[ℂ] K, a ∈ M.commutant ∧ b ∈ M.commutant ∧
      IsSelfAdjoint a ∧ IsSelfAdjoint b ∧ x' = a + Complex.I • b :=
    ⟨(1 / 2 : ℂ) • (x' + star x'), (-(1 / 2 : ℂ) * Complex.I) • (x' - star x'),
      VN.smul_mem_vn M.commutant _ (add_mem hx' (star_mem hx')),
      VN.smul_mem_vn M.commutant _ (sub_mem hx' (star_mem hx')),
      isSelfAdjoint_half_add_star x', isSelfAdjoint_half_I_sub_star x', eq_sa_add_I_smul_sa x'⟩
  have hstar : star x' = a - Complex.I • b := by
    rw [hab, star_add, star_smul, Complex.star_def, Complex.conj_I, hsa.star_eq, hsb.star_eq,
      neg_smul, sub_eq_add_neg]
  rw [hstar, hab, _root_.add_apply, _root_.smul_apply, Am_add_I_smul, Am_commutant_sa M Ω ha hsa,
    Am_commutant_sa M Ω hb hsb, _root_.sub_apply, _root_.smul_apply, map_sub, map_smul]


end Bounded

end Modular

end VN

end CommutingRepetition
