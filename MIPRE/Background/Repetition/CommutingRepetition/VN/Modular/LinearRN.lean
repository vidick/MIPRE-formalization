/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/Modular/LinearRN.lean
-/
/-
# The linear Radon–Nikodym lemma and the operator equation (density stage E4.3a)

Rieffel–van Daele §4, Lemma 4.3, Corollary 4.4 and Lemma 4.5, for a von Neumann
algebra `M` with cyclic separating vector `Ω`, in the bounded formulation of
`VN/Modular/*`:

* **Lemma 4.3** (linear Radon–Nikodym, after Sakai): for self-adjoint `x′ ∈ M′`
  and `Re λ > 0` there is a self-adjoint `x ∈ M` with `P(x′Ω) = P(λ̄ • xΩ)`, i.e.
  `Re⟪yΩ, x′Ω⟫ = Re⟪yΩ, λ̄ xΩ⟫` for all self-adjoint `y ∈ M`. The proof is the
  only place where a compactness argument enters: the set
  `V = {P(λ̄ • xΩ) : x ∈ M_s, ‖x‖ ≤ 1}` is convex and closed (weak-operator
  compactness of the self-adjoint unit ball, `VN/Modular/WOTCompact`), and a
  point `P(x′Ω) ∉ V` would be separated from `V` by a vector `hΩ`, `h ∈ M_s`,
  contradicting the inequality `Re⟪hΩ, x′Ω⟫ ≤ Re⟪hΩ, sgn(h) Ω⟫` (for
  `0 ≤ x′ ≤ 1`).
* **Corollary 4.4**: for `x′ ∈ M′` there is `x ∈ M` with `J T x′Ω = xΩ` and
  `J T x′*Ω = x*Ω`.
* **Lemma 4.5**: for self-adjoint `x′ ∈ M′` and `Re λ > 0` there is `x ∈ M` with
  `T J x′ J T = λ (2 − R) x R + λ̄ R x (2 − R)`.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.Modular.PolarJ
import MIPRE.Background.Repetition.CommutingRepetition.VN.Modular.WOTCompact

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace VN

namespace Modular

open scoped InnerProductSpace ComplexConjugate
open Filter Topology BorelCalc ClosedSubmodule

set_option linter.unusedSectionVars false

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (M : VonNeumannAlgebra K) (Ω : K)

/-! ## Helpers on `𝒦`, `M_s Ω` and `M′ Ω` -/

theorem inner_self_re' (ζ : K) : (⟪ζ, ζ⟫_ℂ).re = ‖ζ‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) ζ

theorem ofReal_smul' (r : ℝ) (v : K) : (r : ℂ) • v = r • v := Complex.coe_smul r v

/-- Elements of the real span of `M_s Ω` are of the form `hΩ` with `h ∈ M_s`. -/
theorem exists_sa_of_mem_saOrbit {v : K} (hv : v ∈ saOrbit M Ω) :
    ∃ h ∈ M, IsSelfAdjoint h ∧ h Ω = v := by
  refine Submodule.span_induction (p := fun v _ => ∃ h ∈ M, IsSelfAdjoint h ∧ h Ω = v) ?_ ?_ ?_ ?_
    hv
  · rintro _ ⟨a, ha, hsa, rfl⟩
    exact ⟨a, ha, hsa, rfl⟩
  · exact ⟨0, zero_mem _, IsSelfAdjoint.zero _, by simp⟩
  · rintro _ _ _ _ ⟨a, ha, hsa, rfl⟩ ⟨b, hb, hsb, rfl⟩
    exact ⟨a + b, add_mem ha hb, hsa.add hsb, by simp⟩
  · rintro c _ _ ⟨a, ha, hsa, rfl⟩
    refine ⟨(c : ℂ) • a, VN.smul_mem_vn M _ ha, ?_, ?_⟩
    · rw [IsSelfAdjoint, star_smul, hsa.star_eq, Complex.star_def, Complex.conj_ofReal]
    · rw [_root_.smul_apply]
      exact (RCLike.real_smul_eq_coe_smul (K := ℂ) c (a Ω)).symm

/-- Vectors of `𝒦` are approximated by `hΩ`, `h ∈ M_s`. -/
theorem exists_sa_approx {v : K} (hv : v ∈ Kre M Ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ h ∈ M, IsSelfAdjoint h ∧ ‖h Ω - v‖ < ε := by
  rw [mem_Kre_iff, Metric.mem_closure_iff] at hv
  obtain ⟨w, hw, hd⟩ := hv ε hε
  obtain ⟨h, hh, hsa, rfl⟩ := exists_sa_of_mem_saOrbit M Ω hw
  exact ⟨h, hh, hsa, by rwa [dist_eq_norm, norm_sub_rev] at hd⟩

/-- Two vectors of `𝒦` with the same real inner products against `M_s Ω` are equal. -/
theorem eq_of_inner_sa_eq {u v : K} (hu : u ∈ Kre M Ω) (hv : v ∈ Kre M Ω)
    (h : ∀ y ∈ M, IsSelfAdjoint y → inner ℝ (y Ω) u = inner ℝ (y Ω) v) : u = v := by
  have hd : u - v ∈ Kre M Ω := (Kre M Ω).toSubmodule.sub_mem hu hv
  have h0 : ∀ w ∈ Kre M Ω, inner ℝ w (u - v) = 0 := fun w hw => by
    refine Kre_induction M Ω (p := fun w => inner ℝ w (u - v) = 0) ?_ ?_ ?_ ?_ ?_ hw
    · exact isClosed_eq (by fun_prop) continuous_const
    · simp
    · intro a b ha hb; rw [inner_add_left, ha, hb, add_zero]
    · intro c a ha; rw [inner_smul_left, ha, mul_zero]
    · intro a ha hsa; rw [inner_sub_right, h a ha hsa, sub_self]
  have := h0 _ hd
  rw [real_inner_self_eq_norm_sq, pow_eq_zero_iff two_ne_zero, norm_eq_zero, sub_eq_zero] at this
  exact this

/-- `Pre` of a vector is determined by real inner products against `M_s Ω`. -/
theorem Pre_eq_Pre_of_inner_sa {u v : K}
    (h : ∀ y ∈ M, IsSelfAdjoint y → inner ℝ (y Ω) u = inner ℝ (y Ω) v) :
    Pre M Ω u = Pre M Ω v := by
  refine eq_of_inner_sa_eq M Ω (Pre_apply_mem M Ω u) (Pre_apply_mem M Ω v) fun y hy hsa => ?_
  rw [← inner_Pre_left M Ω (y Ω) u, ← inner_Pre_left M Ω (y Ω) v,
    Pre_eq_self M Ω (mem_Kre_of_sa M Ω hy hsa)]
  exact h y hy hsa

/-- `Pre (λ̄ • Ω) = Re λ • Ω` (`P Ω = Ω`, `P (iΩ) = i Q Ω = 0`). -/
theorem Pre_conj_smul_Ω (l : ℂ) : Pre M Ω (conj l • Ω) = l.re • Ω := by
  have h1 : conj l • Ω = (l.re : ℂ) • Ω + ((-l.im : ℝ) : ℂ) • (Complex.I • Ω) := by
    rw [smul_smul, ← add_smul]
    congr 1
    apply Complex.ext <;> simp
  rw [h1, map_add]
  have e1 : ((l.re : ℂ) • Ω) = l.re • Ω := (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm
  have e2 : (((-l.im : ℝ) : ℂ) • (Complex.I • Ω)) = (-l.im) • (Complex.I • Ω) :=
    (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm
  rw [e1, e2, map_smul, map_smul, Pre_Ω, Pre_I_smul, Qre_Ω, smul_zero, smul_zero, add_zero]

/-- Elements of the orbit of a von Neumann algebra are of the form `y ξ`, `y ∈ N`. -/
theorem exists_of_mem_orbit_vn (N : VonNeumannAlgebra K) {ξ v : K}
    (hv : v ∈ orbit (N : Set (K →L[ℂ] K)) ξ) : ∃ y ∈ N, y ξ = v := by
  refine Submodule.span_induction (p := fun v _ => ∃ y ∈ N, y ξ = v) ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · exact ⟨0, zero_mem _, by simp⟩
  · rintro _ _ _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, add_mem ha hb, by simp⟩
  · rintro c _ _ ⟨a, ha, rfl⟩
    exact ⟨c • a, VN.smul_mem_vn N c ha, by simp⟩

/-- `M′ Ω` is dense (`Ω` separating for `M`). -/
theorem dense_commutant_orbit (hs : IsSeparating (M : Set (K →L[ℂ] K)) Ω) :
    Dense {v : K | ∃ y ∈ M.commutant, y Ω = v} := by
  have h := hs.isCyclic_commutant
  refine h.mono fun v hv => exists_of_mem_orbit_vn M.commutant hv

/-- Two vectors with the same inner products against the dense set `M′ Ω` are equal. -/
theorem eq_of_inner_commutant (hs : IsSeparating (M : Set (K →L[ℂ] K)) Ω) {u v : K}
    (h : ∀ z ∈ M.commutant, ⟪z Ω, u⟫_ℂ = ⟪z Ω, v⟫_ℂ) : u = v := by
  have hd := dense_commutant_orbit M Ω hs
  have := Continuous.ext_on hd (f := fun w => ⟪w, u⟫_ℂ) (g := fun w => ⟪w, v⟫_ℂ)
    (by fun_prop) (by fun_prop) (by rintro _ ⟨z, hz, rfl⟩; exact h z hz)
  exact ext_inner_left ℂ fun w => congrFun this w

/-- Two operators with the same matrix coefficients on `M′ Ω × M′ Ω` are equal. -/
theorem ext_of_commutant_orbit (hs : IsSeparating (M : Set (K →L[ℂ] K)) Ω) {S₁ S₂ : K →L[ℂ] K}
    (h : ∀ y ∈ M.commutant, ∀ z ∈ M.commutant, ⟪z Ω, S₁ (y Ω)⟫_ℂ = ⟪z Ω, S₂ (y Ω)⟫_ℂ) :
    S₁ = S₂ := by
  have hd := dense_commutant_orbit M Ω hs
  have := Continuous.ext_on hd (f := fun w => S₁ w) (g := fun w => S₂ w) S₁.continuous
    S₂.continuous (by
      rintro _ ⟨y, hy, rfl⟩
      exact eq_of_inner_commutant M Ω hs fun z hz => h y hy z hz)
  ext w
  exact congrFun this w

/-! ## The self-adjoint unit ball and the set `V` -/

/-- The self-adjoint unit ball of `M`. -/
def saBall : Set (K →L[ℂ] K) := {x | x ∈ M ∧ IsSelfAdjoint x ∧ ‖x‖ ≤ 1}

/-- `V = {P(λ̄ • xΩ) : x ∈ M_s, ‖x‖ ≤ 1}`. -/
def Vset (l : ℂ) : Set K := (fun x : K →L[ℂ] K => Pre M Ω (conj l • x Ω)) '' saBall M

theorem convex_Vset (l : ℂ) : Convex ℝ (Vset M Ω l) := by
  rintro _ ⟨x, ⟨hxM, hxs, hxn⟩, rfl⟩ _ ⟨y, ⟨hyM, hys, hyn⟩, rfl⟩ a b ha hb hab
  refine ⟨(a : ℂ) • x + (b : ℂ) • y, ⟨add_mem (VN.smul_mem_vn M _ hxM) (VN.smul_mem_vn M _ hyM),
    ?_, ?_⟩, ?_⟩
  · rw [IsSelfAdjoint, star_add, star_smul, star_smul, hxs.star_eq, hys.star_eq]
    simp
  · calc ‖(a : ℂ) • x + (b : ℂ) • y‖ ≤ ‖(a : ℂ) • x‖ + ‖(b : ℂ) • y‖ := norm_add_le _ _
      _ = a * ‖x‖ + b * ‖y‖ := by
        simp only [norm_smul, Complex.norm_real, Real.norm_of_nonneg ha,
          Real.norm_of_nonneg hb]
      _ ≤ a * 1 + b * 1 := by gcongr
      _ = 1 := by rw [mul_one, mul_one, hab]
  · simp only [_root_.add_apply, _root_.smul_apply, smul_add, map_add]
    have e1 : ((a : ℂ) • (conj l • x Ω)) = a • (conj l • x Ω) :=
      (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm
    have e2 : ((b : ℂ) • (conj l • y Ω)) = b • (conj l • y Ω) :=
      (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm
    rw [smul_comm (conj l) (a : ℂ), smul_comm (conj l) (b : ℂ), e1, e2,
      (Pre M Ω).map_smul_of_tower a, (Pre M Ω).map_smul_of_tower b]

theorem isClosed_Vset (l : ℂ) : IsClosed (Vset M Ω l) := by
  rw [← isSeqClosed_iff_isClosed]
  intro v w hv hvw
  choose x hx hxv using hv
  obtain ⟨L, hLM, hLs, hLn, hL⟩ := WOT.exists_clusterPt_saBall M x fun n => hx n
  refine ⟨L, ⟨hLM, hLs, hLn⟩, ?_⟩
  refine ext_inner_left ℝ fun ζ => ?_
  have key : ∀ y : K →L[ℂ] K, inner ℝ ζ (Pre M Ω (conj l • y Ω)) =
      (conj l * conj ⟪y Ω, Pre M Ω ζ⟫_ℂ).re := fun y => by
    rw [← inner_Pre_left, inner_real_eq_re_inner, inner_smul_right, inner_conj_symm]
  rw [key]
  have h1 : Tendsto (fun n => (conj l * conj ⟪x n Ω, Pre M Ω ζ⟫_ℂ).re) atTop
      (𝓝 (inner ℝ ζ w)) := by
    have hcont : Continuous fun v : K => inner ℝ ζ v := by fun_prop
    have := (hcont.tendsto w).comp hvw
    simp only [Function.comp_def] at this
    refine this.congr fun n => ?_
    rw [← hxv n, key]
  exact WOT.tendsto_eq_of_clusterPt (hL Ω (Pre M Ω ζ)) (Φ := fun c => (conj l * conj c).re)
    (by fun_prop) h1

theorem bddAbove_Vset_norm (l : ℂ) : ∀ v ∈ Vset M Ω l, ‖v‖ ≤ ‖l‖ * ‖Ω‖ := by
  rintro _ ⟨x, ⟨_, _, hxn⟩, rfl⟩
  calc ‖Pre M Ω (conj l • x Ω)‖ ≤ ‖conj l • x Ω‖ := norm_Pre_le M Ω _
    _ = ‖l‖ * ‖x Ω‖ := by rw [norm_smul, RCLike.norm_conj]
    _ ≤ ‖l‖ * (‖x‖ * ‖Ω‖) := by gcongr; exact x.le_opNorm Ω
    _ ≤ ‖l‖ * (1 * ‖Ω‖) := by gcongr
    _ = ‖l‖ * ‖Ω‖ := by ring

/-! ## The sign trick: `Re⟪hΩ, x′Ω⟫ ≤ Re⟪hΩ, sgn(h) Ω⟫` for `0 ≤ x′ ≤ 1` in `M′` -/

/-- `sgn t = 1` for `t ≥ 0` and `-1` otherwise. -/
noncomputable def sgn (t : ℝ) : ℝ := if 0 ≤ t then 1 else -1

theorem bdd_sgn : Bdd sgn := by
  refine ⟨?_, 1, fun t => ?_⟩
  · unfold sgn
    exact Measurable.ite measurableSet_Ici measurable_const measurable_const
  · unfold sgn; split_ifs <;> simp

theorem abs_sgn_le (t : ℝ) : |sgn t| ≤ 1 := by unfold sgn; split_ifs <;> simp

/-- Truncation to `[-c, c]`. -/
noncomputable def clamp (c t : ℝ) : ℝ := max (-c) (min t c)

theorem continuous_clamp (c : ℝ) : Continuous (clamp c) := by unfold clamp; fun_prop

theorem abs_clamp_le {c : ℝ} (hc : 0 ≤ c) (t : ℝ) : |clamp c t| ≤ c := by
  unfold clamp
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_right _ _)

theorem bdd_clamp {c : ℝ} (hc : 0 ≤ c) : Bdd (clamp c) :=
  Bdd.of_continuous (continuous_clamp c) (abs_clamp_le hc)

theorem bdd_abs_clamp {c : ℝ} (hc : 0 ≤ c) : Bdd fun t => |clamp c t| :=
  Bdd.of_continuous (continuous_abs.comp (continuous_clamp c)) fun t => by
    rw [abs_abs]; exact abs_clamp_le hc t

theorem clamp_eq_of_abs_le {c t : ℝ} (h : |t| ≤ c) : clamp c t = t := by
  unfold clamp
  rw [abs_le] at h
  rw [min_eq_left h.2, max_eq_right h.1]

theorem sgn_mul_clamp {c : ℝ} (hc : 0 ≤ c) (t : ℝ) : sgn t * clamp c t = |clamp c t| := by
  unfold sgn clamp
  split_ifs with h
  · rw [one_mul, abs_of_nonneg]
    exact le_max_of_le_right (le_min h hc)
  · rw [neg_one_mul, abs_of_nonpos]
    exact max_le (by linarith) ((min_le_left _ _).trans (not_le.mp h).le)

section Sign

variable {h : K →L[ℂ] K} (hsa : IsSelfAdjoint h)

/-- `h = clamp(h)` since the spectrum lies in `[-‖h‖, ‖h‖]`. -/
theorem bfc_clamp_eq : bfc h hsa (clamp ‖h‖) = h := by
  rw [bfc_cfc _ _ (bdd_clamp (norm_nonneg h)) (continuous_clamp _)]
  calc cfc (clamp ‖h‖) h = cfc (fun t : ℝ => t) h :=
        cfc_congr fun t ht => clamp_eq_of_abs_le (abs_le.mpr (spectrum_subset_Icc_norm h ht))
    _ = h := cfc_id' ℝ h hsa

/-- The sign of `h`, `sgn(h) = bfc h sgn`. -/
noncomputable def sgnOp : K →L[ℂ] K := bfc h hsa sgn

/-- `|h| = bfc h |clamp|`. -/
noncomputable def absOp : K →L[ℂ] K := bfc h hsa fun t => |clamp ‖h‖ t|

theorem sgnOp_isSelfAdjoint : IsSelfAdjoint (sgnOp hsa) := bfc_isSelfAdjoint _ _ bdd_sgn

theorem norm_sgnOp_le : ‖sgnOp hsa‖ ≤ 1 := by
  unfold sgnOp
  rw [← cbfc_ofReal]
  refine norm_cbfc_le _ _ (CBdd.ofReal bdd_sgn) zero_le_one fun t => ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_sgn_le t

theorem sgnOp_mem (hh : h ∈ M) : sgnOp hsa ∈ M := bfc_mem M hsa hh bdd_sgn

theorem absOp_isSelfAdjoint : IsSelfAdjoint (absOp hsa) :=
  bfc_isSelfAdjoint _ _ (bdd_abs_clamp (norm_nonneg h))

theorem absOp_mem (hh : h ∈ M) : absOp hsa ∈ M :=
  bfc_mem M hsa hh (bdd_abs_clamp (norm_nonneg h))

theorem absOp_nonneg : 0 ≤ absOp hsa :=
  bfc_nonneg _ _ (bdd_abs_clamp (norm_nonneg h)) fun t => abs_nonneg _

theorem absOp_sub_nonneg : 0 ≤ absOp hsa - h := by
  have e : absOp hsa - h = bfc h hsa ((fun t => |clamp ‖h‖ t|) - clamp ‖h‖) := by
    rw [bfc_sub _ _ (bdd_abs_clamp (norm_nonneg h)) (bdd_clamp (norm_nonneg h)), absOp,
      bfc_clamp_eq]
  rw [e]
  exact bfc_nonneg _ _ ((bdd_abs_clamp (norm_nonneg h)).sub (bdd_clamp (norm_nonneg h)))
    fun t => by simp only [Pi.sub_apply, sub_nonneg]; exact le_abs_self _

theorem sgnOp_mul : sgnOp hsa * h = absOp hsa := by
  have e := bfc_mul h hsa bdd_sgn (bdd_clamp (norm_nonneg h))
  rw [bfc_clamp_eq] at e
  rw [sgnOp, ← e, absOp]
  congr 1
  funext t
  exact sgn_mul_clamp (norm_nonneg h) t

theorem mul_sgnOp : h * sgnOp hsa = absOp hsa := by
  have e := bfc_mul h hsa (bdd_clamp (norm_nonneg h)) bdd_sgn
  rw [bfc_clamp_eq] at e
  rw [sgnOp, ← e, absOp]
  congr 1
  funext t
  rw [Pi.mul_apply, mul_comm]
  exact sgn_mul_clamp (norm_nonneg h) t

end Sign

/-- A nonnegative element of a von Neumann algebra has a self-adjoint square root in it. -/
theorem exists_sqrt_mem (N : VonNeumannAlgebra K) {A : K →L[ℂ] K} (hA : A ∈ N) (h0 : 0 ≤ A) :
    ∃ r ∈ N, IsSelfAdjoint r ∧ r * r = A := by
  refine ⟨cfc Real.sqrt A, cfc_real_mem N hA _, cfc_predicate _ _, ?_⟩
  have hsa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg h0
  rw [← cfc_mul Real.sqrt Real.sqrt A Real.continuous_sqrt.continuousOn
    Real.continuous_sqrt.continuousOn]
  calc cfc (fun t : ℝ => Real.sqrt t * Real.sqrt t) A = cfc (fun t : ℝ => t) A :=
        cfc_congr fun t ht => Real.mul_self_sqrt (spectrum_nonneg_of_nonneg h0 ht)
    _ = A := cfc_id' ℝ A hsa

theorem im_inner_apply_sa {A : K →L[ℂ] K} (hA : IsSelfAdjoint A) (ξ : K) :
    (⟪ξ, A ξ⟫_ℂ).im = 0 := by
  have : conj ⟪ξ, A ξ⟫_ℂ = ⟪ξ, A ξ⟫_ℂ := by
    rw [inner_conj_symm, inner_sa hA]
  exact (Complex.conj_eq_iff_im.mp this)

/-- RvD's computation (proof of Lemma 4.3): for `h ∈ M_s` and `0 ≤ x′ ≤ 1` in `M′`,
`Re⟪hΩ, x′Ω⟫ ≤ Re⟪hΩ, sgn(h) Ω⟫`. -/
theorem re_inner_le_sgn {h : K →L[ℂ] K} (hh : h ∈ M) (hsa : IsSelfAdjoint h)
    {x' : K →L[ℂ] K} (hx' : x' ∈ M.commutant) (h0 : 0 ≤ x') (h1 : x' ≤ 1) :
    (⟪h Ω, x' Ω⟫_ℂ).re ≤ (⟪h Ω, sgnOp hsa Ω⟫_ℂ).re := by
  obtain ⟨s, hsM, hss, hs2⟩ := exists_sqrt_mem M.commutant hx' h0
  obtain ⟨r, hrM, hrs, hr2⟩ := exists_sqrt_mem M (absOp_mem M hsa hh) (absOp_nonneg hsa)
  have hAM : absOp hsa ∈ M := absOp_mem M hsa hh
  have e1 : x' Ω = s (s Ω) := by rw [← mul_apply_eq_comp, hs2]
  -- step 1: `⟪hΩ, x′Ω⟫ = ⟪sΩ, h (sΩ)⟫`
  have step1 : ⟪h Ω, x' Ω⟫_ℂ = ⟪s Ω, h (s Ω)⟫_ℂ := by
    have e2 : h (s (s Ω)) = s (h (s Ω)) :=
      (congrArg (fun S : K →L[ℂ] K => S (s Ω)) (commutant_mul_of_mem hh hsM)).symm
    rw [← inner_sa hsa, e1, e2, inner_sa hss]
  -- step 2: `Re⟪sΩ, h sΩ⟫ ≤ Re⟪sΩ, |h| sΩ⟫`
  have step2 : (⟪s Ω, h (s Ω)⟫_ℂ).re ≤ (⟪s Ω, absOp hsa (s Ω)⟫_ℂ).re := by
    have := Resolver.Douglas.re_inner_nonneg_of_nonneg (absOp_sub_nonneg hsa) (s Ω)
    rw [_root_.sub_apply, inner_sub_right, Complex.sub_re] at this
    linarith
  -- step 3: `⟪sΩ, |h| sΩ⟫ = ⟪Ω, |h| x′ Ω⟫`
  have step3 : ⟪s Ω, absOp hsa (s Ω)⟫_ℂ = ⟪Ω, absOp hsa (x' Ω)⟫_ℂ := by
    have e2 : absOp hsa (s (s Ω)) = s (absOp hsa (s Ω)) :=
      (congrArg (fun S : K →L[ℂ] K => S (s Ω)) (commutant_mul_of_mem hAM hsM)).symm
    rw [e1, e2, inner_sa hss]
  -- step 4: `Re⟪Ω, |h| x′Ω⟫ ≤ Re⟪Ω, |h| Ω⟫`
  have step4 : (⟪Ω, absOp hsa (x' Ω)⟫_ℂ).re ≤ (⟪Ω, absOp hsa Ω⟫_ℂ).re := by
    have hpos : 0 ≤ (⟪r Ω, (1 - x') (r Ω)⟫_ℂ).re :=
      Resolver.Douglas.re_inner_nonneg_of_nonneg (sub_nonneg.mpr h1) (r Ω)
    have e : ⟪r Ω, (1 - x') (r Ω)⟫_ℂ = ⟪Ω, absOp hsa Ω⟫_ℂ - ⟪Ω, absOp hsa (x' Ω)⟫_ℂ := by
      have hc : r * (1 - x') = (1 - x') * r :=
        (commutant_mul_of_mem hrM (sub_mem (one_mem _) hx')).symm
      have hc2 : absOp hsa * x' = x' * absOp hsa := (commutant_mul_of_mem hAM hx').symm
      have h1' : r ((1 - x') (r Ω)) = absOp hsa Ω - absOp hsa (x' Ω) := by
        calc r ((1 - x') (r Ω)) = (r * (1 - x') * r) Ω := rfl
          _ = ((1 - x') * (r * r)) Ω := by rw [hc, mul_assoc]
          _ = ((1 - x') * absOp hsa) Ω := by rw [hr2]
          _ = absOp hsa Ω - absOp hsa (x' Ω) := by
            rw [sub_mul, one_mul, ← hc2, _root_.sub_apply, mul_apply_eq_comp]
      rw [← inner_sa hrs, h1', inner_sub_right]
    rw [e, Complex.sub_re] at hpos
    linarith
  -- step 5: `⟪Ω, |h| Ω⟫ = ⟪hΩ, sgn(h) Ω⟫`
  have step5 : ⟪Ω, absOp hsa Ω⟫_ℂ = ⟪h Ω, sgnOp hsa Ω⟫_ℂ := by
    rw [← inner_sa hsa, ← mul_apply_eq_comp, mul_sgnOp]
  rw [step1, ← step5]
  exact step2.trans (by rw [step3]; exact step4)

/-- `⟪hΩ, sgn(h) Ω⟫` is real. -/
theorem im_inner_sgn {h : K →L[ℂ] K} (hsa : IsSelfAdjoint h) :
    (⟪h Ω, sgnOp hsa Ω⟫_ℂ).im = 0 := by
  rw [← inner_sa hsa, ← mul_apply_eq_comp, mul_sgnOp]
  exact im_inner_apply_sa (absOp_isSelfAdjoint hsa) Ω

/-! ## RvD Lemma 4.3 -/

/-- Real linearity of `Pre` for real scalars written as complex numbers. -/
theorem Pre_ofReal_smul (r : ℝ) (v : K) : Pre M Ω ((r : ℂ) • v) = (r : ℂ) • Pre M Ω v := by
  have e1 : ((r : ℂ) • v) = r • v := (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm
  have e2 : ((r : ℂ) • Pre M Ω v) = r • Pre M Ω v :=
    (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm
  rw [e1, e2, map_smul]

/-- The core case of Lemma 4.3: `0 ≤ x′ ≤ 1`, `Re λ = 1`. -/
theorem Pre_mem_Vset {x' : K →L[ℂ] K} (hx' : x' ∈ M.commutant) (h0 : 0 ≤ x') (h1 : x' ≤ 1)
    {l : ℂ} (hl : l.re = 1) : Pre M Ω (x' Ω) ∈ Vset M Ω l := by
  by_contra hV
  obtain ⟨f, u₀, hfV, hfx⟩ :=
    geometric_hahn_banach_closed_point (convex_Vset M Ω l) (isClosed_Vset M Ω l) hV
  set h₀ : K := (InnerProductSpace.toDual ℝ K).symm f with hh₀
  have hf : ∀ v, f v = inner ℝ h₀ v := fun v => (InnerProductSpace.toDual_symm_apply).symm
  set h₁ := Pre M Ω h₀ with hh₁
  have hV' : ∀ x ∈ saBall M, inner ℝ h₁ (conj l • x Ω) < u₀ := fun x hx => by
    rw [hh₁, inner_Pre_left, ← hf]
    exact hfV _ ⟨x, hx, rfl⟩
  have hx'' : u₀ < inner ℝ h₁ (x' Ω) := by
    rw [hh₁, inner_Pre_left, ← hf]
    exact hfx
  set g := inner ℝ h₁ (x' Ω) - u₀ with hg
  have hgpos : 0 < g := sub_pos.mpr hx''
  set D := ‖l‖ * ‖Ω‖ + ‖x' Ω‖ + 1 with hD
  have hDpos : 0 < D := by positivity
  obtain ⟨h, hh, hsa, hclose⟩ :=
    exists_sa_approx M Ω (Pre_apply_mem M Ω h₀) (ε := g / (2 * D)) (by positivity)
  set d := h Ω - h₁ with hd
  have hdle : ‖d‖ ≤ g / (2 * D) := hclose.le
  -- the vector `hΩ` separates as well
  have hlt : ∀ x ∈ saBall M, inner ℝ (h Ω) (conj l • x Ω) < inner ℝ (h Ω) (x' Ω) := by
    intro x hx
    have hxn : ‖conj l • x Ω‖ ≤ ‖l‖ * ‖Ω‖ := by
      calc ‖conj l • x Ω‖ = ‖l‖ * ‖x Ω‖ := by rw [norm_smul, RCLike.norm_conj]
        _ ≤ ‖l‖ * (‖x‖ * ‖Ω‖) := by gcongr; exact x.le_opNorm Ω
        _ ≤ ‖l‖ * (1 * ‖Ω‖) := by gcongr; exact hx.2.2
        _ = ‖l‖ * ‖Ω‖ := by ring
    have hb1 : inner ℝ d (conj l • x Ω) ≤ g / 2 := by
      calc inner ℝ d (conj l • x Ω) ≤ ‖d‖ * ‖conj l • x Ω‖ := real_inner_le_norm _ _
        _ ≤ (g / (2 * D)) * D := by
          gcongr
          rw [hD]; linarith [norm_nonneg (x' Ω)]
        _ = g / 2 := by field_simp
    have hb2 : -(g / 2) ≤ inner ℝ d (x' Ω) := by
      have := abs_real_inner_le_norm d (x' Ω)
      have h2 : ‖d‖ * ‖x' Ω‖ ≤ g / 2 := by
        calc ‖d‖ * ‖x' Ω‖ ≤ (g / (2 * D)) * D := by
              gcongr
              rw [hD]; linarith [norm_nonneg l, norm_nonneg Ω, mul_nonneg (norm_nonneg l) (norm_nonneg Ω)]
          _ = g / 2 := by field_simp
      have := (abs_le.mp this).1
      linarith
    have e1 : inner ℝ (h Ω) (conj l • x Ω) = inner ℝ h₁ (conj l • x Ω) + inner ℝ d (conj l • x Ω) := by
      rw [hd, ← inner_add_left, add_sub_cancel]
    have e2 : inner ℝ (h Ω) (x' Ω) = inner ℝ h₁ (x' Ω) + inner ℝ d (x' Ω) := by
      rw [hd, ← inner_add_left, add_sub_cancel]
    have := hV' x hx
    rw [e1, e2]
    linarith
  -- contradiction with the sign trick
  have hmem : sgnOp hsa ∈ saBall M := ⟨sgnOp_mem M hsa hh, sgnOp_isSelfAdjoint hsa, norm_sgnOp_le hsa⟩
  have h1' := hlt _ hmem
  have h2' := re_inner_le_sgn M Ω hh hsa hx' h0 h1
  rw [inner_real_eq_re_inner, inner_real_eq_re_inner, inner_smul_right, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, hl, im_inner_sgn Ω hsa, one_mul, mul_zero, sub_zero] at h1'
  linarith

/-- **RvD Lemma 4.3** (existence): for self-adjoint `x′ ∈ M′` and `Re λ > 0` there is a
self-adjoint `x ∈ M` with `P(x′Ω) = P(λ̄ • xΩ)`. -/
theorem exists_linearRN {x' : K →L[ℂ] K} (hx' : x' ∈ M.commutant) (hsa' : IsSelfAdjoint x')
    {l : ℂ} (hl : 0 < l.re) :
    ∃ x ∈ M, IsSelfAdjoint x ∧ Pre M Ω (x' Ω) = Pre M Ω (conj l • x Ω) := by
  -- normalize `Re λ = 1`
  set μ : ℂ := ((l.re)⁻¹ : ℝ) • l with hμ
  have hμre : μ.re = 1 := by
    rw [hμ, Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, inv_mul_cancel₀ hl.ne']
  have hconj : conj l = (l.re : ℂ) * conj μ := by
    rw [hμ, Complex.real_smul, map_mul, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul,
      mul_inv_cancel₀ hl.ne', Complex.ofReal_one, one_mul]
  -- the core case applied to `x′₁ = (x′ + c)/(2c)`, `c = ‖x′‖`
  by_cases hz : x' = 0
  · refine ⟨0, zero_mem _, IsSelfAdjoint.zero _, ?_⟩
    rw [hz]; simp
  set c := ‖x'‖ with hc
  have hcpos : 0 < c := norm_pos_iff.mpr hz
  set x'₁ : K →L[ℂ] K := ((2 * c)⁻¹ : ℝ) • (x' + (c : ℂ) • 1) with hx'₁
  have hx'₁M : x'₁ ∈ M.commutant := by
    rw [hx'₁, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    exact VN.smul_mem_vn _ _ (add_mem hx' (VN.smul_mem_vn _ _ (one_mem _)))
  have hx'₁sa : IsSelfAdjoint x'₁ := by
    rw [hx'₁]
    refine IsSelfAdjoint.smul ?_ (hsa'.add ?_)
    · exact isSelfAdjoint_iff.mpr rfl
    · rw [RCLike.real_smul_eq_coe_smul (K := ℂ)] at *
      exact IsSelfAdjoint.smul (by rw [IsSelfAdjoint, Complex.star_def, Complex.conj_ofReal])
        (IsSelfAdjoint.one _)
  have hbound : ∀ ζ : K, |(⟪ζ, x' ζ⟫_ℂ).re| ≤ c * ‖ζ‖ ^ 2 := fun ζ => by
    calc |(⟪ζ, x' ζ⟫_ℂ).re| ≤ ‖⟪ζ, x' ζ⟫_ℂ‖ := Complex.abs_re_le_norm _
      _ ≤ ‖ζ‖ * ‖x' ζ‖ := norm_inner_le_norm _ _
      _ ≤ ‖ζ‖ * (c * ‖ζ‖) := by gcongr; exact x'.le_opNorm ζ
      _ = c * ‖ζ‖ ^ 2 := by ring
  have hx'₁re : ∀ ζ : K, (⟪ζ, x'₁ ζ⟫_ℂ).re =
      (2 * c)⁻¹ * ((⟪ζ, x' ζ⟫_ℂ).re + c * ‖ζ‖ ^ 2) := fun ζ => by
    rw [hx'₁, _root_.smul_apply, _root_.add_apply, _root_.smul_apply, one_apply_eq_self,
      ← ofReal_smul', inner_smul_right, inner_add_right, inner_smul_right, Complex.re_ofReal_mul,
      Complex.add_re, Complex.re_ofReal_mul, inner_self_re']
  have h0 : 0 ≤ x'₁ := by
    refine Resolver.Douglas.nonneg_of_re_inner hx'₁sa fun ζ => ?_
    rw [← inner_sa hx'₁sa, hx'₁re]
    have := (abs_le.mp (hbound ζ)).1
    have : 0 ≤ (2 * c)⁻¹ := by positivity
    exact mul_nonneg this (by linarith)
  have h1 : x'₁ ≤ 1 := by
    rw [ContinuousLinearMap.le_def, ← ContinuousLinearMap.nonneg_iff_isPositive]
    refine Resolver.Douglas.nonneg_of_re_inner ((IsSelfAdjoint.one _).sub hx'₁sa) fun ζ => ?_
    rw [_root_.sub_apply, one_apply_eq_self, inner_sub_left, Complex.sub_re, inner_self_re',
      ← inner_sa hx'₁sa, hx'₁re]
    have := (abs_le.mp (hbound ζ)).2
    have hh : (2 * c)⁻¹ * ((⟪ζ, x' ζ⟫_ℂ).re + c * ‖ζ‖ ^ 2) ≤ (2 * c)⁻¹ * (2 * c * ‖ζ‖ ^ 2) := by
      gcongr
      linarith
    rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul] at hh
    linarith
  obtain ⟨x₁, ⟨hx₁M', hx₁sa', -⟩, hx₁⟩ := Pre_mem_Vset M Ω hx'₁M h0 h1 hμre
  -- `x = (2c x₁ − c) / Re λ`
  refine ⟨((l.re)⁻¹ : ℝ) • ((2 * c : ℝ) • x₁ - (c : ℝ) • 1), ?_, ?_, ?_⟩
  · rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ),
      RCLike.real_smul_eq_coe_smul (K := ℂ)]
    exact VN.smul_mem_vn _ _ (sub_mem (VN.smul_mem_vn _ _ hx₁M') (VN.smul_mem_vn _ _ (one_mem _)))
  · refine IsSelfAdjoint.smul (isSelfAdjoint_iff.mpr rfl)
      ((IsSelfAdjoint.smul (isSelfAdjoint_iff.mpr rfl) hx₁sa').sub
        (IsSelfAdjoint.smul (isSelfAdjoint_iff.mpr rfl) (IsSelfAdjoint.one _)))
  · -- `x′ = 2c x′₁ − c`
    have hs1 : conj l * (((l.re)⁻¹ : ℝ) : ℂ) = conj μ := by
      rw [hconj, Complex.ofReal_inv, mul_comm, ← mul_assoc,
        inv_mul_cancel₀ (by exact_mod_cast hl.ne'), one_mul]
    have ex' : x' Ω = ((2 * c : ℝ) : ℂ) • x'₁ Ω - (c : ℂ) • Ω := by
      have : ((2 * c : ℝ) : ℂ) • x'₁ Ω = x' Ω + (c : ℂ) • Ω := by
        rw [hx'₁, _root_.smul_apply, _root_.add_apply, _root_.smul_apply, one_apply_eq_self,
          ← ofReal_smul', smul_smul, ← Complex.ofReal_mul,
          mul_inv_cancel₀ (by positivity : (2 * c : ℝ) ≠ 0), Complex.ofReal_one, one_smul]
      rw [this, add_sub_cancel_right]
    have ex : conj l • (((l.re)⁻¹ : ℝ) • ((2 * c : ℝ) • x₁ - (c : ℝ) • 1)) Ω =
        ((2 * c : ℝ) : ℂ) • (conj μ • x₁ Ω) - (c : ℂ) • (conj μ • Ω) := by
      rw [_root_.smul_apply, _root_.sub_apply, _root_.smul_apply, _root_.smul_apply,
        one_apply_eq_self, ← ofReal_smul', ← ofReal_smul', ← ofReal_smul', smul_smul, hs1,
        smul_sub, smul_comm (conj μ) ((2 * c : ℝ) : ℂ), smul_comm (conj μ) ((c : ℝ) : ℂ)]
    have hx₁' : Pre M Ω (conj μ • x₁ Ω) = Pre M Ω (x'₁ Ω) := hx₁
    rw [ex', ex, map_sub, map_sub, Pre_ofReal_smul, Pre_ofReal_smul, Pre_ofReal_smul,
      Pre_ofReal_smul, ← hx₁', Pre_conj_smul_Ω, hμre, one_smul, Pre_Ω]

/-! ## RvD Corollary 4.4 -/

variable (hs : IsSeparating (M : Set (K →L[ℂ] K)) Ω) (hc : IsCyclic (M : Set (K →L[ℂ] K)) Ω)

include hs hc in
/-- Corollary 4.4 for self-adjoint `x′`: `J T x′Ω = xΩ` with `x ∈ M_s`. -/
theorem exists_Jm_Tm_eq_sa {x' : K →L[ℂ] K} (hx' : x' ∈ M.commutant) (hsa' : IsSelfAdjoint x') :
    ∃ x ∈ M, IsSelfAdjoint x ∧ Jm M Ω (Tm M Ω (x' Ω)) = x Ω := by
  obtain ⟨x, hxM, hxsa, hP⟩ := exists_linearRN M Ω hx' hsa' (l := 1) (by simp)
  refine ⟨x, hxM, hxsa, ?_⟩
  rw [Jm_Tm M Ω hs hc, Am_apply, Qre_commutant_sa M Ω hx' hsa', sub_zero, hP, map_one, one_smul,
    Pre_eq_self M Ω (mem_Kre_of_sa M Ω hxM hxsa)]

include hs hc in
/-- **RvD Corollary 4.4**: for `x′ ∈ M′` there is `x ∈ M` with `J T x′Ω = xΩ` and
`J T x′*Ω = x*Ω`. -/
theorem exists_Jm_Tm_eq {x' : K →L[ℂ] K} (hx' : x' ∈ M.commutant) :
    ∃ x ∈ M, Jm M Ω (Tm M Ω (x' Ω)) = x Ω ∧ Jm M Ω (Tm M Ω (star x' Ω)) = star x Ω := by
  obtain ⟨a', b', ha', hb', hsa, hsb, hab⟩ : ∃ a b : K →L[ℂ] K, a ∈ M.commutant ∧
      b ∈ M.commutant ∧ IsSelfAdjoint a ∧ IsSelfAdjoint b ∧ x' = a + Complex.I • b :=
    ⟨(1 / 2 : ℂ) • (x' + star x'), (-(1 / 2 : ℂ) * Complex.I) • (x' - star x'),
      VN.smul_mem_vn _ _ (add_mem hx' (star_mem hx')),
      VN.smul_mem_vn _ _ (sub_mem hx' (star_mem hx')),
      isSelfAdjoint_half_add_star x', isSelfAdjoint_half_I_sub_star x', eq_sa_add_I_smul_sa x'⟩
  obtain ⟨a, haM, hasa, ha⟩ := exists_Jm_Tm_eq_sa M Ω hs hc ha' hsa
  obtain ⟨b, hbM, hbsa, hb⟩ := exists_Jm_Tm_eq_sa M Ω hs hc hb' hsb
  have hstar : star x' = a' - Complex.I • b' := by
    rw [hab, star_add, star_smul, Complex.star_def, Complex.conj_I, hsa.star_eq, hsb.star_eq,
      neg_smul, sub_eq_add_neg]
  refine ⟨a - Complex.I • b, sub_mem haM (VN.smul_mem_vn _ _ hbM), ?_, ?_⟩
  · rw [hab, Jm_Tm M Ω hs hc, _root_.add_apply, _root_.smul_apply, Am_add_I_smul,
      ← Jm_Tm M Ω hs hc, ← Jm_Tm M Ω hs hc, ha, hb, _root_.sub_apply, _root_.smul_apply]
  · rw [hstar, Jm_Tm M Ω hs hc, _root_.sub_apply, _root_.smul_apply, sub_eq_add_neg, ← smul_neg,
      Am_add_I_smul, map_neg, smul_neg, sub_neg_eq_add, ← Jm_Tm M Ω hs hc, ← Jm_Tm M Ω hs hc, ha,
      hb, star_sub, star_smul, Complex.star_def, Complex.conj_I, hasa.star_eq, hbsa.star_eq,
      _root_.sub_apply, _root_.smul_apply, neg_smul, sub_neg_eq_add]

/-! ## RvD Lemma 4.5 -/

include hs hc in
/-- `⟪ξ, J η⟫ = ⟪η, J ξ⟫`. -/
theorem inner_Jm_right (ξ η : K) : ⟪ξ, Jm M Ω η⟫_ℂ = ⟪η, Jm M Ω ξ⟫_ℂ := by
  rw [← inner_conj_symm, inner_Jm_left M Ω hs hc, inner_conj_symm]

/-- The identity (E1): for all `y ∈ M`,
`⟪yΩ, x′Ω⟫ = λ ⟪xΩ, y*Ω⟫ + λ̄ ⟪yΩ, xΩ⟫`, given `P(x′Ω) = 2 P(λ̄ • xΩ)`. -/
theorem inner_eq_of_Pre_eq {x' x : K →L[ℂ] K} (hx' : x' ∈ M.commutant) (hsa' : IsSelfAdjoint x')
    (hx : x ∈ M) (hxsa : IsSelfAdjoint x) {l : ℂ}
    (hP : Pre M Ω (x' Ω) = (2 : ℂ) • Pre M Ω (conj l • x Ω)) {y : K →L[ℂ] K} (hy : y ∈ M) :
    ⟪y Ω, x' Ω⟫_ℂ = l * ⟪x Ω, star y Ω⟫_ℂ + conj l * ⟪y Ω, x Ω⟫_ℂ := by
  -- the self-adjoint case
  have hsa_case : ∀ a ∈ M, IsSelfAdjoint a →
      ⟪a Ω, x' Ω⟫_ℂ = l * ⟪x Ω, star a Ω⟫_ℂ + conj l * ⟪a Ω, x Ω⟫_ℂ := by
    intro a ha hasa
    have him : (⟪a Ω, x' Ω⟫_ℂ).im = 0 := im_inner_commutant_sa M Ω (mem_Kre_of_sa M Ω ha hasa) hx' hsa'
    have hre : (⟪a Ω, x' Ω⟫_ℂ).re = 2 * (conj l * ⟪a Ω, x Ω⟫_ℂ).re := by
      have e1 : (⟪a Ω, x' Ω⟫_ℂ).re = inner ℝ (a Ω) (Pre M Ω (x' Ω)) := by
        rw [← inner_Pre_left, Pre_eq_self M Ω (mem_Kre_of_sa M Ω ha hasa), inner_real_eq_re_inner]
      rw [e1, hP]
      have e2 : ((2 : ℂ) • Pre M Ω (conj l • x Ω)) = (2 : ℝ) • Pre M Ω (conj l • x Ω) := by
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]; norm_num
      rw [e2, inner_smul_right, ← inner_Pre_left, Pre_eq_self M Ω (mem_Kre_of_sa M Ω ha hasa),
        inner_real_eq_re_inner, inner_smul_right]
    rw [hasa.star_eq, ← inner_conj_symm (a Ω) (x Ω)]
    rw [← inner_conj_symm (a Ω) (x Ω)] at hre
    apply Complex.ext
    · rw [hre, Complex.add_re, Complex.mul_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
        Complex.conj_re, Complex.conj_im]
      ring
    · rw [him, Complex.add_im, Complex.mul_im, Complex.mul_im, Complex.conj_re, Complex.conj_im,
        Complex.conj_re, Complex.conj_im]
      ring
  -- conjugate-linear extension
  obtain ⟨a, b, ha, hb, hasa, hbsa, hab⟩ : ∃ a b : K →L[ℂ] K, a ∈ M ∧ b ∈ M ∧ IsSelfAdjoint a ∧
      IsSelfAdjoint b ∧ y = a + Complex.I • b :=
    ⟨(1 / 2 : ℂ) • (y + star y), (-(1 / 2 : ℂ) * Complex.I) • (y - star y),
      VN.smul_mem_vn M _ (add_mem hy (star_mem hy)), VN.smul_mem_vn M _ (sub_mem hy (star_mem hy)),
      isSelfAdjoint_half_add_star y, isSelfAdjoint_half_I_sub_star y, eq_sa_add_I_smul_sa y⟩
  have hA := hsa_case a ha hasa
  have hB := hsa_case b hb hbsa
  rw [hab, star_add, star_smul, Complex.star_def, Complex.conj_I, _root_.add_apply,
    _root_.smul_apply, _root_.add_apply, _root_.smul_apply, inner_add_left, inner_smul_left,
    inner_add_right, inner_smul_right, inner_add_left, inner_smul_left, hA, hB, Complex.conj_I]
  ring

include hs hc in
/-- **RvD Lemma 4.5**: for self-adjoint `x′ ∈ M′` and `Re λ > 0` there is a self-adjoint `x ∈ M`
with `T (J x′ J) T = λ (2 − R) x R + λ̄ R x (2 − R)`. -/
theorem exists_operator_eq {x' : K →L[ℂ] K} (hx' : x' ∈ M.commutant) (hsa' : IsSelfAdjoint x')
    {l : ℂ} (hl : 0 < l.re) :
    ∃ x ∈ M, IsSelfAdjoint x ∧ Tm M Ω * conjJm M Ω x' * Tm M Ω =
      l • ((2 - R M Ω) * x * R M Ω) + conj l • (R M Ω * x * (2 - R M Ω)) := by
  obtain ⟨x₀, hx₀M, hx₀sa, hP₀⟩ := exists_linearRN M Ω hx' hsa' hl
  obtain ⟨x, hxdef⟩ : ∃ x : K →L[ℂ] K, x = (1 / 2 : ℂ) • x₀ := ⟨_, rfl⟩
  have hxM : x ∈ M := hxdef ▸ VN.smul_mem_vn M _ hx₀M
  have hxsa : IsSelfAdjoint x := hxdef ▸
    IsSelfAdjoint.smul (by rw [IsSelfAdjoint, Complex.star_def, map_div₀, map_one, map_ofNat]) hx₀sa
  have hP : Pre M Ω (x' Ω) = (2 : ℂ) • Pre M Ω (conj l • x Ω) := by
    rw [hP₀, hxdef, _root_.smul_apply, smul_smul, mul_comm, ← smul_smul]
    have e : ((1 / 2 : ℂ) • (conj l • x₀ Ω)) = ((1 / 2 : ℝ) : ℂ) • (conj l • x₀ Ω) := by norm_num
    rw [e, Pre_ofReal_smul, smul_smul]
    norm_num
  have E1 : ∀ y ∈ M, ⟪y Ω, x' Ω⟫_ℂ = l * ⟪x Ω, star y Ω⟫_ℂ + conj l * ⟪y Ω, x Ω⟫_ℂ :=
    fun y hy => inner_eq_of_Pre_eq M Ω hx' hsa' hxM hxsa hP hy
  -- (E2): `⟪yΩ, z x′Ω⟫ = λ ⟪y xΩ, zΩ⟫ + λ̄ ⟪yΩ, z xΩ⟫`
  have E2 : ∀ y ∈ M, ∀ z ∈ M, ⟪y Ω, z (x' Ω)⟫_ℂ =
      l * ⟪y (x Ω), z Ω⟫_ℂ + conj l * ⟪y Ω, z (x Ω)⟫_ℂ := by
    intro y hy z hz
    have := E1 _ (mul_mem (star_mem hz) hy)
    have e1 : ⟪(star z * y) Ω, x' Ω⟫_ℂ = ⟪y Ω, z (x' Ω)⟫_ℂ := by
      rw [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_left]
    have e2 : ⟪x Ω, star (star z * y) Ω⟫_ℂ = ⟪y (x Ω), z Ω⟫_ℂ := by
      rw [star_mul, star_star, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_right]
    have e3 : ⟪(star z * y) Ω, x Ω⟫_ℂ = ⟪y Ω, z (x Ω)⟫_ℂ := by
      rw [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_left]
    rw [e1, e2, e3] at this
    exact this
  refine ⟨x, hxM, hxsa, ext_of_commutant_orbit M Ω hs fun y' hy' z' hz' => ?_⟩
  obtain ⟨y, hyM, hy1, hy2⟩ := exists_Jm_Tm_eq M Ω hs hc hy'
  obtain ⟨z, hzM, hz1, hz2⟩ := exists_Jm_Tm_eq M Ω hs hc hz'
  have hT := Tm_isSelfAdjoint M Ω
  -- left side
  have L : ⟪z' Ω, (Tm M Ω * conjJm M Ω x' * Tm M Ω) (y' Ω)⟫_ℂ = ⟪y Ω, z (x' Ω)⟫_ℂ := by
    rw [mul_apply_eq_comp, mul_apply_eq_comp, conjJm_apply, hy1, ← mul_apply_eq_comp,
      commutant_mul_of_mem hyM hx', mul_apply_eq_comp, inner_sa hT, inner_Jm_right M Ω hs hc, hz1,
      ← mul_apply_eq_comp, ← commutant_mul_of_mem hyM hx', mul_apply_eq_comp, ← inner_sa hsa',
      ← mul_apply_eq_comp, commutant_mul_of_mem hzM hx', mul_apply_eq_comp]
  -- first right term: `⟪y xΩ, zΩ⟫ = ⟪z′Ω, (2−R) x R y′Ω⟫`
  have R1 : ⟪y (x Ω), z Ω⟫_ℂ = ⟪z' Ω, (2 - R M Ω) (x (R M Ω (y' Ω)))⟫_ℂ := by
    have hyx : Tm M Ω (Jm M Ω ((y * x) Ω)) = (2 - R M Ω) (star (y * x) Ω) :=
      Tm_Jm_apply_mem M Ω hs hc (mul_mem hyM hxM)
    have hy2' : star y Ω = R M Ω (y' Ω) := by
      have := Tm_Jm_apply_mem_commutant M Ω hs hc (star_mem hy')
      rw [star_star] at this
      rw [← hy2, Jm_Tm_comm M Ω hs hc, this]
    rw [← hz1, inner_Jm_right M Ω hs hc, ← inner_sa hT, ← mul_apply_eq_comp y x, hyx, star_mul,
      mul_apply_eq_comp, hy2', hxsa.star_eq]
  -- second right term: `⟪yΩ, z xΩ⟫ = ⟪z′Ω, R x (2−R) y′Ω⟫`
  have R2 : ⟪y Ω, z (x Ω)⟫_ℂ = ⟪z' Ω, R M Ω (x ((2 - R M Ω) (y' Ω)))⟫_ℂ := by
    have hzx : Tm M Ω (Jm M Ω ((z * x) Ω)) = (2 - R M Ω) (star (z * x) Ω) :=
      Tm_Jm_apply_mem M Ω hs hc (mul_mem hzM hxM)
    have hz2' : star z Ω = R M Ω (z' Ω) := by
      have := Tm_Jm_apply_mem_commutant M Ω hs hc (star_mem hz')
      rw [star_star] at this
      rw [← hz2, Jm_Tm_comm M Ω hs hc, this]
    have hR := R_isSelfAdjoint M Ω
    have h2R := two_sub_R_isSelfAdjoint M Ω
    rw [← hy1, inner_Jm_left M Ω hs hc, inner_sa hT, ← mul_apply_eq_comp z x, hzx, star_mul,
      mul_apply_eq_comp, hz2', hxsa.star_eq, ← inner_sa h2R, ← inner_sa hxsa, ← inner_sa hR]
  rw [L, E2 y hyM z hzM, R1, R2, _root_.add_apply, _root_.smul_apply, _root_.smul_apply,
    inner_add_right, inner_smul_right, inner_smul_right, mul_apply_eq_comp, mul_apply_eq_comp,
    mul_apply_eq_comp, mul_apply_eq_comp]


end Modular

end VN

end CommutingRepetition
