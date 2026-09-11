/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/Crossed/Modular.lean
-/
/-
# The modular data of the dual state (density stage E5.3, HJX (M4))

For the crossed product `ℛ = M ⋊_σ ℚ` on `ℓ²(ℚ, K)` with the cyclic separating vector
`Ω̂ = δ₀ ⊗ Ω`: the modular operator is `R̂ = 1 ⊗ R`, `T̂ = 1 ⊗ T`, the antiunitary is
`Ĵ(δ_s ⊗ ζ) = δ_{-s} ⊗ J Δ^{is} ζ`, and `Δ̂^{it} = 1 ⊗ Δ^{it}`. Consequently
`σ̂_t(π(y)) = π(σ_t y)`, `σ̂_t(λ(g)) = λ(g)`, and `σ̂_s = Ad λ(s)` on `ℛ` for `s ∈ ℚ`.

Method: the bounded identity `T̂ Ĵ (aΩ̂) = (2 − R̂)(a*Ω̂)` is checked on the generators
`a = λ(g) π(y)` (it is RvD Lemma 4.5 for `(M, Ω)` fiberwise) and passes to all `a ∈ ℛ` by
the density theorem for vector functionals; then the uniqueness lemma
`R_eq_of_proj` identifies `(R̂, T̂ Ĵ)` with the modular data of `(ℛ, Ω̂)`.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.Crossed.Product
import MIPRE.Background.Repetition.CommutingRepetition.VN.Modular.Uniqueness
import MIPRE.Background.Repetition.CommutingRepetition.VN.Density
import MIPRE.Background.Repetition.CommutingRepetition.VN.Crossed.AmpCalc

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace VN

namespace Crossed

open scoped InnerProductSpace ComplexConjugate
open Filter Topology _root_.CommutingRepetition.VN.Modular ClosedSubmodule

set_option linter.unusedSectionVars false

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (M : VonNeumannAlgebra K) (Ω : K)
variable (hs : IsSeparating (M : Set (K →L[ℂ] K)) Ω) (hc : IsCyclic (M : Set (K →L[ℂ] K)) Ω)

/-! ## The antiunitary `Ĵ` -/

include hs hc in
theorem summable_norm_sq_Jh (f : L2Q K) :
    Summable fun h : ℚ => ‖Jm M Ω (Δit M Ω (-(h : ℝ)) (f (-h)))‖ ^ 2 := by
  have : (fun h : ℚ => ‖Jm M Ω (Δit M Ω (-(h : ℝ)) (f (-h)))‖ ^ 2) = fun h => ‖f (-h)‖ ^ 2 := by
    funext h; rw [norm_Jm_apply M Ω hs hc, norm_Δit_apply]
  rw [this]
  exact (Equiv.neg ℚ).summable_iff.mpr (summable_norm_sq f)

/-- `Ĵ` as a conjugate-linear map: `(Ĵ f)(h) = J Δ^{-ih} f(-h)`. -/
noncomputable def JhPre : L2Q K →ₛₗ[starRingEnd ℂ] L2Q K where
  toFun f := mkVec (fun h : ℚ => Jm M Ω (Δit M Ω (-(h : ℝ)) (f (-h)))) (summable_norm_sq_Jh M Ω hs hc f)
  map_add' f k := by
    apply lp.ext
    funext h
    simp only [mkVec_apply, lp.coeFn_add, Pi.add_apply, map_add]
  map_smul' c f := by
    apply lp.ext
    funext h
    simp only [mkVec_apply, lp.coeFn_smul, Pi.smul_apply, map_smul, Jm_smul]

theorem JhPre_apply (f : L2Q K) (h : ℚ) :
    JhPre M Ω hs hc f h = Jm M Ω (Δit M Ω (-(h : ℝ)) (f (-h))) := rfl

theorem norm_JhPre (f : L2Q K) : ‖JhPre M Ω hs hc f‖ = ‖f‖ := by
  have h : ‖JhPre M Ω hs hc f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [norm_sq_eq_tsum, norm_sq_eq_tsum]
    simp only [JhPre_apply, norm_Jm_apply M Ω hs hc, norm_Δit_apply]
    exact (Equiv.neg ℚ).tsum_eq fun h => ‖f h‖ ^ 2
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- **The antiunitary `Ĵ`** of the crossed product. -/
noncomputable def Jh : L2Q K →SL[starRingEnd ℂ] L2Q K :=
  (JhPre M Ω hs hc).mkContinuous 1 fun f => by rw [norm_JhPre, one_mul]

theorem Jh_apply (f : L2Q K) (h : ℚ) : Jh M Ω hs hc f h = Jm M Ω (Δit M Ω (-(h : ℝ)) (f (-h))) := rfl

theorem norm_Jh_apply (f : L2Q K) : ‖Jh M Ω hs hc f‖ = ‖f‖ := norm_JhPre M Ω hs hc f

theorem Jh_sgl (g : ℚ) (v : K) : Jh M Ω hs hc (sgl g v) = sgl (-g) (Jm M Ω (Δit M Ω g v)) := by
  apply lp.ext
  funext h
  rw [Jh_apply, sgl_apply, sgl_apply]
  by_cases hh : h = -g
  · rw [if_pos hh, if_pos (by rw [hh, neg_neg]), hh]
    simp only [Rat.cast_neg, neg_neg]
  · rw [if_neg hh, if_neg (fun h' => hh (by rw [← h', neg_neg])), map_zero, map_zero]

theorem inner_Δit_Δit (t : ℝ) (u v : K) : ⟪Δit M Ω t u, Δit M Ω t v⟫_ℂ = ⟪u, v⟫_ℂ := by
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint, Δit_star,
    ← mul_apply_eq_comp, Δit_neg_mul, one_apply_eq_self]

include hs hc in
theorem inner_Jm_Jm' (u v : K) : ⟪Jm M Ω u, Jm M Ω v⟫_ℂ = ⟪v, u⟫_ℂ := by
  rw [inner_Jm_left M Ω hs hc, Jm_Jm M Ω hs hc]

theorem inner_Jh_Jh (f k : L2Q K) : ⟪Jh M Ω hs hc f, Jh M Ω hs hc k⟫_ℂ = ⟪k, f⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  simp only [Jh_apply, inner_Jm_Jm' M Ω hs hc, inner_Δit_Δit]
  exact (Equiv.neg ℚ).tsum_eq fun h => ⟪k h, f h⟫_ℂ

theorem Jh_Jh (f : L2Q K) : Jh M Ω hs hc (Jh M Ω hs hc f) = f := by
  apply lp.ext
  funext h
  rw [Jh_apply, Jh_apply, neg_neg, ← Jm_Δit M Ω hs hc, Jm_Jm M Ω hs hc, ← mul_apply_eq_comp,
    Rat.cast_neg, neg_neg, Δit_neg_mul, one_apply_eq_self]

theorem inner_Jh_left (f k : L2Q K) : ⟪Jh M Ω hs hc f, k⟫_ℂ = ⟪Jh M Ω hs hc k, f⟫_ℂ := by
  conv_lhs => rw [← Jh_Jh M Ω hs hc k]
  rw [inner_Jh_Jh]

theorem Jh_real_smul (r : ℝ) (f : L2Q K) : Jh M Ω hs hc (r • f) = r • Jh M Ω hs hc f := by
  have e : r • f = (r : ℂ) • f := (Complex.coe_smul r f).symm
  have e' : r • Jh M Ω hs hc f = (r : ℂ) • Jh M Ω hs hc f := (Complex.coe_smul r _).symm
  rw [e, e', map_smulₛₗ, Complex.conj_ofReal]

theorem Jh_amp_R (f : L2Q K) : Jh M Ω hs hc (amp (R M Ω) f) = amp (2 - R M Ω) (Jh M Ω hs hc f) := by
  apply lp.ext
  funext h
  rw [Jh_apply, amp_apply, amp_apply, Jh_apply, ← mul_apply_eq_comp, (Δit_commute_R M Ω _).eq,
    mul_apply_eq_comp, Jm_R M Ω hs hc]

theorem Jh_amp_Tm (f : L2Q K) : Jh M Ω hs hc (amp (Tm M Ω) f) = amp (Tm M Ω) (Jh M Ω hs hc f) := by
  apply lp.ext
  funext h
  rw [Jh_apply, amp_apply, amp_apply, Jh_apply, ← mul_apply_eq_comp, (Δit_commute_Tm M Ω _).eq,
    mul_apply_eq_comp, Jm_Tm_comm M Ω hs hc]

theorem amp_R_isSelfAdjoint : IsSelfAdjoint (amp (R M Ω) : L2Q K →L[ℂ] L2Q K) := by
  show star _ = _
  rw [← amp_star, (R_isSelfAdjoint M Ω).star_eq]

theorem amp_Tm_isSelfAdjoint : IsSelfAdjoint (amp (Tm M Ω) : L2Q K →L[ℂ] L2Q K) := by
  show star _ = _
  rw [← amp_star, (Tm_isSelfAdjoint M Ω).star_eq]

theorem amp_two_sub_R_isSelfAdjoint : IsSelfAdjoint (amp (2 - R M Ω) : L2Q K →L[ℂ] L2Q K) := by
  show star _ = _
  rw [← amp_star, (two_sub_R_isSelfAdjoint M Ω).star_eq]

/-! ## The bounded identity on generators -/

include hs hc in
/-- RvD Lemma 4.5 for `(ℛ, Ω̂)` on a generator `a = λ(g) π(y)`:
`T̂ Ĵ (a Ω̂) = (2 − R̂)(a* Ω̂)`. -/
theorem Th_Jh_gen (g : ℚ) {y : K →L[ℂ] K} (hy : y ∈ M) :
    amp (Tm M Ω) (Jh M Ω hs hc ((shift g * π M Ω y : L2Q K →L[ℂ] L2Q K) (Ωh Ω))) =
      amp (2 - R M Ω) (star (shift g * π M Ω y : L2Q K →L[ℂ] L2Q K) (Ωh Ω)) := by
  rw [mul_apply_eq_comp, shift_π_Ωh, Jh_sgl, amp_sgl, star_mul, shift_star, ← π_star,
    mul_apply_eq_comp, Ωh, shift_sgl, zero_add, π_sgl, amp_sgl]
  congr 1
  rw [Jm_Δit M Ω hs hc, ← mul_apply_eq_comp, ← (Δit_commute_Tm M Ω _).eq, mul_apply_eq_comp,
    Tm_Jm_apply_mem M Ω hs hc hy, ← mul_apply_eq_comp, (Δit_commute_two_sub_R M Ω _).eq,
    mul_apply_eq_comp, Rat.cast_neg, neg_neg, σ_apply, Δit_Ω]

/-! ## The `*`-algebra spanned by the generators -/

/-- The set `{λ(g) π(y) : g ∈ ℚ, y ∈ M}`. -/
def genSet : Set (L2Q K →L[ℂ] L2Q K) := {T | ∃ g : ℚ, ∃ y ∈ M, shift g * π M Ω y = T}

include hs hc in
theorem genSet_mul {a b : L2Q K →L[ℂ] L2Q K} (ha : a ∈ genSet M Ω) (hb : b ∈ genSet M Ω) :
    a * b ∈ genSet M Ω := by
  obtain ⟨g, y, hy, rfl⟩ := ha
  obtain ⟨h, z, hz, rfl⟩ := hb
  refine ⟨g + h, σ M Ω (-(h : ℝ)) y * z, mul_mem (σ_mem M Ω hs hc hy _) hz, ?_⟩
  rw [π_mul, shift_add]
  calc shift g * shift h * (π M Ω (σ M Ω (-(h : ℝ)) y) * π M Ω z)
      = shift g * (shift h * π M Ω (σ M Ω (-(h : ℝ)) y)) * π M Ω z := by simp only [mul_assoc]
    _ = shift g * (π M Ω y * shift h) * π M Ω z := by rw [π_shift]
    _ = _ := by simp only [mul_assoc]

include hs hc in
theorem genSet_star {a : L2Q K →L[ℂ] L2Q K} (ha : a ∈ genSet M Ω) : star a ∈ genSet M Ω := by
  obtain ⟨g, y, hy, rfl⟩ := ha
  refine ⟨-g, σ M Ω (-((-g : ℚ) : ℝ)) (star y), σ_mem M Ω hs hc (star_mem hy) _, ?_⟩
  rw [star_mul, shift_star, ← π_star, ← π_shift]

theorem one_mem_genSet : (1 : L2Q K →L[ℂ] L2Q K) ∈ genSet M Ω :=
  ⟨0, 1, one_mem M, by rw [shift_zero, π_one, one_mul]⟩

include hs hc in
/-- The `*`-subalgebra spanned by the generators `λ(g) π(y)`. -/
noncomputable def spanAlg : StarSubalgebra ℂ (L2Q K →L[ℂ] L2Q K) where
  carrier := Submodule.span ℂ (genSet M Ω)
  mul_mem' := by
    intro a b ha hb
    have key : ∀ b ∈ genSet M Ω, ∀ a ∈ Submodule.span ℂ (genSet M Ω),
        a * b ∈ Submodule.span ℂ (genSet M Ω) := by
      intro b hb a ha
      refine Submodule.span_induction (p := fun a _ => a * b ∈ Submodule.span ℂ (genSet M Ω))
        ?_ ?_ ?_ ?_ ha
      · intro a ha; exact Submodule.subset_span (genSet_mul M Ω hs hc ha hb)
      · rw [zero_mul]; exact zero_mem _
      · intro x y _ _ hx hy; rw [add_mul]; exact add_mem hx hy
      · intro c x _ hx; rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx
    refine Submodule.span_induction (p := fun b _ => a * b ∈ Submodule.span ℂ (genSet M Ω))
      ?_ ?_ ?_ ?_ hb
    · intro b hb; exact key b hb a ha
    · rw [mul_zero]; exact zero_mem _
    · intro x y _ _ hx hy; rw [mul_add]; exact add_mem hx hy
    · intro c x _ hx; rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx
  one_mem' := Submodule.subset_span (one_mem_genSet M Ω)
  add_mem' := fun ha hb => add_mem ha hb
  zero_mem' := zero_mem _
  algebraMap_mem' := fun c => by
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ c (Submodule.subset_span (one_mem_genSet M Ω))
  star_mem' := by
    intro a ha
    refine Submodule.span_induction (p := fun a _ => star a ∈ Submodule.span ℂ (genSet M Ω))
      ?_ ?_ ?_ ?_ ha
    · intro a ha; exact Submodule.subset_span (genSet_star M Ω hs hc ha)
    · rw [star_zero]; exact zero_mem _
    · intro x y _ _ hx hy; rw [star_add]; exact add_mem hx hy
    · intro c x _ hx; rw [star_smul]; exact Submodule.smul_mem _ _ hx

theorem mem_spanAlg_iff {a : L2Q K →L[ℂ] L2Q K} :
    a ∈ spanAlg M Ω hs hc ↔ a ∈ Submodule.span ℂ (genSet M Ω) := Iff.rfl

theorem gens_subset_spanAlg : gens M Ω ⊆ (spanAlg M Ω hs hc : Set (L2Q K →L[ℂ] L2Q K)) := by
  rintro T (⟨y, hy, rfl⟩ | ⟨g, rfl⟩)
  · exact Submodule.subset_span ⟨0, y, hy, by rw [shift_zero, one_mul]⟩
  · exact Submodule.subset_span ⟨g, 1, one_mem M, by rw [π_one, mul_one]⟩

/-! ## The bounded identity on `ℛ` -/

include hs hc in
/-- The identity `T̂ Ĵ (aΩ̂) = (2 − R̂)(a*Ω̂)` for `a` in the spanned `*`-algebra. -/
theorem Th_Jh_spanAlg {a : L2Q K →L[ℂ] L2Q K} (ha : a ∈ spanAlg M Ω hs hc) :
    amp (Tm M Ω) (Jh M Ω hs hc (a (Ωh Ω))) =
      amp (2 - R M Ω) ((star a : L2Q K →L[ℂ] L2Q K) (Ωh Ω)) := by
  rw [mem_spanAlg_iff] at ha
  refine Submodule.span_induction (p := fun a _ =>
    amp (Tm M Ω) (Jh M Ω hs hc (a (Ωh Ω))) =
      amp (2 - R M Ω) ((star a : L2Q K →L[ℂ] L2Q K) (Ωh Ω))) ?_ ?_ ?_ ?_ ha
  · rintro _ ⟨g, y, hy, rfl⟩; exact Th_Jh_gen M Ω hs hc g hy
  · simp only [_root_.zero_apply, map_zero, star_zero]
  · intro x y _ _ hx hy
    simp only [_root_.add_apply, map_add, star_add, hx, hy]
  · intro c x _ hx
    simp only [_root_.smul_apply, map_smulₛₗ, star_smul, hx, Complex.star_def]

include hs hc in
/-- **RvD Lemma 4.5 for `(ℛ, Ω̂)`**: `T̂ Ĵ (aΩ̂) = (2 − R̂)(a*Ω̂)` for all `a ∈ ℛ`. -/
theorem Th_Jh_mem {a : L2Q K →L[ℂ] L2Q K} (ha : a ∈ crossed M Ω) :
    amp (Tm M Ω) (Jh M Ω hs hc (a (Ωh Ω))) =
      amp (2 - R M Ω) ((star a : L2Q K →L[ℂ] L2Q K) (Ωh Ω)) := by
  refine ext_inner_left ℂ fun η => ?_
  have h2R := amp_two_sub_R_isSelfAdjoint M Ω (K := K)
  -- rewrite the left side as a functional of `a*`
  have key : ∀ b : L2Q K →L[ℂ] L2Q K,
      ⟪η, amp (Tm M Ω) (Jh M Ω hs hc ((star b : L2Q K →L[ℂ] L2Q K) (Ωh Ω)))⟫_ℂ =
        ⟪Ωh Ω, b (Jh M Ω hs hc (amp (Tm M Ω) η))⟫_ℂ := by
    intro b
    rw [BorelCalc.inner_sa (amp_Tm_isSelfAdjoint M Ω), ← inner_conj_symm, inner_Jh_left M Ω hs hc,
      inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_right,
      ← ContinuousLinearMap.star_eq_adjoint, star_star]
  have hΛ : ∀ b ∈ crossed M Ω, ⟪Ωh Ω, b (Jh M Ω hs hc (amp (Tm M Ω) η))⟫_ℂ +
      ⟪-(amp (2 - R M Ω) η), b (Ωh Ω)⟫_ℂ = 0 := by
    intro b hb
    refine inner_pair_eq_zero_of_mem_wstar (spanAlg M Ω hs hc) (gens_subset_spanAlg M Ω hs hc) hb
      _ _ _ _ fun b hb => ?_
    have h1 := congrArg (fun v => ⟪η, v⟫_ℂ) (Th_Jh_spanAlg M Ω hs hc (star_mem hb))
    simp only [star_star] at h1
    rw [key b, BorelCalc.inner_sa h2R] at h1
    rw [inner_neg_left, h1, add_neg_cancel]
  have h := hΛ (star a) (star_mem ha)
  rw [inner_neg_left, add_neg_eq_zero] at h
  have k := key (star a)
  rw [star_star] at k
  rw [k, h, BorelCalc.inner_sa h2R]

/-! ## Identification of the modular data -/

include hs hc in
/-- The one-fiber lemma: if `⟪u, yΩ⟫ + ⟪Ω, y v⟫ = 0` for all `y ∈ M` then `R u + T J v = 0`. -/
theorem fiber_orth {u v : K} (h : ∀ y ∈ M, ⟪u, y Ω⟫_ℂ + ⟪Ω, y v⟫_ℂ = 0) :
    R M Ω u + Tm M Ω (Jm M Ω v) = 0 := by
  have hsa : ∀ y ∈ M, IsSelfAdjoint y → ⟪u, y Ω⟫_ℂ + ⟪y Ω, v⟫_ℂ = 0 := fun y hy hys => by
    have := h y hy
    rwa [BorelCalc.inner_sa hys Ω v] at this
  -- `u + v ⊥ 𝒦`
  have hP : Pre M Ω (u + v) = 0 := by
    rw [Pre_eq_zero_iff, Submodule.mem_orthogonal]
    intro k hk
    have hk' : k ∈ Kre M Ω := hk
    refine Kre_induction M Ω (p := fun k => inner ℝ k (u + v) = 0) ?_ ?_ ?_ ?_ ?_ hk'
    · exact isClosed_eq (by fun_prop) continuous_const
    · simp
    · intro x y hx hy
      rw [inner_add_left, hx, hy, add_zero]
    · intro c x hx
      rw [real_inner_smul_left, hx, mul_zero]
    · intro y hy hys
      have := congrArg Complex.re (hsa y hy hys)
      rw [Complex.add_re, Complex.zero_re, ← inner_conj_symm u (y Ω), Complex.conj_re] at this
      simp only [inner_real_eq_re_inner, inner_add_right]
      linarith
  -- `u − v ⊥ i𝒦`
  have hQ : Qre M Ω (u - v) = 0 := by
    rw [Qre_eq_zero_iff, Submodule.mem_orthogonal]
    intro k hk
    have hk' : k ∈ (Kre M Ω).mulI := hk
    rw [mem_mulI_Kre_iff] at hk'
    have hk'' : k = Complex.I • ((-Complex.I) • k) := by
      rw [smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]
    rw [hk'', inner_real_eq_re_inner, inner_smul_left, Complex.conj_I, neg_mul, Complex.neg_re,
      Complex.I_mul_re, neg_neg]
    refine Kre_induction M Ω (p := fun w => (⟪w, u - v⟫_ℂ).im = 0) ?_ ?_ ?_ ?_ ?_ hk'
    · exact isClosed_eq (by fun_prop) continuous_const
    · simp
    · intro x y hx hy
      rw [inner_add_left, Complex.add_im, hx, hy, add_zero]
    · intro c x hx
      rw [← Complex.coe_smul, inner_smul_left, Complex.conj_ofReal, Complex.im_ofReal_mul, hx,
        mul_zero]
    · intro y hy hys
      have := congrArg Complex.im (hsa y hy hys)
      rw [Complex.add_im, Complex.zero_im, ← inner_conj_symm u (y Ω), Complex.conj_im] at this
      simp only [inner_sub_right, Complex.sub_im]
      linarith
  have h1 := two_smul_Pre M Ω (u + v)
  have h2 := two_smul_Qre M Ω (u - v)
  rw [hP, smul_zero, map_add, map_add] at h1
  rw [hQ, smul_zero, map_sub, map_sub] at h2
  rw [Tm_Jm M Ω hs hc]
  have : (2 : ℂ) • (R M Ω u + Am M Ω v) = 0 := by
    calc (2 : ℂ) • (R M Ω u + Am M Ω v)
        = (R M Ω u + R M Ω v + (Am M Ω u + Am M Ω v)) +
          (R M Ω u - R M Ω v - (Am M Ω u - Am M Ω v)) := by rw [two_smul]; abel
      _ = 0 := by rw [← h1, ← h2, add_zero]
  exact (smul_eq_zero.mp this).resolve_left two_ne_zero

/-- The pairing identity characterising `𝒦ᗮ`: `⟪ζ, bΩ⟫ + ⟪Ω, bζ⟫ = 0` for all `b ∈ M`. -/
theorem inner_add_inner_eq_zero_of_mem_orthogonal {ζ : K}
    (hζ : ζ ∈ ((Kre M Ω).toSubmodule)ᗮ) {b : K →L[ℂ] K} (hb : b ∈ M) :
    ⟪ζ, b Ω⟫_ℂ + ⟪Ω, b ζ⟫_ℂ = 0 := by
  rw [Submodule.mem_orthogonal] at hζ
  have hre : ∀ a ∈ M, IsSelfAdjoint a → (⟪ζ, a Ω⟫_ℂ).re = 0 := by
    intro a ha has
    have := hζ (a Ω) (mem_Kre_of_sa M Ω ha has)
    rwa [inner_real_eq_re_inner, ← inner_conj_symm, Complex.conj_re] at this
  have h1 := hre (b + star b) (add_mem hb (star_mem hb)) (IsSelfAdjoint.add_star_self b)
  have h2 := hre (Complex.I • (b - star b)) (VN.smul_mem_vn M _ (sub_mem hb (star_mem hb)))
    (by
      rw [IsSelfAdjoint, star_smul, star_sub, star_star, Complex.star_def, Complex.conj_I,
        neg_smul, ← smul_neg, neg_sub])
  rw [add_apply, inner_add_right, Complex.add_re] at h1
  rw [smul_apply, inner_smul_right, Complex.I_mul_re, sub_apply, inner_sub_right, Complex.sub_im,
    neg_eq_zero, sub_eq_zero] at h2
  have h3 : ⟪Ω, b ζ⟫_ℂ = conj ⟪ζ, (star b) Ω⟫_ℂ := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
      inner_conj_symm]
  rw [h3]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.conj_re, Complex.zero_re]; linarith
  · simp only [Complex.add_im, Complex.conj_im, Complex.zero_im]; linarith

include hs hc in
/-- `hker` for `(ℛ, Ω̂)`: on `𝒦(ℛ, Ω̂)ᗮ`, `R̂ ζ + T̂ Ĵ ζ = 0`, fiberwise from `fiber_orth`. -/
theorem hker_crossed {ζ : L2Q K}
    (hζ : ζ ∈ ((Kre (crossed M Ω) (Ωh Ω)).toSubmodule)ᗮ) :
    amp (R M Ω) ζ + amp (Tm M Ω) (Jh M Ω hs hc ζ) = 0 := by
  apply lp.ext
  funext g
  rw [lp.coeFn_add, Pi.add_apply, amp_apply, amp_apply, Jh_apply, lp.coeFn_zero, Pi.zero_apply]
  refine fiber_orth M Ω hs hc fun y hy => ?_
  have := inner_add_inner_eq_zero_of_mem_orthogonal (crossed M Ω) (Ωh Ω) hζ
    (mul_mem (shift_mem M Ω g) (π_mem M Ω hy))
  rw [mul_apply_eq_comp, shift_π_Ωh, inner_sgl_right, mul_apply_eq_comp, Ωh, inner_sgl_left,
    shift_apply, π_apply, zero_sub, Rat.cast_neg, neg_neg, σ_apply,
    ← ContinuousLinearMap.adjoint_inner_left (Δit M Ω (g : ℝ)),
    ← ContinuousLinearMap.star_eq_adjoint, Δit_star, Δit_Ω] at this
  exact this

include hs hc in
/-- `hfix` for `(ℛ, Ω̂)`: on `𝒦(ℛ, Ω̂)`, `R̂ ζ + T̂ Ĵ ζ = 2ζ`, from the bounded identity. -/
theorem hfix_crossed {ζ : L2Q K} (hζ : ζ ∈ Kre (crossed M Ω) (Ωh Ω)) :
    amp (R M Ω) ζ + amp (Tm M Ω) (Jh M Ω hs hc ζ) = (2 : ℂ) • ζ := by
  refine Kre_induction (crossed M Ω) (Ωh Ω)
    (p := fun ζ => amp (R M Ω) ζ + amp (Tm M Ω) (Jh M Ω hs hc ζ) = (2 : ℂ) • ζ)
    ?_ ?_ ?_ ?_ ?_ hζ
  · exact isClosed_eq ((amp _).continuous.add
      ((amp _).continuous.comp (Jh M Ω hs hc).continuous)) (continuous_const_smul _)
  · simp
  · intro x y hx hy
    rw [map_add, map_add, map_add, smul_add, ← hx, ← hy]
    abel
  · intro c x hx
    rw [← Complex.coe_smul, map_smul, map_smulₛₗ, Complex.conj_ofReal, map_smul, ← smul_add, hx,
      smul_comm]
  · intro a ha has
    have h2 : (2 : K →L[ℂ] K) = (2 : ℂ) • 1 := by rw [two_smul, one_add_one_eq_two]
    rw [Th_Jh_mem M Ω hs hc ha, has.star_eq, ← add_apply, ← amp_add, add_sub_cancel, h2, amp_smul,
      amp_one, smul_apply, one_apply_eq_self]

include hs hc in
/-- **(M4), the operator `R̂`**: `R(ℛ, Ω̂) = 1 ⊗ R`. -/
theorem R_crossed : R (crossed M Ω) (Ωh Ω) = amp (R M Ω) :=
  ((R_eq_of_proj (crossed M Ω) (Ωh Ω) (amp (R M Ω))
    ((amp (Tm M Ω)).comp (Jh M Ω hs hc)) (fun _ hζ => hfix_crossed M Ω hs hc hζ)
    (fun _ hζ => hker_crossed M Ω hs hc hζ)).1).symm

include hs hc in
theorem Am_crossed (ζ : L2Q K) :
    Am (crossed M Ω) (Ωh Ω) ζ = amp (Tm M Ω) (Jh M Ω hs hc ζ) :=
  ((R_eq_of_proj (crossed M Ω) (Ωh Ω) (amp (R M Ω))
    ((amp (Tm M Ω)).comp (Jh M Ω hs hc)) (fun _ hζ => hfix_crossed M Ω hs hc hζ)
    (fun _ hζ => hker_crossed M Ω hs hc hζ)).2 ζ).symm

include hs hc in
/-- **(M4), `T̂`**: `T(ℛ, Ω̂) = 1 ⊗ T`. -/
theorem Tm_crossed : Tm (crossed M Ω) (Ωh Ω) = amp (Tm M Ω) := by
  unfold Tm
  rw [R_crossed M Ω hs hc, amp_cfc (R_isSelfAdjoint M Ω) continuous_gT]
  rfl

include hs hc in
/-- **(M4), `Ĵ`**: the antiunitary of `(ℛ, Ω̂)` is `Ĵ`. -/
theorem Jm_crossed (ζ : L2Q K) : Jm (crossed M Ω) (Ωh Ω) ζ = Jh M Ω hs hc ζ := by
  refine (Jm_eq_of_proj (crossed M Ω) (Ωh Ω) (isSeparating_Ωh M Ω hs hc) (isCyclic_Ωh M Ω hc)
    (Jh M Ω hs hc) ?_ ?_ ζ).symm
  · intro ξ hξ
    rw [R_crossed M Ω hs hc, Tm_crossed M Ω hs hc]
    exact hfix_crossed M Ω hs hc hξ
  · intro ξ hξ
    rw [R_crossed M Ω hs hc, Tm_crossed M Ω hs hc]
    exact hker_crossed M Ω hs hc hξ

include hs hc in
/-- **(M4), the modular group**: `Δ̂^{it} = 1 ⊗ Δ^{it}`. -/
theorem Δit_crossed (t : ℝ) : Δit (crossed M Ω) (Ωh Ω) t = amp (Δit M Ω t) := by
  unfold Δit
  rw [BorelCalc.cbfc_congr_op (R_crossed M Ω hs hc) _ (amp_isSelfAdjoint (R_isSelfAdjoint M Ω)),
    amp_cbfc (R_isSelfAdjoint M Ω) (cbdd_gDel t)]

/-! ## The dual action -/

include hs hc in
theorem σ_crossed (t : ℝ) (x : L2Q K →L[ℂ] L2Q K) :
    σ (crossed M Ω) (Ωh Ω) t x = amp (Δit M Ω t) * x * amp (Δit M Ω (-t)) := by
  unfold σ
  rw [Δit_crossed M Ω hs hc, Δit_crossed M Ω hs hc]

theorem amp_mul_diag {x : ℚ → K →L[ℂ] K} (hx : IsBddFam x) (y : K →L[ℂ] K) :
    amp y * diag x = diag fun s => y * x s :=
  (diag_mul (IsBddFam.const y) hx).symm

theorem diag_mul_amp {x : ℚ → K →L[ℂ] K} (hx : IsBddFam x) (y : K →L[ℂ] K) :
    diag x * amp y = diag fun s => x s * y :=
  (diag_mul hx (IsBddFam.const y)).symm

include hs hc in
/-- `σ̂_t(π(y)) = π(σ_t y)`. -/
theorem σ_crossed_π (t : ℝ) (y : K →L[ℂ] K) :
    σ (crossed M Ω) (Ωh Ω) t (π M Ω y) = π M Ω (σ M Ω t y) := by
  rw [σ_crossed M Ω hs hc]
  unfold π
  rw [amp_mul_diag (isBddFam_π M Ω y), diag_mul_amp ((IsBddFam.const _).mul (isBddFam_π M Ω y))]
  congr 1
  funext s
  show σ M Ω t (σ M Ω (-(s : ℝ)) y) = σ M Ω (-(s : ℝ)) (σ M Ω t y)
  rw [← σ_add, add_comm, σ_add]

include hs hc in
/-- `σ̂_t(λ(g)) = λ(g)`. -/
theorem σ_crossed_shift (t : ℝ) (g : ℚ) :
    σ (crossed M Ω) (Ωh Ω) t (shift g) = shift g := by
  rw [σ_crossed M Ω hs hc, ← shift_amp, mul_assoc, ← amp_mul, Δit_mul_neg, amp_one, mul_one]

include hs hc in
theorem Δit_crossed_commute_shift (t : ℝ) (g : ℚ) :
    Commute (Δit (crossed M Ω) (Ωh Ω) t) (shift g) :=
  (σ_eq_self_iff _ _ t _).mp (σ_crossed_shift M Ω hs hc t g)

include hs hc in
theorem shift_commute_R (g : ℚ) : Commute (shift g) (R (crossed M Ω) (Ωh Ω)) := by
  rw [R_crossed M Ω hs hc]
  exact shift_amp g _

theorem inner_amp_Δit_conj (t : ℝ) (a : L2Q K →L[ℂ] L2Q K) (u v : L2Q K) :
    ⟪u, (amp (Δit M Ω t) * a * amp (Δit M Ω (-t))) v⟫_ℂ =
      ⟪amp (Δit M Ω (-t)) u, a (amp (Δit M Ω (-t)) v)⟫_ℂ := by
  rw [mul_apply_eq_comp, mul_apply_eq_comp, ← ContinuousLinearMap.adjoint_inner_right,
    ← ContinuousLinearMap.star_eq_adjoint, ← amp_star, Δit_star, neg_neg]

theorem inner_shift_conj (g : ℚ) (a : L2Q K →L[ℂ] L2Q K) (u v : L2Q K) :
    ⟪u, (shift g * a * shift (-g) : L2Q K →L[ℂ] L2Q K) v⟫_ℂ =
      ⟪shift (-g) u, a (shift (-g) v)⟫_ℂ := by
  rw [mul_apply_eq_comp, mul_apply_eq_comp, ← ContinuousLinearMap.adjoint_inner_right,
    ← ContinuousLinearMap.star_eq_adjoint, shift_star, neg_neg]

include hs hc in
/-- On the spanned `*`-algebra, `σ̂_s = Ad λ(s)` for `s ∈ ℚ`. -/
theorem σ_crossed_rat_spanAlg (s : ℚ) {a : L2Q K →L[ℂ] L2Q K} (ha : a ∈ spanAlg M Ω hs hc) :
    σ (crossed M Ω) (Ωh Ω) (s : ℝ) a = shift s * a * shift (-s) := by
  rw [mem_spanAlg_iff] at ha
  refine Submodule.span_induction
    (p := fun a _ => σ (crossed M Ω) (Ωh Ω) (s : ℝ) a = shift s * a * shift (-s)) ?_ ?_ ?_ ?_ ha
  · rintro _ ⟨g, y, _, rfl⟩
    rw [σ_mul, σ_crossed_shift M Ω hs hc, σ_crossed_π M Ω hs hc, ← shift_π_shift]
    simp only [← mul_assoc]
    rw [shift_comm g s]
  · simp only [σ, mul_zero, zero_mul]
  · intro x y _ _ hx hy
    rw [σ_add_op, hx, hy, mul_add, add_mul]
  · intro c x _ hx
    rw [σ_smul, hx, mul_smul_comm, smul_mul_assoc]

include hs hc in
/-- **The dual action is inner on the rationals**: `σ̂_s(x) = λ(s) x λ(s)*` for `s ∈ ℚ`, `x ∈ ℛ`. -/
theorem σ_crossed_rat (s : ℚ) {x : L2Q K →L[ℂ] L2Q K} (hx : x ∈ crossed M Ω) :
    σ (crossed M Ω) (Ωh Ω) (s : ℝ) x = shift s * x * shift (-s) := by
  refine BorelCalc.ext_of_inner fun u v => ?_
  rw [σ_crossed M Ω hs hc, inner_amp_Δit_conj, inner_shift_conj]
  have := inner_pair_eq_zero_of_mem_wstar (spanAlg M Ω hs hc) (gens_subset_spanAlg M Ω hs hc) hx
    (amp (Δit M Ω (-(s : ℝ))) u) (-(shift (-s) u)) (amp (Δit M Ω (-(s : ℝ))) v) (shift (-s) v)
    fun a ha => by
      rw [inner_neg_left, ← inner_amp_Δit_conj, ← inner_shift_conj, ← σ_crossed M Ω hs hc,
        σ_crossed_rat_spanAlg M Ω hs hc s ha, add_neg_cancel]
  rwa [inner_neg_left, add_neg_eq_zero] at this

end Crossed

end VN

end CommutingRepetition
