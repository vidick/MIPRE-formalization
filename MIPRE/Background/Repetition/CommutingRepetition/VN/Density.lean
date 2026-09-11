/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/Density.lean
-/
/-
# The von Neumann density theorem for vector functionals (density stage E5)

For a star-closed set `S ⊆ B(H)`, a `*`-subalgebra `𝔄 ⊇ S` and `x ∈ W*(S) = S″`: a
functional of the form `a ↦ ⟪U, (a ⊗ 1) V⟫` on `ℓ²(ℕ, H)` (i.e. a countable sum of vector
functionals `∑ ⟪u_k, a v_k⟫`) that vanishes on `𝔄` vanishes at `x`. Proof: the projection
`p` onto `[(𝔄 ⊗ 1) V]` commutes with `𝔄 ⊗ 1`, so its matrix entries lie in `S′` and `p`
commutes with `x ⊗ 1`; hence `(x ⊗ 1) V ∈ [(𝔄 ⊗ 1) V] ⊥ U`.

This is the only form of the bicommutant theorem the density programme needs: it lets
identities proved for the generators `λ(g) π(y)` of a crossed product pass to the whole
algebra (E5.3).
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.Amplification
import MIPRE.Background.Repetition.CommutingRepetition.VN.Generated

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace VN

open scoped InnerProductSpace
open Filter Topology

set_option linter.unusedSectionVars false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## Star projections and invariant subspaces -/

/-- A star projection commutes with every operator that, together with its adjoint, leaves
its range invariant. -/
theorem commute_of_range_invariant {e y : H →L[ℂ] H} (he : IsStarProjection e)
    (h : ∀ v, e (y (e v)) = y (e v)) (h' : ∀ v, e (star y (e v)) = star y (e v)) :
    Commute e y := by
  have h1 : e * y * e = y * e := by ext v; simpa only [mul_apply_eq_comp] using h v
  have h2 : e * star y * e = star y * e := by ext v; simpa only [mul_apply_eq_comp] using h' v
  have h3 : e * y * e = e * y := by
    have := congrArg star h2
    rw [star_mul, star_mul, star_star, he.isSelfAdjoint.star_eq, star_mul, star_star,
      he.isSelfAdjoint.star_eq] at this
    rw [mul_assoc]
    exact this
  rw [Commute, SemiconjBy, ← h3, h1]

/-! ## Matrix entries on `ℓ²(ℕ, H)` -/

/-- The `(j, k)` matrix entry of an operator on `ℓ²(ℕ, H)`. -/
noncomputable def entry (T : Hinf H →L[ℂ] Hinf H) (j k : ℕ) : H →L[ℂ] H := ev j ∘L T ∘L sgl k

theorem entry_apply (T : Hinf H →L[ℂ] Hinf H) (j k : ℕ) (v : H) :
    entry T j k v = T (sgl k v) j := rfl

theorem commute_entry_of_commute {T : Hinf H →L[ℂ] Hinf H} {x : H →L[ℂ] H}
    (h : Commute T (ampl x)) (j k : ℕ) : Commute (entry T j k) x := by
  rw [Commute, SemiconjBy]
  ext v
  simp only [mul_apply_eq_comp, entry_apply]
  rw [← ampl_sgl, ← mul_apply_eq_comp, h.eq, mul_apply_eq_comp, ampl_apply]

theorem commute_ampl_of_entries {T : Hinf H →L[ℂ] Hinf H} {x : H →L[ℂ] H}
    (h : ∀ j k, Commute (entry T j k) x) : Commute T (ampl x) := by
  rw [Commute, SemiconjBy]
  refine ContinuousLinearMap.ext fun f => ?_
  simp only [mul_apply_eq_comp]
  have h1 : HasSum (fun k => T (sgl k (x (f k)))) (T (ampl x f)) := by
    have := hasSum_sgl (ampl x f)
    simp only [ampl_apply] at this
    exact T.hasSum this
  have h2 : HasSum (fun k => ampl x (T (sgl k (f k)))) (ampl x (T f)) :=
    (ampl x ∘L T).hasSum (hasSum_sgl f)
  have h3 : ∀ k, T (sgl k (x (f k))) = ampl x (T (sgl k (f k))) := by
    intro k
    apply lp.ext
    funext j
    have := congrArg (fun S : H →L[ℂ] H => S (f k)) (h j k).eq
    simp only [mul_apply_eq_comp, entry_apply] at this
    rw [ampl_apply]
    exact this
  have h2' : HasSum (fun k => T (sgl k (x (f k)))) (ampl x (T f)) := by
    simpa only [h3] using h2
  exact h1.unique h2'

/-! ## The density theorem -/

/-- **von Neumann density for vector functionals.** If `S ⊆ 𝔄` with `𝔄` a `*`-subalgebra,
`x ∈ W*(S)` and `⟪U, (a ⊗ 1) V⟫ = 0` for all `a ∈ 𝔄`, then `⟪U, (x ⊗ 1) V⟫ = 0`. -/
theorem inner_ampl_eq_zero_of_mem_wstar {S : Set (H →L[ℂ] H)} (𝔄 : StarSubalgebra ℂ (H →L[ℂ] H))
    (hS : S ⊆ 𝔄) {x : H →L[ℂ] H} (hx : x ∈ wstar S) (U V : Hinf H)
    (h : ∀ a ∈ 𝔄, ⟪U, ampl a V⟫_ℂ = 0) : ⟪U, ampl x V⟫_ℂ = 0 := by
  classical
  -- the closed subspace `W = [(𝔄 ⊗ 1) V]`
  set S₀ : Set (Hinf H) := {w | ∃ a ∈ 𝔄, ampl a V = w} with hS₀
  set W : Submodule ℂ (Hinf H) := (Submodule.span ℂ S₀).topologicalClosure with hW
  have hWc : (W : Set (Hinf H)) = closure (Submodule.span ℂ S₀ : Set (Hinf H)) :=
    Submodule.topologicalClosure_coe _
  -- invariance of `W` under `𝔄 ⊗ 1`
  have hinv : ∀ a ∈ 𝔄, ∀ w ∈ W, ampl a w ∈ W := by
    intro a ha w hw
    have hspan : ∀ w ∈ Submodule.span ℂ S₀, ampl a w ∈ Submodule.span ℂ S₀ := by
      intro w hw
      refine Submodule.span_induction (p := fun w _ => ampl a w ∈ Submodule.span ℂ S₀) ?_ ?_ ?_ ?_ hw
      · rintro _ ⟨b, hb, rfl⟩
        have hmem : ampl a (ampl b V) ∈ S₀ := by
          rw [hS₀, Set.mem_ofPred_eq]
          exact ⟨a * b, mul_mem ha hb, by rw [ampl_mul, mul_apply_eq_comp]⟩
        exact Submodule.subset_span hmem
      · rw [map_zero]; exact zero_mem _
      · intro u v _ _ hu hv; rw [map_add]; exact add_mem hu hv
      · intro c u _ hu; rw [map_smul]; exact Submodule.smul_mem _ c hu
    have hw' : w ∈ closure (Submodule.span ℂ S₀ : Set (Hinf H)) := by rw [← hWc]; exact hw
    show ampl a w ∈ (W : Set (Hinf H))
    rw [hWc]
    have himg : ampl a '' (Submodule.span ℂ S₀ : Set (Hinf H)) ⊆
        (Submodule.span ℂ S₀ : Set (Hinf H)) := by
      rintro _ ⟨u, hu, rfl⟩; exact hspan u hu
    exact closure_mono himg (image_closure_subset_closure_image (ampl a).continuous ⟨w, hw', rfl⟩)
  set p : Hinf H →L[ℂ] Hinf H := W.starProjection with hp
  have hpW : ∀ v, p v ∈ W := fun v => Submodule.starProjection_apply_mem W v
  have hpfix : ∀ v ∈ W, p v = v := fun v hv => Submodule.starProjection_eq_self_iff.mpr hv
  -- `p` commutes with `𝔄 ⊗ 1`
  have hcomm : ∀ a ∈ 𝔄, Commute p (ampl a) := by
    intro a ha
    refine commute_of_range_invariant isStarProjection_starProjection (fun v => ?_) (fun v => ?_)
    · exact hpfix _ (hinv a ha _ (hpW v))
    · rw [← ampl_star]
      exact hpfix _ (hinv (star a) (star_mem ha) _ (hpW v))
  -- hence its entries lie in the centralizer of `S`, so `p` commutes with `x ⊗ 1`
  have hpx : Commute p (ampl x) := by
    refine commute_ampl_of_entries fun j k => ?_
    have hcent : entry p j k ∈ StarSubalgebra.centralizer ℂ S := by
      rw [StarSubalgebra.mem_centralizer_iff]
      intro s hs
      exact ⟨(commute_entry_of_commute (hcomm s (hS hs)) j k).eq.symm,
        (commute_entry_of_commute (hcomm (star s) (star_mem (hS hs))) j k).eq.symm⟩
    exact mem_wstar_iff.mp hx _ hcent
  -- `V ∈ W`, so `(x ⊗ 1) V ∈ W`
  have hV : V ∈ W := by
    show V ∈ (W : Set (Hinf H))
    rw [hWc]
    have hVS : V ∈ S₀ := by
      rw [hS₀, Set.mem_ofPred_eq]
      exact ⟨1, one_mem 𝔄, by rw [ampl_one, one_apply_eq_self]⟩
    exact subset_closure (Submodule.subset_span hVS)
  have hxV : ampl x V ∈ W := by
    have := congrArg (fun S : Hinf H →L[ℂ] Hinf H => S V) hpx.eq
    simp only [mul_apply_eq_comp, hpfix V hV] at this
    rw [← this]; exact hpW _
  -- `U ⊥ W`
  have hU : ∀ w ∈ W, ⟪U, w⟫_ℂ = 0 := by
    intro w hw
    have hspan : ∀ w ∈ Submodule.span ℂ S₀, ⟪U, w⟫_ℂ = 0 := by
      intro w hw
      refine Submodule.span_induction (p := fun w _ => ⟪U, w⟫_ℂ = 0) ?_ ?_ ?_ ?_ hw
      · rintro _ ⟨a, ha, rfl⟩; exact h a ha
      · exact inner_zero_right _
      · intro u v _ _ hu hv; rw [inner_add_right, hu, hv, add_zero]
      · intro c u _ hu; rw [inner_smul_right, hu, mul_zero]
    have hw' : w ∈ closure (Submodule.span ℂ S₀ : Set (Hinf H)) := by rw [← hWc]; exact hw
    have hcl : IsClosed {w : Hinf H | ⟪U, w⟫_ℂ = 0} :=
      isClosed_eq (continuous_const.inner continuous_id) continuous_const
    exact hcl.closure_subset_iff.mpr hspan hw'
  exact hU _ hxV

/-! ## Two-vector form -/

theorem inner_sgl_sgl_nat (j k : ℕ) (u v : H) :
    ⟪sgl j u, sgl k v⟫_ℂ = if j = k then ⟪u, v⟫_ℂ else 0 := by
  rw [lp.inner_eq_tsum]
  have : (fun i => ⟪sgl j u i, sgl k v i⟫_ℂ) = fun i => if i = j then ⟪u, sgl k v j⟫_ℂ else 0 := by
    funext i
    by_cases hi : i = j
    · subst hi; rw [if_pos rfl, sgl_apply_self]
    · rw [if_neg hi, sgl_apply_ne j u hi, inner_zero_left]
  rw [this, tsum_ite_eq]
  by_cases hjk : j = k
  · subst hjk; rw [if_pos rfl, sgl_apply_self]
  · rw [if_neg hjk, sgl_apply_ne k v hjk, inner_zero_right]

theorem inner_pair_ampl (a : H →L[ℂ] H) (u₁ u₂ v₁ v₂ : H) :
    ⟪sgl 0 u₁ + sgl 1 u₂, ampl a (sgl 0 v₁ + sgl 1 v₂)⟫_ℂ = ⟪u₁, a v₁⟫_ℂ + ⟪u₂, a v₂⟫_ℂ := by
  rw [map_add, ampl_sgl, ampl_sgl, inner_add_left, inner_add_right, inner_add_right,
    inner_sgl_sgl_nat, inner_sgl_sgl_nat, inner_sgl_sgl_nat, inner_sgl_sgl_nat]
  simp

/-- **Density for a pair of vector functionals**: if `⟪u₁, a v₁⟫ + ⟪u₂, a v₂⟫ = 0` for all
`a ∈ 𝔄` then also for `x ∈ W*(S)`. -/
theorem inner_pair_eq_zero_of_mem_wstar {S : Set (H →L[ℂ] H)} (𝔄 : StarSubalgebra ℂ (H →L[ℂ] H))
    (hS : S ⊆ 𝔄) {x : H →L[ℂ] H} (hx : x ∈ wstar S) (u₁ u₂ v₁ v₂ : H)
    (h : ∀ a ∈ 𝔄, ⟪u₁, a v₁⟫_ℂ + ⟪u₂, a v₂⟫_ℂ = 0) : ⟪u₁, x v₁⟫_ℂ + ⟪u₂, x v₂⟫_ℂ = 0 := by
  rw [← inner_pair_ampl]
  exact inner_ampl_eq_zero_of_mem_wstar 𝔄 hS hx _ _ fun a ha => by
    rw [inner_pair_ampl]; exact h a ha

/-- **Density for one vector functional.** -/
theorem inner_eq_zero_of_mem_wstar {S : Set (H →L[ℂ] H)} (𝔄 : StarSubalgebra ℂ (H →L[ℂ] H))
    (hS : S ⊆ 𝔄) {x : H →L[ℂ] H} (hx : x ∈ wstar S) (u v : H)
    (h : ∀ a ∈ 𝔄, ⟪u, a v⟫_ℂ = 0) : ⟪u, x v⟫_ℂ = 0 := by
  have := inner_pair_eq_zero_of_mem_wstar 𝔄 hS hx u 0 v 0 fun a ha => by
    rw [h a ha, inner_zero_left, add_zero]
  rwa [inner_zero_left, add_zero] at this

end VN

end CommutingRepetition
