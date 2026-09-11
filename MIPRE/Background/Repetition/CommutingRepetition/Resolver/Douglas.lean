/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Resolver/Douglas.lean
-/
/-
# The Douglas factorization with commutation transport (node 1.2.6.4)

For operators `c` and a finite family `x k` on a Hilbert space with
`∑ₖ xₖ* xₖ ≤ c* c`, there are operators `z k` with

* `z k * c = x k`,
* `∑ₖ (z k)* (z k) ≤ 1`,
* `z k` commutes with every operator `R` such that `R`, `R*` commute with `c`
  and `R` commutes with each `x k`.

Construction: on `range c` set `z (c η) := x η` (well defined and
contractive since `‖x η‖ ≤ ‖c η‖`), extend to the closure `K` of `range c`
by continuity, and compose with the orthogonal projection onto `K`. The
commutation transport is what puts `z k` into the block von Neumann algebra
of `VN/BlockOperators.lean` (entries commuting with the right action), so
no strong-operator limits are needed.

With equality `∑ₖ xₖ* xₖ = c* c`, `c* (1 − ∑ₖ zₖ* zₖ) c = 0`, which gives the
manuscript's singular-safe POVMs `𝖠ᵃ = ∑_{k ∈ a} zₖ* zₖ + [a = a₀](1 − Z)`
(04_resolver_corner.tex, eqs alice-corner-povm / bob-corner-povm), with
`c* 𝖠ᵃ c = ∑_{k ∈ a} xₖ* xₖ`. Nothing here is a manuscript statement.
-/
import Mathlib

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace Resolver

namespace Douglas

open scoped BigOperators InnerProductSpace

set_option linter.unusedSectionVars false

variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [CompleteSpace 𝓗]

/-! ## Inner-product facts -/

theorem mulA (f g : 𝓗 →L[ℂ] 𝓗) (ξ : 𝓗) : (f * g) ξ = f (g ξ) := rfl

theorem oneA (ξ : 𝓗) : (1 : 𝓗 →L[ℂ] 𝓗) ξ = ξ := rfl

theorem re_inner_star_mul (T : 𝓗 →L[ℂ] 𝓗) (η : 𝓗) :
    (⟪η, (star T * T) η⟫_ℂ).re = ‖T η‖ ^ 2 := by
  rw [mulA, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right T η (T η),
    ← RCLike.re_to_complex]
  exact inner_self_eq_norm_sq (T η)

/-- Positivity of a self-adjoint operator from its quadratic form. -/
theorem nonneg_of_re_inner {T : 𝓗 →L[ℂ] 𝓗} (hT : IsSelfAdjoint T)
    (h : ∀ ξ, 0 ≤ (⟪T ξ, ξ⟫_ℂ).re) : 0 ≤ T := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_def']
  exact ⟨hT, fun ξ => h ξ⟩

theorem re_inner_nonneg_of_nonneg {T : 𝓗 →L[ℂ] 𝓗} (hT : 0 ≤ T) (ξ : 𝓗) :
    0 ≤ (⟪ξ, T ξ⟫_ℂ).re := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive] at hT
  exact hT.re_inner_nonneg_right ξ

/-- `‖x η‖ ≤ ‖c η‖` when `x* x ≤ c* c`. -/
theorem norm_apply_le_of_le {x c : 𝓗 →L[ℂ] 𝓗} (h : star x * x ≤ star c * c) (η : 𝓗) :
    ‖x η‖ ≤ ‖c η‖ := by
  have h1 := re_inner_nonneg_of_nonneg (sub_nonneg.mpr h) η
  rw [sub_apply, inner_sub_right, Complex.sub_re, re_inner_star_mul, re_inner_star_mul] at h1
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp (by linarith)

variable {κ : Type*} [Fintype κ]

theorem sum_sq_norm_apply_le {x : κ → 𝓗 →L[ℂ] 𝓗} {c : 𝓗 →L[ℂ] 𝓗}
    (h : ∑ k, star (x k) * x k ≤ star c * c) (η : 𝓗) :
    ∑ k, ‖x k η‖ ^ 2 ≤ ‖c η‖ ^ 2 := by
  have h1 := re_inner_nonneg_of_nonneg (sub_nonneg.mpr h) η
  rw [sub_apply, inner_sub_right, Complex.sub_re, re_inner_star_mul, sum_apply, inner_sum,
    Complex.re_sum] at h1
  simp only [re_inner_star_mul] at h1
  linarith

theorem le_of_sum_le {x : κ → 𝓗 →L[ℂ] 𝓗} {c : 𝓗 →L[ℂ] 𝓗}
    (h : ∑ k, star (x k) * x k ≤ star c * c) (k : κ) : star (x k) * x k ≤ star c * c := by
  refine le_trans ?_ h
  exact Finset.single_le_sum (fun j _ => star_mul_self_nonneg (x j)) (Finset.mem_univ k)

/-! ## The construction -/

variable (c : 𝓗 →L[ℂ] 𝓗)

/-- The closure of the range of `c`. -/
noncomputable def K : Submodule ℂ 𝓗 := (LinearMap.range (c : 𝓗 →ₗ[ℂ] 𝓗)).topologicalClosure

theorem range_le_K : LinearMap.range (c : 𝓗 →ₗ[ℂ] 𝓗) ≤ K c := Submodule.le_topologicalClosure _

instance : (K c).HasOrthogonalProjection := by
  unfold K; infer_instance

theorem apply_mem_K (η : 𝓗) : c η ∈ K c := range_le_K c (LinearMap.mem_range_self (c : 𝓗 →ₗ[ℂ] 𝓗) η)

/-- The inclusion `range c → K`. -/
noncomputable def incl : ↥(LinearMap.range (c : 𝓗 →ₗ[ℂ] 𝓗)) →L[ℂ] ↥(K c) :=
  LinearMap.mkContinuous (Submodule.inclusion (range_le_K c)) 1 fun v => by
    simp

theorem incl_apply (v : ↥(LinearMap.range (c : 𝓗 →ₗ[ℂ] 𝓗))) : ((incl c v : ↥(K c)) : 𝓗) = v := rfl

theorem denseRange_incl : DenseRange (incl c) := by
  rw [denseRange_iff_closure_range, Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
  have h : Subtype.val '' Set.range (incl c) = (LinearMap.range (c : 𝓗 →ₗ[ℂ] 𝓗) : Set 𝓗) := by
    ext w
    constructor
    · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
      exact v.2
    · intro hw
      exact ⟨incl c ⟨w, hw⟩, ⟨⟨w, hw⟩, rfl⟩, rfl⟩
  rw [h]
  ext w
  simp only [Set.mem_preimage, Set.mem_univ, iff_true]
  have : (w : 𝓗) ∈ closure (LinearMap.range (c : 𝓗 →ₗ[ℂ] 𝓗) : Set 𝓗) := by
    rw [← Submodule.topologicalClosure_coe]; exact w.2
  exact this

theorem isUniformInducing_incl : IsUniformInducing (incl c) :=
  ((AddMonoidHomClass.isometry_iff_norm _).mpr fun _ => rfl).isUniformInducing

/-- A preimage under `c` of a range element. -/
noncomputable def rep (v : ↥(LinearMap.range (c : 𝓗 →ₗ[ℂ] 𝓗))) : 𝓗 := (LinearMap.mem_range.mp v.2).choose

theorem c_rep (v : ↥(LinearMap.range (c : 𝓗 →ₗ[ℂ] 𝓗))) : c (rep c v) = v :=
  (LinearMap.mem_range.mp v.2).choose_spec

/-! ## Invariance of `K` under commuting operators -/

variable {R : 𝓗 →L[ℂ] 𝓗}

theorem K_invariant (hRc : R * c = c * R) {w : 𝓗} (hw : w ∈ K c) : R w ∈ K c := by
  have hcl : IsClosed {w : 𝓗 | R w ∈ K c} :=
    (Submodule.isClosed_topologicalClosure _).preimage R.continuous
  have hsub : (LinearMap.range (c : 𝓗 →ₗ[ℂ] 𝓗) : Set 𝓗) ⊆ {w : 𝓗 | R w ∈ K c} := by
    rintro _ ⟨η, rfl⟩
    show R (c η) ∈ K c
    rw [← mulA, hRc, mulA]
    exact apply_mem_K c _
  have : (w : 𝓗) ∈ closure (LinearMap.range (c : 𝓗 →ₗ[ℂ] 𝓗) : Set 𝓗) := by
    rw [← Submodule.topologicalClosure_coe]; exact hw
  exact closure_minimal hsub hcl this

theorem K_invariant_star (hRc' : star R * c = c * star R) {w : 𝓗} (hw : w ∈ K c) :
    star R w ∈ K c := by
  have hcl : IsClosed {w : 𝓗 | star R w ∈ K c} :=
    (Submodule.isClosed_topologicalClosure _).preimage (star R).continuous
  have hsub : (LinearMap.range (c : 𝓗 →ₗ[ℂ] 𝓗) : Set 𝓗) ⊆ {w : 𝓗 | star R w ∈ K c} := by
    rintro _ ⟨η, rfl⟩
    show star R (c η) ∈ K c
    rw [← mulA, hRc', mulA]
    exact apply_mem_K c _
  have : (w : 𝓗) ∈ closure (LinearMap.range (c : 𝓗 →ₗ[ℂ] 𝓗) : Set 𝓗) := by
    rw [← Submodule.topologicalClosure_coe]; exact hw
  exact closure_minimal hsub hcl this

theorem Kperp_invariant (hRc' : star R * c = c * star R) {ζ : 𝓗} (hζ : ζ ∈ (K c)ᗮ) :
    R ζ ∈ (K c)ᗮ := by
  rw [Submodule.mem_orthogonal] at hζ ⊢
  intro u hu
  rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint]
  exact hζ _ (K_invariant_star c hRc' hu)


section Factor

variable {c}
variable {x : κ → 𝓗 →L[ℂ] 𝓗} (hx : ∑ k, star (x k) * x k ≤ star c * c)
include hx

theorem welldef (k : κ) {η η' : 𝓗} (h : c η = c η') : x k η = x k η' := by
  have h1 := norm_apply_le_of_le (le_of_sum_le hx k) (η - η')
  rw [map_sub, map_sub, h, sub_self, norm_zero] at h1
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h1)

/-- `z` on `range c`: `c η ↦ x k η`. -/
noncomputable def z₀ (k : κ) : ↥(LinearMap.range (c : 𝓗 →ₗ[ℂ] 𝓗)) →L[ℂ] 𝓗 :=
  LinearMap.mkContinuous
    { toFun := fun v => x k (rep c v)
      map_add' := fun v w => by
        rw [← map_add]
        refine welldef hx k ?_
        rw [c_rep, map_add, c_rep, c_rep]; rfl
      map_smul' := fun a v => by
        simp only [RingHom.id_apply]
        rw [← map_smul]
        refine welldef hx k ?_
        rw [c_rep, map_smul, c_rep]; rfl } 1 fun v => by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
    calc ‖x k (rep c v)‖ ≤ ‖c (rep c v)‖ := norm_apply_le_of_le (le_of_sum_le hx k) _
      _ = ‖v‖ := by rw [c_rep]; rfl

theorem z₀_apply (k : κ) (v : ↥(LinearMap.range (c : 𝓗 →ₗ[ℂ] 𝓗))) : z₀ hx k v = x k (rep c v) := rfl

theorem z₀_apply_c (k : κ) (η : 𝓗) : z₀ hx k ⟨c η, LinearMap.mem_range_self (c : 𝓗 →ₗ[ℂ] 𝓗) η⟩ = x k η := by
  rw [z₀_apply]
  exact welldef hx k (c_rep c _)

/-- `z` on `K`, by continuous extension. -/
noncomputable def zK (k : κ) : ↥(K c) →L[ℂ] 𝓗 := (z₀ hx k).extend (incl c)

theorem zK_incl (k : κ) (v : ↥(LinearMap.range (c : 𝓗 →ₗ[ℂ] 𝓗))) : zK hx k (incl c v) = z₀ hx k v :=
  ContinuousLinearMap.extend_eq _ (denseRange_incl c) (isUniformInducing_incl c) v

/-- The Douglas factor `z k := zK k ∘ P_K`. -/
noncomputable def z (k : κ) : 𝓗 →L[ℂ] 𝓗 := zK hx k ∘L (K c).orthogonalProjectionOnto

theorem z_apply_mem (k : κ) {w : 𝓗} (hw : w ∈ K c) : z hx k w = zK hx k ⟨w, hw⟩ := by
  unfold z
  rw [ContinuousLinearMap.comp_apply]
  congr 1
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := K c) ⟨w, hw⟩

theorem z_apply_c (k : κ) (η : 𝓗) : z hx k (c η) = x k η := by
  rw [z_apply_mem hx k (apply_mem_K c η)]
  have : (⟨c η, apply_mem_K c η⟩ : ↥(K c)) = incl c ⟨c η, LinearMap.mem_range_self (c : 𝓗 →ₗ[ℂ] 𝓗) η⟩ := rfl
  rw [this, zK_incl, z₀_apply_c]

/-- `z k * c = x k`. -/
theorem z_mul_c (k : κ) : z hx k * c = x k := by
  ext η
  exact z_apply_c hx k η

theorem z_apply_orthogonal (k : κ) {ζ : 𝓗} (hζ : ζ ∈ (K c)ᗮ) : z hx k ζ = 0 := by
  unfold z
  rw [ContinuousLinearMap.comp_apply, Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr hζ, map_zero]

/-- The quadratic bound on `K`, by density. -/
theorem sum_sq_norm_zK_le (w : ↥(K c)) : ∑ k, ‖zK hx k w‖ ^ 2 ≤ ‖w‖ ^ 2 := by
  refine (denseRange_incl c).induction_on w ?_ fun v => ?_
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · simp only [zK_incl, z₀_apply]
    calc ∑ k, ‖x k (rep c v)‖ ^ 2 ≤ ‖c (rep c v)‖ ^ 2 := sum_sq_norm_apply_le hx _
      _ = ‖(incl c v : ↥(K c))‖ ^ 2 := by rw [c_rep]; rfl

theorem sum_sq_norm_z_le (ξ : 𝓗) : ∑ k, ‖z hx k ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2 := by
  show ∑ k, ‖zK hx k ((K c).orthogonalProjectionOnto ξ)‖ ^ 2 ≤ ‖ξ‖ ^ 2
  refine (sum_sq_norm_zK_le hx _).trans ?_
  have h : ‖(K c).orthogonalProjectionOnto ξ‖ ≤ ‖ξ‖ :=
    Submodule.norm_orthogonalProjectionOnto_apply_le (K c) ξ
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- `∑ₖ zₖ* zₖ ≤ 1`. -/
theorem sum_star_z_mul_z_le_one : ∑ k, star (z hx k) * z hx k ≤ 1 := by
  rw [← sub_nonneg]
  refine nonneg_of_re_inner ?_ fun ξ => ?_
  · rw [IsSelfAdjoint, star_sub, star_one, star_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [star_mul, star_star]
  · rw [sub_apply, inner_sub_left, Complex.sub_re, oneA, sum_apply, sum_inner,
      Complex.re_sum]
    have h1 : (⟪ξ, ξ⟫_ℂ).re = ‖ξ‖ ^ 2 := by
      rw [← RCLike.re_to_complex]; exact inner_self_eq_norm_sq ξ
    have h2 : ∀ k, (⟪(star (z hx k) * z hx k) ξ, ξ⟫_ℂ).re = ‖z hx k ξ‖ ^ 2 := by
      intro k
      rw [← inner_conj_symm, Complex.conj_re]
      exact re_inner_star_mul _ _
    simp only [h2, h1]
    linarith [sum_sq_norm_z_le hx ξ]

/-! ## Commutation transport -/

theorem z_comm {R : 𝓗 →L[ℂ] 𝓗} (hRc : R * c = c * R) (hRc' : star R * c = c * star R)
    (hRx : ∀ k, R * x k = x k * R) (k : κ) : R * z hx k = z hx k * R := by
  -- on `K`
  have hK : ∀ w : ↥(K c), R (zK hx k w) = z hx k (R w) := by
    intro w
    refine (denseRange_incl c).induction_on w ?_ fun v => ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · rw [zK_incl, z₀_apply]
      have hv : (incl c v : 𝓗) = c (rep c v) := by rw [incl_apply, c_rep]
      rw [hv]
      show R (x k (rep c v)) = z hx k (R (c (rep c v)))
      rw [← mulA R c, hRc, mulA, z_apply_c, ← mulA R (x k), hRx, mulA]
  ext ξ
  simp only [mulA]
  have hdec : ξ = (K c).starProjection ξ + (ξ - (K c).starProjection ξ) := by abel
  have hP : (K c).starProjection ξ ∈ K c := Submodule.starProjection_apply_mem _ _
  have hQ : ξ - (K c).starProjection ξ ∈ (K c)ᗮ := Submodule.sub_starProjection_mem_orthogonal _
  have e1 : z hx k ξ = z hx k ((K c).starProjection ξ) := by
    conv_lhs => rw [hdec]
    rw [map_add, z_apply_orthogonal hx k hQ, add_zero]
  have e2 : z hx k (R ξ) = z hx k (R ((K c).starProjection ξ)) := by
    conv_lhs => rw [hdec]
    rw [map_add, map_add, z_apply_orthogonal hx k (Kperp_invariant c hRc' hQ), add_zero]
  rw [e1, e2, z_apply_mem hx k hP]
  exact hK ⟨_, hP⟩

end Factor

/-! ## The singular-safe POVM -/

section POVM

variable {A' : Type*} [Fintype A'] [DecidableEq A'] (lab : κ → A') (a₀ : A')
variable {c : 𝓗 →L[ℂ] 𝓗} {x : κ → 𝓗 →L[ℂ] 𝓗} (hxe : ∑ k, star (x k) * x k = star c * c)
include hxe

/-- `Z := ∑ₖ zₖ* zₖ`. -/
noncomputable def Z : 𝓗 →L[ℂ] 𝓗 := ∑ k, star (z hxe.le k) * z hxe.le k

theorem Z_le_one : Z hxe ≤ 1 := sum_star_z_mul_z_le_one hxe.le

theorem one_sub_Z_nonneg : 0 ≤ 1 - Z hxe := sub_nonneg.mpr (Z_le_one hxe)

theorem star_c_mul_Z_mul_c : star c * Z hxe * c = star c * c := by
  unfold Z
  rw [Finset.mul_sum, Finset.sum_mul, ← hxe]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← z_mul_c hxe.le k, star_mul]
  noncomm_ring

theorem star_c_mul_one_sub_Z_mul_c : star c * (1 - Z hxe) * c = 0 := by
  rw [mul_sub, sub_mul, mul_one, star_c_mul_Z_mul_c, sub_self]

/-- The POVM element for the answer `a`: the squares of the factors labelled `a`,
plus the defect `1 − Z` on the fallback answer. -/
noncomputable def povm (a : A') : 𝓗 →L[ℂ] 𝓗 :=
  (∑ k, if lab k = a then star (z hxe.le k) * z hxe.le k else 0)
    + if a = a₀ then 1 - Z hxe else 0

theorem povm_nonneg (a : A') : 0 ≤ povm lab a₀ hxe a := by
  unfold povm
  refine add_nonneg (Finset.sum_nonneg fun k _ => ?_) ?_
  · split_ifs
    · exact star_mul_self_nonneg _
    · exact le_rfl
  · split_ifs
    · exact one_sub_Z_nonneg hxe
    · exact le_rfl

theorem sum_povm : ∑ a, povm lab a₀ hxe a = 1 := by
  unfold povm
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  show Z hxe + (1 - Z hxe) = 1
  abel

theorem star_c_mul_povm_mul_c (a : A') :
    star c * povm lab a₀ hxe a * c = ∑ k, if lab k = a then star (x k) * x k else 0 := by
  unfold povm
  rw [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
  have h2 : star c * (if a = a₀ then 1 - Z hxe else 0) * c = 0 := by
    split_ifs
    · exact star_c_mul_one_sub_Z_mul_c hxe
    · simp
  rw [h2, add_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs
  · rw [← z_mul_c hxe.le k, star_mul]
    noncomm_ring
  · simp

end POVM

end Douglas

end Resolver

end CommutingRepetition
