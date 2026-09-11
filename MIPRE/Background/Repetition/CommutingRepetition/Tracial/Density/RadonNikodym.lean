/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Tracial/Density/RadonNikodym.lean
-/
/-
# Dominated functionals as commutant operators, and the tracially embeddable
package (stage E2)

For a tracial state `τ` on `𝒞`, a positive `σ` and a positive functional `ω`
dominated by `τ_σ := τ(σ* · σ)`, the operator `G := V* V` with
`V := (GNS(τ_σ) → GNS(ω)) ∘ (GNS(τ) → GNS(τ_σ))*` on `L²(𝒞, τ)` is positive,
commutes with the left regular representation, and satisfies
`⟪ι(aσ), G ι(cσ)⟫ = ω(a* c)`. This is the bounded Radon–Nikodym theorem in the
form the interface `TraciallyEmbeddableCorrelation` consumes for Bob's effects
(PLAN-density.md §1.3): a family `ω_b` summing to `τ_σ` yields a POVM in the
commutant after adding the deficit `1 − e′` (the projection onto the cyclic
subspace of `ι σ`) to one outcome. The assembly theorem
`exists_traciallyEmbeddable` packages everything. Proof-side infrastructure.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Tracial.Density.TracialGNS

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace Density

open scoped InnerProductSpace ComplexOrder
open UniformSpace Completion PositiveLinearMap

variable {𝒞 : Type} [CStarAlgebra 𝒞] [PartialOrder 𝒞] [StarOrderedRing 𝒞]

/-! ### Two continuous linear maps agreeing on a dense range -/

theorem clm_ext_of_denseRange {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ι : Type*} {f : ι → H}
    (hf : DenseRange f) {S T : H →L[ℂ] K} (h : ∀ i, S (f i) = T (f i)) : S = T :=
  ContinuousLinearMap.ext_on (Dense.mono Submodule.subset_span hf) (by rintro _ ⟨i, rfl⟩; exact h i)

/-- An operator determined by its matrix coefficients on a dense range. -/
theorem clm_ext_inner_of_denseRange {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} {f : ι → H} (hf : DenseRange f) {S T : H →L[ℂ] H}
    (h : ∀ i j, ⟪f i, S (f j)⟫_ℂ = ⟪f i, T (f j)⟫_ℂ) : S = T := by
  refine clm_ext_of_denseRange hf fun j => ?_
  refine ext_inner_left ℂ fun v => ?_
  refine hf.induction_on v ?_ fun i => h i j
  exact isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)

/-! ### The contraction between the GNS spaces of dominated functionals -/

section Compress

variable (ω ρ : 𝒞 →ₚ[ℂ] ℂ) (hle : ∀ a : 𝒞, ω (star a * a) ≤ ρ (star a * a))

/-- The identity of `𝒞` as a contraction `PreGNS ρ → PreGNS ω`, for `ω ≤ ρ`. -/
noncomputable def gnsCompressPre : ρ.PreGNS →L[ℂ] ω.PreGNS :=
  (ω.toPreGNS.toLinearMap ∘ₗ ρ.ofPreGNS.toLinearMap).mkContinuous 1 fun x => by
    rw [one_mul, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.real_le_real,
      Complex.ofReal_pow, Complex.ofReal_pow, preGNS_norm_sq, preGNS_norm_sq]
    simpa using hle (ρ.ofPreGNS x)

/-- The contraction `GNS ρ → GNS ω` induced by `ω ≤ ρ`. -/
noncomputable def gnsCompress : ρ.GNS →L[ℂ] ω.GNS := (gnsCompressPre ω ρ hle).completion

theorem gnsCompress_ιGNS (a : 𝒞) : gnsCompress ω ρ hle (ιGNS ρ a) = ιGNS ω a := by
  rw [ιGNS_apply, ιGNS_apply, gnsCompress, ContinuousLinearMap.completion_apply_coe]
  rfl

theorem gnsCompress_gns (m : 𝒞) :
    gnsCompress ω ρ hle ∘L ρ.gnsStarAlgHom m = ω.gnsStarAlgHom m ∘L gnsCompress ω ρ hle := by
  refine clm_ext_of_denseRange (denseRange_ιGNS ρ) fun a => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, gns_apply_ιGNS,
    gnsCompress_ιGNS, gnsCompress_ιGNS, gns_apply_ιGNS]

end Compress

/-! ### The conjugated functional `τ_σ = τ(σ* · σ)` and the isometry `GNS(τ_σ) → GNS(τ)` -/

section Conj

variable (τ : 𝒞 →ₚ[ℂ] ℂ) (σ : 𝒞)

/-- `τ_σ(a) := τ(σ* a σ)`. -/
noncomputable def conjState : 𝒞 →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀
    (τ.toLinearMap ∘ₗ LinearMap.mulLeft ℂ (star σ) ∘ₗ LinearMap.mulRight ℂ σ) fun a ha => by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply,
        LinearMap.mulLeft_apply, LinearMap.coe_coe]
      have := map_nonneg τ (star_left_conjugate_nonneg ha σ)
      rwa [mul_assoc] at this

theorem conjState_apply (a : 𝒞) : conjState τ σ a = τ (star σ * (a * σ)) := rfl

/-- `x ↦ x σ` as an isometry `PreGNS τ_σ → PreGNS τ`. -/
noncomputable def embedPre : (conjState τ σ).PreGNS →L[ℂ] τ.PreGNS :=
  (τ.toPreGNS.toLinearMap ∘ₗ LinearMap.mulRight ℂ σ ∘ₗ (conjState τ σ).ofPreGNS.toLinearMap).mkContinuous
    1 fun x => by
      rw [one_mul, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.real_le_real,
        Complex.ofReal_pow, Complex.ofReal_pow, preGNS_norm_sq, preGNS_norm_sq]
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        LinearMap.mulRight_apply, ofPreGNS_toPreGNS, conjState_apply, star_mul, mul_assoc]
      exact le_rfl

theorem embedPre_apply (x : (conjState τ σ).PreGNS) :
    embedPre τ σ x = τ.toPreGNS ((conjState τ σ).ofPreGNS x * σ) := rfl

/-- The isometry `GNS(τ_σ) → GNS(τ)`, `[a] ↦ ι(aσ)`. -/
noncomputable def embed : (conjState τ σ).GNS →L[ℂ] τ.GNS := (embedPre τ σ).completion

theorem embed_ιGNS (a : 𝒞) : embed τ σ (ιGNS (conjState τ σ) a) = ιGNS τ (a * σ) := by
  rw [ιGNS_apply, ιGNS_apply, embed, ContinuousLinearMap.completion_apply_coe, embedPre_apply,
    ofPreGNS_toPreGNS]

theorem inner_embed (u v : (conjState τ σ).GNS) : ⟪embed τ σ u, embed τ σ v⟫_ℂ = ⟪u, v⟫_ℂ := by
  induction u, v using induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x y =>
    rw [embed, ContinuousLinearMap.completion_apply_coe, ContinuousLinearMap.completion_apply_coe,
      inner_coe, inner_coe, preGNS_inner_def, preGNS_inner_def, embedPre_apply, embedPre_apply,
      ofPreGNS_toPreGNS, ofPreGNS_toPreGNS, conjState_apply, star_mul, mul_assoc, mul_assoc]

theorem adjoint_embed_comp_embed :
    ContinuousLinearMap.adjoint (embed τ σ) ∘L embed τ σ = ContinuousLinearMap.id ℂ _ := by
  ext u
  refine ext_inner_left ℂ fun v => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, inner_embed,
    ContinuousLinearMap.id_apply]

theorem gns_comp_embed (m : 𝒞) :
    τ.gnsStarAlgHom m ∘L embed τ σ = embed τ σ ∘L (conjState τ σ).gnsStarAlgHom m := by
  refine clm_ext_of_denseRange (denseRange_ιGNS (conjState τ σ)) fun a => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, gns_apply_ιGNS, embed_ιGNS,
    embed_ιGNS, gns_apply_ιGNS, mul_assoc]

theorem adjoint_gns (ρ : 𝒞 →ₚ[ℂ] ℂ) (m : 𝒞) :
    ContinuousLinearMap.adjoint (ρ.gnsStarAlgHom m) = ρ.gnsStarAlgHom (star m) := by
  rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]

theorem adjoint_embed_comp_gns (m : 𝒞) :
    ContinuousLinearMap.adjoint (embed τ σ) ∘L τ.gnsStarAlgHom m =
      (conjState τ σ).gnsStarAlgHom m ∘L ContinuousLinearMap.adjoint (embed τ σ) := by
  have h := congrArg ContinuousLinearMap.adjoint (gns_comp_embed τ σ (star m))
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, adjoint_gns, adjoint_gns,
    star_star] at h
  exact h

/-- The projection onto the closure of `L(𝒞) ι σ`. -/
noncomputable def cyclicProj : τ.GNS →L[ℂ] τ.GNS :=
  embed τ σ ∘L ContinuousLinearMap.adjoint (embed τ σ)

theorem cyclicProj_embed (u : (conjState τ σ).GNS) : cyclicProj τ σ (embed τ σ u) = embed τ σ u := by
  rw [cyclicProj, ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply
    (ContinuousLinearMap.adjoint (embed τ σ)), adjoint_embed_comp_embed, ContinuousLinearMap.id_apply]

theorem cyclicProj_comp_gns (m : 𝒞) :
    cyclicProj τ σ ∘L τ.gnsStarAlgHom m = τ.gnsStarAlgHom m ∘L cyclicProj τ σ := by
  rw [cyclicProj, ContinuousLinearMap.comp_assoc, adjoint_embed_comp_gns,
    ← ContinuousLinearMap.comp_assoc, ← gns_comp_embed, ContinuousLinearMap.comp_assoc]

theorem cyclicProj_mul_self : cyclicProj τ σ * cyclicProj τ σ = cyclicProj τ σ := by
  show cyclicProj τ σ ∘L cyclicProj τ σ = cyclicProj τ σ
  rw [cyclicProj, ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc
    (ContinuousLinearMap.adjoint (embed τ σ)), adjoint_embed_comp_embed,
    ContinuousLinearMap.id_comp]

theorem adjoint_cyclicProj : ContinuousLinearMap.adjoint (cyclicProj τ σ) = cyclicProj τ σ := by
  rw [cyclicProj, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]

theorem one_sub_cyclicProj_isPositive : (1 - cyclicProj τ σ).IsPositive := by
  have hp : (1 - cyclicProj τ σ) * (1 - cyclicProj τ σ) = 1 - cyclicProj τ σ := by
    rw [mul_sub, sub_mul, sub_mul, one_mul, one_mul, mul_one, cyclicProj_mul_self, sub_self, sub_zero]
  have hsa : ContinuousLinearMap.adjoint (1 - cyclicProj τ σ) = 1 - cyclicProj τ σ := by
    rw [map_sub, ContinuousLinearMap.adjoint_one, adjoint_cyclicProj]
  have := ContinuousLinearMap.isPositive_adjoint_comp_self (1 - cyclicProj τ σ)
  rwa [hsa, show (1 - cyclicProj τ σ) ∘L (1 - cyclicProj τ σ) =
    (1 - cyclicProj τ σ) * (1 - cyclicProj τ σ) from rfl, hp] at this

theorem one_sub_cyclicProj_ι (a : 𝒞) : (1 - cyclicProj τ σ) (ιGNS τ (a * σ)) = 0 := by
  rw [← embed_ιGNS, sub_apply, one_apply_eq_self, cyclicProj_embed, sub_self]

end Conj

/-! ### The Radon–Nikodym operator of a dominated functional -/

section RN

variable (τ : 𝒞 →ₚ[ℂ] ℂ) (σ : 𝒞) (ω : 𝒞 →ₚ[ℂ] ℂ)
  (hle : ∀ a : 𝒞, ω (star a * a) ≤ conjState τ σ (star a * a))

/-- `V := gnsCompress ∘ embed*`. -/
noncomputable def rnV : τ.GNS →L[ℂ] ω.GNS :=
  gnsCompress ω (conjState τ σ) hle ∘L ContinuousLinearMap.adjoint (embed τ σ)

/-- The Radon–Nikodym operator `G = V* V`. -/
noncomputable def rnOp : τ.GNS →L[ℂ] τ.GNS :=
  ContinuousLinearMap.adjoint (rnV τ σ ω hle) ∘L rnV τ σ ω hle

theorem rnOp_isPositive : (rnOp τ σ ω hle).IsPositive :=
  ContinuousLinearMap.isPositive_adjoint_comp_self _

theorem rnV_embed (u : (conjState τ σ).GNS) :
    rnV τ σ ω hle (embed τ σ u) = gnsCompress ω (conjState τ σ) hle u := by
  rw [rnV, ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply
    (ContinuousLinearMap.adjoint (embed τ σ)), adjoint_embed_comp_embed, ContinuousLinearMap.id_apply]

/-- The matrix coefficients: `⟪ι(aσ), G ι(cσ)⟫ = ω(a* c)`. -/
theorem inner_rnOp (a c : 𝒞) :
    ⟪ιGNS τ (a * σ), rnOp τ σ ω hle (ιGNS τ (c * σ))⟫_ℂ = ω (star a * c) := by
  rw [← embed_ιGNS, ← embed_ιGNS, rnOp, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, rnV_embed, rnV_embed, gnsCompress_ιGNS, gnsCompress_ιGNS,
    inner_ιGNS]

/-- `G` commutes with the left regular representation. -/
theorem rnOp_comp_gns (m : 𝒞) :
    rnOp τ σ ω hle ∘L τ.gnsStarAlgHom m = τ.gnsStarAlgHom m ∘L rnOp τ σ ω hle := by
  have hV : rnV τ σ ω hle ∘L τ.gnsStarAlgHom m = ω.gnsStarAlgHom m ∘L rnV τ σ ω hle := by
    rw [rnV, ContinuousLinearMap.comp_assoc, adjoint_embed_comp_gns, ← ContinuousLinearMap.comp_assoc,
      gnsCompress_gns, ContinuousLinearMap.comp_assoc]
  have hV' : ContinuousLinearMap.adjoint (rnV τ σ ω hle) ∘L ω.gnsStarAlgHom m =
      τ.gnsStarAlgHom m ∘L ContinuousLinearMap.adjoint (rnV τ σ ω hle) := by
    have h := congrArg ContinuousLinearMap.adjoint
      (show rnV τ σ ω hle ∘L τ.gnsStarAlgHom (star m) = ω.gnsStarAlgHom (star m) ∘L rnV τ σ ω hle by
        rw [rnV, ContinuousLinearMap.comp_assoc, adjoint_embed_comp_gns,
          ← ContinuousLinearMap.comp_assoc, gnsCompress_gns, ContinuousLinearMap.comp_assoc])
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, adjoint_gns, adjoint_gns,
      star_star] at h
    exact h.symm
  rw [rnOp, ContinuousLinearMap.comp_assoc, hV, ← ContinuousLinearMap.comp_assoc, hV',
    ContinuousLinearMap.comp_assoc]

theorem rnOp_commute (m : 𝒞) : Commute (rnOp τ σ ω hle) (τ.gnsStarAlgHom m) :=
  rnOp_comp_gns τ σ ω hle m

theorem cyclicProj_commute (m : 𝒞) : Commute (cyclicProj τ σ) (τ.gnsStarAlgHom m) :=
  cyclicProj_comp_gns τ σ m

/-! ### Assembly -/

/-- `G = embed ∘ (C* C) ∘ embed*`. -/
theorem rnOp_eq (a : 𝒞) :
    rnOp τ σ ω hle = embed τ σ ∘L (ContinuousLinearMap.adjoint (gnsCompress ω (conjState τ σ) hle) ∘L
      gnsCompress ω (conjState τ σ) hle) ∘L ContinuousLinearMap.adjoint (embed τ σ) := by
  rw [rnOp, rnV, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc]

end RN

section Sum

variable (τ : 𝒞 →ₚ[ℂ] ℂ) (σ : 𝒞)

/-- If dominated functionals sum to `τ_σ`, their Radon–Nikodym operators sum to the cyclic
projection. -/
theorem sum_rnOp {ι : Type*} [Fintype ι] (ω : ι → 𝒞 →ₚ[ℂ] ℂ)
    (hle : ∀ i a, ω i (star a * a) ≤ conjState τ σ (star a * a))
    (hsum : ∀ a, ∑ i, ω i a = conjState τ σ a) :
    ∑ i, rnOp τ σ (ω i) (hle i) = cyclicProj τ σ := by
  have hC : ∑ i, ContinuousLinearMap.adjoint (gnsCompress (ω i) (conjState τ σ) (hle i)) ∘L
      gnsCompress (ω i) (conjState τ σ) (hle i) = 1 := by
    refine clm_ext_inner_of_denseRange (denseRange_ιGNS (conjState τ σ)) fun a c => ?_
    rw [ContinuousLinearMap.sum_apply, inner_sum, one_apply_eq_self, inner_ιGNS, ← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, gnsCompress_ιGNS,
      gnsCompress_ιGNS, inner_ιGNS]
  have hC' : ∀ w, ∑ i, ContinuousLinearMap.adjoint (gnsCompress (ω i) (conjState τ σ) (hle i))
      (gnsCompress (ω i) (conjState τ σ) (hle i) w) = w := fun w => by
    have := congrArg (fun T : (conjState τ σ).GNS →L[ℂ] (conjState τ σ).GNS => T w) hC
    simpa only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
      one_apply_eq_self] using this
  ext v
  rw [ContinuousLinearMap.sum_apply]
  simp only [rnOp_eq τ σ _ _ (1 : 𝒞), ContinuousLinearMap.comp_apply]
  rw [← map_sum, hC', cyclicProj, ContinuousLinearMap.comp_apply]

/-- **The tracially embeddable package** of a tracial state `τ`, a positive `σ` with
`τ(σ²) = 1`, Alice POVMs in `𝒞`, and Bob given by positive functionals `ω_b^y` summing to
`τ(σ · σ)`: the correlation is `re ω_b^y(E_a^x)`. -/
theorem exists_traciallyEmbeddable {Xc Ac : Type} [Fintype Xc] [Fintype Ac] [Nonempty Ac]
    (hτ1 : τ 1 = 1) (hτ : ∀ a b : 𝒞, τ (a * b) = τ (b * a))
    (hσ : 0 ≤ σ) (hσ1 : τ (σ * σ) = 1)
    (E : Xc → Ac → 𝒞) (hE0 : ∀ x a, 0 ≤ E x a) (hE1 : ∀ x, ∑ a, E x a = 1)
    (ω : Xc → Ac → 𝒞 →ₚ[ℂ] ℂ) (hω : ∀ y a, ∑ b, ω y b a = conjState τ σ a) :
    ∃ q : TraciallyEmbeddableCorrelation Xc Ac,
      ∀ x y a b, q.toCorrelation x y a b = (ω y b (E x a)).re := by
  classical
  have hσsa : IsSelfAdjoint σ := IsSelfAdjoint.of_nonneg hσ
  have hle : ∀ y b a, ω y b (star a * a) ≤ conjState τ σ (star a * a) := fun y b a => by
    rw [← hω y]
    exact Finset.single_le_sum (f := fun b => ω y b (star a * a))
      (fun b _ => map_nonneg _ (star_mul_self_nonneg a)) (Finset.mem_univ b)
  obtain ⟨b₀⟩ := ‹Nonempty Ac›
  let G : Xc → Ac → τ.GNS →L[ℂ] τ.GNS := fun y b =>
    rnOp τ σ (ω y b) (hle y b) + if b = b₀ then 1 - cyclicProj τ σ else 0
  have hσn : (ofTracialState τ hτ1 hτ).τ (star σ * σ) = 1 := by
    show τ (star σ * σ) = 1
    rw [hσsa.star_eq]
    exact hσ1
  have hσp : IsPosElem (σ : (ofTracialState τ hτ1 hτ).A) := isPosElem_of_nonneg hσ
  have hEp : ∀ x a, IsPosElem (E x a : (ofTracialState τ hτ1 hτ).A) := fun x a =>
    isPosElem_of_nonneg (hE0 x a)
  refine ⟨{ M := ofTracialState τ hτ1 hτ
            σ := σ
            σ_pos := hσp
            σ_normalized := hσn
            E := E
            E_pos := hEp
            E_sum := hE1
            G := G
            G_pos := ?_
            G_sum := ?_
            G_commutant := ?_ }, ?_⟩
  · intro y b
    refine (rnOp_isPositive τ σ _ _).add ?_
    split_ifs
    · exact one_sub_cyclicProj_isPositive τ σ
    · exact ContinuousLinearMap.isPositive_zero
  · intro y
    show ∑ b, (rnOp τ σ (ω y b) (hle y b) + if b = b₀ then 1 - cyclicProj τ σ else 0) = 1
    rw [Finset.sum_add_distrib, sum_rnOp τ σ (ω y) (hle y) (hω y)]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    abel
  · intro y b m
    show Commute (rnOp τ σ (ω y b) (hle y b) + if b = b₀ then 1 - cyclicProj τ σ else 0)
      (τ.gnsStarAlgHom m)
    refine (rnOp_commute τ σ _ _ m).add_left ?_
    split_ifs
    · exact (Commute.one_left _).sub_left (cyclicProj_commute τ σ m)
    · exact Commute.zero_left _
  · intro x y a b
    have hEsa : IsSelfAdjoint (E x a) := IsSelfAdjoint.of_nonneg (hE0 x a)
    show (⟪ιGNS τ σ, τ.gnsStarAlgHom (E x a) ((rnOp τ σ (ω y b) (hle y b) +
      if b = b₀ then 1 - cyclicProj τ σ else 0) (ιGNS τ σ))⟫_ℂ).re = _
    have h0 : (if b = b₀ then 1 - cyclicProj τ σ else (0 : τ.GNS →L[ℂ] τ.GNS)) (ιGNS τ σ) = 0 := by
      split_ifs
      · rw [show ιGNS τ σ = ιGNS τ (1 * σ) by rw [one_mul], one_sub_cyclicProj_ι]
      · rfl
    rw [_root_.add_apply, h0, add_zero, ← ContinuousLinearMap.adjoint_inner_left, adjoint_gns,
      hEsa.star_eq, gns_apply_ιGNS, show ιGNS τ σ = ιGNS τ (1 * σ) by rw [one_mul], inner_rnOp,
      mul_one, hEsa.star_eq]

end Sum

end Density

end CommutingRepetition
