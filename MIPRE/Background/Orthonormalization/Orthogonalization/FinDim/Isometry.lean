/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/FinDim/Isometry.lean
-/
/-
# Isometric completion in finite dimension (Step F2, Lemma 3.2 of the paper)

Given `T : H → K` and a positive self-adjoint `s` on `H` with `T* T = s²`
(so `‖T v‖ = ‖s v‖`), and a subspace `L ≤ K` with `range T ≤ L` and
`dim L = dim H`, there is an isometry `u : H → K` onto `L` with `u ∘ s = T`.
This is the finite-dimensional content of Lemma 3.2 (`lem:polar_decom_finite`):
the polar part `u₀` of `T` (defined on `range s = range |T|`) is completed on
`ker s` by any isometry onto the orthogonal complement of `range T` inside `L`,
which has the right dimension because `dim L = dim H`.

Proof-side; nothing here is a statement of the paper.
-/
import Mathlib

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace Orthogonalization.FinDim

open scoped InnerProductSpace ComplexOrder
open Module ContinuousLinearMap

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]

/-- `‖T v‖² = ⟪s² v, v⟫` when `T* T = s * s`. -/
theorem inner_apply_eq_of_adjoint_comp_eq (T : H →L[ℂ] K) (s : H →L[ℂ] H)
    (hT : adjoint T ∘L T = s ∘L s) (v w : H) :
    ⟪T v, T w⟫_ℂ = ⟪(s ∘L s) v, w⟫_ℂ := by
  rw [← hT, comp_apply, adjoint_inner_left]

/-- **Isometric completion.** -/
theorem exists_isometry_completion (T : H →L[ℂ] K) (s : H →L[ℂ] H)
    (hs : IsSelfAdjoint s) (hs0 : 0 ≤ s) (hT : adjoint T ∘L T = s ∘L s)
    (L : Submodule ℂ K) (hTL : LinearMap.range (T : H →ₗ[ℂ] K) ≤ L) (hL : finrank ℂ L = finrank ℂ H) :
    ∃ u : H →L[ℂ] K, adjoint u ∘L u = 1 ∧ u ∘L adjoint u = L.starProjection ∧
      u ∘L s = T := by
  classical
  -- the eigenbasis of `s`
  have hsS : (s : H →ₗ[ℂ] H).IsSymmetric := (isSelfAdjoint_iff_isSymmetric).mp hs
  set n := finrank ℂ H with hn
  let b : OrthonormalBasis (Fin n) ℂ H := hsS.eigenvectorBasis rfl
  let τ : Fin n → ℝ := hsS.eigenvalues rfl
  have hb : ∀ k, s (b k) = (τ k : ℂ) • b k := fun k => hsS.apply_eigenvectorBasis rfl k
  have hτ : ∀ k, 0 ≤ τ k := by
    intro k
    have hpos : (s : H →ₗ[ℂ] H).IsPositive := (isPositive_toLinearMap_iff s).mpr
      ((nonneg_iff_isPositive s).mp hs0)
    exact hpos.nonneg_eigenvalues rfl k
  -- `⟪T (b k), T (b l)⟫ = τ k ^ 2 δ_{kl}`
  have hTb : ∀ k l, ⟪T (b k), T (b l)⟫_ℂ = ((τ k : ℂ) * τ k) * ⟪b k, b l⟫_ℂ := by
    intro k l
    rw [inner_apply_eq_of_adjoint_comp_eq T s hT, comp_apply, hb k, map_smul, hb k,
      smul_smul, inner_smul_left]
    simp
  have hTb_zero : ∀ k, τ k = 0 → T (b k) = 0 := by
    intro k hk
    have := hTb k k
    rw [hk] at this
    simp only [Complex.ofReal_zero, mul_zero, zero_mul] at this
    exact inner_self_eq_zero.mp this
  -- the normalized images `e k = τ k⁻¹ • T (b k)` for `τ k ≠ 0`, viewed inside `L`
  have hTmem : ∀ v, T v ∈ L := fun v => hTL ⟨v, rfl⟩
  let S := {k : Fin n // τ k ≠ 0}
  let e : S → L := fun k => ⟨((τ k.1)⁻¹ : ℂ) • T (b k.1), L.smul_mem _ (hTmem _)⟩
  have he : Orthonormal ℂ e := by
    rw [orthonormal_iff_ite]
    intro k l
    simp only [e, Submodule.coe_inner, inner_smul_left, inner_smul_right, hTb, map_inv₀,
      Complex.conj_ofReal, orthonormal_iff_ite.mp b.orthonormal]
    by_cases hkl : k = l
    · subst hkl
      have : (τ k.1 : ℂ) ≠ 0 := by exact_mod_cast k.2
      simp [this]
    · have : k.1 ≠ l.1 := fun h => hkl (Subtype.ext h)
      simp [this, hkl]
  -- `range T`, as a subspace of `L`, is spanned by the `e k`; its orthogonal complement
  -- inside `L` has dimension `n - card S`
  let V : Submodule ℂ L := Submodule.span ℂ (Set.range e)
  have hVfin : finrank ℂ V = Fintype.card S := finrank_span_eq_card he.linearIndependent
  have hcardS : Fintype.card S + Fintype.card {k : Fin n // ¬ τ k ≠ 0} = n := by
    have h1 := Fintype.card_subtype_compl (fun k : Fin n => τ k ≠ 0)
    have h2 := Fintype.card_subtype_le (fun k : Fin n => τ k ≠ 0)
    have hS : Fintype.card S = Fintype.card {k : Fin n // τ k ≠ 0} := rfl
    simp only [Fintype.card_fin] at h1 h2
    omega
  have hVperp : finrank ℂ Vᗮ = Fintype.card {k : Fin n // ¬ τ k ≠ 0} := by
    have h1 := Submodule.finrank_add_finrank_orthogonal V
    rw [hVfin, hL] at h1
    omega
  let f : OrthonormalBasis (Fin (finrank ℂ Vᗮ)) ℂ Vᗮ := stdOrthonormalBasis ℂ Vᗮ
  let φ : {k : Fin n // ¬ τ k ≠ 0} ≃ Fin (finrank ℂ Vᗮ) :=
    Fintype.equivFinOfCardEq hVperp.symm
  -- the combined orthonormal family in `L`
  let g : Fin n → L := fun k => if hk : τ k ≠ 0 then e ⟨k, hk⟩ else (f (φ ⟨k, hk⟩) : L)
  have hg : Orthonormal ℂ g := by
    rw [orthonormal_iff_ite]
    intro k l
    by_cases hk : τ k ≠ 0 <;> by_cases hl : τ l ≠ 0
    · simp only [g, dif_pos hk, dif_pos hl]
      rw [orthonormal_iff_ite.mp he]
      by_cases hkl : k = l
      · subst hkl; simp
      · have : (⟨k, hk⟩ : S) ≠ ⟨l, hl⟩ := fun h => hkl (congrArg Subtype.val h)
        simp [hkl, this]
    · simp only [g, dif_pos hk, dif_neg hl]
      have hmem : e ⟨k, hk⟩ ∈ V := Submodule.subset_span ⟨_, rfl⟩
      have := (f (φ ⟨l, hl⟩)).2
      rw [Submodule.mem_orthogonal] at this
      have hne : k ≠ l := fun h => hl (h ▸ hk)
      simpa [hne] using this _ hmem
    · simp only [g, dif_neg hk, dif_pos hl]
      have hmem : e ⟨l, hl⟩ ∈ V := Submodule.subset_span ⟨_, rfl⟩
      have := (f (φ ⟨k, hk⟩)).2
      rw [Submodule.mem_orthogonal'] at this
      have hne : k ≠ l := fun h => hk (h ▸ hl)
      simpa [hne] using this _ hmem
    · simp only [g, dif_neg hk, dif_neg hl]
      rw [← Submodule.coe_inner, orthonormal_iff_ite.mp f.orthonormal]
      by_cases hkl : k = l
      · subst hkl; simp
      · have : φ ⟨k, hk⟩ ≠ φ ⟨l, hl⟩ := fun h => hkl (congrArg Subtype.val (φ.injective h))
        simp [hkl, this]
  -- hence an orthonormal basis of `L` indexed by `Fin n`
  have hcard : Fintype.card (Fin n) = finrank ℂ L := by rw [Fintype.card_fin, hL]
  have hspan : (⊤ : Submodule ℂ L) ≤ Submodule.span ℂ (Set.range g) := by
    rw [Submodule.eq_top_of_finrank_eq
      ((finrank_span_eq_card hg.linearIndependent).trans hcard)]
  let B : OrthonormalBasis (Fin n) ℂ L := OrthonormalBasis.mk hg hspan
  have hB : ∀ k, B k = g k := fun k => congrFun (OrthonormalBasis.coe_mk hg hspan) k
  -- the isometry `H ≃ L ↪ K`
  let iso : H →ₗᵢ[ℂ] K := L.subtypeₗᵢ.comp (b.equiv B (Equiv.refl _)).toLinearIsometry
  refine ⟨iso.toContinuousLinearMap, iso.adjoint_comp_self, ?_, ?_⟩
  · -- `u u* = starProjection L`: `u u* w` lies in `L` and `w - u u* w ⊥ L`
    ext w
    symm
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact ((b.equiv B (Equiv.refl _)) (adjoint iso.toContinuousLinearMap w)).2
    · intro y hy
      obtain ⟨z, rfl⟩ : ∃ z, iso.toContinuousLinearMap z = y :=
        ⟨(b.equiv B (Equiv.refl _)).symm ⟨y, hy⟩, by
          show ((b.equiv B (Equiv.refl _)) ((b.equiv B (Equiv.refl _)).symm ⟨y, hy⟩) : K) = y
          rw [LinearIsometryEquiv.apply_symm_apply]⟩
      rw [← adjoint_inner_left iso.toContinuousLinearMap z, map_sub, comp_apply]
      have h1 : adjoint iso.toContinuousLinearMap (iso.toContinuousLinearMap
          (adjoint iso.toContinuousLinearMap w)) = adjoint iso.toContinuousLinearMap w := by
        rw [← comp_apply, iso.adjoint_comp_self, one_apply_eq_self]
      rw [h1, sub_self, inner_zero_left]
  · -- `u ∘ s = T`: check on the eigenbasis
    apply ContinuousLinearMap.coe_injective
    apply b.toBasis.ext
    intro k
    show iso.toContinuousLinearMap (s (b k)) = T (b k)
    rw [hb k, map_smul]
    show (τ k : ℂ) • (iso (b k)) = T (b k)
    have hiso : iso (b k) = (B k : K) := by
      simp [iso, OrthonormalBasis.equiv_apply_basis]
    rw [hiso, hB k]
    by_cases hk : τ k ≠ 0
    · simp only [g, dif_pos hk, e, smul_smul]
      have : (τ k : ℂ) * (τ k : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (by exact_mod_cast hk)
      rw [this, one_smul]
    · have hk' : τ k = 0 := not_not.mp hk
      rw [hTb_zero k hk', hk']
      simp

end Orthogonalization.FinDim
