/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/Blocks/Factor.lean
-/
/-
# Tier T1b: the blocks of a minimal central projection

For a minimal central projection `z` of a von Neumann algebra `M` on a
finite-dimensional space, the block `M z` is a full matrix algebra: choosing a
minimal projection `e ≤ z` of `M` and a unit vector `ξ ∈ e H`, the orbit
`L = M ξ` is an `M`-invariant subspace of `z H` on which `M z` acts
*irreducibly* (`e M e = ℂ e`) and *faithfully* (the central support of `e`
is `z`), so compression to `L` is a bijection `M z → B(L)` (Schur's lemma and
the finite-dimensional bicommutant theorem give surjectivity). The transport
theorem then gives Theorem 1.2 at `z` (`orthAt_of_isMinimalCentral`).
Proof-side only.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.Cutdown
import MIPRE.Background.Orthonormalization.Orthogonalization.Blocks.Minimal
import MIPRE.Background.Orthonormalization.Orthogonalization.Blocks.Bicommutant
import MIPRE.Background.Orthonormalization.Orthogonalization.Blocks.Transport

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace Orthogonalization.Blocks

open scoped BigOperators ComplexOrder InnerProductSpace
open CommutingRepetition.VN Module

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

theorem inner_apply_of_isSelfAdjoint {e : H →L[ℂ] H} (he : IsSelfAdjoint e) (x w : H) :
    ⟪x, e w⟫_ℂ = ⟪e x, w⟫_ℂ := by
  have he' : ContinuousLinearMap.adjoint e = e := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact he.star_eq
  conv_lhs => rw [← he']
  rw [ContinuousLinearMap.adjoint_inner_right]

/-- The orbit `M ξ` of a vector under `M`, as a submodule. -/
noncomputable def orbitSubmodule (M : VonNeumannAlgebra H) (ξ : H) : Submodule ℂ H :=
  Submodule.map ((ContinuousLinearMap.apply ℂ H ξ : (H →L[ℂ] H) →L[ℂ] H) : (H →L[ℂ] H) →ₗ[ℂ] H)
    (Subalgebra.toSubmodule M.toStarSubalgebra.toSubalgebra)

theorem mem_orbitSubmodule (M : VonNeumannAlgebra H) {ξ v : H} :
    v ∈ orbitSubmodule M ξ ↔ ∃ x ∈ M, x ξ = v := by
  rw [orbitSubmodule, Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, by simpa using hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, by simpa using hx, rfl⟩

/-- **The block of a minimal central projection is a full matrix algebra**, in the form
consumed by the transport theorem: Theorem 1.2 holds at every minimal central
projection. -/
theorem orthAt_of_isMinimalCentral (M : VonNeumannAlgebra H) {z : H →L[ℂ] H}
    (hz : IsMinimalCentral M z) (ι : Type*) [Fintype ι] : OrthAt M z ι := by
  classical
  have hzc := hz.isCentralProj
  have hzP : IsStarProjection z := hzc.isStarProjection
  have hzM : z ∈ M := hzc.mem
  -- a minimal projection `e ≤ z` and a unit vector `ξ ∈ e H`
  obtain ⟨e, he⟩ := exists_isMinimalProjIn M hzP hzM hz.ne_zero
  have heP := he.isStarProjection
  have heM := he.mem
  have hze : z * e = e := proj_mul_left_of_mul_right heP hzP he.mul_eq
  obtain ⟨v₀, hv₀⟩ := ContinuousLinearMap.exists_ne_zero he.ne_zero
  set ξ : H := ((‖e v₀‖ : ℂ))⁻¹ • e v₀ with hξ
  have hξ1 : ‖ξ‖ = 1 := norm_smul_inv_norm hv₀
  have heξ : e ξ = ξ := by
    rw [hξ, map_smul, ← mul_apply_eq_comp, heP.isIdempotentElem.eq]
  have hzξ : z ξ = ξ := by
    conv_lhs => rw [← heξ]
    rw [← mul_apply_eq_comp, hze, heξ]
  -- the orbit `L = M ξ`
  set L := orbitSubmodule M ξ with hL
  have hξL : ξ ∈ L := (mem_orbitSubmodule M).mpr ⟨1, one_mem M, one_apply_eq_self ξ⟩
  have hLz : ∀ v ∈ L, z v = v := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := (mem_orbitSubmodule M).mp hv
    rw [← mul_apply_eq_comp, (hzc.commute x hx).eq, mul_apply_eq_comp, hzξ]
  have hLM : ∀ x ∈ M, ∀ v ∈ L, x v ∈ L := by
    intro x hx v hv
    obtain ⟨y, hy, rfl⟩ := (mem_orbitSubmodule M).mp hv
    exact (mem_orbitSubmodule M).mpr ⟨x * y, mul_mem hx hy, mul_apply_eq_comp x y ξ⟩
  -- the scalar identity `e y* y e = ‖y ξ‖² e` for `y ∈ M` (`e M e = ℂ e`)
  have hkey : ∀ y ∈ M, e * star y * y * e = ((‖y ξ‖ ^ 2 : ℝ) : ℂ) • e := by
    intro y hy
    set t := e * star y * y * e with ht
    have htM : t ∈ M := mul_mem (mul_mem (mul_mem heM (star_mem hy)) hy) heM
    have htsa : IsSelfAdjoint t := by
      have : t = star (y * e) * (y * e) := by
        rw [ht, star_mul, heP.isSelfAdjoint.star_eq]
        noncomm_ring
      rw [this]
      exact IsSelfAdjoint.star_mul_self _
    have hete : e * t * e = t := by
      calc e * t * e = (e * e) * star y * y * (e * e) := by rw [ht]; noncomm_ring
        _ = t := by rw [heP.isIdempotentElem.eq, ht]
    obtain ⟨c, hc⟩ := exists_eq_smul_of_isMinimalProjIn M he htM htsa hete
    have h1 : ⟪ξ, t ξ⟫_ℂ = ((‖y ξ‖ ^ 2 : ℝ) : ℂ) := by
      have ht' : t ξ = e (star y (y ξ)) := by
        rw [ht]
        simp only [mul_apply_eq_comp, heξ]
      rw [ht', inner_apply_of_isSelfAdjoint heP.isSelfAdjoint, heξ,
        ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
        inner_self_eq_norm_sq_to_K]
      norm_cast
    have h2 : ⟪ξ, t ξ⟫_ℂ = (c : ℂ) := by
      rw [hc, smul_apply, inner_smul_right, heξ, inner_self_eq_norm_sq_to_K, hξ1]
      simp
    have hc' : c = ‖y ξ‖ ^ 2 := Complex.ofReal_injective (h2.symm.trans h1)
    rw [hc, hc']
  -- injectivity of the compression on `M z`
  have hinj : ∀ x ∈ M, x * z = x → compressTo L x = 0 → x = 0 := by
    intro x hx hxz hcx
    have hxL : ∀ v ∈ L, x v = 0 := by
      intro v hv
      have h := congrArg (fun S : L →L[ℂ] L => (S ⟨v, hv⟩ : H)) hcx
      simp only [coe_compressTo_apply_of_invariant L (hLM x hx)] at h
      simpa using h
    have hxye : ∀ y ∈ M, x * y * e = 0 := by
      intro y hy
      have h := hkey (x * y) (mul_mem hx hy)
      have h0 : (x * y) ξ = 0 := by
        rw [mul_apply_eq_comp]
        exact hxL _ ((mem_orbitSubmodule M).mpr ⟨y, hy, rfl⟩)
      rw [h0, norm_zero, zero_pow two_ne_zero, Complex.ofReal_zero, zero_smul] at h
      have h' : star (x * y * e) * (x * y * e) = 0 := by
        rw [star_mul, heP.isSelfAdjoint.star_eq, ← h]
        noncomm_ring
      exact (CStarRing.star_mul_self_eq_zero_iff _).mp h'
    -- the central projection onto `W = span (M e H)` is `z` (central support of `e`)
    set W : Submodule ℂ H := Submodule.span ℂ {w | ∃ y ∈ M, ∃ u : H, w = y (e u)} with hW
    have hWgen : ∀ y ∈ M, ∀ u, y (e u) ∈ W := fun y hy u => Submodule.subset_span ⟨y, hy, u, rfl⟩
    have hWM : ∀ g ∈ M, ∀ w ∈ W, g w ∈ W := by
      intro g hg
      have hle : W ≤ Submodule.comap (g : H →ₗ[ℂ] H) W := by
        rw [hW]
        refine Submodule.span_le.mpr ?_
        rintro w ⟨y, hy, u, rfl⟩
        show g (y (e u)) ∈ W
        rw [← mul_apply_eq_comp]
        exact hWgen (g * y) (mul_mem hg hy) u
      intro w hw
      exact hle hw
    have hWM' : ∀ g ∈ M.commutant, ∀ w ∈ W, g w ∈ W := by
      intro g hg
      have hle : W ≤ Submodule.comap (g : H →ₗ[ℂ] H) W := by
        rw [hW]
        refine Submodule.span_le.mpr ?_
        rintro w ⟨y, hy, u, rfl⟩
        show g (y (e u)) ∈ W
        rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, commutant_mul_of_mem hy hg,
          mul_assoc, commutant_mul_of_mem heM hg, ← mul_assoc, mul_apply_eq_comp,
          mul_apply_eq_comp]
        exact hWgen y hy (g u)
      intro w hw
      exact hle hw
    set P := W.starProjection with hP
    have hPP : IsStarProjection P := isStarProjection_starProjection
    have hPM' : P ∈ M.commutant := by
      rw [VonNeumannAlgebra.mem_commutant_iff]
      intro g hg
      exact (starProjection_commute_of_invariant W (hWM g hg) (hWM (star g) (star_mem hg))).eq
    have hPM : P ∈ M := by
      rw [VonNeumannAlgebra.IsStarProjection.mem_iff hPP]
      intro y hy
      rw [hP, Submodule.range_starProjection, Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
      exact hWM' y hy
    have hPc : IsCentralProj M P :=
      ⟨hPP, hPM, fun x hx => (VonNeumannAlgebra.mem_commutant_iff.mp hPM' x hx).symm⟩
    have hP0 : P ≠ 0 := by
      intro h0
      have hmem : e v₀ ∈ W := by simpa using hWgen 1 (one_mem M) v₀
      have h1 : P (e v₀) = e v₀ := Submodule.starProjection_eq_self_iff.mpr hmem
      rw [h0] at h1
      exact hv₀ (by simpa using h1.symm)
    have hPz : P * z = P := by
      have h1 : z * P = P := by
        refine mul_eq_self_of_range_le hzP ?_
        rw [hP, Submodule.range_starProjection, hW]
        refine Submodule.span_le.mpr ?_
        rintro w ⟨y, hy, u, rfl⟩
        refine ⟨y (e u), ?_⟩
        show z (y (e u)) = y (e u)
        rw [← mul_apply_eq_comp, (hzc.commute y hy).eq, mul_apply_eq_comp, ← mul_apply_eq_comp z e,
          hze]
      have h2 := congrArg star h1
      rwa [star_mul, hPP.isSelfAdjoint.star_eq, hzP.isSelfAdjoint.star_eq] at h2
    have hPeq : P = z := by
      rcases hz.minimal P hPc hPz with h | h
      · exact absurd h hP0
      · exact h
    have hxW : ∀ w ∈ W, x w = 0 := by
      have hle : W ≤ LinearMap.ker (x : H →ₗ[ℂ] H) := by
        rw [hW]
        refine Submodule.span_le.mpr ?_
        rintro w ⟨y, hy, u, rfl⟩
        show x (y (e u)) = 0
        rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, hxye y hy, zero_apply]
      intro w hw
      exact hle hw
    ext w
    rw [zero_apply]
    calc x w = x (z w) := by rw [← mul_apply_eq_comp, hxz]
      _ = x (P w) := by rw [hPeq]
      _ = 0 := hxW _ (Submodule.starProjection_apply_mem W w)
  -- surjectivity of the compression: the compressed algebra is irreducible
  have hsurj : ∀ y : L →L[ℂ] L, ∃ x ∈ M, x * z = x ∧ compressTo L x = y := by
    let A : StarSubalgebra ℂ (L →L[ℂ] L) :=
      { carrier := {S | ∃ x ∈ M, compressTo L x = S}
        mul_mem' := by
          rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
          exact ⟨x * y, mul_mem hx hy, compressTo_mul_of_invariant L x (hLM y hy)⟩
        one_mem' := ⟨1, one_mem M, compressTo_one L⟩
        add_mem' := by
          rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
          exact ⟨x + y, add_mem hx hy, compressTo_add L x y⟩
        zero_mem' := ⟨0, zero_mem M, compressTo_zero L⟩
        algebraMap_mem' := fun c => ⟨algebraMap ℂ _ c,
          VonNeumannAlgebra.mem_carrier.mp (M.toStarSubalgebra.algebraMap_mem c), by
          rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, compressTo_smul,
            compressTo_one]⟩
        star_mem' := by
          rintro _ ⟨x, hx, rfl⟩
          exact ⟨star x, star_mem hx, compressTo_star L x⟩ }
    have hA : IsIrreducible A := by
      intro W' hW'
      by_cases hbot : W' = ⊥
      · exact Or.inl hbot
      right
      obtain ⟨w, hwW', hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
      obtain ⟨y, hy, hyw⟩ := (mem_orbitSubmodule M).mp w.2
      have hnorm : ‖y ξ‖ ≠ 0 := by
        rw [hyw]
        exact norm_ne_zero_iff.mpr fun h => hw0 (Subtype.ext h)
      have hc : ((‖y ξ‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast pow_ne_zero 2 hnorm
      -- `ξ ∈ W'`: `ξ = ‖y ξ‖⁻² (e y*) w`
      have hξW' : (⟨ξ, hξL⟩ : L) ∈ W' := by
        have h1 : compressTo L (e * star y) ∈ A := ⟨e * star y, mul_mem heM (star_mem hy), rfl⟩
        have h2 : compressTo L (e * star y) w ∈ W' := hW' _ h1 w hwW'
        have h3 : (⟨ξ, hξL⟩ : L) = ((‖y ξ‖ ^ 2 : ℝ) : ℂ)⁻¹ • compressTo L (e * star y) w := by
          apply Subtype.ext
          rw [Submodule.coe_smul,
            coe_compressTo_apply_of_invariant L (hLM _ (mul_mem heM (star_mem hy))), ← hyw]
          show ξ = ((‖y ξ‖ ^ 2 : ℝ) : ℂ)⁻¹ • (e * star y) (y ξ)
          have h4 : (e * star y) (y ξ) = (e * star y * y * e) ξ := by
            simp only [mul_apply_eq_comp, heξ]
          rw [h4, hkey y hy, smul_apply, heξ, smul_smul, inv_mul_cancel₀ hc, one_smul]
        rw [h3]
        exact W'.smul_mem _ h2
      rw [eq_top_iff]
      rintro ⟨v, hv⟩ -
      obtain ⟨x, hx, rfl⟩ := (mem_orbitSubmodule M).mp hv
      have h5 : (⟨x ξ, hv⟩ : L) = compressTo L x ⟨ξ, hξL⟩ := by
        apply Subtype.ext
        rw [coe_compressTo_apply_of_invariant L (hLM x hx)]
      rw [h5]
      exact hW' _ ⟨x, hx, rfl⟩ _ hξW'
    intro y
    obtain ⟨x, hx, hxy⟩ := mem_of_isIrreducible A hA y
    refine ⟨x * z, mul_mem hx hzM, by rw [mul_assoc, hzP.isIdempotentElem.eq], ?_⟩
    rw [compressTo_mul_of_invariant L x (fun v hv => by rw [hLz v hv]; exact hv),
      compressTo_eq_one_of_forall_apply_eq L hLz, mul_one, hxy]
  exact orthAt_of_compress_bijective M hzc L hLz hLM hinj hsurj ι

end Orthogonalization.Blocks
