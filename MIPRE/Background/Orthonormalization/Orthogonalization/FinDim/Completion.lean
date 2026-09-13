/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/FinDim/Completion.lean
-/
/-
# Step F2 in finite dimension: producing the isometry data

From projections `q i` commuting with the POVM elements `a i` and with
`∑ tr(q i) = dim H` (the output of Lemma 3.1), build the block-wise partial
isometry `w` of `IsometryData` (the paper's `u` of Lemma 3.2 read block by
block): `T := ∑ embed i ∘ q i √a i : H → H^ι` satisfies `T* T = y = (√y)²`
with `y = ∑ q i a i`, its range lies in the range of the block projection
`Q = ∑ embed i ∘ q i ∘ proj i`, whose dimension is `∑ tr(q i) = dim H`; the
isometric completion `u` of `T` then gives `w i := proj i ∘ u`. Proof-side.
-/
import Mathlib
import MIPRE.Background.Orthonormalization.Orthogonalization.Positivity
import MIPRE.Background.Orthonormalization.Orthogonalization.IsometryData
import MIPRE.Background.Orthonormalization.Orthogonalization.FinDim.Blocks
import MIPRE.Background.Orthonormalization.Orthogonalization.FinDim.Isometry

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace Orthogonalization.FinDim

open scoped InnerProductSpace ComplexOrder
open ContinuousLinearMap Module Orthogonalization

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem blockProj_isStarProjection (q : ι → H →L[ℂ] H) (hq : ∀ i, IsStarProjection (q i)) :
    IsStarProjection (blockProj q) := by
  refine ⟨?_, ?_⟩
  · show blockProj q ∘L blockProj q = blockProj q
    ext w j
    show (blockProj q (blockProj q w)) j = (blockProj q w) j
    rw [blockProj_apply_coord, blockProj_apply_coord, ← ContinuousLinearMap.mul_apply, (hq j).isIdempotentElem.eq]
  · rw [IsSelfAdjoint, star_eq_adjoint]
    symm
    rw [eq_adjoint_iff]
    intro w w'
    simp only [PiLp.inner_apply, blockProj_apply_coord]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← adjoint_inner_left, ← star_eq_adjoint, (hq j).isSelfAdjoint.star_eq]

/-- The trace of the block projection is the sum of the traces of the blocks. -/
theorem trace_blockProj (q : ι → H →L[ℂ] H) :
    LinearMap.trace ℂ (BlockSpace H ι) (blockProj q : BlockSpace H ι →ₗ[ℂ] BlockSpace H ι) =
      ∑ i, LinearMap.trace ℂ H (q i : H →ₗ[ℂ] H) := by
  have hcoe : ((blockProj q : BlockSpace H ι →L[ℂ] BlockSpace H ι) :
      BlockSpace H ι →ₗ[ℂ] BlockSpace H ι) =
      ∑ i, ((embed i ∘L q i ∘L proj i : BlockSpace H ι →L[ℂ] BlockSpace H ι) :
        BlockSpace H ι →ₗ[ℂ] BlockSpace H ι) := by
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.sum_apply]
    simp only [ContinuousLinearMap.coe_coe]
    rw [blockProj, sumCLM]
  rw [hcoe, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  show LinearMap.trace ℂ (BlockSpace H ι)
      (((embed i : H →L[ℂ] BlockSpace H ι) : H →ₗ[ℂ] BlockSpace H ι) ∘ₗ
        (((q i : H →L[ℂ] H) : H →ₗ[ℂ] H) ∘ₗ
          ((proj i : BlockSpace H ι →L[ℂ] H) : BlockSpace H ι →ₗ[ℂ] H))) = _
  rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc]
  have : ((proj i : BlockSpace H ι →L[ℂ] H) : BlockSpace H ι →ₗ[ℂ] H) ∘ₗ
      ((embed i : H →L[ℂ] BlockSpace H ι) : H →ₗ[ℂ] BlockSpace H ι) = LinearMap.id := by
    ext v
    exact proj_embed_same i v
  rw [this, LinearMap.comp_id]

/-- **Step F2**: the isometry data exist in finite dimension. -/
theorem exists_isometryData (a q : ι → H →L[ℂ] H) (ha0 : ∀ i, 0 ≤ a i)
    (hq : ∀ i, IsStarProjection (q i)) (hqa : ∀ i, Commute (q i) (a i))
    (htr : ∑ i, LinearMap.trace ℂ H (q i : H →ₗ[ℂ] H) = (finrank ℂ H : ℂ)) :
    ∃ w : ι → H →L[ℂ] H, IsometryData a q w := by
  classical
  -- square roots of the `a i` and of `y = ∑ q i a i`
  set r : ι → H →L[ℂ] H := fun i => CFC.sqrt (a i) with hr
  have hr0 : ∀ i, 0 ≤ r i := fun i => CFC.sqrt_nonneg (a i)
  have hrsa : ∀ i, star (r i) = r i := fun i => (IsSelfAdjoint.of_nonneg (hr0 i)).star_eq
  have hrr : ∀ i, r i * r i = a i := fun i => CFC.sqrt_mul_sqrt_self (a i) (ha0 i)
  have hqr : ∀ i, Commute (q i) (r i) := fun i => Orthogonalization.Commute.sqrt (hqa i)
  have hqsa : ∀ i, star (q i) = q i := fun i => (hq i).isSelfAdjoint.star_eq
  have hqq : ∀ i, q i * q i = q i := fun i => (hq i).isIdempotentElem.eq
  set y : H →L[ℂ] H := ∑ i, q i * a i with hy
  have hy0 : 0 ≤ y :=
    Finset.sum_nonneg fun i _ => mul_nonneg_of_commute (hq i).nonneg (ha0 i) (hqa i)
  set s : H →L[ℂ] H := CFC.sqrt y with hs_def
  have hs0 : 0 ≤ s := CFC.sqrt_nonneg y
  have hss : s * s = y := CFC.sqrt_mul_sqrt_self y hy0
  have hs : IsSelfAdjoint s := IsSelfAdjoint.of_nonneg hs0
  -- the block map `T` and `T* T = s²`
  set T : H →L[ℂ] BlockSpace H ι := blockMap (fun i => q i * r i) with hT_def
  have hT : adjoint T ∘L T = s ∘L s := by
    ext v
    rw [comp_apply, comp_apply, ← ContinuousLinearMap.mul_apply, hss, hy, sumCLM]
    -- `T* (T v) = ∑ i, (q i r i)* (q i r i) v`
    have h1 : adjoint T (T v) = ∑ i, adjoint (q i * r i) (proj i (T v)) := by
      have : adjoint T = ∑ i, adjoint (q i * r i) ∘L proj i := by
        simp only [T, blockMap, map_sum, adjoint_comp, adjoint_embed]
      rw [this, sumCLM]
      rfl
    rw [h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hT_def, proj_blockMap_apply, ← comp_apply, ← star_eq_adjoint]
    show (star (q i * r i) * (q i * r i)) v = (q i * a i) v
    congr 1
    rw [star_mul, hrsa, hqsa, mul_assoc, ← mul_assoc (q i), hqq, ← mul_assoc, ← (hqr i).eq,
      mul_assoc, hrr]
  -- the block projection `Q`, its range `L` and `dim L = dim H`
  set Q := blockProj q with hQ_def
  have hQproj := blockProj_isStarProjection q hq
  set L : Submodule ℂ (BlockSpace H ι) := LinearMap.range (Q : BlockSpace H ι →ₗ[ℂ] _) with hL_def
  have hTL : LinearMap.range (T : H →ₗ[ℂ] BlockSpace H ι) ≤ L := by
    rintro _ ⟨v, rfl⟩
    refine ⟨T v, ?_⟩
    show Q (T v) = T v
    rw [hQ_def, hT_def, blockProj_blockMap]
    have hfun : (fun i => q i ∘L (q i * r i)) = fun i => q i * r i := by
      funext i
      rw [← mul_def, ← mul_assoc, hqq]
    rw [hfun]
  have hL : finrank ℂ L = finrank ℂ H := by
    have hproj : LinearMap.IsProj L (Q : BlockSpace H ι →ₗ[ℂ] BlockSpace H ι) :=
      ⟨fun x => ⟨x, rfl⟩, by
        rintro _ ⟨x, rfl⟩
        show Q (Q x) = Q x
        rw [← ContinuousLinearMap.mul_apply, hQproj.isIdempotentElem.eq]⟩
    have htrQ := hproj.trace
    rw [hQ_def, trace_blockProj, htr] at htrQ
    exact_mod_cast htrQ.symm
  -- the isometric completion and its blocks
  obtain ⟨u, hu1, hu2, hu3⟩ := exists_isometry_completion T s hs hs0 hT L hTL hL
  have hQL : L.starProjection = Q := by
    obtain ⟨_, hQ'⟩ := isStarProjection_iff_eq_starProjection_range.mp hQproj
    exact hQ'.symm
  refine ⟨fun i => proj i ∘L u, ?_, ?_, ?_⟩
  · -- (W1)
    ext v
    rw [sumCLM]
    have : ∀ i, (star (proj i ∘L u) * (proj i ∘L u)) v = adjoint u (embed i (proj i (u v))) := by
      intro i
      rw [ContinuousLinearMap.mul_apply, star_eq_adjoint, adjoint_comp, adjoint_proj, comp_apply,
        comp_apply]
    simp only [this]
    rw [← map_sum, sum_embed_proj_apply, ← comp_apply, hu1, one_apply_eq_self]
  · -- (W2)
    intro i j
    ext v
    rw [ContinuousLinearMap.mul_apply, star_eq_adjoint, adjoint_comp, adjoint_proj, comp_apply,
      comp_apply, ← comp_apply u, hu2, hQL, hQ_def, proj_blockProj_embed]
    split_ifs <;> simp
  · -- (W3)
    intro i
    rw [mul_def, comp_assoc, hu3, hT_def, proj_comp_blockMap]

end Orthogonalization.FinDim
