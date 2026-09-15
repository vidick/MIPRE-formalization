/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/FinDim/Blocks.lean
-/
/-
# The block space `H^ι` and its coordinate maps

`BlockSpace H ι := PiLp 2 (fun _ : ι => H)` is the Hilbert space direct sum of
`card ι` copies of `H`; `embed i : H → H^ι` and `proj i : H^ι → H` are the
coordinate maps, adjoint to each other, with `proj i ∘ embed j = δᵢⱼ` and
`∑ embed i ∘ proj i = 1`. This is the paper's `M_n(M)` picture read on
vectors (cf. the sister project's `VN/BlockOperators`, which is specific to
its tracial standard forms). Proof-side.
-/
import Mathlib

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace Orthogonalization.FinDim

open scoped InnerProductSpace
open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (H) in
/-- The Hilbert space direct sum `H^ι`. -/
abbrev BlockSpace (ι : Type*) : Type _ := PiLp 2 (fun _ : ι => H)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Evaluating a finite sum of block vectors coordinatewise. -/
theorem sumA {κ : Type*} (s : Finset κ) (f : κ → BlockSpace H ι) (j : ι) :
    (∑ k ∈ s, f k) j = ∑ k ∈ s, f k j := by
  show WithLp.ofLp (∑ k ∈ s, f k) j = ∑ k ∈ s, WithLp.ofLp (f k) j
  rw [WithLp.ofLp_sum, Finset.sum_apply]

/-- Applying a finite sum of operators. -/
theorem sumCLM {κ : Type*} {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F] (s : Finset κ) (f : κ → E →L[ℂ] F) (v : E) :
    (∑ k ∈ s, f k) v = ∑ k ∈ s, f k v := by
  rw [ContinuousLinearMap.coe_sum', Finset.sum_apply]

/-- Coordinate embedding `v ↦ (0, …, v, …, 0)`. -/
noncomputable def embed (i : ι) : H →L[ℂ] BlockSpace H ι :=
  ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.pi fun j : ι => if j = i then ContinuousLinearMap.id ℂ H else 0)

/-- Coordinate projection. -/
noncomputable def proj (i : ι) : BlockSpace H ι →L[ℂ] H := PiLp.proj 2 (fun _ : ι => H) i

theorem embed_apply (i j : ι) (v : H) : embed i v j = if j = i then v else 0 := by
  unfold embed
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, PiLp.coe_symm_continuousLinearEquiv]
  show (ContinuousLinearMap.pi fun j : ι =>
      if j = i then ContinuousLinearMap.id ℂ H else 0) v j = _
  rw [ContinuousLinearMap.pi_apply]
  split_ifs <;> rfl

theorem proj_apply (i : ι) (w : BlockSpace H ι) : proj i w = w i := rfl

theorem proj_embed (i j : ι) (v : H) : proj i (embed j v) = if i = j then v else 0 := by
  rw [proj_apply, embed_apply]

theorem proj_embed_same (i : ι) (v : H) : proj i (embed i v) = v := by simp [proj_embed]

theorem proj_embed_ne {i j : ι} (h : i ≠ j) (v : H) : proj i (embed j v) = 0 := by
  simp [proj_embed, h]

theorem sum_embed_proj_apply (w : BlockSpace H ι) : ∑ i, embed i (proj i w) = w := by
  ext j
  rw [sumA]
  simp only [embed_apply, proj_apply]
  rw [Finset.sum_ite_eq Finset.univ j]
  simp

theorem inner_embed_left (i : ι) (v : H) (w : BlockSpace H ι) :
    ⟪embed i v, w⟫_ℂ = ⟪v, w i⟫_ℂ := by
  simp only [PiLp.inner_apply, embed_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem adjoint_embed (i : ι) : adjoint (embed (H := H) i) = proj (ι := ι) i := by
  symm
  rw [eq_adjoint_iff]
  intro w v
  rw [proj_apply]
  conv_rhs => rw [← inner_conj_symm, inner_embed_left, inner_conj_symm]

theorem adjoint_proj (i : ι) : adjoint (proj (H := H) (ι := ι) i) = embed i := by
  rw [← adjoint_embed, adjoint_adjoint]

/-- The map `T = ∑ embed i ∘ X i : H → H^ι` with blocks `X i`. -/
noncomputable def blockMap (X : ι → H →L[ℂ] H) : H →L[ℂ] BlockSpace H ι :=
  ∑ i, embed i ∘L X i

theorem blockMap_apply (X : ι → H →L[ℂ] H) (v : H) : blockMap X v = ∑ i, embed i (X i v) := by
  rw [blockMap, sumCLM]; rfl

theorem proj_blockMap_apply (X : ι → H →L[ℂ] H) (i : ι) (v : H) :
    proj i (blockMap X v) = X i v := by
  rw [blockMap_apply, proj_apply, sumA]
  simp only [embed_apply]
  rw [Finset.sum_ite_eq Finset.univ i]
  simp

theorem proj_comp_blockMap (X : ι → H →L[ℂ] H) (i : ι) : proj i ∘L blockMap X = X i := by
  ext v
  exact proj_blockMap_apply X i v

/-- The block projection `Q = ∑ embed i ∘ q i ∘ proj i` on `H^ι`. -/
noncomputable def blockProj (q : ι → H →L[ℂ] H) : BlockSpace H ι →L[ℂ] BlockSpace H ι :=
  ∑ i, embed i ∘L q i ∘L proj i

theorem blockProj_apply (q : ι → H →L[ℂ] H) (w : BlockSpace H ι) :
    blockProj q w = ∑ i, embed i (q i (w i)) := by
  rw [blockProj, sumCLM]; rfl

theorem blockProj_apply_coord (q : ι → H →L[ℂ] H) (w : BlockSpace H ι) (j : ι) :
    blockProj q w j = q j (w j) := by
  rw [blockProj_apply, sumA]
  simp only [embed_apply]
  rw [Finset.sum_ite_eq Finset.univ j]
  simp

theorem proj_blockProj_embed (q : ι → H →L[ℂ] H) (i j : ι) (v : H) :
    proj i (blockProj q (embed j v)) = if i = j then q i v else 0 := by
  rw [proj_apply, blockProj_apply_coord, embed_apply]
  split_ifs with h
  · subst h; rfl
  · simp

theorem blockProj_blockMap (q X : ι → H →L[ℂ] H) (v : H) :
    blockProj q (blockMap X v) = blockMap (fun i => q i ∘L X i) v := by
  ext j
  rw [blockProj_apply_coord]
  show q j (proj j (blockMap X v)) = proj j (blockMap (fun i => q i ∘L X i) v)
  rw [proj_blockMap_apply, proj_blockMap_apply]
  rfl

end Orthogonalization.FinDim
