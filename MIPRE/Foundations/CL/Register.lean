/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import Mathlib.LinearAlgebra.Pi

/-!
# Register subspaces

The linear spaces of the conditionally linear machinery (blueprint `sec:ps-cl`, paper
`linear.tex`) are `V = F^ι` for a finite index type `ι`, and the subspaces that occur in it are
*register subspaces*: spans of subsets of the standard basis, hence determined by a set
`S : Finset ι` of coordinates (paper `preliminaries.tex`, "Register subspace"). This file fixes
the two pieces of vocabulary in which everything else is written.

* `MIPRE.CL.proj S : (ι → F) →ₗ[F] (ι → F)` is the coordinate projection onto `V_S` along the
  complementary register subspace `V_{Sᶜ}`: the paper's `x ↦ x^{V_S}`.
* `MIPRE.CL.RegLinear F S` is a linear map "on `V_S`", presented as an endomorphism `L` of the
  ambient space with `proj S ∘ L ∘ proj S = L`: it reads only the coordinates in `S` and writes
  only there. This is how the paper's `L₁ : V₁ → V₁` and `L_{k,u} : V_{k,u} → V_{k,u}` are
  handled, and it makes the paper's shorthand `x^{L} = L(x^{V_S})` literally `L x`
  (`RegLinear.apply_proj`).

Everything here is elementary; the point is to fix names and `simp` lemmas.
-/

namespace MIPRE.CL

variable {F : Type*} [Semiring F] {ι : Type*} [DecidableEq ι]

/-! ## Coordinate projections -/

/-- The coordinate projection onto the register subspace `V_S`: it keeps the coordinates in
`S` and zeroes the others (the paper's `x ↦ x^{V_S}`, the projection onto `V_S` parallel to
`V_{Sᶜ}`). -/
def proj (S : Finset ι) : (ι → F) →ₗ[F] (ι → F) where
  toFun x i := if i ∈ S then x i else 0
  map_add' x y := by ext i; by_cases h : i ∈ S <;> simp [h]
  map_smul' c x := by ext i; by_cases h : i ∈ S <;> simp [h]

@[simp] theorem proj_apply (S : Finset ι) (x : ι → F) (i : ι) :
    proj S x i = if i ∈ S then x i else 0 := rfl

theorem proj_apply_of_mem {S : Finset ι} {i : ι} (h : i ∈ S) (x : ι → F) :
    proj S x i = x i := by simp [h]

theorem proj_apply_of_not_mem {S : Finset ι} {i : ι} (h : i ∉ S) (x : ι → F) :
    proj S x i = 0 := by simp [h]

@[simp] theorem proj_proj (S T : Finset ι) (x : ι → F) : proj S (proj T x) = proj (S ∩ T) x := by
  ext i; by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [hS, hT]

theorem proj_proj_self (S : Finset ι) (x : ι → F) : proj S (proj S x) = proj S x := by simp

@[simp] theorem proj_empty (x : ι → F) : proj (∅ : Finset ι) x = 0 := by ext i; simp

@[simp] theorem proj_univ [Fintype ι] (x : ι → F) : proj (Finset.univ : Finset ι) x = x := by
  ext i; simp

theorem proj_proj_of_subset {S T : Finset ι} (h : S ⊆ T) (x : ι → F) :
    proj S (proj T x) = proj S x := by
  rw [proj_proj, Finset.inter_eq_left.mpr h]

theorem proj_proj_of_subset' {S T : Finset ι} (h : S ⊆ T) (x : ι → F) :
    proj T (proj S x) = proj S x := by
  rw [proj_proj, Finset.inter_eq_right.mpr h]

theorem proj_proj_of_disjoint {S T : Finset ι} (h : Disjoint S T) (x : ι → F) :
    proj S (proj T x) = 0 := by
  rw [proj_proj, Finset.disjoint_iff_inter_eq_empty.mp h, proj_empty]

theorem proj_add_proj_compl [Fintype ι] (S : Finset ι) (x : ι → F) :
    proj S x + proj Sᶜ x = x := by
  ext i; by_cases h : i ∈ S <;> simp [h]

theorem proj_compl_add_proj [Fintype ι] (S : Finset ι) (x : ι → F) :
    proj Sᶜ x + proj S x = x := by
  rw [add_comm, proj_add_proj_compl]

theorem proj_union_of_disjoint {S T : Finset ι} (h : Disjoint S T) (x : ι → F) :
    proj (S ∪ T) x = proj S x + proj T x := by
  ext i
  by_cases hS : i ∈ S
  · have hT : i ∉ T := Finset.disjoint_left.mp h hS
    simp [hS, hT]
  · by_cases hT : i ∈ T <;> simp [hS, hT]

theorem proj_sdiff [Fintype ι] (S T : Finset ι) (x : ι → F) :
    proj (T \ S) x = proj T (proj Sᶜ x) := by
  rw [proj_proj, Finset.sdiff_eq_inter_compl]

theorem proj_eq_self_iff {S : Finset ι} {x : ι → F} : proj S x = x ↔ ∀ i, i ∉ S → x i = 0 := by
  constructor
  · intro h i hi
    rw [← congrFun h i, proj_apply_of_not_mem hi]
  · intro h
    ext i
    by_cases hi : i ∈ S
    · simp [hi]
    · simp [hi, h i hi]

/-- The register subspace `V_S`, as a submodule: the vectors vanishing outside `S`. -/
def register (S : Finset ι) : Submodule F (ι → F) := LinearMap.range (proj S)

theorem mem_register_iff {S : Finset ι} {x : ι → F} : x ∈ register (F := F) S ↔ proj S x = x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact proj_proj_self S y
  · intro h
    exact ⟨x, h⟩

theorem proj_mem_register (S : Finset ι) (x : ι → F) : proj S x ∈ register (F := F) S :=
  ⟨x, rfl⟩

theorem register_mono {S T : Finset ι} (h : S ⊆ T) : register (F := F) S ≤ register T := by
  rintro x ⟨y, rfl⟩
  exact ⟨proj S y, proj_proj_of_subset' h y⟩

/-! ## Linear maps on a register subspace -/

variable (F) in
/-- A linear map on the register subspace `V_S`, presented as an endomorphism `L` of the
ambient space with `proj S ∘ L ∘ proj S = L`: it depends only on the coordinates in `S`, and its
values lie in `V_S`. This is the paper's `L₁ : V₁ → V₁`; the paper's shorthand
`x^{L₁} = L₁(x^{V₁})` is then just `L₁ x` (`RegLinear.apply_proj`). -/
structure RegLinear (S : Finset ι) where
  /-- The underlying endomorphism of the ambient space. -/
  toLinearMap : (ι → F) →ₗ[F] (ι → F)
  /-- `L = proj S ∘ L ∘ proj S`. -/
  proj_comp_proj' : ∀ x, proj S (toLinearMap (proj S x)) = toLinearMap x

namespace RegLinear

variable {S T : Finset ι}

instance : FunLike (RegLinear F S) (ι → F) (ι → F) where
  coe L := L.toLinearMap
  coe_injective L L' h := by
    obtain ⟨L, _⟩ := L
    obtain ⟨L', _⟩ := L'
    congr
    exact DFunLike.coe_injective h

instance : LinearMapClass (RegLinear F S) F (ι → F) (ι → F) where
  map_add L := L.toLinearMap.map_add
  map_smulₛₗ L := L.toLinearMap.map_smul

@[simp] theorem coe_toLinearMap (L : RegLinear F S) : ⇑L.toLinearMap = ⇑L := rfl

@[simp] theorem toLinearMap_apply (L : RegLinear F S) (x : ι → F) : L.toLinearMap x = L x := rfl

theorem proj_comp_proj (L : RegLinear F S) (x : ι → F) : proj S (L (proj S x)) = L x :=
  L.proj_comp_proj' x

/-- The values of `L` lie in `V_S`. -/
@[simp] theorem proj_apply (L : RegLinear F S) (x : ι → F) : proj S (L x) = L x := by
  conv_lhs => rw [← L.proj_comp_proj x]
  rw [proj_proj_self, L.proj_comp_proj]

/-- `L` reads only the coordinates in `S`: `L(x^{V_S}) = L x`. -/
@[simp] theorem apply_proj (L : RegLinear F S) (x : ι → F) : L (proj S x) = L x := by
  rw [← L.proj_comp_proj (proj S x), proj_proj_self, L.proj_comp_proj]

theorem apply_proj_of_subset (L : RegLinear F S) (h : S ⊆ T) (x : ι → F) :
    L (proj T x) = L x := by
  rw [← L.apply_proj (proj T x), proj_proj_of_subset h, L.apply_proj]

theorem proj_apply_of_subset (L : RegLinear F S) (h : S ⊆ T) (x : ι → F) :
    proj T (L x) = L x := by
  rw [← L.proj_apply x, proj_proj_of_subset' h, L.proj_apply]

theorem apply_proj_of_disjoint (L : RegLinear F S) (h : Disjoint S T) (x : ι → F) :
    L (proj T x) = 0 := by
  rw [← L.apply_proj (proj T x), proj_proj_of_disjoint h, map_zero]

theorem proj_apply_of_disjoint (L : RegLinear F S) (h : Disjoint T S) (x : ι → F) :
    proj T (L x) = 0 := by
  rw [← L.proj_apply x, proj_proj_of_disjoint h]

theorem apply_proj_compl [Fintype ι] (L : RegLinear F S) (x : ι → F) : L (proj Sᶜ x) = 0 :=
  L.apply_proj_of_disjoint disjoint_compl_right x

theorem proj_compl_apply [Fintype ι] (L : RegLinear F S) (x : ι → F) : proj Sᶜ (L x) = 0 :=
  L.proj_apply_of_disjoint disjoint_compl_left x

@[ext] theorem ext {L L' : RegLinear F S} (h : ∀ x, L x = L' x) : L = L' := DFunLike.ext L L' h

instance : Zero (RegLinear F S) := ⟨⟨0, fun _ => by simp⟩⟩

@[simp] theorem zero_apply (x : ι → F) : (0 : RegLinear F S) x = 0 := rfl

/-- The identity of `V_S`, which is `proj S` on the ambient space. -/
def id (S : Finset ι) : RegLinear F S := ⟨proj S, fun x => by simp⟩

@[simp] theorem id_apply (x : ι → F) : RegLinear.id (F := F) S x = proj S x := rfl

/-- Compress an endomorphism of the ambient space to a map on `V_S`: `proj S ∘ L ∘ proj S`. -/
def ofLinearMap (S : Finset ι) (L : (ι → F) →ₗ[F] (ι → F)) : RegLinear F S :=
  ⟨proj S ∘ₗ L ∘ₗ proj S, fun x => by simp⟩

@[simp] theorem ofLinearMap_apply (L : (ι → F) →ₗ[F] (ι → F)) (x : ι → F) :
    ofLinearMap S L x = proj S (L (proj S x)) := rfl

/-- A map on `V_S` is a map on `V_T` whenever `S ⊆ T`. -/
def castLE (h : S ⊆ T) (L : RegLinear F S) : RegLinear F T :=
  ⟨L.toLinearMap, fun x => by
    simp only [toLinearMap_apply, L.apply_proj_of_subset h, L.proj_apply_of_subset h]⟩

@[simp] theorem castLE_apply (h : S ⊆ T) (L : RegLinear F S) (x : ι → F) :
    L.castLE h x = L x := rfl

/-- The sum of a map on `V_S` and a map on `V_T`, as a map on `V_{S ∪ T}`: their direct sum
when `S` and `T` are disjoint. -/
def directSum (L : RegLinear F S) (M : RegLinear F T) : RegLinear F (S ∪ T) :=
  ⟨L.toLinearMap + M.toLinearMap, fun x => by
    simp only [LinearMap.add_apply, toLinearMap_apply, map_add,
      L.apply_proj_of_subset Finset.subset_union_left,
      M.apply_proj_of_subset Finset.subset_union_right,
      L.proj_apply_of_subset Finset.subset_union_left,
      M.proj_apply_of_subset Finset.subset_union_right]⟩

@[simp] theorem directSum_apply (L : RegLinear F S) (M : RegLinear F T) (x : ι → F) :
    L.directSum M x = L x + M x := rfl

end RegLinear

end MIPRE.CL
