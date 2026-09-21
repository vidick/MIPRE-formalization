/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.RegisterMixing
import MIPRE.Foundations.CL.Register

/-! # The concrete coordinate splits for nested CL registers -/

noncomputable section

namespace MIPRE.Introspection

open Finset Classical

set_option linter.unusedSectionVars false

variable {ι F : Type*} [Fintype ι] [DecidableEq ι]

/-- Splitting an ambient assignment into a register and its complement. -/
def ambientSplit (V : Finset ι) : (ι → F) ≃ (V → F) × (↥(Vᶜ) → F) where
  toFun v := (fun i => v i, fun i => v i)
  invFun p i := if h : i ∈ V then p.1 ⟨i, h⟩ else p.2 ⟨i, mem_compl.mpr h⟩
  left_inv v := by funext i; dsimp only; split <;> rfl
  right_inv p := by
    apply Prod.ext
    · funext i
      simp only [dif_pos i.property]
    · funext i
      simp only [dif_neg (mem_compl.mp i.property)]

/-- Split `V` into the selected coordinates `U`, enumerated by `Fin`, and `V \ U`.
This is an actual coordinate restriction and assembly, rather than a cardinality choice. -/
def coordinateSplit (U V : Finset ι) (hUV : U ⊆ V) :
    (V → F) ≃ (Fin (Fintype.card U) → F) × (↥(V \ U) → F) where
  toFun v := (fun j => v ⟨(Fintype.equivFin U).symm j,
    hUV ((Fintype.equivFin U).symm j).property⟩,
    fun i => v ⟨i, (mem_sdiff.mp i.property).1⟩)
  invFun p i := if h : i.val ∈ U then p.1 (Fintype.equivFin U ⟨i, h⟩)
    else p.2 ⟨i, mem_sdiff.mpr ⟨i.property, h⟩⟩
  left_inv v := by
    funext i
    dsimp only
    split <;> simp only [Equiv.symm_apply_apply]
  right_inv p := by
    apply Prod.ext
    · funext j
      simp only [dif_pos ((Fintype.equivFin U).symm j).property]
      change p.1 ((Fintype.equivFin U) ((Fintype.equivFin U).symm j)) = p.1 j
      rw [Equiv.apply_symm_apply]
    · funext i
      simp only [dif_neg (mem_sdiff.mp i.property).2]

variable [Field F]

/-- Insert an enumerated vector into its ambient register, setting all other coordinates to zero. -/
def coordinateInsert (U : Finset ι) : (Fin (Fintype.card U) → F) →ₗ[F] (ι → F) where
  toFun v i := if h : i ∈ U then v (Fintype.equivFin U ⟨i, h⟩) else 0
  map_add' v w := by funext i; by_cases hi : i ∈ U <;> simp [hi]
  map_smul' c v := by funext i; by_cases hi : i ∈ U <;> simp [hi]

/-- Restrict the ambient assignment to the enumerated register. -/
def coordinateRestrict (U : Finset ι) : (ι → F) →ₗ[F] (Fin (Fintype.card U) → F) where
  toFun v j := v ((Fintype.equivFin U).symm j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem coordinateRestrict_insert (U : Finset ι)
    (v : Fin (Fintype.card U) → F) : coordinateRestrict U (coordinateInsert U v) = v := by
  funext j
  simp only [coordinateRestrict, coordinateInsert, LinearMap.coe_mk, AddHom.coe_mk,
    dif_pos ((Fintype.equivFin U).symm j).property]
  change v ((Fintype.equivFin U) ((Fintype.equivFin U).symm j)) = v j
  rw [Equiv.apply_symm_apply]

theorem coordinateInsert_restrict (U : Finset ι) (v : ι → F) :
    coordinateInsert U (coordinateRestrict U v) = CL.proj U v := by
  funext i
  by_cases hi : i ∈ U
  · simp only [coordinateInsert, coordinateRestrict, LinearMap.coe_mk, AddHom.coe_mk,
      dif_pos hi, Equiv.symm_apply_apply, CL.proj_apply, if_pos hi]
  · simp only [coordinateInsert, LinearMap.coe_mk, AddHom.coe_mk, dif_neg hi,
      CL.proj_apply, if_neg hi]

/-- The paper's map on `U` in the coordinate presentation used by the Pauli library. -/
def coordinateLinear {U : Finset ι} (L : CL.RegLinear F U) :
    (Fin (Fintype.card U) → F) →ₗ[F] (Fin (Fintype.card U) → F) :=
  coordinateRestrict U ∘ₗ L.toLinearMap ∘ₗ coordinateInsert U

/-- Restricting the ambient CL linear map commutes with passing to register coordinates. -/
theorem coordinateLinear_restrict {U : Finset ι} (L : CL.RegLinear F U) (v : ι → F) :
    coordinateLinear L (coordinateRestrict U v) = coordinateRestrict U (L v) := by
  simp only [coordinateLinear, LinearMap.comp_apply, coordinateInsert_restrict,
    CL.RegLinear.toLinearMap_apply, CL.RegLinear.apply_proj]

/-- Reassembling the coordinate result recovers the original CL linear map exactly. -/
theorem coordinateInsert_linear {U : Finset ι} (L : CL.RegLinear F U)
    (v : Fin (Fintype.card U) → F) :
    coordinateInsert U (coordinateLinear L v) = L (coordinateInsert U v) := by
  simp only [coordinateLinear, LinearMap.comp_apply, coordinateInsert_restrict,
    CL.RegLinear.toLinearMap_apply, CL.RegLinear.proj_apply]

end MIPRE.Introspection

end
