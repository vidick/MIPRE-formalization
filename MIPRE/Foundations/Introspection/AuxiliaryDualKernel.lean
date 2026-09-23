/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AuxiliaryDualProgram
import MIPRE.Foundations.Introspection.RegisterCoordinates

/-! # Coordinate-independent kernel tests for auxiliary dual answers

The semantic dual uses a chosen local enumeration, but equality of its outputs
is characterized intrinsically by the ambient dot product. The general finite
index API permits coordinate transport without transporting chosen complements.
-/

noncomputable section
namespace MIPRE.Introspection.AuxiliaryDual
open Finset
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {S : Finset ι}

/-- The semantic local dual, inserted back into the ambient register. -/
def registerDual (L : CL.RegLinear F S) : (ι → F) →ₗ[F] (ι → F) :=
  coordinateInsert S ∘ₗ CL.lperp (coordinateLinear L) ∘ₗ coordinateRestrict S

theorem coordinateInsert_injective : Function.Injective (coordinateInsert (F := F) S) := by
  intro x y h
  simpa only [coordinateRestrict_insert] using congrArg (coordinateRestrict S) h

theorem coordinate_dot_sum (x y : ι → F) :
    CL.dotForm F (Fintype.card S) (coordinateRestrict S x) (coordinateRestrict S y) =
      ∑ i, x i * CL.proj S y i := by
  calc
    _ = ∑ i : S, x i * y i := by
      simpa only [CL.dotForm_apply, coordinateRestrict, LinearMap.coe_mk, AddHom.coe_mk] using
        (Fintype.equivFin S).symm.sum_comp (fun i : S => x i * y i)
    _ = ∑ i ∈ S, x i * y i := Finset.sum_coe_sort S (fun i => x i * y i)
    _ = _ := by simp [CL.proj_apply, mul_ite]

theorem coordinateLinear_zero_iff (L : CL.RegLinear F S) (x : ι → F) :
    coordinateLinear L (coordinateRestrict S x) = 0 ↔ L x = 0 := by
  constructor
  · intro h
    have hi := congrArg (coordinateInsert S) h
    simpa only [coordinateInsert_linear, coordinateInsert_restrict,
      CL.RegLinear.apply_proj, map_zero] using hi
  · intro h
    rw [coordinateLinear_restrict, h, map_zero]

theorem registerDual_zero_iff_local (L : CL.RegLinear F S) (x : ι → F) :
    registerDual L x = 0 ↔
      coordinateRestrict S x ∈ CL.perp (coordinateLinear L).ker := by
  change coordinateInsert S (CL.lperp (coordinateLinear L) (coordinateRestrict S x)) = 0 ↔ _
  rw [← map_zero (coordinateInsert (F := F) S), coordinateInsert_injective.eq_iff]
  change coordinateRestrict S x ∈ (CL.lperp (coordinateLinear L)).ker ↔ _
  rw [CL.ker_lperp]

/-- Intrinsic kernel characterization on any finite ambient coordinate type. -/
theorem registerDual_zero_iff_dot (L : CL.RegLinear F S) (x : ι → F) :
    registerDual L x = 0 ↔ ∀ y : ι → F, L y = 0 → ∑ i, y i * CL.proj S x i = 0 := by
  rw [registerDual_zero_iff_local, CL.mem_perp]
  constructor
  · intro h y hy
    have hc := h (coordinateRestrict S y) ((coordinateLinear_zero_iff L y).mpr hy)
    exact (coordinate_dot_sum y x).symm.trans hc
  · intro h y hy
    change coordinateLinear L y = 0 at hy
    have hk : L (coordinateInsert S y) = 0 := by
      rw [← coordinateInsert_linear, hy, map_zero]
    have hc := h (coordinateInsert S y) hk
    rw [← coordinate_dot_sum, coordinateRestrict_insert] at hc
    exact hc

theorem registerDual_eq_iff_dot (L : CL.RegLinear F S) (x y : ι → F) :
    registerDual L x = registerDual L y ↔
      ∀ z : ι → F, L z = 0 → ∑ i, z i * CL.proj S (x - y) i = 0 := by
  rw [← registerDual_zero_iff_dot, map_sub, sub_eq_zero]

theorem registerDual_idempotent (L : CL.RegLinear F S) (x : ι → F) :
    registerDual L (registerDual L x) = registerDual L x := by
  simp only [registerDual, LinearMap.comp_apply, coordinateRestrict_insert]
  congr 1
  apply map_canonLin_of_le_ker
  rw [CL.ker_lperp]

section FiniteCoordinates
variable {n : ℕ} {T : Finset (Fin n)}

theorem coordinate_dot (x y : Fin n → F) :
    CL.dotForm F (Fintype.card T) (coordinateRestrict T x) (coordinateRestrict T y) =
      CL.dotForm F n x (CL.proj T y) := coordinate_dot_sum x y

/-- The local-coordinate dual kernel can be tested on a projected ambient vector. -/
theorem registerDual_zero_iff (L : CL.RegLinear F T) (x : Fin n → F) :
    registerDual L x = 0 ↔ CL.proj T x ∈ CL.perp L.toLinearMap.ker := by
  simpa only [CL.mem_perp, CL.dotForm_apply, LinearMap.mem_ker,
    CL.RegLinear.toLinearMap_apply] using registerDual_zero_iff_dot L x

/-- Comparing two semantic dual labels is an ambient row-space membership test. -/
theorem registerDual_eq_iff (L : CL.RegLinear F T) (x y : Fin n → F) :
    registerDual L x = registerDual L y ↔
      CL.proj T (x - y) ∈ CL.perp L.toLinearMap.ker := by
  rw [← registerDual_zero_iff, map_sub, sub_eq_zero]

end FiniteCoordinates
end MIPRE.Introspection.AuxiliaryDual
end
