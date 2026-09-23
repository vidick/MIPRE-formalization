/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AuxiliaryCanonicalProgram

/-! # Executable canonical dual of a binary linear map

The rows of a matrix span the dot-product orthogonal complement of its
kernel. Canonical elimination of those rows therefore computes the exact
`CL.lperp`, including for singular matrices and in dimension zero.
-/

noncomputable section
namespace MIPRE.Introspection.AuxiliaryDual

open Cost Cost.PolyTimeFun LowDegree.BinaryLinear
set_option backward.isDefEq.respectTransparency false

variable {F : Type*} [Field F] {m n : ℕ}

/-- A linear map killing a subspace also kills the part removed by canonical
reduction. This permits changing quotient representatives without identifying
two coordinate enumerations. -/
theorem map_canonLin_of_le_ker {V : Type*} [AddCommGroup V] [Module F V]
    (S : Submodule F (Fin n → F)) (D : (Fin n → F) →ₗ[F] V)
    (hS : S ≤ D.ker) (x : Fin n → F) : D (CL.canonLin S x) = D x := by
  have h := hS (CL.sub_canonLin_mem S x)
  change D (x - CL.canonLin S x) = 0 at h
  rw [map_sub, sub_eq_zero] at h
  exact h.symm

/-- Orthogonality to all matrix rows is precisely the kernel condition. -/
theorem perp_span_rows (A : Matrix (Fin m) (Fin n) F) :
    CL.perp (Submodule.span F (Set.range A)) = A.mulVecLin.ker := by
  ext x
  rw [CL.mem_perp, LinearMap.mem_ker]
  constructor
  · intro h
    funext i
    exact h (A i) (Submodule.subset_span ⟨i, rfl⟩)
  · intro hx y hy
    have hs : Submodule.span F (Set.range A) ≤ (CL.dotForm F n x).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change CL.dotForm F n x (A i) = 0
      rw [CL.dotForm_comm]
      exact congrFun hx i
    have h := hs hy
    rw [LinearMap.mem_ker, CL.dotForm_comm] at h
    exact h

/-- The matrix rows generate the kernel's dot-product orthogonal complement. -/
theorem span_rows_eq_perp_ker (A : Matrix (Fin m) (Fin n) F) :
    Submodule.span F (Set.range A) = CL.perp A.mulVecLin.ker := by
  rw [← perp_span_rows A, CL.perp_perp]

/-- Uniform polynomial-time evaluation of a square binary map's canonical dual. -/
def dualProg : PolyTimeFun (List BitStr × BitStr) BitStr :=
  AuxiliaryCanonical.canonicalProg

theorem dualProg_correct (A : Matrix (Fin n) (Fin n) (ZMod 2))
    (v : Fin n → ZMod 2) :
    dualProg (matrixBits A, vectorBits v) =
      vectorBits (CL.lperp A.mulVecLin v) := by
  have hr : {x | x ∈ List.ofFn A} = Set.range A := by
    ext x
    simp only [Set.mem_ofPred_eq, List.mem_ofFn, Set.mem_range]
  have hb : matrixBits A = (List.ofFn A).map vectorBits := by
    simp only [matrixBits, List.map_ofFn, Function.comp_def]
  rw [dualProg, hb, AuxiliaryCanonical.canonicalProg_correct, hr, span_rows_eq_perp_ker]
  rfl

/-- Membership in the supplied row span, tested by exact canonical reduction.
The zero vector has the input vector's width, so malformed widths do not become
an implicit promise about the program's termination. -/
def rowSpaceCheck : PolyTimeFun (List BitStr × BitStr) Bool :=
  SAT.ArrayProg.eqBits.comp (AuxiliaryCanonical.canonicalProg.pair
    ((map (const false)).comp snd))

theorem rowSpaceCheck_correct (vs : List (Fin n → ZMod 2)) (v : Fin n → ZMod 2) :
    rowSpaceCheck (vs.map vectorBits, vectorBits v) = true ↔
      v ∈ Submodule.span (ZMod 2) {x | x ∈ vs} := by
  change decide (AuxiliaryCanonical.canonicalProg (vs.map vectorBits, vectorBits v) =
    (vectorBits v).map (fun _ => false)) = true ↔ _
  rw [decide_eq_true_eq, AuxiliaryCanonical.canonicalProg_correct]
  have hz : (vectorBits v).map (fun _ => false) = vectorBits (0 : Fin n → ZMod 2) := by
    simp [vectorBits, bit]
  have hinj : Function.Injective (vectorBits (n := n)) := by
    intro x y h
    simpa only [vectorValue_vectorBits] using congrArg (vectorValue n) h
  rw [hz, hinj.eq_iff]
  change v ∈ (CL.canonLin (Submodule.span (ZMod 2) {x | x ∈ vs})).ker ↔ _
  rw [CL.ker_canonLin]

/-- The executable test is independent of the choice of quotient representatives:
it detects the dot-product orthogonal complement of the matrix kernel. -/
theorem rowSpaceCheck_matrix (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (v : Fin n → ZMod 2) :
    rowSpaceCheck (matrixBits A, vectorBits v) = true ↔ v ∈ CL.perp A.mulVecLin.ker := by
  have hr : {x | x ∈ List.ofFn A} = Set.range A := by
    ext x
    simp only [Set.mem_ofPred_eq, List.mem_ofFn, Set.mem_range]
  have hb : matrixBits A = (List.ofFn A).map vectorBits := by
    simp only [matrixBits, List.map_ofFn, Function.comp_def]
  rw [hb, rowSpaceCheck_correct, hr, span_rows_eq_perp_ker]

end MIPRE.Introspection.AuxiliaryDual
end
