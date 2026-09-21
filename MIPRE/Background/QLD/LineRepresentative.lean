/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.LineRepresentativeProg
import MIPRE.Background.LIDT.Adapter.Geometry

/-! # The executable representative is the Pauli sampler's canonical point

This bridge identifies the uniform Shoup program with the actual `canonLin`
used by both axis and diagonal question maps, including the zero direction.
-/

noncomputable section
namespace MIPRE.QLD.PauliCL
open Introspection.LineProgram SAT

theorem representative_eq_canonLin {F : Type*} [Field F] [DecidableEq F] {n : ℕ}
    (u v : Fin n → F) : representative u v = CL.canonLin (Submodule.span F {v}) u := by
  by_cases hv : ∃ j, v j ≠ 0
  · rw [representative_nonzero u v hv, LIDT.Adapter.rep_eq hv]
  · have hz : v = 0 := by
      funext j
      exact not_not.mp fun h => hv ⟨j, h⟩
    subst v
    simp only [representative, smul_zero, sub_zero]
    have h := CL.sub_canonLin_mem (Submodule.span F {(0 : Fin n → F)}) u
    have he : u - CL.canonLin (Submodule.span F {(0 : Fin n → F)}) u = 0 := by
      simpa using h
    exact sub_eq_zero.mp he

/-- The actual total polynomial-time program computes the canonical base point
used in the seeded axis and diagonal Pauli questions. -/
theorem lineRepresentativeProg_canonLin (k : ℕ) (hk : 1 ≤ k) {n : ℕ}
    (u v : Fin n → (shoupBinField k hk).carrier) :
    lineRepresentativeProg (Cost.unary k, (shoupBinField k hk).vecBits u,
      (shoupBinField k hk).vecBits v) =
      (shoupBinField k hk).vecBits (CL.canonLin
        (Submodule.span (shoupBinField k hk).carrier {v}) u) := by
  rw [lineRepresentativeProg_correct, representative_eq_canonLin]

end MIPRE.QLD.PauliCL
end
