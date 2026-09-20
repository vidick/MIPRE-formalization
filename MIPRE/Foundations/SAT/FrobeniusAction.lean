/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.SAT.NormalGram
import MIPRE.Foundations.LowDegree.BinaryComponents

/-! # The faithful cyclic Frobenius representation -/

noncomputable section

namespace MIPRE.SAT

open Cost LowDegree LowDegree.BinaryLinear

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- A group-algebra coefficient vector acts as the corresponding linearized polynomial. -/
def shoupFrobeniusAction (k : ℕ) (hk : 1 ≤ k) [NeZero k] :
    AddMonoidAlgebra (ZMod 2) (Fin k) →ₐ[ZMod 2]
      Module.End (ZMod 2) (shoupBinField k hk).carrier :=
  AddMonoidAlgebra.lift (ZMod 2) _ _
    ((AlgEquiv.toLinearMapHom (ZMod 2) (shoupBinField k hk).carrier).comp
      (shoupFrobeniusCycle k hk))

theorem shoupFrobeniusAction_eq_sum (k : ℕ) (hk : 1 ≤ k) [NeZero k]
    (z : AddMonoidAlgebra (ZMod 2) (Fin k)) :
    shoupFrobeniusAction k hk z = ∑ i : Fin k, z.coeff i •
      (shoupFrobeniusCycle k hk (Multiplicative.ofAdd i)).toLinearMap := by
  rw [shoupFrobeniusAction, AddMonoidAlgebra.lift_apply,
    Finsupp.sum_fintype _ _ (by intro i; simp)]
  rfl

theorem shoupFrobeniusAction_apply (k : ℕ) (hk : 1 ≤ k) [NeZero k]
    (z : AddMonoidAlgebra (ZMod 2) (Fin k)) (a : (shoupBinField k hk).carrier) :
    shoupFrobeniusAction k hk z a = ∑ i : Fin k, z.coeff i • a ^ (2 ^ i.val) := by
  rw [shoupFrobeniusAction_eq_sum]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, AlgEquiv.toLinearMap_apply,
    shoupFrobeniusCycle_apply]

theorem shoupFrobeniusCycle_injective (k : ℕ) (hk : 1 ≤ k) [NeZero k] :
    Function.Injective (fun i : Fin k => shoupFrobeniusCycle k hk (Multiplicative.ofAdd i)) := by
  intro i j hij
  have he := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod 2)
    (shoupBinField k hk).carrier).injective
      (a₁ := (finCongr (shoupBinField_finrank k hk)).symm i)
      (a₂ := (finCongr (shoupBinField_finrank k hk)).symm j) hij
  exact (finCongr (shoupBinField_finrank k hk)).symm.injective he

/-- Faithfulness follows from independence of the distinct Frobenius automorphisms. -/
theorem shoupFrobeniusAction_injective (k : ℕ) (hk : 1 ≤ k) [NeZero k] :
    Function.Injective (shoupFrobeniusAction k hk) := by
  have hli : LinearIndependent (ZMod 2) (fun i : Fin k =>
      (shoupFrobeniusCycle k hk (Multiplicative.ofAdd i)).toLinearMap) :=
    (linearIndependent_algHom_toLinearMap' (ZMod 2)
      (shoupBinField k hk).carrier (shoupBinField k hk).carrier).comp
      (fun i => (shoupFrobeniusCycle k hk (Multiplicative.ofAdd i)).toAlgHom)
      (AlgEquiv.coe_toAlgHom_injective.comp (shoupFrobeniusCycle_injective k hk))
  apply (injective_iff_map_eq_zero (shoupFrobeniusAction k hk).toLinearMap).mpr
  intro z hz
  change shoupFrobeniusAction k hk z = 0 at hz
  rw [shoupFrobeniusAction_eq_sum] at hz
  have hc := (Fintype.linearIndependent_iff.mp hli) _ hz
  apply AddMonoidAlgebra.coeff_injective
  ext i
  exact hc i

/-- A nonzero cyclic operator has a nonzero image among the polynomial-basis vectors. -/
theorem shoupFrobeniusAction_exists_basis_image (k : ℕ) (hk : 1 ≤ k) [NeZero k]
    (z : AddMonoidAlgebra (ZMod 2) (Fin k)) (hz : z ≠ 0) :
    ∃ j : Fin k, shoupFrobeniusAction k hk z (shoupPowerBasis k hk j) ≠ 0 := by
  by_contra h
  push_neg at h
  have he : shoupFrobeniusAction k hk z = 0 :=
    (shoupPowerBasis k hk).ext (fun j => by simpa using h j)
  exact hz (shoupFrobeniusAction_injective k hk (he.trans (map_zero _).symm))

end MIPRE.SAT

end
