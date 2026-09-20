/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.SAT.FrobeniusAction

/-! # A normal element from primitive Frobenius projections -/

noncomputable section

namespace MIPRE.SAT

open Cost LowDegree LowDegree.BinaryLinear

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- Deterministically select the first nonzero element, with zero as the empty default. -/
def firstNonzero {E : Type*} [Zero E] [DecidableEq E] : List E → E
  | [] => 0
  | a :: l => if a = 0 then firstNonzero l else a

theorem firstNonzero_eq_zero_iff {E : Type*} [Zero E] [DecidableEq E] (l : List E) :
    firstNonzero l = 0 ↔ ∀ a ∈ l, a = 0 := by
  induction l with
  | nil => simp [firstNonzero]
  | cons a l ih => by_cases h : a = 0 <;> simp [firstNonzero, h, ih]

theorem firstNonzero_property {E : Type*} [Zero E] [DecidableEq E]
    (P : E → Prop) (hzero : P 0) (l : List E) (hl : ∀ a ∈ l, P a) : P (firstNonzero l) := by
  induction l with
  | nil => exact hzero
  | cons a l ih =>
    unfold firstNonzero
    split
    · exact ih (fun b hb => hl b (by simp [hb]))
    · exact hl a (by simp)

/-- Scan the polynomial basis for the first nonzero image of a cyclic operator. -/
def shoupProjectedVector (k : ℕ) (hk : 1 ≤ k) [NeZero k]
    (e : AddMonoidAlgebra (ZMod 2) (Fin k)) : (shoupBinField k hk).carrier :=
  firstNonzero (List.ofFn (fun j => shoupFrobeniusAction k hk e (shoupPowerBasis k hk j)))

theorem shoupProjectedVector_ne_zero (k : ℕ) (hk : 1 ≤ k) [NeZero k]
    (e : AddMonoidAlgebra (ZMod 2) (Fin k)) (he : e ≠ 0) :
    shoupProjectedVector k hk e ≠ 0 := by
  intro hz
  obtain ⟨j, hj⟩ := shoupFrobeniusAction_exists_basis_image k hk e he
  exact hj ((firstNonzero_eq_zero_iff _).mp hz _ (List.mem_ofFn.mpr ⟨j, rfl⟩))

theorem shoupProjectedVector_supported (k : ℕ) (hk : 1 ≤ k) [NeZero k]
    (e : AddMonoidAlgebra (ZMod 2) (Fin k)) (he : e * e = e) :
    shoupFrobeniusAction k hk e (shoupProjectedVector k hk e) = shoupProjectedVector k hk e := by
  apply firstNonzero_property (fun a => shoupFrobeniusAction k hk e a = a) (map_zero _) _
  intro a ha
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
  change (shoupFrobeniusAction k hk e * shoupFrobeniusAction k hk e) _ = _
  rw [← map_mul, he]

/-- Sum the selected nonzero projected vectors, in the computed component order. -/
def shoupNormalElement (k : ℕ) (hk : 1 ≤ k) [NeZero k] : (shoupBinField k hk).carrier :=
  ∑ i : Fin (groupComponents k).length, shoupProjectedVector k hk ((groupComponents k).get i)

theorem shoupNormalElement_projection (k : ℕ) (hk : 1 ≤ k) [NeZero k]
    (j : Fin (groupComponents k).length) :
    shoupFrobeniusAction k hk ((groupComponents k).get j) (shoupNormalElement k hk) =
      shoupProjectedVector k hk ((groupComponents k).get j) := by
  let l := groupComponents k
  have hl := groupComponents_family k
  have ho (i : Fin l.length) (hij : i ≠ j) : l.get j * l.get i = 0 := by
    rcases lt_or_gt_of_ne hij with h | h
    · rw [mul_comm]
      exact hl.orthogonal.rel_get_of_lt h
    · exact hl.orthogonal.rel_get_of_lt h
  have hx (i : Fin l.length) :
      shoupFrobeniusAction k hk (l.get j) (shoupProjectedVector k hk (l.get i)) =
        if i = j then shoupProjectedVector k hk (l.get j) else 0 := by
    by_cases hij : i = j
    · subst i
      rw [if_pos rfl]
      exact shoupProjectedVector_supported k hk _ (hl.idempotent _ (List.get_mem _ _))
    · rw [if_neg hij, ← shoupProjectedVector_supported k hk (l.get i)
        (hl.idempotent _ (List.get_mem _ _))]
      change (shoupFrobeniusAction k hk (l.get j) * shoupFrobeniusAction k hk (l.get i)) _ = 0
      rw [← map_mul, ho i hij, map_zero, LinearMap.zero_apply]
  change shoupFrobeniusAction k hk (l.get j) (∑ i, shoupProjectedVector k hk (l.get i)) = _
  rw [map_sum]
  simp only [hx, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rfl

/-- Evaluation at the constructed element is a linear map from the cyclic algebra. -/
def shoupNormalOrbitMap (k : ℕ) (hk : 1 ≤ k) [NeZero k] :
    AddMonoidAlgebra (ZMod 2) (Fin k) →ₗ[ZMod 2] (shoupBinField k hk).carrier where
  toFun r := shoupFrobeniusAction k hk r (shoupNormalElement k hk)
  map_add' r s := by simp
  map_smul' c r := by simp

/-- No nonzero cyclic operator kills the sum: each primitive component has its own nonzero image. -/
theorem shoupNormalOrbitMap_injective (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k) :
    Function.Injective (shoupNormalOrbitMap k hk) := by
  haveI : Finite (AddMonoidAlgebra (ZMod 2) (Fin k)) :=
    Finite.of_injective _ (groupCoordinates k).injective
  apply (injective_iff_map_eq_zero (shoupNormalOrbitMap k hk)).mpr
  intro r hr
  have hsq : Function.Bijective (fun x : AddMonoidAlgebra (ZMod 2) (Fin k) => x * x) :=
    mul_self_bijective (ZMod.charP 2) (by simpa using hodd)
  have he (i : Fin (groupComponents k).length) : (groupComponents k).get i * r = 0 := by
    let e := (groupComponents k).get i
    have hem := List.get_mem (groupComponents k) i
    have hep := groupComponents_primitive k e hem
    by_contra hne
    obtain ⟨y, hy⟩ := hep.exists_mul_eq hsq (e * r) hne (by rw [← mul_assoc, hep.2.1])
    have h : shoupFrobeniusAction k hk e (shoupNormalElement k hk) = 0 := by
      calc
        shoupFrobeniusAction k hk e (shoupNormalElement k hk) =
            shoupFrobeniusAction k hk ((e * r) * y) (shoupNormalElement k hk) := by rw [hy]
        _ = shoupFrobeniusAction k hk (e * y)
            (shoupFrobeniusAction k hk r (shoupNormalElement k hk)) := by
          rw [show (e * r) * y = (e * y) * r by ring, map_mul]
          rfl
        _ = 0 := by change shoupFrobeniusAction k hk (e * y) (shoupNormalOrbitMap k hk r) = 0
                    rw [hr, map_zero]
    rw [shoupNormalElement_projection] at h
    exact shoupProjectedVector_ne_zero k hk e hep.1 h
  have hs : (∑ i : Fin (groupComponents k).length, (groupComponents k).get i) = 1 := by
    simpa using (groupComponents_family k).sum_eq_one
  calc
    r = (∑ i : Fin (groupComponents k).length, (groupComponents k).get i) * r := by rw [hs, one_mul]
    _ = 0 := by rw [Finset.sum_mul]; simp only [he, Finset.sum_const_zero]

/-- The orbit of the computed normal element is linearly independent. -/
theorem shoupNormalElement_linearIndependent (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k) :
    LinearIndependent (ZMod 2) (fun i : Fin k => shoupNormalElement k hk ^ (2 ^ i.val)) := by
  have h := (Module.Basis.ofEquivFun (groupCoordinates k)).linearIndependent.map'
    (shoupNormalOrbitMap k hk) (LinearMap.ker_eq_bot.mpr (shoupNormalOrbitMap_injective k hk hodd))
  suffices he : (fun i : Fin k => shoupNormalElement k hk ^ (2 ^ i.val)) =
      (shoupNormalOrbitMap k hk) ∘ (Module.Basis.ofEquivFun (groupCoordinates k)) by
    rw [he]
    exact h
  funext i
  simp only [Function.comp_apply, Module.Basis.coe_ofEquivFun]
  change _ = shoupFrobeniusAction k hk ((groupCoordinates k).symm (Pi.single i 1)) _
  rw [shoupFrobeniusAction_apply]
  simp [groupCoordinates_symm_apply]

/-- The explicitly constructed Frobenius orbit as a basis. -/
def shoupNormalBasis (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k) :
    Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier :=
  basisOfLinearIndependentOfCardEqFinrank (shoupNormalElement_linearIndependent k hk hodd)
    (by simp [shoupBinField_finrank k hk])

@[simp] theorem shoupNormalBasis_apply (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (i : Fin k) : shoupNormalBasis k hk hodd i = shoupNormalElement k hk ^ (2 ^ i.val) := by
  rw [shoupNormalBasis, coe_basisOfLinearIndependentOfCardEqFinrank]

theorem shoupNormalBasis_normal (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k) :
    IsNormalBasis (shoupNormalBasis k hk hodd) := by
  refine ⟨shoupNormalElement k hk, fun i => ?_⟩
  simp

end MIPRE.SAT

end
