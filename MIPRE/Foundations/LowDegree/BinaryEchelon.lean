/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryElimination
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Field.ZMod

/-! # Triangular pivot bases and certified binary reduction -/

namespace MIPRE.LowDegree.BinaryLinear

variable {n t : ℕ}

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- In insertion order, each row has pivot one and every later row vanishes
at that pivot. Pivots need not be numerically ordered. -/
def IsPivotBasis : List (Pivot n t) → Prop
  | [] => True
  | p :: b => p.2.1 p.1 = 1 ∧ (∀ q ∈ b, q.2.1 p.1 = 0) ∧ IsPivotBasis b

theorem binary_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

theorem typedReduceStep_pivot_zero (r : Row n t) (p : Pivot n t)
    (hp : p.2.1 p.1 = 1) : (typedReduceStep r p).1 p.1 = 0 := by
  rcases binary_eq_zero_or_one (r.1 p.1) with h | h
  · simp [typedReduceStep, h]
  · simp only [typedReduceStep, h, if_true, Pi.add_apply, hp]
    decide

theorem typedReduceStep_preserves_zero (r : Row n t) (p : Pivot n t) (j : Fin n)
    (hr : r.1 j = 0) (hp : p.2.1 j = 0) : (typedReduceStep r p).1 j = 0 := by
  unfold typedReduceStep
  split <;> simp [hr, hp]

theorem typedReduce_preserves_zero (b : List (Pivot n t)) (r : Row n t) (j : Fin n)
    (hr : r.1 j = 0) (hb : ∀ p ∈ b, p.2.1 j = 0) : (typedReduce b r).1 j = 0 := by
  induction b generalizing r with
  | nil => exact hr
  | cons p b ih =>
    exact ih _ (typedReduceStep_preserves_zero r p j hr (hb p (by simp)))
      (fun q hq => hb q (by simp [hq]))

/-- Reducing against a triangular basis zeros all of its pivot coordinates. -/
theorem typedReduce_pivots_zero (b : List (Pivot n t)) (hb : IsPivotBasis b)
    (r : Row n t) : ∀ p ∈ b, (typedReduce b r).1 p.1 = 0 := by
  induction b generalizing r with
  | nil => simp
  | cons p b ih =>
    intro q hq
    rcases List.mem_cons.mp hq with hqp | hq
    · subst q
      exact typedReduce_preserves_zero b (typedReduceStep r p) p.1
        (typedReduceStep_pivot_zero r p hb.1) hb.2.1
    · exact ih hb.2.2 (typedReduceStep r p) q hq

/-- A reduced nonzero row can be appended at any of its nonzero coordinates. -/
theorem IsPivotBasis.append_reduced {b : List (Pivot n t)} (hb : IsPivotBasis b)
    (r : Row n t) (j : Fin n) (hj : (typedReduce b r).1 j = 1) :
    IsPivotBasis (b ++ [(j, typedReduce b r)]) := by
  have hz := typedReduce_pivots_zero b hb r
  generalize typedReduce b r = s at hj hz ⊢
  induction b with
  | nil => exact ⟨hj, by simp, trivial⟩
  | cons p b ih =>
    refine ⟨hb.1, ?_, ih hb.2.2 (fun q hq => hz q (by simp [hq]))⟩
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hb.2.1 q hq
    · obtain rfl := List.mem_singleton.mp hq
      exact hz p (by simp)

/-- The vector family extracted in insertion order. -/
def pivotVectors (b : List (Pivot n t)) : Fin b.length → (Fin n → ZMod 2) :=
  fun i => (b[i]).2.1

theorem pivotVectors_cons (p : Pivot n t) (b : List (Pivot n t)) :
    pivotVectors (p :: b) = Fin.cons p.2.1 (pivotVectors b) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- Triangular pivots certify linear independence of the stored vectors. -/
theorem IsPivotBasis.linearIndependent {b : List (Pivot n t)} (hb : IsPivotBasis b) :
    LinearIndependent (ZMod 2) (pivotVectors b) := by
  induction b with
  | nil =>
    dsimp only [List.length_nil]
    exact linearIndependent_empty_type
  | cons p b ih =>
    rw [pivotVectors_cons]
    apply (linearIndependent_finCons (K := ZMod 2) (v := pivotVectors b) (x := p.2.1)).mpr
    refine ⟨ih hb.2.2, ?_⟩
    let π : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 := LinearMap.proj p.1
    have hs : Submodule.span (ZMod 2) (Set.range (pivotVectors b)) ≤ π.ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact hb.2.1 b[i] (List.getElem_mem i.isLt)
    intro h
    have hz : p.2.1 p.1 = 0 := hs h
    rw [hb.1] at hz
    exact one_ne_zero hz

/-- A pivot basis contains at most the ambient dimension many rows. -/
theorem IsPivotBasis.length_le {b : List (Pivot n t)} (hb : IsPivotBasis b) :
    b.length ≤ n := by
  have h := hb.linearIndependent.fintype_card_le_finrank
  simpa using h

end MIPRE.LowDegree.BinaryLinear
