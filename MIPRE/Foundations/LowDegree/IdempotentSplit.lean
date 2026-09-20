/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.FiniteReducedComponents
import MIPRE.Foundations.LowDegree.BinaryEchelon

/-! # Deterministic refinement by binary idempotents -/

noncomputable section

namespace MIPRE.LowDegree

variable {R : Type*} [CommRing R] [DecidableEq R]

/-- Split a component by a fixed idempotent and omit its zero children. -/
def splitComponent (e b : R) : List R :=
  [e * b, e * (1 - b)].filter (fun x => decide (x ≠ 0))

theorem mem_splitComponent (e b x : R) :
    x ∈ splitComponent e b ↔ (x = e * b ∨ x = e * (1 - b)) ∧ x ≠ 0 := by
  simp [splitComponent, and_comm]

theorem splitComponent_sum (e b : R) : (splitComponent e b).sum = e := by
  have h : e * b + e * (1 - b) = e := by ring
  by_cases h₁ : e * b = 0 <;> by_cases h₂ : e * (1 - b) = 0 <;>
    simp [splitComponent, h₁, h₂] at h ⊢ <;> exact h

theorem splitComponent_factor {e b x : R} (hx : x ∈ splitComponent e b) :
    ∃ c, x = e * c := by
  rcases (mem_splitComponent e b x).mp hx with ⟨h | h, _⟩
  · exact ⟨b, h⟩
  · exact ⟨1 - b, h⟩

theorem one_sub_idempotent {b : R} (hb : b * b = b) : (1 - b) * (1 - b) = 1 - b := by
  calc
    (1 - b) * (1 - b) = 1 - b - b + b * b := by ring
    _ = 1 - b := by rw [hb]; ring

theorem mul_idempotent {e b : R} (he : e * e = e) (hb : b * b = b) :
    (e * b) * (e * b) = e * b := by
  calc
    (e * b) * (e * b) = (e * e) * (b * b) := by ring
    _ = e * b := by rw [he, hb]

theorem splitComponent_idempotent {e b : R} (he : e * e = e) (hb : b * b = b)
    {x : R} (hx : x ∈ splitComponent e b) : x * x = x := by
  rcases (mem_splitComponent e b x).mp hx with ⟨rfl | rfl, _⟩
  · exact mul_idempotent he hb
  · exact mul_idempotent he (one_sub_idempotent hb)

theorem splitComponent_pairwise (e : R) {b : R} (hb : b * b = b) :
    (splitComponent e b).Pairwise (fun x y => x * y = 0) := by
  apply List.Pairwise.filter
  have hc : (e * b) * (e * (1 - b)) = 0 := by
    calc
      (e * b) * (e * (1 - b)) = (e * e) * (b - b * b) := by ring
      _ = 0 := by rw [hb, sub_self, mul_zero]
  simp [hc]

/-- A finite complete family of nonzero orthogonal idempotents. -/
structure ComponentFamily (l : List R) : Prop where
  nonzero : ∀ e ∈ l, e ≠ 0
  idempotent : ∀ e ∈ l, e * e = e
  orthogonal : l.Pairwise (fun e f => e * f = 0)
  sum_eq_one : l.sum = 1

/-- Refine all current components in the fixed input order. -/
def splitComponents (l : List R) (b : R) : List R := l.flatMap (fun e => splitComponent e b)

theorem ComponentFamily.split {l : List R} (hl : ComponentFamily l) {b : R} (hb : b * b = b) :
    ComponentFamily (splitComponents l b) := by
  constructor
  · intro x hx
    obtain ⟨e, _, hx⟩ := List.mem_flatMap.mp hx
    exact ((mem_splitComponent e b x).mp hx).2
  · intro x hx
    obtain ⟨e, he, hx⟩ := List.mem_flatMap.mp hx
    exact splitComponent_idempotent (hl.idempotent e he) hb hx
  · apply List.pairwise_flatMap.mpr
    refine ⟨fun e _ => splitComponent_pairwise e hb, hl.orthogonal.imp ?_⟩
    intro e f hef x hx y hy
    obtain ⟨c, rfl⟩ := splitComponent_factor hx
    obtain ⟨d, rfl⟩ := splitComponent_factor hy
    calc
      (e * c) * (f * d) = (e * f) * (c * d) := by ring
      _ = 0 := by rw [hef, zero_mul]
  · have hs (l : List R) : (splitComponents l b).sum = l.sum := by
      induction l with
      | nil => rfl
      | cons e l ih =>
        simpa only [splitComponents, List.flatMap_cons, List.sum_append,
          splitComponent_sum, List.sum_cons] using congrArg (fun x => e + x) ih
    exact (hs l).trans hl.sum_eq_one

/-- A component is wholly inside or outside a supplied idempotent. -/
def DecidesComponent (e b : R) : Prop := e * b = 0 ∨ e * b = e

theorem splitComponent_decides {e b x : R} (hb : b * b = b) (hx : x ∈ splitComponent e b) :
    DecidesComponent x b := by
  rcases (mem_splitComponent e b x).mp hx with ⟨rfl | rfl, _⟩
  · right
    rw [mul_assoc, hb]
  · left
    calc
      (e * (1 - b)) * b = e * (b - b * b) := by ring
      _ = 0 := by rw [hb, sub_self, mul_zero]

theorem splitComponent_preserves {e b c x : R} (hc : DecidesComponent e c)
    (hx : x ∈ splitComponent e b) : DecidesComponent x c := by
  obtain ⟨d, rfl⟩ := splitComponent_factor hx
  have hm : (e * d) * c = (e * c) * d := by ring
  rcases hc with h | h
  · left
    rw [hm, h, zero_mul]
  · right
    rw [hm, h]

/-- Iterate the deterministic refinement over a fixed generating family. -/
def splitAllComponents (l bs : List R) : List R := bs.foldl splitComponents l

theorem ComponentFamily.splitAll {l bs : List R} (hl : ComponentFamily l)
    (hb : ∀ b ∈ bs, b * b = b) : ComponentFamily (splitAllComponents l bs) := by
  induction bs generalizing l with
  | nil => exact hl
  | cons b bs ih =>
    exact ih (hl.split (hb b (by simp))) (fun c hc => hb c (by simp [hc]))

theorem splitAllComponents_preserves {l bs : List R} {c : R}
    (hc : ∀ e ∈ l, DecidesComponent e c) :
    ∀ e ∈ splitAllComponents l bs, DecidesComponent e c := by
  induction bs generalizing l with
  | nil => exact hc
  | cons b bs ih =>
    apply ih
    intro x hx
    obtain ⟨e, he, hx⟩ := List.mem_flatMap.mp hx
    exact splitComponent_preserves (hc e he) hx

theorem splitAllComponents_decides {l bs : List R}
    (hb : ∀ b ∈ bs, b * b = b) :
    ∀ e ∈ splitAllComponents l bs, ∀ b ∈ bs, DecidesComponent e b := by
  induction bs generalizing l with
  | nil => simp
  | cons c bs ih =>
    intro e he b hbmem
    rcases List.mem_cons.mp hbmem with hbc | hbmem
    · subst b
      apply splitAllComponents_preserves (l := splitComponents l c) (bs := bs) ?_ e he
      intro x hx
      obtain ⟨d, _, hx⟩ := List.mem_flatMap.mp hx
      exact splitComponent_decides (hb c (by simp)) hx
    · exact ih (fun b hb' => hb b (by simp [hb'])) e he b hbmem

section BinarySpan

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
variable [Algebra (ZMod 2) R]

/-- Deciding each generator means deciding every binary linear combination. -/
theorem decidesComponent_of_mem_span (e : R) (bs : List R)
    (hb : ∀ b ∈ bs, DecidesComponent e b) (z : R)
    (hz : z ∈ Submodule.span (ZMod 2) {b | b ∈ bs}) : DecidesComponent e z := by
  let L : R →ₗ[ZMod 2] R :=
    { toFun := fun x => e * x
      map_add' := fun x y => mul_add e x y
      map_smul' := fun c x => by simp only [RingHom.id_apply, mul_smul_comm] }
  have hs : Submodule.span (ZMod 2) {b | b ∈ bs} ≤
      (Submodule.span (ZMod 2) ({e} : Set R)).comap L := by
    apply Submodule.span_le.mpr
    intro b hbmem
    change e * b ∈ Submodule.span (ZMod 2) ({e} : Set R)
    rcases hb b hbmem with h | h
    · rw [h]
      exact Submodule.zero_mem _
    · rw [h]
      exact Submodule.subset_span (Set.mem_singleton e)
  have hm : e * z ∈ Submodule.span (ZMod 2) ({e} : Set R) := hs hz
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
  rcases BinaryLinear.binary_eq_zero_or_one c with rfl | rfl
  · left
    simpa only [zero_smul] using hc.symm
  · right
    simpa only [one_smul] using hc.symm

/-- Separating a spanning family of fixed vectors makes every remaining component primitive. -/
theorem splitAllComponents_primitive {l bs : List R} (hl : ComponentFamily l)
    (hb : ∀ b ∈ bs, b * b = b)
    (hspan : ∀ z : R, z * z = z → z ∈ Submodule.span (ZMod 2) {b | b ∈ bs}) :
    ∀ e ∈ splitAllComponents l bs, PrimitiveBinaryComponent e := by
  intro e he
  have hf := hl.splitAll hb
  refine ⟨hf.nonzero e he, hf.idempotent e he, fun z hz => ?_⟩
  exact decidesComponent_of_mem_span e bs (splitAllComponents_decides hb e he) z (hspan z hz)

/-- Nonzero orthogonal idempotents are linearly independent over the binary base field. -/
theorem ComponentFamily.linearIndependent {l : List R} (hl : ComponentFamily l) :
    LinearIndependent (ZMod 2) (fun i : Fin l.length => l.get i) := by
  have ho (i j : Fin l.length) (hij : i ≠ j) : l.get i * l.get j = 0 := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact hl.orthogonal.rel_get_of_lt h
    · rw [mul_comm]
      exact hl.orthogonal.rel_get_of_lt h
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have h := congrArg (fun x : R => x * l.get j) hc
  simp only [Finset.sum_mul, smul_mul_assoc, zero_mul] at h
  have he (i : Fin l.length) : l.get i * l.get j = if i = j then l.get j else 0 := by
    split
    · subst i
      exact hl.idempotent _ (List.get_mem _ _)
    · exact ho i j ‹i ≠ j›
  simp only [he, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  exact (smul_eq_zero.mp h).resolve_right (hl.nonzero _ (List.get_mem _ _))

/-- Thus refinement can retain at most the ambient vector-space dimension. -/
theorem ComponentFamily.length_le_finrank [Module.Finite (ZMod 2) R]
    {l : List R} (hl : ComponentFamily l) : l.length ≤ Module.finrank (ZMod 2) R := by
  simpa using hl.linearIndependent.fintype_card_le_finrank

end BinarySpan

end MIPRE.LowDegree

end
