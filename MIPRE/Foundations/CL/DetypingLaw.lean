/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.CL.Detyping

/-! # The joint law of detyped questions

On an ordered edge the graph view depends only on the player's own type.
Conditioning on the valid-edge event gives the uniform ordered-edge law and
one shared uniform content seed, exactly as in `types.tex`, `def:detyped-CL`.
-/

noncomputable section

namespace MIPRE.CL.Detyping

open Finset Classical

variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]

set_option linter.unusedSectionVars false

/-- The fixed valid graph question of one type, independent of the neighboring type. -/
def view (E : T → T → Prop) [DecidableRel E] (w : Bool) (u : T) : Graph.Coord T → ZMod 2 :=
  fun p => if p.1 = w then Graph.encode E u p.2 else if p = (!w, (true, u)) then 1 else 0

/-- Every valid local sample is exactly the fixed graph question of its selected type. -/
theorem graph_output_of_select (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (g : Graph.Coord T → ZMod 2) {u : T} (h : select E w g = some u) :
    (Graph.presentation E w).eval g = view E w u := by
  obtain ⟨hu, hbit⟩ := (select_eq_some_iff E w g u).mp h
  have hd := (Graph.decode_eq_some_iff E _ u).mpr hu
  rw [Graph.presentation_eval]
  unfold Graph.mask
  rw [hd]
  funext ⟨b, q⟩
  by_cases hb : b = w
  · subst b
    simpa [view] using congrFun hu q
  · simp only [Pi.add_apply, proj_apply, Graph.mem_own, hb, if_false,
      Finset.mem_singleton, zero_add, view]
    split_ifs with he
    · rw [he]
      exact hbit
    · rfl

/-- On an adjacent seed the two players select exactly its two endpoint types. -/
theorem select_pairSeed (E : T → T → Prop) [DecidableRel E]
    (hE : ∀ u v, E u v → E v u) (w : Bool) (uv : T × T) (huv : E uv.1 uv.2) :
    select E w (Graph.pairSeed E uv) = some (if w then uv.2 else uv.1) := by
  apply (select_eq_some_iff _ _ _ _).mpr
  cases w <;> constructor
  · rfl
  · simp [Graph.pairSeed, Graph.encode, hE _ _ huv]
  · rfl
  · simp [Graph.pairSeed, Graph.encode, huv]

/-- On valid seeds the detyped question retains precisely the selected type's content. -/
theorem presentation_eval_valid {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (P : T → CLFun (ZMod 2) ι ℓ) (hP : ∀ t, (P t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (g : Graph.Coord T → ZMod 2) (v : ι → ZMod 2) {u : T}
    (hu : select E w g = some u) :
    (presentation E w P).eval (Sum.elim g v) = Sum.elim (view E w u) ((P u).eval v) := by
  rw [presentation_eval E w P hP hℓ]
  change Sum.elim ((Graph.presentation E w).eval g) ((selected P (select E w g)).eval v) = _
  rw [graph_output_of_select E w g hu, hu]
  rfl

/-- On invalid local seeds the entire content output is zero. -/
theorem presentation_eval_invalid {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (P : T → CLFun (ZMod 2) ι ℓ) (hP : ∀ t, (P t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (g : Graph.Coord T → ZMod 2) (v : ι → ZMod 2) (hg : ¬Graph.localValid E w g) :
    (presentation E w P).eval (Sum.elim g v) = Sum.elim ((Graph.presentation E w).eval g) 0 := by
  rw [presentation_eval E w P hP hℓ]
  change Sum.elim ((Graph.presentation E w).eval g) ((selected P (select E w g)).eval v) = _
  rw [(select_eq_none_iff E w g).mpr hg]
  simp [selected]

/-- The joint valid-seed sum is exactly the typed edge-and-common-seed sum.
In particular, no independence of the two content outputs is asserted or needed. -/
theorem sum_valid_questions {ℓ : ℕ} {M : Type*} [AddCommMonoid M]
    (E : T → T → Prop) [DecidableRel E] (hE : ∀ u v, E u v → E v u)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ) (hP : ∀ w t, (P w t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (f : (Coord T ι → ZMod 2) → (Coord T ι → ZMod 2) → M) :
    ∑ g ∈ Graph.validSeeds E, ∑ v : ι → ZMod 2,
      f ((presentation E false (P false)).eval (Sum.elim g v))
        ((presentation E true (P true)).eval (Sum.elim g v)) =
    ∑ uv ∈ Graph.edges E, ∑ v : ι → ZMod 2,
      f (Sum.elim (view E false uv.1) ((P false uv.1).eval v))
        (Sum.elim (view E true uv.2) ((P true uv.2).eval v)) := by
  rw [Graph.sum_validSeeds]
  apply Finset.sum_congr rfl
  intro uv huv
  have he : E uv.1 uv.2 := (Finset.mem_filter.mp huv).2
  apply Finset.sum_congr rfl
  intro v _
  rw [presentation_eval_valid E false (P false) (hP false) hℓ _ v
      (select_pairSeed E hE false uv he),
    presentation_eval_valid E true (P true) (hP true) hℓ _ v
      (select_pairSeed E hE true uv he)]
  rfl

/-- The conditional joint law is the uniform ordered-edge law with a shared uniform seed. -/
theorem conditional_average {ℓ : ℕ}
    (E : T → T → Prop) [DecidableRel E] (hE : ∀ u v, E u v → E v u)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ) (hP : ∀ w t, (P w t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (f : (Coord T ι → ZMod 2) → (Coord T ι → ZMod 2) → ℝ) :
    (∑ g ∈ Graph.validSeeds E, ∑ v : ι → ZMod 2,
      f ((presentation E false (P false)).eval (Sum.elim g v))
        ((presentation E true (P true)).eval (Sum.elim g v))) /
      ((Graph.validSeeds E).card * Fintype.card (ι → ZMod 2)) =
    (∑ uv ∈ Graph.edges E, ∑ v : ι → ZMod 2,
      f (Sum.elim (view E false uv.1) ((P false uv.1).eval v))
        (Sum.elim (view E true uv.2) ((P true uv.2).eval v))) /
      ((Graph.edges E).card * Fintype.card (ι → ZMod 2)) := by
  rw [sum_valid_questions E hE P hP hℓ, Graph.card_validSeeds]

end MIPRE.CL.Detyping
