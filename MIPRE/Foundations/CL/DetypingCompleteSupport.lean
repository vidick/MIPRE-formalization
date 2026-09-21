/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.CL.DetypingGame
import MIPRE.Foundations.GameDouble

/-! # The common measurement rule and support of detyping

Both players use one decoder of graph views. It agrees with their own type
selector on sampled questions, and otherwise selects a deterministic fallback.
This is the player-independent rule in `types.tex`, `lem:detyping-verifiers`.
-/

noncomputable section

namespace MIPRE.CL.Detyping

open Finset Classical

variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]

set_option linter.unusedSectionVars false

/-- The common decoder recognizes either player's full valid graph view. -/
def decodeView (E : T → T → Prop) [DecidableRel E]
    (g : Graph.Coord T → ZMod 2) : Option (Bool × T) :=
  if h : ∃ u, g = view E false u then some (false, h.choose)
  else if h : ∃ u, g = view E true u then some (true, h.choose)
  else none

/-- Graph views uniquely determine the type within either pattern family. -/
theorem view_injective (E : T → T → Prop) [DecidableRel E] (w : Bool) :
    Function.Injective (view E w) := by
  intro u v h
  have hs := congrArg (select E w) h
  simpa only [select_view, Option.some.injEq] using hs

/-- The common decoder recognizes every valid question with its original tag. -/
theorem decodeView_view (E : T → T → Prop) [DecidableRel E] (w : Bool) (u : T) :
    decodeView E (view E w u) = some (w, u) := by
  cases w
  · have h : ∃ v, view E false u = view E false v := ⟨u, rfl⟩
    simp only [decodeView, dif_pos h]
    rw [← view_injective E false h.choose_spec]
  · have h : ¬∃ v, view E true u = view E false v := by
      rintro ⟨v, hv⟩
      exact view_disjoint E v u hv.symm
    have h' : ∃ v, view E true u = view E true v := ⟨u, rfl⟩
    simp only [decodeView, dif_neg h, dif_pos h']
    rw [← view_injective E true h'.choose_spec]

/-- The graph sampler always erases the other player's vertex block. -/
theorem graph_output_opposite_vertex (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (g : Graph.Coord T → ZMod 2) (u : T) :
    (Graph.presentation E w).eval g (!w, (false, u)) = 0 := by
  rw [Graph.presentation_eval]
  simp only [Pi.add_apply, proj_apply, Graph.mem_own, Bool.not_eq_self, if_false, zero_add]
  unfold Graph.mask
  cases Graph.decode E (fun p => g (w, p)) <;> simp

/-- A sampled graph view cannot be a valid view of the opposite player. -/
theorem graph_output_ne_opposite_view (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (g : Graph.Coord T → ZMod 2) (u : T) :
    (Graph.presentation E w).eval g ≠ view E (!w) u := by
  intro h
  have hh := congrFun h (!w, (false, u))
  rw [graph_output_opposite_vertex] at hh
  simp [view, Graph.encode] at hh

/-- On a sampled graph view, the common decoder is exactly the local selector. -/
theorem decodeView_output (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (g : Graph.Coord T → ZMod 2) :
    decodeView E ((Graph.presentation E w).eval g) = (select E w g).map (w, ·) := by
  cases hs : select E w g with
  | some u => rw [graph_output_of_select E w g hs, decodeView_view]; rfl
  | none =>
    have hown : ¬∃ u, (Graph.presentation E w).eval g = view E w u := by
      rintro ⟨u, hu⟩
      have hh := congrArg (select E w) hu
      rw [select_output, select_view, hs] at hh
      cases hh
    have hopp : ¬∃ u, (Graph.presentation E w).eval g = view E (!w) u := by
      rintro ⟨u, hu⟩
      exact graph_output_ne_opposite_view E w g u hu
    cases w <;> simp only [Bool.not_false, Bool.not_true] at hopp <;>
      simp [decodeView, hown, hopp]

/-- Decode a full question, retaining its content register. -/
def decodeQuestion (E : T → T → Prop) [DecidableRel E] (q : Coord T ι → ZMod 2) :
    Option (Bool × Question T ι) :=
  (decodeView E (pull .inl q)).map fun wu => (wu.1, wu.2, pull .inr q)

/-- A fixed embedded typed question is decoded exactly. -/
theorem decodeQuestion_question (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (q : Question T ι) : decodeQuestion E (question E w q) = some (w, q) := by
  change (decodeView E (view E w q.1)).map _ = _
  rw [decodeView_view]
  rfl

/-- On samples the decoder selects the original typed content, or the trivial branch. -/
theorem decodeQuestion_output {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (P : T → CLFun (ZMod 2) ι ℓ) (hP : ∀ t, (P t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (g : Graph.Coord T → ZMod 2) (v : ι → ZMod 2) :
    decodeQuestion E ((presentation E w P).eval (Sum.elim g v)) =
      (select E w g).map (fun u => (w, u, (P u).eval v)) := by
  cases hs : select E w g with
  | some u =>
    rw [presentation_eval_valid E w P hP hℓ g v hs]
    exact decodeQuestion_question E w (u, (P u).eval v)
  | none =>
    rw [presentation_eval E w P hP hℓ]
    change (decodeView E ((Graph.presentation E w).eval g)).map _ = _
    rw [decodeView_output, hs]
    rfl

/-- Successful selection by both players identifies the common edge seed. -/
theorem selects_pairSeed (E : T → T → Prop) [DecidableRel E]
    (hE : ∀ u v, E u v → E v u) (g : Graph.Coord T → ZMod 2) {u v : T}
    (hu : select E false g = some u) (hv : select E true g = some v) :
    E u v ∧ g = Graph.pairSeed E (u, v) := by
  have hgu : Graph.localValid E false g := ⟨u, (select_eq_some_iff E false g u).mp hu⟩
  have hgv : Graph.localValid E true g := ⟨v, (select_eq_some_iff E true g v).mp hv⟩
  obtain ⟨uv, he, rfl⟩ := (Graph.localValid_both_iff E hE g).mp ⟨hgu, hgv⟩
  have hu' := (select_pairSeed E hE false uv he).symm.trans hu
  have hv' := (select_pairSeed E hE true uv he).symm.trans hv
  simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hu' hv'
  cases uv
  simp_all

end MIPRE.CL.Detyping
