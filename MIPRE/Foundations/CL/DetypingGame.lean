/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.CL.DetypingLaw
import MIPRE.Foundations.SampledGame

/-! # The finite typed and detyped games

This is the game at a fixed verifier index, before ambient-program compilation.
The detyped predicate accepts outside valid edge views. On valid views it calls
the original predicate. The answer alphabets here are unchanged; the separate
program-level cutoff and answer truncation obligations are not hidden here.
-/

noncomputable section

namespace MIPRE.CL.Detyping

open Finset Classical

private theorem sampled_dist_cl {J : Type*} [Fintype J] [DecidableEq J]
    (L R : (J → ZMod 2) → (J → ZMod 2)) (x y : J → ZMod 2) :
    SampledGame.dist L R x y = clDist L R x y := by
  rw [SampledGame.dist_eq_card]
  unfold clDist
  congr 2
  apply congrArg Finset.card
  ext s
  simp

variable {T ι A B : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
  [Fintype A] [Fintype B]

set_option linter.unusedSectionVars false

/-- Typed questions carry a type and its sampled content. -/
abbrev Question (T ι : Type*) := T × (ι → ZMod 2)

/-- Embed a typed question using the type's fixed local graph view. -/
def question (E : T → T → Prop) [DecidableRel E] (w : Bool) (q : Question T ι) :
    Coord T ι → ZMod 2 := Sum.elim (view E w q.1) q.2

/-- A valid graph view decodes to its type. -/
theorem select_view (E : T → T → Prop) [DecidableRel E] (w : Bool) (u : T) :
    select E w (view E w u) = some u := by
  apply (select_eq_some_iff _ _ _ _).mpr
  constructor
  · funext p
    simp [view]
  · simp [view]

/-- The two players' families of valid graph views are disjoint. -/
theorem view_disjoint (E : T → T → Prop) [DecidableRel E] (u v : T) :
    view E false u ≠ view E true v := by
  intro h
  have hh := congrFun h (false, (false, u))
  simp [view, Graph.encode] at hh

/-- The detyped predicate: call the typed predicate on an edge view, otherwise accept. -/
def accepts (E : T → T → Prop) [DecidableRel E]
    (D : Question T ι → Question T ι → A → B → Bool)
    (x y : Coord T ι → ZMod 2) (a : A) (b : B) : Bool :=
  match select E false (pull .inl x), select E true (pull .inl y) with
  | some u, some v =>
    if E u v ∧ pull .inl x = view E false u ∧ pull .inl y = view E true v then
      D (u, pull .inr x) (v, pull .inr y) a b
    else true
  | _, _ => true

/-- On an edge, the fixed graph views make the detyped predicate exactly the typed one. -/
theorem accepts_question (E : T → T → Prop) [DecidableRel E]
    (D : Question T ι → Question T ι → A → B → Bool)
    (x y : Question T ι) (h : E x.1 y.1) (a : A) (b : B) :
    accepts E D (question E false x) (question E true y) a b = D x y a b := by
  unfold accepts question
  change (match select E false (view E false x.1), select E true (view E true y.1) with
    | some u, some v =>
      if E u v ∧ view E false x.1 = view E false u ∧ view E true y.1 = view E true v then
        D (u, x.2) (v, y.2) a b else true
    | _, _ => true) = _
  rw [select_view, select_view]
  simp [h]

/-- Ordered adjacent pairs, including loops. -/
abbrev Edge (E : T → T → Prop) [DecidableRel E] := ↥(Graph.edges E)

/-- The typed sample space is an ordered edge together with one common content seed. -/
abbrev TypedSeed (E : T → T → Prop) [DecidableRel E] (ι : Type*) := Edge E × (ι → ZMod 2)

/-- One player's typed question from an edge and common seed. -/
def typedQuestion {ℓ : ℕ} {E : T → T → Prop} [DecidableRel E]
    (P : Bool → T → CLFun (ZMod 2) ι ℓ) (w : Bool) (z : TypedSeed E ι) : Question T ι :=
  let u := if w then z.1.val.2 else z.1.val.1
  (u, (P w u).eval z.2)

/-- The actual finite typed game, sampling a uniform ordered edge and common seed. -/
def typedGame {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (hne : (Graph.edges E).Nonempty)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ)
    (D : Question T ι → Question T ι → A → B → Bool) : Game (Question T ι) (Question T ι) A B := by
  letI : Nonempty (Edge E) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  exact SampledGame.game (typedQuestion (E := E) P false) (typedQuestion P true) D

/-- The actual finite detyped game, using the constructed CL presentations. -/
def game {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
    (P : Bool → T → CLFun (ZMod 2) ι ℓ)
    (D : Question T ι → Question T ι → A → B → Bool) :
    Game (Coord T ι → ZMod 2) (Coord T ι → ZMod 2) A B :=
  SampledGame.game (presentation E false (P false)).eval
    (presentation E true (P true)).eval (accepts E D)

/-- The finite game's law is the library's CL distribution of the constructed presentations. -/
theorem game_mu_eq_clDist {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
    (P : Bool → T → CLFun (ZMod 2) ι ℓ)
    (D : Question T ι → Question T ι → A → B → Bool) (x y : Coord T ι → ZMod 2) :
    (game E P D).μ x y = clDist (presentation E false (P false)).eval
      (presentation E true (P true)).eval x y := by
  change SampledGame.dist (presentation E false (P false)).eval
    (presentation E true (P true)).eval x y = _
  exact sampled_dist_cl _ _ _ _

/-- Restrict the strategy's measurements to fixed graph views; its state and dimensions persist. -/
def restrict {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (hne : (Graph.edges E).Nonempty)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ)
    (D : Question T ι → Question T ι → A → B → Bool) (S : TensorProductStrategy (game E P D)) :
    TensorProductStrategy (typedGame E hne P D) :=
  S.relabel (typedGame E hne P D) (question E false) (question E true) (.refl A) (.refl B)

/-- Restriction literally preserves the shared state. -/
theorem restrict_state {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (hne : (Graph.edges E).Nonempty)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ)
    (D : Question T ι → Question T ι → A → B → Bool) (S : TensorProductStrategy (game E P D)) :
    (restrict E hne P D S).ψ = S.ψ := rfl

/-- Conditional failure agrees on every edge, with no change of state. -/
theorem restrict_failAt {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (hne : (Graph.edges E).Nonempty)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ)
    (D : Question T ι → Question T ι → A → B → Bool) (S : TensorProductStrategy (game E P D))
    (x y : Question T ι) (h : E x.1 y.1) :
    (restrict E hne P D S).failAt x y = S.failAt (question E false x) (question E true y) := by
  unfold TensorProductStrategy.failAt TensorProductStrategy.succAt
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  change (if D x y a b then (1 : ℝ) else 0) * _ =
    (if accepts E D (question E false x) (question E true y) a b then 1 else 0) * _
  rw [accepts_question E D x y h]
  rfl

/-- The typed failure is the uniform edge-and-content average of the restricted failures. -/
theorem typed_failure {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (hne : (Graph.edges E).Nonempty)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ)
    (D : Question T ι → Question T ι → A → B → Bool) (S : TensorProductStrategy (typedGame E hne P D)) :
    1 - S.value =
      (∑ uv ∈ Graph.edges E, ∑ v : ι → ZMod 2,
        S.failAt (uv.1, (P false uv.1).eval v) (uv.2, (P true uv.2).eval v)) /
      ((Graph.edges E).card * Fintype.card (ι → ZMod 2)) := by
  let _ : Nonempty (Edge E) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  refine (SampledGame.one_sub_value (typedQuestion (E := E) P false) (typedQuestion P true) D S).trans ?_
  simp only [Fintype.card_prod, Fintype.card_coe, Nat.cast_mul, Fintype.sum_prod_type,
    typedQuestion, Bool.false_eq_true, ↓reduceIte]
  congr 1
  exact Finset.sum_coe_sort (Graph.edges E) (fun uv => ∑ v : ι → ZMod 2,
    S.failAt (uv.1, (P false uv.1).eval v) (uv.2, (P true uv.2).eval v))

/-- The detyped failure is the uniform average over its independent graph and content seeds. -/
theorem failure {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
    (P : Bool → T → CLFun (ZMod 2) ι ℓ)
    (D : Question T ι → Question T ι → A → B → Bool) (S : TensorProductStrategy (game E P D)) :
    1 - S.value =
      (∑ g : Graph.Coord T → ZMod 2, ∑ v : ι → ZMod 2,
        S.failAt ((presentation E false (P false)).eval (Sum.elim g v))
          ((presentation E true (P true)).eval (Sum.elim g v))) /
      ((16 : ℝ) ^ Fintype.card T * Fintype.card (ι → ZMod 2)) := by
  refine (SampledGame.one_sub_value _ _ _ S).trans ?_
  let e := Equiv.sumArrowEquivProdArrow (Graph.Coord T) ι (ZMod 2)
  have hc := Fintype.card_congr e
  rw [hc, Fintype.card_prod, Graph.card_seeds, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  congr 1
  rw [← Fintype.sum_prod_type']
  exact (e.symm.sum_comp (fun z => S.failAt
    ((presentation E false (P false)).eval z) ((presentation E true (P true)).eval z))).symm

end MIPRE.CL.Detyping
