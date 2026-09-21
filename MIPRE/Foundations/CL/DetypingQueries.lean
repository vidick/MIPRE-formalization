/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.CL.Detyping

/-! # Query routing for the detyped CL presentation

The semantic specification of all branches of `types.tex`, `def:detyped-sampler`.
The level indices of factor and linear queries are zero based, as in `CLFun`.
These are equalities of the actual presentations' queries, not extra assumptions
on a future sampler program.
-/

noncomputable section

namespace MIPRE.CL

open Finset Classical

namespace CLFun

variable {F ι : Type*} [Semiring F] [DecidableEq ι] {k ℓ : ℕ}

/-- Truncation after concatenation keeps the full first part and truncates the second. -/
theorem truncate_concat_add (L : CLFun F ι k) (R : (ι → F) → CLFun F ι ℓ) (j : ℕ) :
    (L.concat R).truncate (j + k) = L.concat (fun u => (R u).truncate j) := by
  induction L generalizing R with
  | zero => simp [concat]
  | cons S L next ih =>
    simp only [concat_cons, Nat.add_succ, truncate_succ_cons]
    congr 1
    funext x
    exact ih x _

/-- Truncation inside the first part never visits a concatenation's continuation. -/
theorem truncate_concat_le (L : CLFun F ι k) (R : (ι → F) → CLFun F ι ℓ)
    (j : ℕ) (hj : j ≤ k) : (L.concat R).truncate j = L.truncate j := by
  induction L generalizing R j with
  | zero =>
    have : j = 0 := by omega
    subst j
    simp
  | cons S L next ih =>
    cases j with
    | zero => simp
    | succ j =>
      simp only [concat_cons, truncate_succ_cons]
      congr 1
      funext x
      exact ih x _ j (by omega)

end CLFun

namespace Detyping

variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]

set_option linter.unusedSectionVars false

private theorem content_proj_graph_compl (S : Finset (Graph.Coord T))
    (x : Coord T ι → ZMod 2) :
    pull .inr (proj (S.map Function.Embedding.inl)ᶜ x) = pull .inr x := by
  funext i
  simp [pull]

private theorem graph_prefix (S : Finset (Graph.Coord T)) (x : Coord T ι → ZMod 2) :
    pull .inl (proj (S.map Function.Embedding.inl) x +
      proj (Sᶜ.map Function.Embedding.inl) (proj (S.map Function.Embedding.inl)ᶜ x)) =
      pull .inl x := by
  rw [pull_add, pull_proj, pull_proj, pull_proj_compl, proj_proj_self, proj_add_proj_compl]

/-- Expanding the first two levels exposes the exact prefix used for type selection. -/
theorem presentation_cons {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (P : T → CLFun (ZMod 2) ι ℓ) :
    presentation E w P =
      .cons ((Graph.own w).map Function.Embedding.inl) ((RegLinear.id (Graph.own w)).embed .inl)
        (fun a => .cons ((Graph.own w)ᶜ.map Function.Embedding.inl)
          ((Graph.second E w (pull .inl a)).embed .inl)
          (fun b => (selected P (select E w (pull .inl (a + b)))).embed .inr)) := by
  simp [presentation, Graph.presentation, CLFun.embed, CLFun.concat]

/-- Marginals through level two are precisely graph marginals with zero content. -/
theorem marginal_graph {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (P : T → CLFun (ZMod 2) ι ℓ) (j : ℕ) (hj : j ≤ 2) (x : Coord T ι → ZMod 2) :
    ((presentation E w P).truncate j).eval x =
      push .inl (((Graph.presentation E w).truncate j).eval (pull .inl x)) := by
  rw [presentation, CLFun.truncate_concat_le _ _ j hj, CLFun.eval_truncate_embed]

/-- Later marginals pair the full graph question with the selected content marginal. -/
theorem marginal_content {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (P : T → CLFun (ZMod 2) ι ℓ) (hP : ∀ t, (P t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (j : ℕ) (x : Coord T ι → ZMod 2) :
    ((presentation E w P).truncate (j + 2)).eval x = Sum.elim
      ((Graph.presentation E w).eval (pull .inl x))
      (((selected P (select E w (pull .inl x))).truncate j).eval (pull .inr x)) := by
  have hs : ∀ u, (selected P u).ExactlyOn univ := by
    intro u
    cases u with
    | none => exact CLFun.zeroOn_exactlyOn _ _ (fun h => False.elim (by omega))
    | some t => exact hP t
  rw [presentation, CLFun.truncate_concat_add, CLFun.SupportedOn.eval_concat
    ((Graph.presentation_exactlyOn E w).embed .inl).supportedOn
    (fun x => (((hs _).embed .inr).supportedOn.truncate j)) disjoint_registers]
  simp only [CLFun.eval_embed, pull_push, select_output, CLFun.eval_truncate_embed]
  funext q
  cases q <;> simp

/-- The first factor is the player's own two graph blocks. -/
theorem factor_first {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (P : T → CLFun (ZMod 2) ι ℓ) (x : Coord T ι → ZMod 2) :
    (presentation E w P).factorOfPrefix 0 x = (Graph.own w).map Function.Embedding.inl := rfl

/-- The second factor is the entire opposite pair of graph blocks. -/
theorem factor_second {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (P : T → CLFun (ZMod 2) ι ℓ) (x : Coord T ι → ZMod 2) :
    (presentation E w P).factorOfPrefix 1 x = (Graph.own w)ᶜ.map Function.Embedding.inl := rfl

/-- Later factors are exactly the selected content factors, read from the content prefix. -/
theorem factor_content {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (P : T → CLFun (ZMod 2) ι ℓ) (j : ℕ) (x : Coord T ι → ZMod 2) :
    (presentation E w P).factorOfPrefix (j + 2) x =
      ((selected P (select E w (pull .inl x))).factorOfPrefix j (pull .inr x)).map
        Function.Embedding.inr := by
  rw [presentation_cons]
  simp only [Nat.add_succ, Nat.add_zero, CLFun.factorOfPrefix_cons_succ,
    CLFun.factorOfPrefix_embed, graph_prefix, content_proj_graph_compl]

/-- The first linear query copies the player's own graph blocks. -/
theorem linear_first {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (P : T → CLFun (ZMod 2) ι ℓ) (x y : Coord T ι → ZMod 2) :
    (presentation E w P).mapOfPrefix 0 x y = push .inl (proj (Graph.own w) (pull .inl y)) := rfl

/-- The second linear query keeps the neighbor bit selected by the graph prefix. -/
theorem linear_second {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (P : T → CLFun (ZMod 2) ι ℓ) (x y : Coord T ι → ZMod 2) :
    (presentation E w P).mapOfPrefix 1 x y =
      push .inl (Graph.second E w (proj (Graph.own w) (pull .inl x)) (pull .inl y)) := by
  rw [presentation_cons]
  simp only [CLFun.mapOfPrefix_cons_succ, CLFun.mapOfPrefix_cons_zero,
    RegLinear.toLinearMap_apply, RegLinear.embed_apply, pull_proj]

/-- Later linear queries are exactly the selected typed queries, with zero graph output. -/
theorem linear_content {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (P : T → CLFun (ZMod 2) ι ℓ) (j : ℕ) (x y : Coord T ι → ZMod 2) :
    (presentation E w P).mapOfPrefix (j + 2) x y =
      push .inr ((selected P (select E w (pull .inl x))).mapOfPrefix j
        (pull .inr x) (pull .inr y)) := by
  rw [presentation_cons]
  simp only [Nat.add_succ, Nat.add_zero, CLFun.mapOfPrefix_cons_succ,
    CLFun.mapOfPrefix_embed, graph_prefix, content_proj_graph_compl]

end Detyping
end MIPRE.CL
