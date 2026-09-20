/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.CL.Basic
import Mathlib.Data.Finset.Image

/-! # Embedding conditionally linear presentations in a larger register

Extending a presentation by zero along an injection preserves its evaluation,
marginal, factor and linear-map queries. This puts the graph and content parts
of detyping on disjoint registers without changing their query interfaces.
-/

noncomputable section

namespace MIPRE.CL

open Classical

set_option linter.unusedSectionVars false

variable {F ι κ : Type*} [Semiring F] [DecidableEq ι] [DecidableEq κ]

/-- Read the coordinates in the image of an embedding. -/
def pull (e : ι ↪ κ) (x : κ → F) : ι → F := fun i => x (e i)

/-- Extend by zero outside the image of an embedding. -/
def push (e : ι ↪ κ) (x : ι → F) : κ → F :=
  fun j => if h : ∃ i, e i = j then x h.choose else 0

@[simp] theorem push_apply (e : ι ↪ κ) (x : ι → F) (i : ι) : push e x (e i) = x i := by
  have h : ∃ a, e a = e i := ⟨i, rfl⟩
  rw [push, dif_pos h]
  congr 1
  exact e.injective h.choose_spec

@[simp] theorem pull_push (e : ι ↪ κ) (x : ι → F) : pull e (push e x) = x := by
  funext i
  exact push_apply e x i

@[simp] theorem push_zero (e : ι ↪ κ) : push e (0 : ι → F) = 0 := by
  funext j
  simp [push]

@[simp] theorem push_add (e : ι ↪ κ) (x y : ι → F) :
    push e (x + y) = push e x + push e y := by
  funext j
  simp only [push, Pi.add_apply]
  split_ifs <;> simp

@[simp] theorem pull_add (e : ι ↪ κ) (x y : κ → F) :
    pull e (x + y) = pull e x + pull e y := rfl

@[simp] theorem pull_zero (e : ι ↪ κ) : pull e (0 : κ → F) = 0 := rfl

@[simp] theorem push_inl_left (x : ι → F) (i : ι) :
    push (Function.Embedding.inl (β := κ)) x (Sum.inl i) = x i := push_apply _ _ _

@[simp] theorem push_inr_right (x : κ → F) (j : κ) :
    push (Function.Embedding.inr (α := ι)) x (Sum.inr j) = x j := push_apply _ _ _

@[simp] theorem push_inl_right (x : ι → F) (j : κ) :
    push Function.Embedding.inl x (Sum.inr j) = 0 := by simp [push]

@[simp] theorem push_inr_left (x : κ → F) (i : ι) :
    push Function.Embedding.inr x (Sum.inl i) = 0 := by simp [push]

/-- Restriction of the projection onto an embedded register. -/
theorem pull_proj (e : ι ↪ κ) (S : Finset ι) (x : κ → F) :
    pull e (proj (S.map e) x) = proj S (pull e x) := by
  funext i
  simp [pull]

/-- Restriction of the projection onto the remaining registers. -/
theorem pull_proj_compl [Fintype ι] [Fintype κ] (e : ι ↪ κ) (S : Finset ι)
    (x : κ → F) : pull e (proj (S.map e)ᶜ x) = proj Sᶜ (pull e x) := by
  funext i
  simp [pull]

/-- Projection commutes with extension by zero. -/
theorem proj_push (e : ι ↪ κ) (S : Finset ι) (x : ι → F) :
    proj (S.map e) (push e x) = push e (proj S x) := by
  funext j
  by_cases h : ∃ i, e i = j
  · obtain ⟨i, rfl⟩ := h
    simp
  · have hm : j ∉ S.map e := by
      simpa only [Finset.mem_map, not_exists, not_and] using
        fun i (_ : i ∈ S) => fun hi => h ⟨i, hi⟩
    simp [push, h, hm]

namespace RegLinear

/-- The same register-linear operation on an embedded register. -/
def embed (e : ι ↪ κ) {S : Finset ι} (L : RegLinear F S) : RegLinear F (S.map e) where
  toLinearMap :=
    { toFun := fun x => push e (L (pull e x))
      map_add' := fun x y => by simp
      map_smul' := fun c x => by
        change push e (L (c • pull e x)) = c • push e (L (pull e x))
        rw [map_smul]
        funext j
        simp only [push, Pi.smul_apply]
        split_ifs <;> simp }
  proj_comp_proj' x := by
    change proj (S.map e) (push e (L (pull e (proj (S.map e) x)))) = _
    rw [pull_proj, L.apply_proj, proj_push, L.proj_apply]
    rfl

@[simp] theorem embed_apply (e : ι ↪ κ) {S : Finset ι} (L : RegLinear F S) (x : κ → F) :
    L.embed e x = push e (L (pull e x)) := rfl

end RegLinear

namespace CLFun

variable {ℓ : ℕ}

/-- Extend every factor and map of a presentation along a coordinate injection. -/
def embed (e : ι ↪ κ) : {ℓ : ℕ} → CLFun F ι ℓ → CLFun F κ ℓ
  | _, zero => zero
  | _, cons S L next => cons (S.map e) (L.embed e) fun x => (next (pull e x)).embed e

/-- Embedded factors still partition precisely the embedded original register. -/
theorem ExactlyOn.embed (e : ι ↪ κ) {P : CLFun F ι ℓ} {S : Finset ι}
    (hP : P.ExactlyOn S) : (P.embed e).ExactlyOn (S.map e) := by
  induction P generalizing S with
  | zero =>
    change S = ∅ at hP
    simp [CLFun.embed, hP]
  | cons U L next ih =>
    refine ⟨Finset.map_subset_map.mpr hP.1, fun x => ?_⟩
    rw [← Finset.map_sdiff]
    exact ih _ (hP.2 _)

variable [Fintype ι] [Fintype κ]

/-- The embedded CL function acts only on its original coordinates. -/
theorem eval_embed (e : ι ↪ κ) (P : CLFun F ι ℓ) (x : κ → F) :
    (P.embed e).eval x = push e (P.eval (pull e x)) := by
  induction P generalizing x with
  | zero => simp [embed]
  | cons S L next ih =>
    simp only [embed, eval_cons, RegLinear.embed_apply, pull_push, ih,
      pull_proj_compl, push_add]

/-- Marginal queries are transported by the same coordinate embedding. -/
theorem eval_truncate_embed (e : ι ↪ κ) (P : CLFun F ι ℓ) (j : ℕ) (x : κ → F) :
    ((P.embed e).truncate j).eval x = push e ((P.truncate j).eval (pull e x)) := by
  induction j generalizing ℓ P x with
  | zero => simp
  | succ j ih =>
    cases P with
    | zero => simp [embed, eval_truncate_zero]
    | cons S L next =>
      simp only [embed, truncate_succ_cons, eval_cons, RegLinear.embed_apply,
        pull_push, ih, pull_proj_compl, push_add]

/-- Factor queries from an arbitrary prefix commute with embedding. -/
theorem factorOfPrefix_embed (e : ι ↪ κ) (P : CLFun F ι ℓ) (j : ℕ) (x : κ → F) :
    (P.embed e).factorOfPrefix j x = (P.factorOfPrefix j (pull e x)).map e := by
  induction P generalizing j x with
  | zero => simp [embed]
  | cons S L next ih =>
    cases j with
    | zero => rfl
    | succ j =>
      simp only [embed, factorOfPrefix_cons_succ, pull_proj, ih, pull_proj_compl]

/-- Linear-map queries from an arbitrary prefix commute with embedding. -/
theorem mapOfPrefix_embed (e : ι ↪ κ) (P : CLFun F ι ℓ) (j : ℕ) (x y : κ → F) :
    (P.embed e).mapOfPrefix j x y = push e (P.mapOfPrefix j (pull e x) (pull e y)) := by
  induction P generalizing j x with
  | zero => simp [embed]
  | cons S L next ih =>
    cases j with
    | zero => rfl
    | succ j =>
      simp only [embed, mapOfPrefix_cons_succ, pull_proj, ih, pull_proj_compl]

end CLFun
end MIPRE.CL
