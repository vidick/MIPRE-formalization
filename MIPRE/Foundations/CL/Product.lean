/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.CL.Closure
import MIPRE.Foundations.CL.Embedding

/-!
# Padding to a given level, and the product of two presentations

Two constructions the answer-reduced sampler needs (`sec:ar-verifier`, `ld_compiler.tex`): its
CL functions are the direct sums of the oracularized sampler's, with `ℓ` levels, and the
downsized PCP sampler's, with three, on disjoint registers, at the common level `max ℓ 3`.

* `CLFun.liftTo T L h P` pads `P` with trivial levels to exactly `L ≥ ℓ` levels (`liftN` pads by
  a number of levels, and `ℓ + (L - ℓ)` is not `L` by definition, so the level is cast along
  `castLevel`). Evaluation and exactness are unchanged (`eval_liftTo`, `ExactlyOn.liftTo`).
* `CLFun.prod P Q` is the presentation on `ι ⊕ κ` running `P` on the left coordinates and `Q` on
  the right: the paper's direct sum on `V₁ ⊕ V₂`, as `directSum` of the two embeddings. It is
  exact on everything when both are (`ExactlyOn.prod`), and evaluates componentwise
  (`eval_prod`).
-/

noncomputable section

namespace MIPRE.CL.CLFun

open Finset

variable {F : Type*} [Semiring F] {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

/-! ## Casting and padding the level -/

/-- A presentation with `a` levels as one with `b = a` levels. -/
def castLevel {a b : ℕ} (h : a = b) (P : CLFun F ι a) : CLFun F ι b := h ▸ P

theorem ExactlyOn.castLevel {a b : ℕ} (h : a = b) {P : CLFun F ι a} {T : Finset ι}
    (hP : P.ExactlyOn T) : (P.castLevel h).ExactlyOn T := by
  subst h; exact hP

@[simp] theorem eval_castLevel [Fintype ι] {a b : ℕ} (h : a = b) (P : CLFun F ι a) (x : ι → F) :
    (P.castLevel h).eval x = P.eval x := by
  subst h; rfl

@[simp] theorem truncate_castLevel {a b : ℕ} (h : a = b) (P : CLFun F ι a) (j : ℕ) :
    (P.castLevel h).truncate j = P.truncate j := by
  subst h; rfl

@[simp] theorem factorOfPrefix_castLevel [Fintype ι] {a b : ℕ} (h : a = b) (P : CLFun F ι a)
    (j : ℕ) (u : ι → F) : (P.castLevel h).factorOfPrefix j u = P.factorOfPrefix j u := by
  subst h; rfl

@[simp] theorem mapOfPrefix_castLevel [Fintype ι] {a b : ℕ} (h : a = b) (P : CLFun F ι a)
    (j : ℕ) (u : ι → F) : (P.castLevel h).mapOfPrefix j u = P.mapOfPrefix j u := by
  subst h; rfl

variable {ℓ : ℕ}

/-- **Pad to exactly `L` levels**, the extra levels trivial on `V_T`. -/
def liftTo (T : Finset ι) (L : ℕ) (h : ℓ ≤ L) (P : CLFun F ι ℓ) : CLFun F ι L :=
  (P.liftN T (L - ℓ)).castLevel (Nat.add_sub_cancel' h)

theorem ExactlyOn.liftTo {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.ExactlyOn T) (L : ℕ)
    (h : ℓ ≤ L) : (P.liftTo T L h).ExactlyOn T :=
  (hP.liftN _).castLevel _

@[simp] theorem eval_liftTo [Fintype ι] (T : Finset ι) (L : ℕ) (h : ℓ ≤ L) (P : CLFun F ι ℓ)
    (x : ι → F) : (P.liftTo T L h).eval x = P.eval x := by
  simp [liftTo]

/-! ## The product of two presentations -/

/-- **The product**: `P` on the left coordinates, `Q` on the right. -/
def prod (P : CLFun F ι ℓ) (Q : CLFun F κ ℓ) : CLFun F (ι ⊕ κ) ℓ :=
  (P.embed (Function.Embedding.inl)).directSum (Q.embed (Function.Embedding.inr))

omit [DecidableEq ι] [DecidableEq κ] in
theorem disjoint_map_inl_inr (S : Finset ι) (S' : Finset κ) :
    Disjoint (S.map Function.Embedding.inl) (S'.map Function.Embedding.inr) := by
  rw [Finset.disjoint_left]
  intro a ha ha'
  obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp ha
  obtain ⟨j, -, h⟩ := Finset.mem_map.mp ha'
  cases h

theorem ExactlyOn.prod [Fintype ι] [Fintype κ] {P : CLFun F ι ℓ} {Q : CLFun F κ ℓ}
    (hP : P.ExactlyOn univ) (hQ : Q.ExactlyOn univ) : (P.prod Q).ExactlyOn univ := by
  have h := (hP.embed Function.Embedding.inl).directSum (hQ.embed Function.Embedding.inr)
    (disjoint_map_inl_inr _ _)
  have hu : (univ : Finset ι).map Function.Embedding.inl ∪ (univ : Finset κ).map
      Function.Embedding.inr = univ := by
    ext a; rcases a with i | j <;> simp
  rwa [hu] at h

theorem eval_prod [Fintype ι] [Fintype κ] (P : CLFun F ι ℓ) (Q : CLFun F κ ℓ)
    (hP : P.ExactlyOn univ) (hQ : Q.ExactlyOn univ) (x : ι ⊕ κ → F) :
    (P.prod Q).eval x
      = Sum.elim (P.eval (fun i => x (.inl i))) (Q.eval (fun j => x (.inr j))) := by
  rw [prod, SupportedOn.eval_directSum ((hP.embed _).supportedOn) ((hQ.embed _).supportedOn)
    (disjoint_map_inl_inr _ _), eval_embed, eval_embed]
  funext a
  rcases a with i | j
  · simp only [Pi.add_apply, push_inl_left, push_inr_left, add_zero, Sum.elim_inl]
    rfl
  · simp only [Pi.add_apply, push_inl_right, push_inr_right, zero_add, Sum.elim_inr]
    rfl

end MIPRE.CL.CLFun

end
