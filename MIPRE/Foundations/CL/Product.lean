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

/-! ## The queries of a direct sum

A sampler answers marginal, linear-map and factor queries (`truncate`, `mapOfPrefix`,
`factorOfPrefix`). For a direct sum of presentations on disjoint register subspaces each query is
answered componentwise; for a padded presentation, as for the unpadded one. -/

variable [Fintype ι]

/-- A presentation on `V_T` reads its prefix only on `T`. -/
theorem SupportedOn.factorOfPrefix_proj {P : CLFun F ι ℓ} {T U : Finset ι} (hP : P.SupportedOn T)
    (h : T ⊆ U) (j : ℕ) (u : ι → F) : P.factorOfPrefix j (proj U u) = P.factorOfPrefix j u := by
  induction P generalizing T U j u with
  | zero => rfl
  | cons S L next ih =>
    obtain ⟨hS, hnext⟩ := hP
    cases j with
    | zero => rfl
    | succ j =>
      have h₁ : T \ S ⊆ Sᶜ ∩ U := fun i hi => by
        rw [Finset.mem_sdiff] at hi
        exact Finset.mem_inter.mpr ⟨Finset.mem_compl.mpr hi.2, h hi.1⟩
      have h₂ : T \ S ⊆ Sᶜ := fun i hi => Finset.mem_compl.mpr (Finset.mem_sdiff.mp hi).2
      simp only [factorOfPrefix_cons_succ, proj_proj_of_subset (hS.trans h), proj_proj]
      rw [ih _ (hnext _) h₁, ih _ (hnext _) h₂]

/-- A presentation on `V_T` reads its prefix only on `T`. -/
theorem SupportedOn.mapOfPrefix_proj {P : CLFun F ι ℓ} {T U : Finset ι} (hP : P.SupportedOn T)
    (h : T ⊆ U) (j : ℕ) (u : ι → F) : P.mapOfPrefix j (proj U u) = P.mapOfPrefix j u := by
  induction P generalizing T U j u with
  | zero => rfl
  | cons S L next ih =>
    obtain ⟨hS, hnext⟩ := hP
    cases j with
    | zero => rfl
    | succ j =>
      have h₁ : T \ S ⊆ Sᶜ ∩ U := fun i hi => by
        rw [Finset.mem_sdiff] at hi
        exact Finset.mem_inter.mpr ⟨Finset.mem_compl.mpr hi.2, h hi.1⟩
      have h₂ : T \ S ⊆ Sᶜ := fun i hi => Finset.mem_compl.mpr (Finset.mem_sdiff.mp hi).2
      simp only [mapOfPrefix_cons_succ, proj_proj_of_subset (hS.trans h), proj_proj]
      rw [ih _ (hnext _) h₁, ih _ (hnext _) h₂]

private theorem sdiff_subset_compl_union {S S' T T' : Finset ι} (hS' : S' ⊆ T')
    (hTT' : Disjoint T T') : T \ S ⊆ (S ∪ S')ᶜ := fun i hi => by
  rw [Finset.mem_sdiff] at hi
  rw [Finset.mem_compl, Finset.mem_union]
  exact fun h => h.elim hi.2 fun h' => Finset.disjoint_left.mp hTT' hi.1 (hS' h')

private theorem sdiff_subset_compl {S T : Finset ι} : T \ S ⊆ Sᶜ := fun _ hi =>
  Finset.mem_compl.mpr (Finset.mem_sdiff.mp hi).2

theorem factorOfPrefix_directSum {P Q : CLFun F ι ℓ} {T T' : Finset ι} (hP : P.SupportedOn T)
    (hQ : Q.SupportedOn T') (hTT' : Disjoint T T') (j : ℕ) (u : ι → F) :
    (P.directSum Q).factorOfPrefix j u = P.factorOfPrefix j u ∪ Q.factorOfPrefix j u := by
  induction P generalizing T T' j u with
  | zero => rw [Q.eq_zero]; simp
  | cons S L next ih =>
    cases Q with
    | cons S' L' next' =>
      obtain ⟨hS, hnext⟩ := hP
      obtain ⟨hS', hnext'⟩ := hQ
      cases j with
      | zero => rfl
      | succ j =>
        simp only [directSum_cons, factorOfPrefix_cons_succ,
          proj_proj_of_subset Finset.subset_union_left,
          proj_proj_of_subset Finset.subset_union_right]
        rw [ih _ (hnext _) (hnext' _) (Finset.disjoint_of_subset_left Finset.sdiff_subset
          (Finset.disjoint_of_subset_right Finset.sdiff_subset hTT')),
          (hnext _).factorOfPrefix_proj (sdiff_subset_compl_union hS' hTT'),
          (hnext' _).factorOfPrefix_proj (Finset.union_comm S S' ▸
            sdiff_subset_compl_union hS hTT'.symm),
          (hnext _).factorOfPrefix_proj sdiff_subset_compl,
          (hnext' _).factorOfPrefix_proj sdiff_subset_compl]

theorem mapOfPrefix_directSum {P Q : CLFun F ι ℓ} {T T' : Finset ι} (hP : P.SupportedOn T)
    (hQ : Q.SupportedOn T') (hTT' : Disjoint T T') (j : ℕ) (u : ι → F) :
    (P.directSum Q).mapOfPrefix j u = P.mapOfPrefix j u + Q.mapOfPrefix j u := by
  induction P generalizing T T' j u with
  | zero => rw [Q.eq_zero]; simp
  | cons S L next ih =>
    cases Q with
    | cons S' L' next' =>
      obtain ⟨hS, hnext⟩ := hP
      obtain ⟨hS', hnext'⟩ := hQ
      cases j with
      | zero => rfl
      | succ j =>
        simp only [directSum_cons, mapOfPrefix_cons_succ,
          proj_proj_of_subset Finset.subset_union_left,
          proj_proj_of_subset Finset.subset_union_right]
        rw [ih _ (hnext _) (hnext' _) (Finset.disjoint_of_subset_left Finset.sdiff_subset
          (Finset.disjoint_of_subset_right Finset.sdiff_subset hTT')),
          (hnext _).mapOfPrefix_proj (sdiff_subset_compl_union hS' hTT'),
          (hnext' _).mapOfPrefix_proj (Finset.union_comm S S' ▸
            sdiff_subset_compl_union hS hTT'.symm),
          (hnext _).mapOfPrefix_proj sdiff_subset_compl,
          (hnext' _).mapOfPrefix_proj sdiff_subset_compl]

theorem eval_truncate_directSum {P Q : CLFun F ι ℓ} {T T' : Finset ι} (hP : P.SupportedOn T)
    (hQ : Q.SupportedOn T') (hTT' : Disjoint T T') (j : ℕ) (x : ι → F) :
    ((P.directSum Q).truncate j).eval x = (P.truncate j).eval x + (Q.truncate j).eval x := by
  induction j generalizing ℓ P Q T T' x with
  | zero => simp
  | succ j ih =>
    cases P with
    | zero => rw [Q.eq_zero]; simp [eval_truncate_zero]
    | cons S L next =>
      cases Q with
      | cons S' L' next' =>
        obtain ⟨hS, hnext⟩ := hP
        obtain ⟨hS', hnext'⟩ := hQ
        have hSS' : Disjoint S S' :=
          Finset.disjoint_of_subset_left hS (Finset.disjoint_of_subset_right hS' hTT')
        have h₁ : proj S (L.directSum L' x) = L x := by
          rw [RegLinear.directSum_apply, map_add, L.proj_apply, L'.proj_apply_of_disjoint hSS',
            add_zero]
        have h₂ : proj S' (L.directSum L' x) = L' x := by
          rw [RegLinear.directSum_apply, map_add, L.proj_apply_of_disjoint hSS'.symm,
            L'.proj_apply, zero_add]
        rw [directSum_cons, truncate_succ_cons, eval_cons, h₁, h₂,
          ih (hnext _) (hnext' _) (Finset.disjoint_of_subset_left Finset.sdiff_subset
            (Finset.disjoint_of_subset_right Finset.sdiff_subset hTT')),
          truncate_succ_cons, truncate_succ_cons, eval_cons, eval_cons,
          RegLinear.directSum_apply,
          ((hnext _).truncate j).eval_proj_of_subset (sdiff_subset_compl_union hS' hTT'),
          ((hnext' _).truncate j).eval_proj_of_subset (Finset.union_comm S S' ▸
            sdiff_subset_compl_union hS hTT'.symm),
          ((hnext _).truncate j).eval_proj_of_subset sdiff_subset_compl,
          ((hnext' _).truncate j).eval_proj_of_subset sdiff_subset_compl,
          add_add_add_comm]

/-! ## The queries of a padded presentation -/

theorem eval_truncate_lift (T : Finset ι) (P : CLFun F ι ℓ) (j : ℕ) (x : ι → F) :
    ((P.lift T).truncate j).eval x = (P.truncate j).eval x := by
  induction j generalizing ℓ P T x with
  | zero => simp
  | succ j ih =>
    cases P with
    | zero => simp [lift, eval_truncate_zero]
    | cons S L next => simp only [lift, truncate_succ_cons, eval_cons, ih]

theorem factorOfPrefix_lift {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.ExactlyOn T) (j : ℕ)
    (u : ι → F) : (P.lift T).factorOfPrefix j u = P.factorOfPrefix j u := by
  induction P generalizing T j u with
  | zero =>
    have hT : T = ∅ := hP
    cases j <;> simp [lift, hT]
  | cons S L next ih =>
    cases j with
    | zero => rfl
    | succ j => exact ih _ (hP.2 _) _ _

theorem mapOfPrefix_lift (T : Finset ι) (P : CLFun F ι ℓ) (j : ℕ) (u : ι → F) :
    (P.lift T).mapOfPrefix j u = P.mapOfPrefix j u := by
  induction P generalizing T j u with
  | zero => cases j <;> rfl
  | cons S L next ih =>
    cases j with
    | zero => rfl
    | succ j => exact ih _ _ _ _

theorem eval_truncate_liftN (T : Finset ι) (n : ℕ) (P : CLFun F ι ℓ) (j : ℕ) (x : ι → F) :
    ((P.liftN T n).truncate j).eval x = (P.truncate j).eval x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [liftN, eval_truncate_lift, ih]

theorem factorOfPrefix_liftN {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.ExactlyOn T) (n j : ℕ)
    (u : ι → F) : (P.liftN T n).factorOfPrefix j u = P.factorOfPrefix j u := by
  induction n with
  | zero => rfl
  | succ n ih => rw [liftN, factorOfPrefix_lift (hP.liftN n), ih]

theorem mapOfPrefix_liftN (T : Finset ι) (n : ℕ) (P : CLFun F ι ℓ) (j : ℕ) (u : ι → F) :
    (P.liftN T n).mapOfPrefix j u = P.mapOfPrefix j u := by
  induction n with
  | zero => rfl
  | succ n ih => rw [liftN, mapOfPrefix_lift, ih]

@[simp] theorem eval_truncate_liftTo (T : Finset ι) (L : ℕ) (h : ℓ ≤ L) (P : CLFun F ι ℓ) (j : ℕ)
    (x : ι → F) : ((P.liftTo T L h).truncate j).eval x = (P.truncate j).eval x := by
  rw [liftTo, truncate_castLevel, eval_truncate_liftN]

theorem factorOfPrefix_liftTo {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.ExactlyOn T) (L : ℕ)
    (h : ℓ ≤ L) (j : ℕ) (u : ι → F) :
    (P.liftTo T L h).factorOfPrefix j u = P.factorOfPrefix j u := by
  rw [liftTo, factorOfPrefix_castLevel, factorOfPrefix_liftN hP]

@[simp] theorem mapOfPrefix_liftTo (T : Finset ι) (L : ℕ) (h : ℓ ≤ L) (P : CLFun F ι ℓ) (j : ℕ)
    (u : ι → F) : (P.liftTo T L h).mapOfPrefix j u = P.mapOfPrefix j u := by
  rw [liftTo, mapOfPrefix_castLevel, mapOfPrefix_liftN]

/-! ## The queries of a product -/

variable [Fintype κ]

theorem eval_truncate_prod (P : CLFun F ι ℓ) (Q : CLFun F κ ℓ) (hP : P.ExactlyOn univ)
    (hQ : Q.ExactlyOn univ) (j : ℕ) (x : ι ⊕ κ → F) :
    ((P.prod Q).truncate j).eval x
      = Sum.elim ((P.truncate j).eval (fun i => x (.inl i)))
          ((Q.truncate j).eval (fun i => x (.inr i))) := by
  rw [prod, eval_truncate_directSum ((hP.embed _).supportedOn) ((hQ.embed _).supportedOn)
    (disjoint_map_inl_inr _ _), eval_truncate_embed, eval_truncate_embed]
  funext a
  rcases a with i | i
  · simp only [Pi.add_apply, push_inl_left, push_inr_left, add_zero, Sum.elim_inl]
    rfl
  · simp only [Pi.add_apply, push_inl_right, push_inr_right, zero_add, Sum.elim_inr]
    rfl

theorem factorOfPrefix_prod (P : CLFun F ι ℓ) (Q : CLFun F κ ℓ) (hP : P.ExactlyOn univ)
    (hQ : Q.ExactlyOn univ) (j : ℕ) (u : ι ⊕ κ → F) :
    (P.prod Q).factorOfPrefix j u
      = (P.factorOfPrefix j (fun i => u (.inl i))).map Function.Embedding.inl ∪
          (Q.factorOfPrefix j (fun i => u (.inr i))).map Function.Embedding.inr := by
  rw [prod, factorOfPrefix_directSum ((hP.embed _).supportedOn) ((hQ.embed _).supportedOn)
    (disjoint_map_inl_inr _ _), factorOfPrefix_embed, factorOfPrefix_embed]
  rfl

theorem mapOfPrefix_prod (P : CLFun F ι ℓ) (Q : CLFun F κ ℓ) (hP : P.ExactlyOn univ)
    (hQ : Q.ExactlyOn univ) (j : ℕ) (u y : ι ⊕ κ → F) :
    (P.prod Q).mapOfPrefix j u y
      = Sum.elim (P.mapOfPrefix j (fun i => u (.inl i)) (fun i => y (.inl i)))
          (Q.mapOfPrefix j (fun i => u (.inr i)) (fun i => y (.inr i))) := by
  rw [prod, mapOfPrefix_directSum ((hP.embed _).supportedOn) ((hQ.embed _).supportedOn)
    (disjoint_map_inl_inr _ _), LinearMap.add_apply, mapOfPrefix_embed, mapOfPrefix_embed]
  funext a
  rcases a with i | i
  · simp only [Pi.add_apply, push_inl_left, push_inr_left, add_zero, Sum.elim_inl]
    rfl
  · simp only [Pi.add_apply, push_inl_right, push_inr_right, zero_add, Sum.elim_inr]
    rfl

end MIPRE.CL.CLFun

end
