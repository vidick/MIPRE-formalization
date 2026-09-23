/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.SourcePadding

/-! # Queries for source padding at unchanged depth

The extra zero register is consumed at the first factor. Linear queries are
the original queries extended by zero; subsequent factor queries have no
extra coordinates. These equations hold for arbitrary prefixes.
-/

noncomputable section
namespace MIPRE.Introspection.SourcePadding
open Finset Classical CL

variable {F I J : Type*} [Field F]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

private theorem pull_proj_union_compl (e : I ↪ J) (S : Finset I) (O : Finset J)
    (hO : Disjoint (univ.map e) O) (x : J → F) :
    pull e (proj (S.map e ∪ O)ᶜ x) = proj Sᶜ (pull e x) := by
  funext i
  have hi : e i ∉ O := Finset.disjoint_left.mp hO (by simp)
  simp [pull, hi]

/-- Every padded marginal is the original marginal extended by zero. -/
theorem eval_truncate_embed_zeroOn (e : I ↪ J) {ℓ : ℕ} (P : CLFun F I ℓ)
    (O : Finset J) (hO : Disjoint (univ.map e) O) (j : ℕ) (x : J → F) :
    (((P.embed e).directSum (CLFun.zeroOn O ℓ)).truncate j).eval x =
      push e ((P.truncate j).eval (pull e x)) := by
  induction j generalizing ℓ P O x with
  | zero => simp
  | succ j ih =>
    cases P with
    | zero => simp [CLFun.embed, CLFun.zeroOn, CLFun.eval_truncate_zero]
    | cons S L next =>
      simp only [CLFun.embed, CLFun.zeroOn, CLFun.directSum_cons,
        CLFun.truncate_succ_cons, CLFun.eval_cons, RegLinear.directSum_apply,
        RegLinear.zero_apply, add_zero, RegLinear.embed_apply]
      rw [proj_push, L.proj_apply, pull_push,
        ih _ ∅ (by simp), pull_proj_union_compl e S O hO, push_add]

theorem depthFamily_eval_truncate {ℓ : ℕ} (e : I ↪ J) (L : Bool → CLFun F I ℓ)
    (w : Bool) (j : ℕ) (x : J → F) :
    ((depthFamily e L w).truncate j).eval x =
      push e (((L w).truncate j).eval (pull e x)) :=
  eval_truncate_embed_zeroOn e (L w) _
    (Finset.disjoint_left.mpr fun i hi hci => (Finset.mem_compl.mp hci) hi) j x

theorem pull_attained_prefix {ℓ : ℕ} (e : I ↪ J) (L : Bool → CLFun F I ℓ)
    (w : Bool) (j : ℕ) (u : J → F)
    (hu : ∃ x, u = ((depthFamily e L w).truncate j).eval x) :
    ∃ x, pull e u = ((L w).truncate j).eval x := by
  obtain ⟨x, rfl⟩ := hu
  refine ⟨pull e x, ?_⟩
  rw [depthFamily_eval_truncate, pull_push]

/-- Zero padding does not change any source linear map query. -/
theorem mapOfPrefix_embed_zeroOn (e : I ↪ J) {ℓ : ℕ} (P : CLFun F I ℓ)
    (O : Finset J) (hO : Disjoint (univ.map e) O) (j : ℕ) (u y : J → F) :
    ((P.embed e).directSum (CLFun.zeroOn O ℓ)).mapOfPrefix j u y =
      push e (P.mapOfPrefix j (pull e u) (pull e y)) := by
  induction P generalizing O j u with
  | zero => simp [CLFun.embed, CLFun.zeroOn]
  | cons S L next ih =>
    cases j with
    | zero =>
      simp [CLFun.embed, CLFun.zeroOn, RegLinear.directSum_apply]
    | succ j =>
      simp only [CLFun.embed, CLFun.zeroOn, CLFun.directSum_cons,
        CLFun.mapOfPrefix_cons_succ]
      rw [proj_proj_of_subset Finset.subset_union_left, pull_proj,
        ih _ ∅ (by simp), pull_proj_union_compl e S O hO]

/-- Only the first source factor also consumes the unused coordinates. -/
theorem factorOfPrefix_embed_zeroOn (e : I ↪ J) {ℓ : ℕ} (P : CLFun F I ℓ)
    (O : Finset J) (hO : Disjoint (univ.map e) O) (j : ℕ) (u : J → F) :
    ((P.embed e).directSum (CLFun.zeroOn O ℓ)).factorOfPrefix j u =
      (P.factorOfPrefix j (pull e u)).map e ∪ (if ℓ = 0 ∨ j ≠ 0 then ∅ else O) := by
  induction P generalizing O j u with
  | zero => simp [CLFun.embed, CLFun.zeroOn]
  | cons S L next ih =>
    cases j with
    | zero => simp [CLFun.embed, CLFun.zeroOn]
    | succ j =>
      simp only [CLFun.embed, CLFun.zeroOn, CLFun.directSum_cons,
        CLFun.factorOfPrefix_cons_succ]
      rw [proj_proj_of_subset Finset.subset_union_left, pull_proj,
        ih _ ∅ (by simp), pull_proj_union_compl e S O hO]
      simp

theorem depthFamily_mapOfPrefix {ℓ : ℕ} (e : I ↪ J) (L : Bool → CLFun F I ℓ)
    (w : Bool) (j : ℕ) (u y : J → F) :
    (depthFamily e L w).mapOfPrefix j u y =
      push e ((L w).mapOfPrefix j (pull e u) (pull e y)) := by
  exact mapOfPrefix_embed_zeroOn e (L w) _
    (Finset.disjoint_left.mpr fun i hi hci => (Finset.mem_compl.mp hci) hi) j u y

theorem depthFamily_factorOfPrefix {ℓ : ℕ} (e : I ↪ J) (L : Bool → CLFun F I ℓ)
    (hℓ : 0 < ℓ) (w : Bool) (j : ℕ) (u : J → F) :
    (depthFamily e L w).factorOfPrefix j u =
      ((L w).factorOfPrefix j (pull e u)).map e ∪
        (if j = 0 then (univ.map e)ᶜ else ∅) := by
  rw [depthFamily, family, factorOfPrefix_embed_zeroOn e (L w) _
    (Finset.disjoint_left.mpr fun i hi hci => (Finset.mem_compl.mp hci) hi)]
  by_cases hj : j = 0 <;> simp [hj, Nat.ne_of_gt hℓ]

end MIPRE.Introspection.SourcePadding
end
