/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.CL.DetypingSoundness

/-! # Detyping with different answer alphabets

Soundness allows coarse-graining the detyped answers on the same state. The
only predicate hypothesis is the required acceptance implication on valid
questions; the longer-answer predicate may reject additional answers. This
accounts for the cutoff/truncation distinction in `types.tex`.
-/

noncomputable section

namespace MIPRE.CL.Detyping

open Finset Classical

variable {T ι A B A' B' : Type*} [Fintype T] [DecidableEq T]
  [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B] [Fintype A'] [Fintype B']
  [DecidableEq A'] [DecidableEq B']

/-- Restrict to typed views and merge answer outcomes, retaining the original state. -/
def restrictAnswers {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
    (hne : (Graph.edges E).Nonempty) (P : Bool → T → CLFun (ZMod 2) ι ℓ)
    (D : Question T ι → Question T ι → A → B → Bool)
    (D' : Question T ι → Question T ι → A' → B' → Bool)
    (rA : Question T ι → A → A') (rB : Question T ι → B → B')
    (S : TensorProductStrategy (game E P D)) : TensorProductStrategy (typedGame E hne P D') :=
  S.adapt (typedGame E hne P D') (question E false) (question E true) rA rB

/-- Coarse-graining after restriction literally preserves the shared state. -/
theorem restrictAnswers_state {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
    (hne : (Graph.edges E).Nonempty) (P : Bool → T → CLFun (ZMod 2) ι ℓ)
    (D : Question T ι → Question T ι → A → B → Bool)
    (D' : Question T ι → Question T ι → A' → B' → Bool)
    (rA : Question T ι → A → A') (rB : Question T ι → B → B')
    (S : TensorProductStrategy (game E P D)) :
    (restrictAnswers E hne P D D' rA rB S).ψ = S.ψ := rfl

/-- Acceptance-preserving answer maps cannot increase conditional failure on an edge. -/
theorem restrictAnswers_failAt_le {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
    (hne : (Graph.edges E).Nonempty) (P : Bool → T → CLFun (ZMod 2) ι ℓ)
    (D : Question T ι → Question T ι → A → B → Bool)
    (D' : Question T ι → Question T ι → A' → B' → Bool)
    (rA : Question T ι → A → A') (rB : Question T ι → B → B')
    (S : TensorProductStrategy (game E P D)) (x y : Question T ι) (hxy : E x.1 y.1)
    (hD : ∀ a b, D x y a b = true → D' x y (rA x a) (rB y b) = true) :
    (restrictAnswers E hne P D D' rA rB S).failAt x y ≤
      (restrict E hne P D S).failAt x y := by
  rw [restrict_failAt E hne P D S x y hxy]
  apply S.failAt_adapt_le
  intro a b h
  apply hD a b
  exact (accepts_question E D x y hxy a b).symm.trans h

/-- The same-state soundness factor survives answer truncation and cutoff rejections. -/
theorem restrictAnswers_failure_le {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
    (hE : ∀ u v, E u v → E v u) (hne : (Graph.edges E).Nonempty)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ) (hP : ∀ w t, (P w t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (D : Question T ι → Question T ι → A → B → Bool)
    (D' : Question T ι → Question T ι → A' → B' → Bool)
    (rA : Question T ι → A → A') (rB : Question T ι → B → B')
    (hD : ∀ x y, E x.1 y.1 → ∀ a b, D x y a b = true → D' x y (rA x a) (rB y b) = true)
    (S : TensorProductStrategy (game E P D)) :
    1 - (restrictAnswers E hne P D D' rA rB S).value ≤
      (16 : ℝ) ^ Fintype.card T * (1 - S.value) := by
  apply le_trans _ (restrict_failure_le E hE hne P hP hℓ D S)
  rw [typed_failure E hne P D', typed_failure E hne P D]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro uv huv
  have he : E uv.1 uv.2 := (Finset.mem_filter.mp huv).2
  apply Finset.sum_le_sum
  intro z _
  exact restrictAnswers_failAt_le E hne P D D' rA rB S _ _ he (hD _ _ he)

/-- A near-perfect longer-answer strategy yields the asserted shorter-answer strategy. -/
theorem restrictAnswers_value_ge {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
    (hE : ∀ u v, E u v → E v u) (hne : (Graph.edges E).Nonempty)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ) (hP : ∀ w t, (P w t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (D : Question T ι → Question T ι → A → B → Bool)
    (D' : Question T ι → Question T ι → A' → B' → Bool)
    (rA : Question T ι → A → A') (rB : Question T ι → B → B')
    (hD : ∀ x y, E x.1 y.1 → ∀ a b, D x y a b = true → D' x y (rA x a) (rB y b) = true)
    (S : TensorProductStrategy (game E P D)) {ε : ℝ} (hS : 1 - ε ≤ S.value) :
    1 - (16 : ℝ) ^ Fintype.card T * ε ≤ (restrictAnswers E hne P D D' rA rB S).value := by
  have h := restrictAnswers_failure_le E hE hne P hP hℓ D D' rA rB hD S
  have hp : 0 ≤ (16 : ℝ) ^ Fintype.card T := pow_nonneg (by norm_num) _
  nlinarith

end MIPRE.CL.Detyping
