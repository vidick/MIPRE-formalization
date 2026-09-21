/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.TypeGraph
import MIPRE.Foundations.CL.DetypingGame

/-! # The typed introspection CL presentation

The three-level Pauli presentations are retained verbatim. Every auxiliary
type uses the zero presentation, padded to three levels with a full factor
partition. Both players use the same family. The corresponding finite game
has an exactly uniform ordered-edge law, and the cross-introspection edge
asks the two zero-content questions with probability the inverse edge count.
-/

noncomputable section

namespace MIPRE.Introspection.TypedPresentation

open Finset Classical

variable {PauliType F ι : Type*} [Fintype ι] [DecidableEq ι] [Semiring F] {ℓ : ℕ}

/-- The typed sampler's complete three-level CL family. -/
def family (P : PauliType → CL.CLFun F ι 3) : QuestionType PauliType ℓ → CL.CLFun F ι 3
  | .inl p => P p
  | .inr _ => CL.CLFun.zeroOn univ 3

/-- The inherited Pauli presentations are unchanged. -/
theorem family_pauli (P : PauliType → CL.CLFun F ι 3) (p : PauliType) :
    family (ℓ := ℓ) P (QuestionType.pauli p) = P p := rfl

/-- The auxiliary zero presentation still partitions the full register. -/
theorem family_exactlyOn (P : PauliType → CL.CLFun F ι 3)
    (hP : ∀ p, (P p).ExactlyOn univ) (t : QuestionType PauliType ℓ) :
    (family P t).ExactlyOn univ := by
  cases t with
  | inl p => exact hP p
  | inr t => exact CL.CLFun.zeroOn_exactlyOn univ 3 (by omega)

/-- All auxiliary questions have zero content. -/
@[simp] theorem eval_aux (P : PauliType → CL.CLFun F ι 3) (t : AuxType ℓ)
    (w : Bool) (z : ι → F) : (family P (.inr (t, w))).eval z = 0 :=
  CL.CLFun.eval_zeroOn univ 3 z

/-- The zero-content assertion holds at every truncation level. -/
theorem marginal_aux (P : PauliType → CL.CLFun F ι 3) (t : AuxType ℓ)
    (w : Bool) (j : ℕ) (z : ι → F) : ((family P (.inr (t, w))).truncate j).eval z = 0 :=
  CL.CLFun.eval_truncate_zeroOn univ 3 j z

/-- Every linear query for an auxiliary question is the zero map. -/
theorem linear_aux (P : PauliType → CL.CLFun F ι 3) (t : AuxType ℓ)
    (w : Bool) (j : ℕ) (u : ι → F) : (family P (.inr (t, w))).mapOfPrefix j u = 0 :=
  CL.CLFun.mapOfPrefix_zeroOn univ 3 j u

/-- The first auxiliary factor consumes the register; later factors are empty. -/
theorem factor_aux (P : PauliType → CL.CLFun F ι 3) (t : AuxType ℓ)
    (w : Bool) (j : ℕ) (u : ι → F) :
    (family P (.inr (t, w))).factorOfPrefix j u = if j = 0 then univ else ∅ := by
  simpa [family] using CL.CLFun.factorOfPrefix_zeroOn (F := F) (univ : Finset ι) 3 j u

/-- Auxiliary questions jointly have zero content even though their seed is shared. -/
theorem joint_aux_zero (P : PauliType → CL.CLFun F ι 3) (t u : AuxType ℓ)
    (w w' : Bool) (z : ι → F) :
    ((family P (.inr (t, w))).eval z, (family P (.inr (u, w'))).eval z) = (0, 0) := by simp

section Game

variable [Fintype PauliType] [DecidableEq PauliType]
  {A B : Type*} [Fintype A] [Fintype B]

/-- The actual finite typed introspection game, for the supplied decision predicate. -/
def game (E : PauliType → PauliType → Bool) (X Z : PauliType) (ℓ : ℕ)
    (P : PauliType → CL.CLFun (ZMod 2) ι 3)
    (D : CL.Detyping.Question (QuestionType PauliType ℓ) ι →
      CL.Detyping.Question (QuestionType PauliType ℓ) ι → A → B → Bool) :=
  CL.Detyping.typedGame (TypeGraph.Adj E X Z) (TypeGraph.edges_nonempty E X Z ℓ)
    (fun _ => family P) D

/-- A fixed edge between auxiliary types has exactly inverse-edge-count probability. -/
theorem mu_aux (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) ι 3)
    (D : CL.Detyping.Question (QuestionType PauliType ℓ) ι →
      CL.Detyping.Question (QuestionType PauliType ℓ) ι → A → B → Bool)
    (t u : AuxType ℓ) (w w' : Bool)
    (h : TypeGraph.Adj E X Z (.inr (t, w)) (.inr (u, w'))) :
    (game E X Z ℓ P D).μ (.inr (t, w), 0) (.inr (u, w'), 0) =
      ((TypeGraph.edges E X Z ℓ).card : ℝ)⁻¹ := by
  let G := TypeGraph.Adj (ℓ := ℓ) E X Z
  let e₀ : CL.Detyping.Edge G := ⟨(.inr (t, w), .inr (u, w')), by
    simp only [CL.Graph.edges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h⟩
  have heq (e : CL.Detyping.Edge G) (z : ι → ZMod 2) :
      (CL.Detyping.typedQuestion (fun _ => family P) false (e, z),
        CL.Detyping.typedQuestion (fun _ => family P) true (e, z)) =
        ((.inr (t, w), 0), (.inr (u, w'), 0)) ↔ e = e₀ := by
    constructor
    · intro hh
      apply Subtype.ext
      have hh' := congrArg (fun p => (p.1.1, p.2.1)) hh
      exact hh'
    · rintro rfl
      simp [CL.Detyping.typedQuestion, e₀]
  unfold game CL.Detyping.typedGame SampledGame.game SampledGame.dist
  dsimp only
  simp only [Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type, heq,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, mul_one]
  have hc : (Fintype.card (ι → ZMod 2) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [mul_inv_rev, mul_assoc, mul_left_comm, inv_mul_cancel₀ hc, mul_one]
  simp only [Fintype.card_coe, TypeGraph.edges]

/-- The cross-introspection test occurs at exactly the inverse ordered-edge count. -/
theorem mu_cross_introspect (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) ι 3)
    (D : CL.Detyping.Question (QuestionType PauliType ℓ) ι →
      CL.Detyping.Question (QuestionType PauliType ℓ) ι → A → B → Bool) :
    (game E X Z ℓ P D).μ (QuestionType.introspect false, 0) (QuestionType.introspect true, 0) =
      ((TypeGraph.edges E X Z ℓ).card : ℝ)⁻¹ :=
  mu_aux E X Z P D .introspect .introspect false true (TypeGraph.adj_cross_introspect E X Z)

/-- Failure on one auxiliary edge is bounded by the ordered-edge count times total failure. -/
theorem failAt_aux_le (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) ι 3)
    (D : CL.Detyping.Question (QuestionType PauliType ℓ) ι →
      CL.Detyping.Question (QuestionType PauliType ℓ) ι → A → B → Bool)
    (S : TensorProductStrategy (game E X Z ℓ P D))
    (t u : AuxType ℓ) (w w' : Bool)
    (h : TypeGraph.Adj E X Z (.inr (t, w)) (.inr (u, w'))) :
    S.failAt (.inr (t, w), 0) (.inr (u, w'), 0) ≤
      (TypeGraph.edges E X Z ℓ).card * (1 - S.value) := by
  let x : CL.Detyping.Question (QuestionType PauliType ℓ) ι := (.inr (t, w), 0)
  let y : CL.Detyping.Question (QuestionType PauliType ℓ) ι := (.inr (u, w'), 0)
  have hterm : (game E X Z ℓ P D).μ x y * S.failAt x y ≤ 1 - S.value := by
    rw [S.one_sub_value_eq_sum_failAt]
    apply le_trans (Finset.single_le_sum (f := fun q => (game E X Z ℓ P D).μ x q * S.failAt x q)
      (fun q _ => mul_nonneg ((game E X Z ℓ P D).μ_nonneg x q) (S.failAt_nonneg x q)) (mem_univ y))
    exact Finset.single_le_sum
      (fun p _ => Finset.sum_nonneg fun q _ =>
        mul_nonneg ((game E X Z ℓ P D).μ_nonneg p q) (S.failAt_nonneg p q)) (mem_univ x)
  change (game E X Z ℓ P D).μ (.inr (t, w), 0) (.inr (u, w'), 0) * _ ≤ _ at hterm
  rw [mu_aux E X Z P D t u w w' h, inv_mul_eq_div] at hterm
  have hc : (0 : ℝ) < (TypeGraph.edges E X Z ℓ).card := by
    exact_mod_cast (TypeGraph.edges_nonempty E X Z ℓ).card_pos
  simpa [mul_comm] using (div_le_iff₀ hc).mp hterm

/-- Near-perfect typed play gives the cross-introspection bound used in extraction. -/
theorem failAt_cross_introspect_le (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) ι 3)
    (D : CL.Detyping.Question (QuestionType PauliType ℓ) ι →
      CL.Detyping.Question (QuestionType PauliType ℓ) ι → A → B → Bool)
    (S : TensorProductStrategy (game E X Z ℓ P D)) {ε : ℝ} (hS : 1 - ε ≤ S.value) :
    S.failAt (QuestionType.introspect false, 0) (QuestionType.introspect true, 0) ≤
      (TypeGraph.edges E X Z ℓ).card * ε := by
  have h := failAt_aux_le E X Z P D S .introspect .introspect false true
    (TypeGraph.adj_cross_introspect E X Z)
  have hc : (0 : ℝ) ≤ (TypeGraph.edges E X Z ℓ).card := Nat.cast_nonneg _
  nlinarith

end Game
end MIPRE.Introspection.TypedPresentation
