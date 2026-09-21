/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.CL.DetypingCompleteSupport

/-! # PCC completeness of finite-game detyping

The complete strategy uses the input strategy's dimension and one common
measurement rule for both players. Invalid local graph views select a constant
measurement. On jointly valid views, the original strategy is played on the
same ordered edge and common content seed.
-/

noncomputable section

namespace MIPRE.CL.Detyping

open Finset Classical Matrix Kronecker

private theorem sample_dist_pos_iff {S X Y : Type*} [Fintype S] [Nonempty S]
    [Fintype X] [Fintype Y] (qA : S → X) (qB : S → Y) (x : X) (y : Y) :
    0 < SampledGame.dist qA qB x y ↔ ∃ s, qA s = x ∧ qB s = y := by
  rw [SampledGame.dist_eq_card, div_pos_iff_of_pos_right (by exact_mod_cast Fintype.card_pos)]
  simp only [Nat.cast_pos, Finset.card_pos, Finset.nonempty_def, Finset.mem_filter,
    Finset.mem_univ, true_and]

private theorem sample_failAt_zero {U X Y A B : Type*} [Fintype U] [Nonempty U]
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (qA : U → X) (qB : U → Y) (D : X → Y → A → B → Bool)
    (S : TensorProductStrategy (SampledGame.game qA qB D)) (hS : S.value = 1) (u : U) :
    S.failAt (qA u) (qB u) = 0 := by
  have h := SampledGame.one_sub_value qA qB D S
  rw [hS, sub_self, eq_comm, div_eq_zero_iff] at h
  have hz : (Fintype.card U : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => S.failAt_nonneg (qA v) (qB v))).mp
    (h.resolve_right hz) u (Finset.mem_univ u)

private theorem failAt_zero_of_accepts {X Y A B : Type*} [Fintype X] [Fintype Y]
    [Fintype A] [Fintype B] {G : Game X Y A B} (S : TensorProductStrategy G)
    (x : X) (y : Y) (h : ∀ a b, G.D x y a b = true) : S.failAt x y = 0 := by
  simp only [TensorProductStrategy.failAt, TensorProductStrategy.succAt, h,
    ↓reduceIte, one_mul, S.sum_born, sub_self]

variable {T ι A : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
  [Fintype A] [DecidableEq A]

set_option linter.unusedSectionVars false

/-- The input measurements on decoded questions, with a deterministic fallback.
The outer doubling tag is ignored, so both players use literally the same rule. -/
def complete {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (hne : (Graph.edges E).Nonempty)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ)
    (D : Question T ι → Question T ι → A → A → Bool)
    (S : SyncStrategy (typedGame E hne P D).doubled) (a₀ : A) :
    SyncStrategy (game E P D).doubled where
  d := S.d
  d_pos := S.d_pos
  P :=
    { M := fun p a => match decodeQuestion E p.2 with
        | some q => S.P.M q a
        | none => if a = a₀ then 1 else 0
      selfAdjoint := fun p a => by
        cases decodeQuestion E p.2
        · split_ifs <;> simp
        · exact S.P.selfAdjoint _ _
      projective := fun p a => by
        cases decodeQuestion E p.2
        · split_ifs <;> simp
        · exact S.P.projective _ _
      normalized := fun p => by
        cases decodeQuestion E p.2
        · simp
        · exact S.P.normalized _ }

/-- Detyping keeps the Hilbert space dimension exactly. -/
theorem complete_d {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (hne : (Graph.edges E).Nonempty)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ)
    (D : Question T ι → Question T ι → A → A → Bool)
    (S : SyncStrategy (typedGame E hne P D).doubled) (a₀ : A) :
    (complete E hne P D S a₀).d = S.d := rfl

/-- The canonical tensor realizations use literally the same shared state. -/
theorem complete_state {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
    (hne : (Graph.edges E).Nonempty) (P : Bool → T → CLFun (ZMod 2) ι ℓ)
    (D : Question T ι → Question T ι → A → A → Bool)
    (S : SyncStrategy (typedGame E hne P D).doubled) (a₀ : A) :
    (complete E hne P D S a₀).toTensorProductStrategy.undouble.ψ =
      S.toTensorProductStrategy.undouble.ψ := rfl

/-- Both tagged players use the same measurement on every question, including invalid ones. -/
theorem complete_player_independent {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
    (hne : (Graph.edges E).Nonempty) (P : Bool → T → CLFun (ZMod 2) ι ℓ)
    (D : Question T ι → Question T ι → A → A → Bool)
    (S : SyncStrategy (typedGame E hne P D).doubled) (a₀ : A)
    (q : Coord T ι → ZMod 2) (a : A) :
    (complete E hne P D S a₀).P.M (false, q) a =
      (complete E hne P D S a₀).P.M (true, q) a := rfl

/-- On every valid view the common measurement rule is the original typed rule. -/
theorem complete_M_question {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
    (hne : (Graph.edges E).Nonempty) (P : Bool → T → CLFun (ZMod 2) ι ℓ)
    (D : Question T ι → Question T ι → A → A → Bool)
    (S : SyncStrategy (typedGame E hne P D).doubled) (a₀ : A)
    (tag w : Bool) (q : Question T ι) (a : A) :
    (complete E hne P D S a₀).P.M (tag, question E w q) a = S.P.M (w, q) a := by
  change (match decodeQuestion E (question E w q) with
    | some q' => S.P.M q' a | none => if a = a₀ then 1 else 0) = _
  rw [decodeQuestion_question]

/-- The typed distribution gives positive mass to every edge and content seed. -/
theorem typed_mu_pos {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
    (hne : (Graph.edges E).Nonempty) (P : Bool → T → CLFun (ZMod 2) ι ℓ)
    (D : Question T ι → Question T ι → A → A → Bool)
    {u v : T} (huv : E u v) (z : ι → ZMod 2) :
    0 < (typedGame E hne P D).μ (u, (P false u).eval z) (v, (P true v).eval z) := by
  let _ : Nonempty (Edge E) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  apply (sample_dist_pos_iff _ _ _ _).mpr
  refine ⟨(⟨(u, v), by simp [Graph.edges, huv]⟩, z), ?_, ?_⟩ <;> rfl

/-- At each detyped seed, the two measurements commute if the original strategy is PCC. -/
theorem complete_commutes_sample {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
    (hE : ∀ u v, E u v → E v u) (hne : (Graph.edges E).Nonempty)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ) (hP : ∀ w t, (P w t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (D : Question T ι → Question T ι → A → A → Bool)
    (S : SyncStrategy (typedGame E hne P D).doubled) (hS : S.IsPCC) (a₀ : A)
    (g : Graph.Coord T → ZMod 2) (z : ι → ZMod 2) (a b : A) :
    let R := complete E hne P D S a₀
    let x := (presentation E false (P false)).eval (Sum.elim g z)
    let y := (presentation E true (P true)).eval (Sum.elim g z)
    R.P.M (false, x) a * R.P.M (true, y) b = R.P.M (true, y) b * R.P.M (false, x) a := by
  dsimp only
  let M : Bool → A → Matrix (Fin S.d) (Fin S.d) ℂ := fun w a =>
    match decodeQuestion E ((presentation E w (P w)).eval (Sum.elim g z)) with
    | some q => S.P.M q a | none => if a = a₀ then 1 else 0
  change M false a * M true b = M true b * M false a
  dsimp only [M]
  simp only [decodeQuestion_output E false (P false) (hP false) hℓ,
    decodeQuestion_output E true (P true) (hP true) hℓ]
  cases hu : select E false g with
  | none => simp only [Option.map_none]; split_ifs <;> simp only [one_mul, mul_one, zero_mul, mul_zero]
  | some u =>
    cases hv : select E true g with
    | none => simp only [Option.map_some, Option.map_none]; split_ifs <;> simp only [one_mul, mul_one, zero_mul, mul_zero]
    | some v =>
      simp only [Option.map_some]
      apply hS
      simp only [Game.doubled_μ, and_self, ↓reduceIte]
      exact typed_mu_pos E hne P D (selects_pairSeed E hE g hu hv).1 z

/-- The completed strategy is PCC on the entire support of the detyped game. -/
theorem complete_isPCC {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
    (hE : ∀ u v, E u v → E v u) (hne : (Graph.edges E).Nonempty)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ) (hP : ∀ w t, (P w t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (D : Question T ι → Question T ι → A → A → Bool)
    (S : SyncStrategy (typedGame E hne P D).doubled) (hS : S.IsPCC) (a₀ : A) :
    (complete E hne P D S a₀).IsPCC := by
  rintro ⟨w, x⟩ ⟨w', y⟩ hxy a b
  rw [Game.doubled_μ] at hxy
  split_ifs at hxy with hw
  · rcases hw with ⟨rfl, rfl⟩
    obtain ⟨s, rfl, rfl⟩ := (sample_dist_pos_iff _ _ _ _).mp hxy
    have hs : s = Sum.elim (pull .inl s) (pull .inr s) := by ext p; cases p <;> rfl
    rw [hs]
    exact complete_commutes_sample E hE hne P hP hℓ D S hS a₀ _ _ a b
  · exact False.elim (lt_irrefl 0 hxy)

/-- If a player has an invalid local sample, the detyped predicate always accepts. -/
theorem accepts_sample_of_none {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
    (P : Bool → T → CLFun (ZMod 2) ι ℓ) (hP : ∀ w t, (P w t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (D : Question T ι → Question T ι → A → A → Bool)
    (g : Graph.Coord T → ZMod 2) (z : ι → ZMod 2)
    (h : select E false g = none ∨ select E true g = none) (a b : A) :
    accepts E D ((presentation E false (P false)).eval (Sum.elim g z))
      ((presentation E true (P true)).eval (Sum.elim g z)) a b = true := by
  rw [presentation_eval E false (P false) (hP false) hℓ,
    presentation_eval E true (P true) (hP true) hℓ]
  unfold accepts
  change (match select E false ((Graph.presentation E false).eval g),
    select E true ((Graph.presentation E true).eval g) with
    | some u, some v => _ | _, _ => true) = _
  rw [select_output, select_output]
  rcases h with h | h
  · rw [h]
  · rw [h]; cases select E false g <;> rfl

/-- On valid views the completed strategy has exactly the original conditional failure. -/
theorem complete_failAt_question {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
    (hne : (Graph.edges E).Nonempty) (P : Bool → T → CLFun (ZMod 2) ι ℓ)
    (D : Question T ι → Question T ι → A → A → Bool)
    (S : SyncStrategy (typedGame E hne P D).doubled) (a₀ : A)
    (x y : Question T ι) (hxy : E x.1 y.1) :
    (complete E hne P D S a₀).toTensorProductStrategy.undouble.failAt
      (question E false x) (question E true y) =
      S.toTensorProductStrategy.undouble.failAt x y := by
  unfold TensorProductStrategy.failAt TensorProductStrategy.succAt
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  change (if accepts E D (question E false x) (question E true y) a b then 1 else 0) *
      (star (maxEntangled S.d) ⬝ᵥ
        (((complete E hne P D S a₀).P.M (false, question E false x) a ⊗ₖ
          ((complete E hne P D S a₀).P.M (true, question E true y) b)ᵀ) *ᵥ maxEntangled S.d)).re = _
  rw [accepts_question E D x y hxy, complete_M_question, complete_M_question]
  rfl

/-- Every actual sample is won with certainty by completion of a perfect typed strategy. -/
theorem complete_failAt_sample {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
    (hE : ∀ u v, E u v → E v u) (hne : (Graph.edges E).Nonempty)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ) (hP : ∀ w t, (P w t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (D : Question T ι → Question T ι → A → A → Bool)
    (S : SyncStrategy (typedGame E hne P D).doubled) (hval : S.value = 1) (a₀ : A)
    (g : Graph.Coord T → ZMod 2) (z : ι → ZMod 2) :
    (complete E hne P D S a₀).toTensorProductStrategy.undouble.failAt
      ((presentation E false (P false)).eval (Sum.elim g z))
      ((presentation E true (P true)).eval (Sum.elim g z)) = 0 := by
  by_cases h : select E false g = none ∨ select E true g = none
  · exact failAt_zero_of_accepts _ _ _ (accepts_sample_of_none E P hP hℓ D g z h)
  · obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp (fun hu => h (Or.inl hu))
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (fun hv => h (Or.inr hv))
    have he : E u v := (selects_pairSeed E hE g hu hv).1
    rw [presentation_eval_valid E false (P false) (hP false) hℓ g z hu,
      presentation_eval_valid E true (P true) (hP true) hℓ g z hv]
    change (complete E hne P D S a₀).toTensorProductStrategy.undouble.failAt
      (question E false (u, (P false u).eval z)) (question E true (v, (P true v).eval z)) = 0
    rw [complete_failAt_question E hne P D S a₀ _ _ he]
    let _ : Nonempty (Edge E) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
    have hs : S.toTensorProductStrategy.undouble.value = 1 := by
      rw [TensorProductStrategy.value_undouble, SyncStrategy.value_toTensorProductStrategy, hval]
    exact sample_failAt_zero (typedQuestion (E := E) P false) (typedQuestion P true) D
      S.toTensorProductStrategy.undouble hs (⟨(u, v), by simp [Graph.edges, he]⟩, z)

/-- Completion preserves perfect value. -/
theorem complete_value {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
    (hE : ∀ u v, E u v → E v u) (hne : (Graph.edges E).Nonempty)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ) (hP : ∀ w t, (P w t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (D : Question T ι → Question T ι → A → A → Bool)
    (S : SyncStrategy (typedGame E hne P D).doubled) (hval : S.value = 1) (a₀ : A) :
    (complete E hne P D S a₀).value = 1 := by
  have h := SampledGame.one_sub_value (presentation E false (P false)).eval
    (presentation E true (P true)).eval (accepts E D)
    (complete E hne P D S a₀).toTensorProductStrategy.undouble
  have hz : ∀ s : Coord T ι → ZMod 2,
      (complete E hne P D S a₀).toTensorProductStrategy.undouble.failAt
        ((presentation E false (P false)).eval s) ((presentation E true (P true)).eval s) = 0 := by
    intro s
    have hs : s = Sum.elim (pull .inl s) (pull .inr s) := by ext p; cases p <;> rfl
    rw [hs]
    exact complete_failAt_sample E hE hne P hP hℓ D S hval a₀ _ _
  change 1 - (complete E hne P D S a₀).toTensorProductStrategy.undouble.value =
    (∑ s : Coord T ι → ZMod 2,
      (complete E hne P D S a₀).toTensorProductStrategy.undouble.failAt
        ((presentation E false (P false)).eval s) ((presentation E true (P true)).eval s)) /
      Fintype.card (Coord T ι → ZMod 2) at h
  rw [TensorProductStrategy.value_undouble, SyncStrategy.value_toTensorProductStrategy] at h
  simp only [hz, Finset.sum_const_zero, zero_div] at h
  linarith

/-- Finite-game detyping preserves a perfect PCC witness and its dimension. -/
theorem exists_perfectPCC {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
    (hE : ∀ u v, E u v → E v u) (hne : (Graph.edges E).Nonempty)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ) (hP : ∀ w t, (P w t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (D : Question T ι → Question T ι → A → A → Bool)
    (S : SyncStrategy (typedGame E hne P D).doubled) (hS : S.IsPCC) (hval : S.value = 1)
    (a₀ : A) :
    ∃ R : SyncStrategy (game E P D).doubled, R.IsPCC ∧ R.value = 1 ∧ R.d = S.d :=
  ⟨complete E hne P D S a₀, complete_isPCC E hE hne P hP hℓ D S hS a₀,
    complete_value E hE hne P hP hℓ D S hval a₀, rfl⟩

end MIPRE.CL.Detyping
