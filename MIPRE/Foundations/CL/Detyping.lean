/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.CL.Embedding
import MIPRE.Foundations.CL.Closure
import MIPRE.Foundations.CL.Graph

/-! # Detyped conditionally linear functions

The construction of `types.tex`, `def:detyped-CL`: run the graph sampler,
then the selected typed presentation on an independent register. An invalid
graph view selects a zero presentation that still consumes the whole content
register. The conditional law retains the common content seed of both players.

This file constructs the presentations and proves their law. The ambient
program and its runtime are the separate `lem:detype-sampler` obligation.
-/

noncomputable section

namespace MIPRE.CL

open Finset Classical

set_option linter.unusedSectionVars false

namespace CLFun

variable {F ι : Type*} [Semiring F] [DecidableEq ι]

/-- A zero presentation whose first factor consumes `S`, with empty later factors. -/
def zeroOn (S : Finset ι) : (ℓ : ℕ) → CLFun F ι ℓ
  | 0 => .zero
  | ℓ + 1 => .cons S 0 fun _ => zeroOn ∅ ℓ

/-- The zero fallback still partitions all registers when at least one level is available. -/
theorem zeroOn_exactlyOn (S : Finset ι) (ℓ : ℕ) (h : ℓ = 0 → S = ∅) :
    (zeroOn (F := F) S ℓ).ExactlyOn S := by
  induction ℓ generalizing S with
  | zero => exact h rfl
  | succ ℓ ih =>
    refine ⟨Subset.refl S, fun _ => ?_⟩
    simpa using ih ∅ (fun _ => rfl)

/-- Every marginal of the fallback returns zero. -/
theorem eval_truncate_zeroOn [Fintype ι] (S : Finset ι) (ℓ j : ℕ) (x : ι → F) :
    ((zeroOn S ℓ).truncate j).eval x = 0 := by
  induction j generalizing S ℓ x with
  | zero => simp
  | succ j ih =>
    cases ℓ with
    | zero => exact eval_truncate_zero _ _ _
    | succ ℓ => simp [zeroOn, ih]

@[simp] theorem eval_zeroOn [Fintype ι] (S : Finset ι) (ℓ : ℕ) (x : ι → F) :
    (zeroOn S ℓ).eval x = 0 := by
  simpa using eval_truncate_zeroOn S ℓ ℓ x

/-- Fallback linear queries are zero for all prefixes and levels. -/
theorem mapOfPrefix_zeroOn [Fintype ι] (S : Finset ι) (ℓ j : ℕ) (x : ι → F) :
    (zeroOn (F := F) S ℓ).mapOfPrefix j x = 0 := by
  induction ℓ generalizing S j x with
  | zero => rfl
  | succ ℓ ih =>
    cases j with
    | zero => rfl
    | succ j => simp [zeroOn, ih]

/-- Only the first fallback level has a nonempty factor. -/
theorem factorOfPrefix_zeroOn [Fintype ι] (S : Finset ι) (ℓ j : ℕ) (x : ι → F) :
    (zeroOn (F := F) S ℓ).factorOfPrefix j x = if ℓ = 0 ∨ j ≠ 0 then ∅ else S := by
  induction ℓ generalizing S j x with
  | zero => simp [zeroOn]
  | succ ℓ ih => cases j <;> simp [zeroOn, ih]

end CLFun

namespace Detyping

variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]

/-- The graph register followed by the content register. -/
abbrev Coord (T ι : Type*) := Graph.Coord T ⊕ ι

/-- A graph view selects its decoded vertex exactly when its opposite neighbor bit is one.
On graph-sampler outputs this is the paper's nonzero opposite-block test. -/
def select (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (g : Graph.Coord T → ZMod 2) : Option T :=
  match Graph.decode E (fun p => g (w, p)) with
  | some u => if g (!w, (true, u)) = 1 then some u else none
  | none => none

/-- The exact specification of successful type selection. -/
theorem select_eq_some_iff (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (g : Graph.Coord T → ZMod 2) (u : T) :
    select E w g = some u ↔
      (fun p => g (w, p)) = Graph.encode E u ∧ g (!w, (true, u)) = 1 := by
  unfold select
  cases hd : Graph.decode E (fun p => g (w, p)) with
  | none =>
    simp only [reduceCtorEq, false_iff, not_and]
    intro hu
    have := (Graph.decode_eq_some_iff E _ u).mpr hu
    rw [hd] at this
    cases this
  | some v =>
    have hv := (Graph.decode_eq_some_iff E _ v).mp hd
    by_cases hb : g (!w, (true, v)) = 1
    · simp only [if_pos hb, Option.some.injEq]
      constructor
      · rintro rfl
        exact ⟨hv, hb⟩
      · intro hu
        exact Graph.encode_injective E (hv.symm.trans hu.1)
    · simp only [if_neg hb, reduceCtorEq, false_iff, not_and]
      intro hu hbit
      have h := Graph.encode_injective E (hv.symm.trans hu)
      subst v
      exact hb hbit

/-- Type selection is unchanged by passing from a seed to the sampled graph view. -/
theorem select_output (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (g : Graph.Coord T → ZMod 2) : select E w ((Graph.presentation E w).eval g) = select E w g := by
  have hsome : ∀ u, select E w ((Graph.presentation E w).eval g) = some u ↔
      select E w g = some u := by
    intro u
    rw [select_eq_some_iff, select_eq_some_iff]
    have hown : (fun p => (Graph.presentation E w).eval g (w, p)) = fun p => g (w, p) :=
      funext (Graph.presentation_eval_own E w g)
    rw [hown]
    constructor <;> rintro ⟨hu, hb⟩ <;> refine ⟨hu, ?_⟩
    · rwa [Graph.presentation_eval_bit E w g hu] at hb
    · rwa [Graph.presentation_eval_bit E w g hu]
  cases h : select E w g with
  | some u => exact (hsome u).mpr h
  | none =>
    cases h' : select E w ((Graph.presentation E w).eval g) with
    | none => rfl
    | some u => have he := (hsome u).mp h'; rw [h] at he; cases he

/-- Selection fails exactly on locally invalid seeds. -/
theorem select_eq_none_iff (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (g : Graph.Coord T → ZMod 2) : select E w g = none ↔ ¬Graph.localValid E w g := by
  rw [Graph.localValid]
  constructor
  · intro hn ⟨u, hu⟩
    have he := (select_eq_some_iff E w g u).mpr hu
    rw [hn] at he
    cases he
  · intro hn
    cases h : select E w g with
    | none => rfl
    | some u => exact False.elim (hn ⟨u, (select_eq_some_iff E w g u).mp h⟩)

/-- The selected content presentation, with a register-consuming zero fallback. -/
def selected {ℓ : ℕ} (P : T → CLFun (ZMod 2) ι ℓ) (u : Option T) : CLFun (ZMod 2) ι ℓ :=
  match u with
  | some t => P t
  | none => CLFun.zeroOn univ ℓ

/-- The detyped presentation has the two graph levels followed by the typed levels. -/
def presentation {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (P : T → CLFun (ZMod 2) ι ℓ) : CLFun (ZMod 2) (Coord T ι) (ℓ + 2) :=
  ((Graph.presentation E w).embed .inl).concat fun x =>
    (selected P (select E w (pull .inl x))).embed .inr

/-- The graph and content registers are disjoint. -/
theorem disjoint_registers :
    Disjoint ((univ : Finset (Graph.Coord T)).map (Function.Embedding.inl (β := ι)))
      ((univ : Finset ι).map Function.Embedding.inr) := by
  simp [Finset.disjoint_left]

/-- The graph and content registers exhaust the ambient space. -/
theorem union_registers :
    ((univ : Finset (Graph.Coord T)).map (Function.Embedding.inl (β := ι))) ∪
      ((univ : Finset ι).map Function.Embedding.inr) = univ := by
  ext x
  cases x <;> simp

/-- The full detyped sampler partitions its registers on every branch, including rejection. -/
theorem presentation_exactlyOn {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (P : T → CLFun (ZMod 2) ι ℓ) (hP : ∀ t, (P t).ExactlyOn univ) (hℓ : 0 < ℓ) :
    (presentation E w P).ExactlyOn univ := by
  have hs : ∀ u, (selected P u).ExactlyOn univ := by
    intro u
    cases u with
    | none => exact CLFun.zeroOn_exactlyOn _ _ (fun h => False.elim (by omega))
    | some t => exact hP t
  rw [presentation, ← union_registers (T := T) (ι := ι)]
  exact ((Graph.presentation_exactlyOn E w).embed .inl).concat
    (fun x => (hs _).embed .inr) disjoint_registers

/-- The output consists of the sampled graph view and exactly the selected typed output. -/
theorem presentation_eval {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (P : T → CLFun (ZMod 2) ι ℓ) (hP : ∀ t, (P t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (x : Coord T ι → ZMod 2) :
    (presentation E w P).eval x = Sum.elim
      ((Graph.presentation E w).eval (pull .inl x))
      ((selected P (select E w (pull .inl x))).eval (pull .inr x)) := by
  have hs : ∀ u, (selected P u).ExactlyOn univ := by
    intro u
    cases u with
    | none => exact CLFun.zeroOn_exactlyOn _ _ (fun h => False.elim (by omega))
    | some t => exact hP t
  rw [presentation, CLFun.SupportedOn.eval_concat
    ((Graph.presentation_exactlyOn E w).embed .inl).supportedOn
    (fun x => ((hs _).embed .inr).supportedOn) disjoint_registers]
  simp only [CLFun.eval_embed, pull_push, select_output]
  funext j
  cases j <;> simp

/-- The ambient dimension is exactly the graph dimension plus the content dimension. -/
theorem card_coord : Fintype.card (Coord T ι) = 4 * Fintype.card T + Fintype.card ι := by
  simp [Coord, Graph.Coord]
  omega

end Detyping
end MIPRE.CL
