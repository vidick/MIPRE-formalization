/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.Types
import MIPRE.Foundations.CL.Graph

/-! # The introspection type graph

The graph of `introspection.tex`, Figure `fig:type-graph-intro`: the Pauli
subgraph, two chains from Pauli-X through hiding levels to Read, two chains
from Pauli-Z through Sample and Introspect to Read, the cross-introspection
edge, and a loop at every vertex. The construction uses only the Pauli graph
and its two distinguished vertices; no rigidity conclusion is assumed.
-/

namespace MIPRE.Introspection.TypeGraph

open QuestionType Finset

variable {PauliType : Type*} [DecidableEq PauliType] {ℓ : ℕ}

set_option linter.unusedSectionVars false

/-- One orientation of each edge drawn in the source figure. -/
def oriented (E : PauliType → PauliType → Bool) (X Z : PauliType) :
    QuestionType PauliType ℓ → QuestionType PauliType ℓ → Bool
  | .inl p, .inl q => E p q
  | .inl p, .inr (.hide k, _) => decide (p = X ∧ k.val = 0)
  | .inl p, .inr (.sample, _) => decide (p = Z)
  | .inr (.hide k, w), .inr (.hide k', w') => decide (w = w' ∧ k.val + 1 = k'.val)
  | .inr (.hide k, w), .inr (.read, w') => decide (w = w' ∧ k.val + 1 = ℓ)
  | .inr (.sample, w), .inr (.introspect, w') => decide (w = w')
  | .inr (.introspect, w), .inr (.read, w') => decide (w = w')
  | .inr (.introspect, w), .inr (.introspect, w') => decide (w ≠ w')
  | _, _ => false

/-- The graph is undirected and has a self-loop at every type. -/
def adj (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (t u : QuestionType PauliType ℓ) : Bool :=
  decide (t = u) || oriented E X Z t u || oriented E X Z u t

/-- Propositional adjacency, for the graph sampler and finite detyping theorem. -/
abbrev Adj (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (t u : QuestionType PauliType ℓ) : Prop := adj E X Z t u = true

theorem adj_symm (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (t u : QuestionType PauliType ℓ) : adj E X Z t u = adj E X Z u t := by
  simp only [adj, eq_comm]
  ac_rfl

/-- Adjacency has the exact symmetry needed by graph detyping. -/
theorem symmetric (E : PauliType → PauliType → Bool) (X Z : PauliType) :
    ∀ t u : QuestionType PauliType ℓ, Adj E X Z t u → Adj E X Z u t := by
  intro t u h
  change adj E X Z u t = true
  rw [adj_symm]
  exact h

@[simp] theorem adj_self (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (t : QuestionType PauliType ℓ) : adj E X Z t t = true := by simp [adj]

/-- A symmetric reflexive Pauli graph is embedded without adding any Pauli edge. -/
theorem adj_pauli (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (hE : ∀ p q, E p q = E q p) (hloop : ∀ p, E p p = true) (p q : PauliType) :
    adj (ℓ := ℓ) E X Z (pauli p) (pauli q) = E p q := by
  by_cases h : p = q
  · subst q; simp [hloop]
  · simp [adj, oriented, h, ← hE p q]

/-- The Pauli-X vertex starts both hiding chains. -/
theorem adj_pauliX_hide_first (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (hℓ : 0 < ℓ) (w : Bool) : adj E X Z (pauli X) (hide w ⟨0, hℓ⟩) = true := by
  simp [adj, oriented]

/-- Consecutive hiding levels for one original player are connected. -/
theorem adj_hide_next (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (w : Bool) (k k' : Fin ℓ) (h : k.val + 1 = k'.val) :
    adj E X Z (hide w k) (hide w k') = true := by simp [adj, oriented, h]

/-- The last hiding level connects to that player's Read type. -/
theorem adj_hide_read (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (w : Bool) (k : Fin ℓ) (h : k.val + 1 = ℓ) :
    adj E X Z (hide w k) (read w) = true := by simp [adj, oriented, h]

/-- Pauli-Z connects to each Sample type. -/
theorem adj_pauliZ_sample (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (w : Bool) : adj (ℓ := ℓ) E X Z (pauli Z) (sample w) = true := by simp [adj, oriented]

/-- Each Sample type is checked against the corresponding introspection. -/
theorem adj_sample_introspect (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (w : Bool) : adj (ℓ := ℓ) E X Z (sample w) (introspect w) = true := by simp [adj, oriented]

/-- Each Read type is checked against the corresponding introspection. -/
theorem adj_introspect_read (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (w : Bool) : adj (ℓ := ℓ) E X Z (introspect w) (read w) = true := by simp [adj, oriented]

/-- The cross-introspection edge is where the original verifier is tested. -/
theorem adj_cross_introspect (E : PauliType → PauliType → Bool) (X Z : PauliType) :
    adj (ℓ := ℓ) E X Z (introspect false) (introspect true) = true := by simp [adj, oriented]

/-- The only edge between different original-player roles is cross-introspection. -/
theorem adj_different_roles_iff (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (t u : AuxType ℓ) (w w' : Bool) (hw : w ≠ w') :
    adj E X Z (.inr (t, w)) (.inr (u, w')) = true ↔
      t = .introspect ∧ u = .introspect := by
  cases t <;> cases u <;> simp [adj, oriented, hw, Ne.symm hw]

/-- There are exactly two kinds of edges from the Pauli graph into the auxiliary tests. -/
theorem adj_pauli_aux_iff (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (p : PauliType) (t : AuxType ℓ) (w : Bool) :
    adj E X Z (pauli p) (.inr (t, w)) = true ↔
      (p = X ∧ ∃ k : Fin ℓ, t = .hide k ∧ k.val = 0) ∨ (p = Z ∧ t = .sample) := by
  cases t <;> simp [adj, oriented]

/-- Within the hiding tests the graph has precisely same-role consecutive edges and loops. -/
theorem adj_hide_hide_iff (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (w w' : Bool) (k k' : Fin ℓ) :
    adj E X Z (hide w k) (hide w' k') = true ↔
      w = w' ∧ (k = k' ∨ k.val + 1 = k'.val ∨ k'.val + 1 = k.val) := by
  simp only [adj, oriented, Bool.or_eq_true, decide_eq_true_eq, Sum.inr.injEq,
    Prod.mk.injEq, AuxType.hide.injEq]
  have hw : w = w' ↔ w' = w := eq_comm
  tauto

variable [Fintype PauliType]

/-- The actual ordered edge set used by the typed game's distribution. -/
def edges (E : PauliType → PauliType → Bool) (X Z : PauliType) (ℓ : ℕ) :=
  CL.Graph.edges (Adj (ℓ := ℓ) E X Z)

/-- Every introspection graph is nonempty, even with no hiding levels. -/
theorem edges_nonempty (E : PauliType → PauliType → Bool) (X Z : PauliType) (ℓ : ℕ) :
    (edges E X Z ℓ).Nonempty := by
  refine ⟨(introspect false, introspect false), ?_⟩
  simp [edges, CL.Graph.edges, Adj]

/-- The graph's ordered edge count is bounded by the square of its explicit vertex count. -/
theorem card_edges_le (E : PauliType → PauliType → Bool) (X Z : PauliType) (ℓ : ℕ) :
    (edges E X Z ℓ).card ≤ (Fintype.card PauliType + 2 * ℓ + 6) ^ 2 := by
  have h := Finset.card_le_card (Finset.subset_univ (edges E X Z ℓ))
  simpa only [Finset.card_univ, Fintype.card_prod, QuestionType.card, pow_two] using h

/-- The detyping loss has the explicit exponent dictated by the type set. -/
theorem detyping_factor (ℓ : ℕ) :
    (16 : ℝ) ^ Fintype.card (QuestionType PauliType ℓ) =
      (16 : ℝ) ^ (Fintype.card PauliType + 2 * ℓ + 6) := by rw [QuestionType.card]

/-- In particular, the source's 26-type Pauli test gives the factor `16^(2ℓ + 32)`. -/
theorem detyping_factor_of_pauli_card (h : Fintype.card PauliType = 26) (ℓ : ℕ) :
    (16 : ℝ) ^ Fintype.card (QuestionType PauliType ℓ) = (16 : ℝ) ^ (2 * ℓ + 32) := by
  rw [QuestionType.card_of_pauli_card h]

end MIPRE.Introspection.TypeGraph
