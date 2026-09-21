/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.TypedEstimates

/-! # Actual Pauli/auxiliary edge probabilities and agreement estimates

The Pauli-X and Pauli-Z vertices have a fixed question. We state that property
explicitly: the generic Pauli CL family supplied to the typed construction
does not itself force their question to be zero. Both edge orientations have
exactly inverse ordered-edge-count probability.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical

set_option linter.unusedSectionVars false

variable {PauliType κ A B C H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType]
  [Fintype κ] [DecidableEq κ] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  {ℓ : ℕ}

namespace TypedPresentation

/-- An edge whose two questions are constant has exactly its ordered-edge
probability; no injectivity of the sampler's seed map is needed. -/
theorem mu_constant_edge (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3)
    (D : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      CL.Detyping.Question (QuestionType PauliType ℓ) κ → A → B → Bool)
    (t u : QuestionType PauliType ℓ) (x y : κ → ZMod 2)
    (ht : ∀ z, (family P t).eval z = x) (hu : ∀ z, (family P u).eval z = y)
    (hedge : TypeGraph.Adj E X Z t u) :
    (game E X Z ℓ P D).μ (t, x) (u, y) = ((TypeGraph.edges E X Z ℓ).card : ℝ)⁻¹ := by
  let G := TypeGraph.Adj (ℓ := ℓ) E X Z
  let e₀ : CL.Detyping.Edge G := ⟨(t, u), by
    simp only [CL.Graph.edges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hedge⟩
  have heq (e : CL.Detyping.Edge G) (z : κ → ZMod 2) :
      (CL.Detyping.typedQuestion (fun _ => family P) false (e, z),
        CL.Detyping.typedQuestion (fun _ => family P) true (e, z)) = ((t, x), (u, y)) ↔ e = e₀ := by
    constructor
    · intro hh
      apply Subtype.ext
      exact congrArg (fun p => (p.1.1, p.2.1)) hh
    · rintro rfl
      simp [CL.Detyping.typedQuestion, e₀, ht, hu]
  unfold game CL.Detyping.typedGame SampledGame.game SampledGame.dist
  dsimp only
  simp only [Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type, heq,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, mul_one]
  have hc : (Fintype.card (κ → ZMod 2) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [_root_.mul_inv_rev, mul_assoc, mul_left_comm, inv_mul_cancel₀ hc, mul_one]
  simp only [Fintype.card_coe, TypeGraph.edges]

theorem mu_pauli_aux (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3)
    (D : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      CL.Detyping.Question (QuestionType PauliType ℓ) κ → A → B → Bool)
    (p : PauliType) (q : κ → ZMod 2) (hq : ∀ z, (P p).eval z = q)
    (t : AuxType ℓ) (w : Bool) (hedge : TypeGraph.Adj E X Z (.inl p) (.inr (t, w))) :
    (game E X Z ℓ P D).μ (.inl p, q) (.inr (t, w), 0) =
      ((TypeGraph.edges E X Z ℓ).card : ℝ)⁻¹ :=
  mu_constant_edge E X Z P D _ _ q 0 hq (eval_aux P t w) hedge

theorem mu_aux_pauli (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3)
    (D : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      CL.Detyping.Question (QuestionType PauliType ℓ) κ → A → B → Bool)
    (t : AuxType ℓ) (w : Bool) (p : PauliType) (q : κ → ZMod 2)
    (hq : ∀ z, (P p).eval z = q) (hedge : TypeGraph.Adj E X Z (.inr (t, w)) (.inl p)) :
    (game E X Z ℓ P D).μ (.inr (t, w), 0) (.inl p, q) =
      ((TypeGraph.edges E X Z ℓ).card : ℝ)⁻¹ :=
  mu_constant_edge E X Z P D _ _ 0 q (eval_aux P t w) hq hedge

end TypedPresentation

namespace TypedEstimates

/-- Project the tested Pauli answer, retaining all wrong constructors as a
separate malformed outcome. -/
def pauliProjection {V A PA : Type*} (projectPauli : PA → V) :
    ParsedAnswer V A PA → Option V
  | .pauli a => some (projectPauli a)
  | _ => none

theorem constant_edge_agreement_estimate (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3)
    (D : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      CL.Detyping.Question (QuestionType PauliType ℓ) κ → A → B → Bool)
    (ψ : H × K → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ → POVM A H)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ → POVM B K)
    {ε : ℝ} (hfail : 1 - povmValue (TypedPresentation.game E X Z ℓ P D) ψ MA MB ≤ ε)
    (t u : QuestionType PauliType ℓ) (x y : κ → ZMod 2)
    (ht : ∀ z, (TypedPresentation.family P t).eval z = x)
    (hu : ∀ z, (TypedPresentation.family P u).eval z = y)
    (hedge : TypeGraph.Adj E X Z t u) (f : A → C) (g : B → C)
    (hcheck : ∀ a b, D (t, x) (u, y) a b = true → f a = g b) :
    (∑ z, xSqNorm ψ ((((MA (t, x)).map f).mats z).val)
      ((((MB (u, y)).map g).mats z).val)) ≤ 2 * (TypeGraph.edges E X Z ℓ).card * ε := by
  let G := TypedPresentation.game E X Z ℓ P D
  have hterm := sum_mul_condFail_le (G := G) (ψ := ψ) (MA := MA) (MB := MB)
    hψ hfail {((t, x), (u, y))}
  simp only [sum_singleton] at hterm
  change G.μ (t, x) (u, y) * condFail G ψ MA MB (t, x) (u, y) ≤ ε at hterm
  rw [TypedPresentation.mu_constant_edge E X Z P D t u x y ht hu hedge,
    inv_mul_eq_div] at hterm
  have hc : (0 : ℝ) < (TypeGraph.edges E X Z ℓ).card := by
    exact_mod_cast (TypeGraph.edges_nonempty E X Z ℓ).card_pos
  have hcond := (div_le_iff₀ hc).mp hterm
  have hdist := xSqNorm_sum_le_condFail (G := G) (ψ := ψ) (MA := MA) (MB := MB)
    (x := (t, x)) (y := (u, y)) hψ f g hcheck
  calc
    _ ≤ 2 * condFail G ψ MA MB (t, x) (u, y) := hdist
    _ ≤ 2 * (ε * (TypeGraph.edges E X Z ℓ).card) :=
      mul_le_mul_of_nonneg_left hcond (by norm_num)
    _ = _ := by ring

theorem pauli_aux_agreement_estimate (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3)
    (D : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      CL.Detyping.Question (QuestionType PauliType ℓ) κ → A → B → Bool)
    (ψ : H × K → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ → POVM A H)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ → POVM B K)
    {ε : ℝ} (hfail : 1 - povmValue (TypedPresentation.game E X Z ℓ P D) ψ MA MB ≤ ε)
    (p : PauliType) (q : κ → ZMod 2) (hq : ∀ z, (P p).eval z = q)
    (t : AuxType ℓ) (w : Bool) (hedge : TypeGraph.Adj E X Z (.inl p) (.inr (t, w)))
    (f : A → C) (g : B → C)
    (hcheck : ∀ a b, D (.inl p, q) (.inr (t, w), 0) a b = true → f a = g b) :
    (∑ z, xSqNorm ψ ((((MA (.inl p, q)).map f).mats z).val)
      ((((MB (.inr (t, w), 0)).map g).mats z).val)) ≤
        2 * (TypeGraph.edges E X Z ℓ).card * ε :=
  constant_edge_agreement_estimate E X Z P D ψ hψ MA MB hfail (.inl p) (.inr (t, w)) q 0 hq
    (TypedPresentation.eval_aux P t w) hedge f g hcheck

theorem aux_pauli_agreement_estimate (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3)
    (D : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      CL.Detyping.Question (QuestionType PauliType ℓ) κ → A → B → Bool)
    (ψ : H × K → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ → POVM A H)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ → POVM B K)
    {ε : ℝ} (hfail : 1 - povmValue (TypedPresentation.game E X Z ℓ P D) ψ MA MB ≤ ε)
    (t : AuxType ℓ) (w : Bool) (p : PauliType) (q : κ → ZMod 2)
    (hq : ∀ z, (P p).eval z = q) (hedge : TypeGraph.Adj E X Z (.inr (t, w)) (.inl p))
    (f : A → C) (g : B → C)
    (hcheck : ∀ a b, D (.inr (t, w), 0) (.inl p, q) a b = true → f a = g b) :
    (∑ z, xSqNorm ψ ((((MA (.inr (t, w), 0)).map f).mats z).val)
      ((((MB (.inl p, q)).map g).mats z).val)) ≤
        2 * (TypeGraph.edges E X Z ℓ).card * ε :=
  constant_edge_agreement_estimate E X Z P D ψ hψ MA MB hfail (.inr (t, w)) (.inl p) 0 q
    (TypedPresentation.eval_aux P t w) hq hedge f g hcheck

end TypedEstimates

end MIPRE.Introspection
