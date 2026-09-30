/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.TypedEstimates
public import MIPRE.Foundations.RegisterReindex

@[expose] public section

/-! # Restricting a parsed introspection strategy to its Pauli tests

Malformed outer answer constructors are completed at a fixed Pauli answer.
Every originally accepted Pauli answer pair remains accepted, including on
loops, where the parsed predicate checks both consistency and the Pauli rule.
The uniform full type graph bounds the mean failure along each of its edges.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`).
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Matrix Classical
set_option linter.unusedSectionVars false

section Completion
variable {V A PA : Type*} [Fintype V] [Fintype A] [Fintype PA] [DecidableEq PA]
  {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]

/-- Retain an actual Pauli answer and complete every other constructor. -/
def completePauliAnswer (a₀ : PA) : ParsedAnswer V A PA → PA
  | .pauli a => a
  | _ => a₀

/-- The parsed measurement coarse-grained along `completePauliAnswer a₀`, in any ordered
`⋆`-ring: either player's algebra. -/
def completePauliPOVM (a₀ : PA) (M : POVMIn (ParsedAnswer V A PA) R) : POVMIn PA R :=
  M.map (completePauliAnswer a₀)

theorem completePauliPOVM_isPVM (a₀ : PA) (M : POVMIn (ParsedAnswer V A PA) R)
    (hM : IsPVMIn M.op) : IsPVMIn (completePauliPOVM a₀ M).op := by
  rw [show (completePauliPOVM a₀ M).op = _ from funext (POVMIn.map_op _ M)]
  exact hM.coarse _

theorem completePauliPOVM_mats (a₀ a : PA) (M : POVMIn (ParsedAnswer V A PA) R) :
    (completePauliPOVM a₀ M).op a =
      ∑ b ∈ univ.filter (fun b => completePauliAnswer a₀ b = a), M.op b :=
  POVMIn.map_op _ _ _

/-- Only the selected completion answer changes its operator. -/
theorem completePauliPOVM_mats_of_ne (a₀ a : PA) (ha : a ≠ a₀)
    (M : POVMIn (ParsedAnswer V A PA) R) :
    (completePauliPOVM a₀ M).op a = M.op (.pauli a) := by
  rw [completePauliPOVM_mats]
  have hs : univ.filter (fun b : ParsedAnswer V A PA => completePauliAnswer a₀ b = a) =
      {.pauli a} := by
    ext b
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    cases b <;> simp [completePauliAnswer, Ne.symm ha]
  rw [hs, sum_singleton]

end Completion

namespace TypedEstimates
variable {T F ι κ A PA : Type*}
  [Fintype T] [DecidableEq T] [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype A] [Fintype PA] [DecidableEq PA] {ℓ : ℕ}
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ]

theorem check_pauli_completed (L : Bool → CL.CLFun F ι ℓ) (X Z p q : T)
    (project : PA → ι → F) (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : T → T → PA → PA → Bool) (a₀ b₀ : PA)
    (a b : ParsedAnswer (ι → F) A PA)
    (h : TypedPredicate.check L X Z project D DP (.inl p) (.inl q) a b = true) :
    DP p q (completePauliAnswer a₀ a) (completePauliAnswer b₀ b) = true := by
  cases a <;> cases b <;>
    simp only [TypedPredicate.check, TypedPredicate.fits, Bool.false_and,
      Bool.and_false, Bool.false_eq_true] at h
  simp only [Bool.true_and, Bool.and_true, TypedPredicate.directed,
    Bool.and_eq_true] at h
  exact h.2

/-- Completion can only improve the conditional Pauli success probability. -/
theorem completed_pauli_condFail_le (E : T → T → Bool) (X Z : T)
    (P : T → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (project : PA → ι → F) (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : T → T → (κ → ZMod 2) → (κ → ZMod 2) → PA → PA → Bool)
    (GP : Game (CL.Detyping.Question T κ) (CL.Detyping.Question T κ) PA PA)
    (hDP : ∀ x y a b, GP.D x y a b = DP x.1 y.1 x.2 y.2 a b)
    (Ψ : BipartiteModel 𝒞 𝒜 ℬ)
    (MA : CL.Detyping.Question (QuestionType T ℓ) κ → POVMIn (ParsedAnswer (ι → F) A PA) 𝒜)
    (MB : CL.Detyping.Question (QuestionType T ℓ) κ → POVMIn (ParsedAnswer (ι → F) A PA) ℬ)
    (a₀ b₀ : PA) (x y : CL.Detyping.Question T κ) :
    Ψ.condFail GP (fun x => completePauliPOVM a₀ (MA (.inl x.1, x.2)))
      (fun y => completePauliPOVM b₀ (MB (.inl y.1, y.2))) x y ≤
    Ψ.condFail (parsedGame E X Z P L project D DP) MA MB (.inl x.1,x.2) (.inl y.1,y.2) := by
  unfold BipartiteModel.condFail
  apply sub_le_sub_left
  unfold BipartiteModel.condWin completePauliPOVM
  rw [Ψ.sum_weight_bornProb_map]
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  have hn := Ψ.bornProb_nonneg ((MA (.inl x.1,x.2)).op_nonneg a)
    ((MB (.inl y.1,y.2)).op_nonneg b)
  by_cases h : (parsedGame E X Z P L project D DP).D (.inl x.1,x.2) (.inl y.1,y.2) a b = true
  · have hp := check_pauli_completed L X Z x.1 y.1 project D
      (fun p q => DP p q x.2 y.2) a₀ b₀ a b h
    rw [hDP, ite_eq_left h, ite_eq_left hp]
  · rw [ite_eq_right h, zero_mul]
    exact mul_nonneg (by split_ifs <;> norm_num) hn

/-- The full uniform type graph bounds the seed-averaged failure on each
individual edge, without requiring injectivity of the question maps. -/
theorem typed_edge_mean_failure_le {B : Type*} [Fintype B]
    (E : T → T → Bool) (X Z : T) (P : T → CL.CLFun (ZMod 2) κ 3)
    (D : CL.Detyping.Question (QuestionType T ℓ) κ →
      CL.Detyping.Question (QuestionType T ℓ) κ → A → B → Bool)
    (Ψ : BipartiteModel 𝒞 𝒜 ℬ) (hΨ : ‖Ψ.ψ‖ = 1)
    (MA : CL.Detyping.Question (QuestionType T ℓ) κ → POVMIn A 𝒜)
    (MB : CL.Detyping.Question (QuestionType T ℓ) κ → POVMIn B ℬ)
    {ε : ℝ} (hf : 1 - Ψ.povmValue (TypedPresentation.game E X Z ℓ P D) MA MB ≤ ε)
    (p q : QuestionType T ℓ) (hpq : TypeGraph.Adj E X Z p q) :
    (∑ z : κ → ZMod 2, Ψ.condFail (TypedPresentation.game E X Z ℓ P D) MA MB
      (p, (TypedPresentation.family P p).eval z)
      (q, (TypedPresentation.family P q).eval z)) / Fintype.card (κ → ZMod 2) ≤
      (TypeGraph.edges E X Z ℓ).card * ε := by
  let G := TypedPresentation.game E X Z ℓ P D
  let f (e : CL.Detyping.Edge (TypeGraph.Adj (ℓ := ℓ) E X Z)) : ℝ :=
    ∑ z : κ → ZMod 2, Ψ.condFail G MA MB
      (e.val.1, (TypedPresentation.family P e.val.1).eval z)
      (e.val.2, (TypedPresentation.family P e.val.2).eval z)
  let e : CL.Detyping.Edge (TypeGraph.Adj (ℓ := ℓ) E X Z) :=
    ⟨(p,q), mem_filter.mpr ⟨mem_univ _, hpq⟩⟩
  have hfn (e : CL.Detyping.Edge (TypeGraph.Adj (ℓ := ℓ) E X Z)) : 0 ≤ f e := by
    unfold f
    exact Finset.sum_nonneg fun z _ =>
      Ψ.condFail_nonneg (G := G) (MA := MA) (MB := MB) hΨ _ _
  have he : f e ≤ ∑ e, f e :=
    Finset.single_le_sum (f := f) (fun e _ => hfn e) (mem_univ e)
  have hh : (∑ e, f e) /
      ((TypeGraph.edges E X Z ℓ).card * (Fintype.card (κ → ZMod 2) : ℝ)) ≤ ε := by
    have hh := hf
    rw [Ψ.one_sub_povmValue_eq] at hh
    change (∑ x, ∑ y, SampledGame.dist
      (CL.Detyping.typedQuestion (E := TypeGraph.Adj (ℓ := ℓ) E X Z)
        (fun _ => TypedPresentation.family P) false)
      (CL.Detyping.typedQuestion (E := TypeGraph.Adj (ℓ := ℓ) E X Z)
        (fun _ => TypedPresentation.family P) true) x y *
        Ψ.condFail G MA MB x y) ≤ ε at hh
    rw [SampledGame.sum_dist_mul] at hh
    simpa only [Fintype.sum_prod_type, Fintype.card_prod, Fintype.card_coe,
      Nat.cast_mul, CL.Detyping.typedQuestion, Bool.false_eq_true, ↓reduceIte,
      TypeGraph.edges, f] using hh
  have hc : (0 : ℝ) < Fintype.card (κ → ZMod 2) := by exact_mod_cast Fintype.card_pos
  have hE : (0 : ℝ) < (TypeGraph.edges E X Z ℓ).card := by
    exact_mod_cast (TypeGraph.edges_nonempty E X Z ℓ).card_pos
  have hh' := (div_le_iff₀ (mul_pos hE hc)).mp hh
  apply (div_le_iff₀ hc).mpr
  change f e ≤ _
  calc f e ≤ ∑ e, f e := he
    _ ≤ ε * ((TypeGraph.edges E X Z ℓ).card * (Fintype.card (κ → ZMod 2) : ℝ)) := hh'
    _ = _ := by ring

end TypedEstimates
end MIPRE.Introspection
end

end
