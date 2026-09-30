/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.AdaptiveInductionIteration


@[expose] public section

/-! # Exchanging players in the actual parsed introspection game

The Pauli predicate is transposed explicitly; no symmetry of that predicate
is assumed. The directed auxiliary checks already include both orientations,
so the original decision predicate and role-indexed CL maps stay unchanged.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): exchanging the players is the
swapped model `Ξ.swap`, whose register model is the swapped register model
(`BipartiteModel.regSwap`, with both homomorphisms the identity), so the value, the primitive Z
errors and the hiding errors move between the two players with no loss.
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Matrix Classical
set_option linter.unusedSectionVars false

/-- A uniform seed involution exchanging the question maps gives a symmetric law. -/
theorem sampled_dist_swap_of_equiv {S Q : Type*} [Fintype S] [Fintype Q]
    (qA qB : S → Q) (e : S ≃ S)
    (hA : ∀ s, qA (e s) = qB s) (hB : ∀ s, qB (e s) = qA s) (x y : Q) :
    SampledGame.dist qA qB x y = SampledGame.dist qA qB y x := by
  unfold SampledGame.dist
  congr 1
  calc
    (∑ s, if (qA s, qB s) = (x, y) then (1 : ℝ) else 0) =
        ∑ s, if (qA (e s), qB (e s)) = (y, x) then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      rw [hA, hB]
      simp only [Prod.mk.injEq, and_comm]
    _ = _ := e.sum_comp (fun s => if (qA s, qB s) = (y, x) then (1 : ℝ) else 0)

namespace TypedPresentation

variable {PauliType κ A B : Type*} [Fintype PauliType] [DecidableEq PauliType]
  [Fintype κ] [DecidableEq κ] [Fintype A] [Fintype B]

/-- The exact involution of the uniformly sampled ordered type edges. -/
def edgeSwap (E : PauliType → PauliType → Bool) (X Z : PauliType) (ℓ : ℕ) :
    CL.Detyping.Edge (TypeGraph.Adj (ℓ := ℓ) E X Z) ≃
      CL.Detyping.Edge (TypeGraph.Adj (ℓ := ℓ) E X Z) where
  toFun e := ⟨e.val.swap, by
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    exact TypeGraph.symmetric E X Z _ _ (mem_filter.mp e.property).2⟩
  invFun e := ⟨e.val.swap, by
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    exact TypeGraph.symmetric E X Z _ _ (mem_filter.mp e.property).2⟩
  left_inv e := by apply Subtype.ext; rfl
  right_inv e := by apply Subtype.ext; rfl

/-- Reversing the ordered edge and retaining the common seed exchanges the
two questions, for arbitrary Pauli samplers. -/
theorem mu_swap (E : PauliType → PauliType → Bool) (X Z : PauliType) (ℓ : ℕ)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3)
    (D D' : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      CL.Detyping.Question (QuestionType PauliType ℓ) κ → A → B → Bool)
    (x y : CL.Detyping.Question (QuestionType PauliType ℓ) κ) :
    (game E X Z ℓ P D').μ x y = (game E X Z ℓ P D).μ y x := by
  change SampledGame.dist (CL.Detyping.typedQuestion
      (E := TypeGraph.Adj (ℓ := ℓ) E X Z) (fun _ => family P) false)
      (CL.Detyping.typedQuestion (fun _ => family P) true) x y =
    SampledGame.dist (CL.Detyping.typedQuestion
      (E := TypeGraph.Adj (ℓ := ℓ) E X Z) (fun _ => family P) false)
      (CL.Detyping.typedQuestion (fun _ => family P) true) y x
  let e := (edgeSwap E X Z ℓ).prodCongr (Equiv.refl (κ → ZMod 2))
  exact sampled_dist_swap_of_equiv _ _ e (fun _ => rfl) (fun _ => rfl) x y

end TypedPresentation

namespace TypedEstimates

variable {PauliType PauliAnswer F ι κ A : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype A] {ℓ : ℕ}

/-- Transpose every Pauli input, including the actual question contents. -/
def transposePauliPredicate
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool) :=
  fun p q x y a b => DP q p y x b a

theorem transposePauliPredicate_transpose
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool) :
    transposePauliPredicate (transposePauliPredicate DP) = DP := rfl

set_option backward.isDefEq.respectTransparency false in
theorem questionCheck_transpose (L : Bool → CL.CLFun F ι ℓ) (X Z : PauliType)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (q r : CL.Detyping.Question (QuestionType PauliType ℓ) κ)
    (a b : ParsedAnswer (ι → F) A PauliAnswer) :
    questionCheck L X Z projectPauli D (transposePauliPredicate DP) q r a b =
      questionCheck L X Z projectPauli D DP r q b a := by
  apply Bool.eq_iff_iff.mpr
  simp only [questionCheck, TypedPredicate.check, Bool.and_eq_true]
  constructor
  all_goals
    rintro ⟨⟨⟨⟨⟨ht, hu⟩, hc⟩, hp⟩, hd⟩, hr⟩
    refine ⟨⟨⟨⟨⟨hu, ht⟩, ?_⟩, ?_⟩, hr⟩, hd⟩
    · by_cases h : q.1 = r.1
      · simp only [if_pos h, if_pos h.symm, decide_eq_true_eq] at hc ⊢
        exact hc.symm
      · simp only [if_neg h, if_neg (Ne.symm h)]
    · clear ht hu hc hd hr
      rcases q with ⟨q, x⟩
      rcases r with ⟨r, y⟩
      cases q <;> cases r <;> cases a <;> cases b <;> exact hp

/-- Transposing the Pauli predicate exchanges the players of the parsed game. -/
theorem parsedGame_transpose (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool) :
    parsedGame E X Z P L projectPauli D (transposePauliPredicate DP) =
      (parsedGame E X Z P L projectPauli D DP).swap := by
  have hμ : (parsedGame E X Z P L projectPauli D (transposePauliPredicate DP)).μ =
      (parsedGame E X Z P L projectPauli D DP).swap.μ :=
    funext fun x => funext fun y => TypedPresentation.mu_swap E X Z ℓ P
      (questionCheck L X Z projectPauli D DP)
      (questionCheck L X Z projectPauli D (transposePauliPredicate DP)) x y
  have hD : (parsedGame E X Z P L projectPauli D (transposePauliPredicate DP)).D =
      (parsedGame E X Z P L projectPauli D DP).swap.D :=
    funext fun x => funext fun y => funext fun a => funext fun b =>
      questionCheck_transpose L X Z projectPauli D DP x y a b
  generalize parsedGame E X Z P L projectPauli D (transposePauliPredicate DP) = G at hμ hD
  cases G
  cases hμ
  cases hD
  rfl

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [StarModule ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [StarModule ℂ ℬ]
  [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ]
  [StarProper ℬ] (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The register model of the swapped model is the swapped register model: Born probabilities
agree, along `regSwap`. -/
theorem swap_reg_bornProb (Y : Matrix I I ℬ) (X : Matrix I I 𝒜) :
    (Ξ.swap.reg I).bornProb Y X = (Ξ.reg I).swap.bornProb Y X :=
  BipartiteModel.LocalIsometry.bornProb_of_W_ψ Ξ.regSwap_W_ψ Y X

theorem swap_reg_povmValue {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A']
    [Fintype B'] (G : Game X' Y' A' B') (PA : X' → POVMIn A' (Matrix I I ℬ))
    (PB : Y' → POVMIn B' (Matrix I I 𝒜)) :
    (Ξ.swap.reg I).povmValue G PA PB = (Ξ.reg I).swap.povmValue G PA PB := by
  unfold BipartiteModel.povmValue BipartiteModel.condWin
  simp only [swap_reg_bornProb]

theorem swap_reg_stateSqNorm (Y : Matrix I I ℬ) :
    (Ξ.swap.reg I).stateSqNorm Y = (Ξ.reg I).swap.stateSqNorm Y :=
  BipartiteModel.LocalIsometry.stateSqNorm_of_W_ψ Ξ.regSwap_W_ψ Y

theorem swap_reg_swap_stateSqNorm (X : Matrix I I 𝒜) :
    (Ξ.swap.reg I).swap.stateSqNorm X = (Ξ.reg I).stateSqNorm X :=
  BipartiteModel.LocalIsometry.swap_stateSqNorm_of_W_ψ Ξ.regSwap_W_ψ X

theorem swap_reg_xSqNorm (Y : Matrix I I ℬ) (X : Matrix I I 𝒜) :
    (Ξ.swap.reg I).xSqNorm Y X = (Ξ.reg I).xSqNorm X Y :=
  (BipartiteModel.LocalIsometry.xSqNorm_of_W_ψ Ξ.regSwap_W_ψ Y X).trans ((Ξ.reg I).xSqNorm_swap X Y)

/-- The original game's value is preserved by exchanging players and
transposing only the supplied Pauli predicate. -/
theorem parsedGame_value_swap (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) 𝒜))
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) ℬ)) :
    (Ξ.swap.reg (ι → F)).povmValue
        (parsedGame E X Z P L projectPauli D (transposePauliPredicate DP)) MB MA =
      (Ξ.reg (ι → F)).povmValue (parsedGame E X Z P L projectPauli D DP) MA MB := by
  rw [swap_reg_povmValue, parsedGame_transpose, BipartiteModel.povmValue_swap_game]

theorem introBobZError_swap (projectPauli : PauliAnswer → ι → F)
    (Z : PauliType) (q : κ → ZMod 2)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) 𝒜)) :
    introBobZError projectPauli Z q Ξ.swap MA = introAliceZError projectPauli Z q Ξ MA :=
  Finset.sum_congr rfl fun _ _ => swap_reg_swap_stateSqNorm Ξ _

theorem introAliceZError_swap (projectPauli : PauliAnswer → ι → F)
    (Z : PauliType) (q : κ → ZMod 2)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) ℬ)) :
    introAliceZError projectPauli Z q Ξ.swap MB = introBobZError projectPauli Z q Ξ MB :=
  Finset.sum_congr rfl fun _ _ => swap_reg_stateSqNorm Ξ _

theorem hidingAliceError_swap (L : Bool → CL.CLFun F ι ℓ) (w : Bool)
    (hL : (L w).SupportedOn univ)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) ℬ)) (j : Fin ℓ) :
    hidingAliceError L w hL Ξ.swap MB j = hidingBobError L w hL Ξ MB j :=
  Finset.sum_congr rfl fun _ _ => swap_reg_xSqNorm Ξ _ _

theorem hidingBobError_swap (L : Bool → CL.CLFun F ι ℓ) (w : Bool)
    (hL : (L w).SupportedOn univ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) 𝒜)) (j : Fin ℓ) :
    hidingBobError L w hL Ξ.swap MA j = hidingAliceError L w hL Ξ MA j :=
  Finset.sum_congr rfl fun _ _ => swap_reg_xSqNorm Ξ _ _

end TypedEstimates
end MIPRE.Introspection
end

end
