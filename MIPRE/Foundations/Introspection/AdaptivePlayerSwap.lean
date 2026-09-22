/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AdaptiveInductionIteration
import MIPRE.Foundations.Swap

/-! # Exchanging players in the actual parsed introspection game

The Pauli predicate is transposed explicitly; no symmetry of that predicate
is assumed. The directed auxiliary checks already include both orientations,
so the original decision predicate and role-indexed CL maps stay unchanged.
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Matrix Classical
set_option linter.unusedSectionVars false

variable {I H K : Type*} [Fintype I] [DecidableEq I]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

/-- Swapping the parties swaps only the auxiliary state behind the common
EPR register. -/
theorem swapVec_registerState (ξ : H × K → ℂ) :
    swapVec (registerState I ξ) = registerState I (swapVec ξ) := by
  funext p
  rcases p with ⟨⟨i, k⟩, j, h⟩
  simp [swapVec, registerState, expVec, registerEPR, eq_comm]

theorem xSqNorm_swapVec (ψ : H × K → ℂ)
    (M : Matrix H H ℂ) (N : Matrix K K ℂ) :
    xSqNorm (swapVec ψ) N M = xSqNorm ψ M N := by
  rw [xSqNorm_eq_snorm_sq, snorm_swapVec_aOp_sub_bOp, xSqNorm_eq_sq]

theorem snorm_swapVec_bOp (ψ : H × K → ℂ) (M : Matrix H H ℂ) :
    snorm (swapVec ψ) (bOp M) = snorm ψ (aOp M) := by
  have h := snorm_swapVec_aOp (swapVec ψ) M
  simpa only [swapVec_swapVec, norm_stateVecB_eq_snorm] using h.symm

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

/-- The original game's value is preserved by exchanging players and
transposing only the supplied Pauli predicate. -/
theorem parsedGame_value_swap (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (ξ : H × K → ℂ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H))
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × K)) :
    povmValue (parsedGame E X Z P L projectPauli D (transposePauliPredicate DP))
      (registerState (ι → F) (swapVec ξ)) MB MA =
        povmValue (parsedGame E X Z P L projectPauli D DP)
          (registerState (ι → F) ξ) MA MB := by
  rw [← swapVec_registerState]
  have hc (x y : CL.Detyping.Question (QuestionType PauliType ℓ) κ) :
      condWin (parsedGame E X Z P L projectPauli D (transposePauliPredicate DP))
        (swapVec (registerState (ι → F) ξ)) MB MA x y =
      condWin (parsedGame E X Z P L projectPauli D DP)
        (registerState (ι → F) ξ) MA MB y x := by
    unfold condWin
    change (∑ a, ∑ b, (if questionCheck L X Z projectPauli D
      (transposePauliPredicate DP) x y a b then (1 : ℝ) else 0) *
      bornProb (swapVec (registerState (ι → F) ξ)) ((MB x).mats a).val ((MA y).mats b).val) = _
    simp only [questionCheck_transpose, bornProb_swapVec]
    exact Finset.sum_comm
  unfold povmValue
  simp_rw [hc, show ∀ x y,
    (parsedGame E X Z P L projectPauli D (transposePauliPredicate DP)).μ x y =
      (parsedGame E X Z P L projectPauli D DP).μ y x from
        TypedPresentation.mu_swap E X Z ℓ P _ _]
  exact Finset.sum_comm

/-- Alice's primitive computational-basis error, with malformed Pauli
answers kept as the separate option outcome. -/
def introAliceZError (projectPauli : PauliAnswer → ι → F) (Z : PauliType)
    (q : κ → ZMod 2) (ξ : H × K → ℂ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H)) : ℝ :=
  ∑ z, stateSqNorm (registerState (ι → F) ξ)
    ((((MA (QuestionType.pauli Z, q)).map (pauliProjection projectPauli)).mats z).val -
      (aOp (readout (some : (ι → F) → Option (ι → F)) z) :
        Matrix ((ι → F) × H) _ ℂ))

theorem introBobZError_swap (projectPauli : PauliAnswer → ι → F) (Z : PauliType)
    (q : κ → ZMod 2) (ξ : H × K → ℂ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H)) :
    introBobZError projectPauli Z q (swapVec ξ) MA =
      introAliceZError projectPauli Z q ξ MA := by
  unfold introBobZError introAliceZError
  rw [← swapVec_registerState]
  simp only [snorm_swapVec_bOp, stateSqNorm, stateNorm, norm_stateVec_eq_snorm]

theorem hidingAliceError_swap (L : Bool → CL.CLFun F ι ℓ) (w : Bool)
    (hL : (L w).SupportedOn univ) (ξ : H × K → ℂ)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × K)) (j : Fin ℓ) :
    hidingAliceError L w hL (swapVec ξ) MB j = hidingBobError L w hL ξ MB j := by
  unfold hidingAliceError hidingBobError
  rw [← swapVec_registerState]
  simp only [xSqNorm_swapVec]

theorem hidingBobError_swap (L : Bool → CL.CLFun F ι ℓ) (w : Bool)
    (hL : (L w).SupportedOn univ) (ξ : H × K → ℂ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H)) (j : Fin ℓ) :
    hidingBobError L w hL (swapVec ξ) MA j = hidingAliceError L w hL ξ MA j := by
  have h := hidingAliceError_swap L w hL (swapVec ξ) MA j
  simpa only [swapVec_swapVec] using h.symm

end TypedEstimates
end MIPRE.Introspection
end
