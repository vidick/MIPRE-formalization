/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.HidingMaps
import MIPRE.Foundations.Introspection.ConditionalNormalizer

/-! # Normalizer replacement on the parsed adjacent hiding edge

The test error and conditional relation below are consequences of the actual
parsed game's failure. The remaining inputs are the preceding fine rigidity
estimate and the later prefix marginal estimate used in the induction.
-/

noncomputable section

namespace MIPRE.Introspection.TypedEstimates

open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder

set_option linter.unusedSectionVars false

/-- Express conditional distance in terms of the fine operators, leaving the
later measurement's map intact. -/
theorem conditionalCoarseDistance_fibSum
    {H K I O Y Z : Type*}
    [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
    [Fintype I] [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
    (ψ : H × K → ℂ) (M : POVM I H) (N : POVM O K)
    (f : Y → I → Z) (g : O → Y × Z) :
    conditionalCoarseDistance ψ M N f g =
      ∑ p : Y × Z, snorm ψ (bOp (((N.map g).mats p).val) -
        fibSum (fun i => (M.mats i).val) (f p.1) p.2 ⊗ₖ
          (∑ z, ((N.map g).mats (p.1, z)).val)) ^ 2 := by
  unfold conditionalCoarseDistance
  apply Finset.sum_congr rfl
  intro p _
  rw [POVM.map_mats (f p.1) M p.2, fibSum]


variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}

/-- Extract the success probability of an actual adjacent hiding edge from
the game's uniform ordered-edge distribution. -/
theorem hiding_next_condWin_lower
    (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (ψ : H × K → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) H)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) K)
    {ε : ℝ} (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP) ψ MA MB ≤ ε)
    (w : Bool) (k j : Fin ℓ) (hk : k.val + 1 = j.val) :
    1 - (TypeGraph.edges E X Z ℓ).card * ε ≤
      condWin (parsedGame E X Z P L projectPauli D DP) ψ MA MB
        (QuestionType.hide w k, 0) (QuestionType.hide w j, 0) := by
  let G := parsedGame E X Z P L projectPauli D DP
  let q : CL.Detyping.Question (QuestionType PauliType ℓ) κ := (QuestionType.hide w k, 0)
  let r : CL.Detyping.Question (QuestionType PauliType ℓ) κ := (QuestionType.hide w j, 0)
  have hterm := sum_mul_condFail_le (G := G) (ψ := ψ) (MA := MA) (MB := MB)
    hψ hfail {(q, r)}
  simp only [sum_singleton] at hterm
  change (TypedPresentation.game E X Z ℓ P (questionCheck L X Z projectPauli D DP)).μ
    (.inr (.hide k, w), 0) (.inr (.hide j, w), 0) * condFail G ψ MA MB q r ≤ ε at hterm
  rw [TypedPresentation.mu_aux E X Z P (questionCheck L X Z projectPauli D DP)
    (.hide k) (.hide j) w w (TypeGraph.adj_hide_next E X Z w k j hk), inv_mul_eq_div] at hterm
  have hc : (0 : ℝ) < (TypeGraph.edges E X Z ℓ).card := by
    exact_mod_cast (TypeGraph.edges_nonempty E X Z ℓ).card_pos
  have hcond := (div_le_iff₀ hc).mp hterm
  unfold condFail at hcond
  change 1 - _ ≤ condWin G ψ MA MB q r
  nlinarith

/-- The parsed hiding test supplies conditional consistency after Alice's
answer has already been reduced to the preceding hiding label. -/
theorem hiding_next_guarded_estimate
    (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (ψ : H × K → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) H)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) K)
    {ε : ℝ} (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP) ψ MA MB ≤ ε)
    (w : Bool) (k j : Fin ℓ) (hk : k.val + 1 = j.val)
    (hL : (L w).SupportedOn univ)
    (hMB : IsPVM (fun b => ((MB (QuestionType.hide w j, 0)).mats b).val)) :
    conditionalCoarseDistance ψ
      ((MA (QuestionType.hide w k, 0)).map (hidingCoarse (L w) k.val))
      (MB (QuestionType.hide w j, 0))
      (hidingNextGuarded (L w) k.val) (hidingNextLater (L w) k.val) ≤
        2 * (TypeGraph.edges E X Z ℓ).card * ε := by
  have hwin := hiding_next_condWin_lower E X Z P L projectPauli D DP ψ hψ
    MA MB hfail w k j hk
  have h := conditional_coarse_consistency ψ (norm_evec_eq_one_of_unit hψ)
    (MA (QuestionType.hide w k, 0)) (MB (QuestionType.hide w j, 0)) hMB
    (fun y a => hidingNextGuarded (L w) k.val y (hidingCoarse (L w) k.val a))
    (hidingNextLater (L w) k.val)
    (TypedPredicate.check L X Z projectPauli D (fun p s => DP p s 0 0)
      (QuestionType.hide w k) (QuestionType.hide w j))
    (δ := (TypeGraph.edges E X Z ℓ).card * ε) hwin
    (fun a b hab => hiding_next_accepts_guarded L X Z projectPauli D
      (fun p s => DP p s 0 0) w k j hk hL hab)
  simpa only [conditionalCoarseDistance, POVM.map_map, Function.comp_def, mul_assoc] using h

/-- **Actual hiding normalizer step.** Replace the later conditional marginal
by a commuting ideal prefix at error `6 |E| ε + 3 η + 3 εfine`. The keyed map
acts on the preceding fine hiding label, and every parsed answer is included. -/
theorem hiding_next_normalizer_estimate
    (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (ψ : H × K → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) H)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) K)
    {ε η εfine : ℝ}
    (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP) ψ MA MB ≤ ε)
    (w : Bool) (k j : Fin ℓ) (hk : k.val + 1 = j.val)
    (hL : (L w).SupportedOn univ)
    (hMA : IsPVM (fun a => ((MA (QuestionType.hide w k, 0)).mats a).val))
    (hMB : IsPVM (fun b => ((MB (QuestionType.hide w j, 0)).mats b).val))
    (ideal : Option ((ι → F) × (ι → F) × (ι → F)) → Matrix K K ℂ)
    (Q : Option (ι → F) → Matrix K K ℂ)
    (hideal : IsPVM ideal) (hprefix : IsPVM Q)
    (hcomm : ∀ y i, Commute (Q y) (ideal i))
    (hfine : ∑ i, xSqNorm ψ
      ((((MA (QuestionType.hide w k, 0)).map (hidingCoarse (L w) k.val)).mats i).val)
      (ideal i) ≤ εfine)
    (hnorm : ∑ y, snorm ψ (bOp
      ((∑ z, (((MB (QuestionType.hide w j, 0)).map
        (hidingNextLater (L w) k.val)).mats (y, z)).val) - Q y)) ^ 2 ≤ η) :
    (∑ p, snorm ψ
      (bOp ((((MB (QuestionType.hide w j, 0)).map
        (hidingNextLater (L w) k.val)).mats p).val) -
        bOp (conditionalIdeal ideal Q (hidingNextGuarded (L w) k.val) p)) ^ 2) ≤
      6 * (TypeGraph.edges E X Z ℓ).card * ε + 3 * η + 3 * εfine := by
  let M : POVM (Option ((ι → F) × (ι → F) × (ι → F))) H :=
    (MA (QuestionType.hide w k, 0)).map (hidingCoarse (L w) k.val)
  let N : POVM (Option (ι → F) × Option ((ι → F) × (ι → F) × (ι → F))) K :=
    (MB (QuestionType.hide w j, 0)).map (hidingNextLater (L w) k.val)
  have hm : IsPVM (fun i => (M.mats i).val) :=
    isPVM_povm_map (MA (QuestionType.hide w k, 0)) hMA (hidingCoarse (L w) k.val)
  have hc := hiding_next_guarded_estimate E X Z P L projectPauli D DP ψ hψ
    MA MB hfail w k j hk hL hMB
  change conditionalCoarseDistance ψ M (MB (QuestionType.hide w j, 0))
    (hidingNextGuarded (L w) k.val) (hidingNextLater (L w) k.val) ≤ _ at hc
  rw [conditionalCoarseDistance_fibSum] at hc
  have hN (dec : DecidableEq
      (Option (ι → F) × Option ((ι → F) × (ι → F) × (ι → F))))
      (p : Option (ι → F) × Option ((ι → F) × (ι → F) × (ι → F))) :
      ((@POVM.map (ParsedAnswer (ι → F) A PauliAnswer) K _ _ _
        (Option (ι → F) × Option ((ι → F) × (ι → F) × (ι → F))) _ dec
        (hidingNextLater (L w) k.val) (MB (QuestionType.hide w j, 0))).mats p).val =
        (N.mats p).val := by
    simp only [N, POVM.map_mats, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : hidingNextLater (L w) k.val a = p
    · simp only [if_pos ha]
    · simp only [if_neg ha]
  simp only [hN] at hc
  have h := conditional_coarse_ideal_replacement ψ (norm_evec_eq_one_of_unit hψ)
    (fun i => (M.mats i).val) ideal Q (fun p => (N.mats p).val)
    (hidingNextGuarded (L w) k.val)
    (α := 2 * (TypeGraph.edges E X Z ℓ).card * ε) (η := η) (ε := εfine)
    hm
    hideal hprefix hcomm hfine hnorm
    hc
  exact h.trans_eq (by ring)

end MIPRE.Introspection.TypedEstimates

end
