/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.HidingMaps
public import MIPRE.Foundations.Introspection.ConditionalNormalizer

@[expose] public section

/-! # Normalizer replacement on the parsed adjacent hiding edge

The test error and conditional relation below are consequences of the actual
parsed game's failure. The remaining inputs are the preceding fine rigidity
estimate and the later prefix marginal estimate used in the induction.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the strategy is a pair of
POVM families in the two players' algebras, the ideal fine and prefix measurements are families
in the second player's algebra, and the coarse fine operators are `fibSumIn` of the first
player's measurement.
-/

noncomputable section

namespace MIPRE.Introspection.TypedEstimates

open Finset Classical

set_option linter.unusedSectionVars false

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- Relabelling twice is relabelling once (`POVMIn.map_map`, which lives in a module this one
does not import). -/
private theorem povmIn_map_map {R X Y W : Type*} [Ring R] [StarRing R] [PartialOrder R]
    [StarOrderedRing R] [Fintype X] [Fintype Y] [DecidableEq Y] [Fintype W] [DecidableEq W]
    (M : POVMIn X R) (f : X → Y) (g : Y → W) : (M.map f).map g = M.map fun a => g (f a) := by
  refine POVMIn.ext' fun c => ?_
  simp only [POVMIn.map_op, Finset.sum_filter]
  have h : ∀ y, (if g y = c then ∑ x, (if f x = y then M.op x else 0) else 0)
      = ∑ x, if f x = y then (if g y = c then M.op x else 0) else 0 := fun y => by
    split_ifs <;> simp
  simp_rw [h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_ite_eq univ (f x) (fun y => if g y = c then M.op x else 0),
    ite_eq_left (Finset.mem_univ _)]

/-- Express conditional distance in terms of the fine operators, leaving the
later measurement's map intact. -/
theorem conditionalCoarseDistance_fibSum
    {I O Y Z : Type*}
    [Fintype I] [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
    (Ψ : BipartiteModel 𝒞 𝒜 ℬ) (M : POVMIn I 𝒜) (N : POVMIn O ℬ)
    (f : Y → I → Z) (g : O → Y × Z) :
    conditionalCoarseDistance Ψ M N f g =
      ∑ p : Y × Z, Ψ.snorm (Ψ.πB ((N.map g).op p) -
        Ψ.πA (fibSumIn M.op (f p.1) p.2) * Ψ.πB (∑ z, (N.map g).op (p.1, z))) ^ 2 := by
  unfold conditionalCoarseDistance
  apply Finset.sum_congr rfl
  intro p _
  rw [POVMIn.map_op (f p.1) M p.2, fibSumIn]

variable {PauliType PauliAnswer F ι κ A : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype A] {ℓ : ℕ}

/-- Extract the success probability of an actual adjacent hiding edge from
the game's uniform ordered-edge distribution. -/
theorem hiding_next_condWin_lower
    (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (Ψ : BipartiteModel 𝒞 𝒜 ℬ) (hΨ : ‖Ψ.ψ‖ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) 𝒜)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) ℬ)
    {ε : ℝ} (hfail : 1 - Ψ.povmValue (parsedGame E X Z P L projectPauli D DP) MA MB ≤ ε)
    (w : Bool) (k j : Fin ℓ) (hk : k.val + 1 = j.val) :
    1 - (TypeGraph.edges E X Z ℓ).card * ε ≤
      Ψ.condWin (parsedGame E X Z P L projectPauli D DP) MA MB
        (QuestionType.hide w k, 0) (QuestionType.hide w j, 0) := by
  let G := parsedGame E X Z P L projectPauli D DP
  let q : CL.Detyping.Question (QuestionType PauliType ℓ) κ := (QuestionType.hide w k, 0)
  let r : CL.Detyping.Question (QuestionType PauliType ℓ) κ := (QuestionType.hide w j, 0)
  have hterm := Ψ.sum_mul_condFail_le (G := G) (MA := MA) (MB := MB) hΨ hfail {(q, r)}
  simp only [sum_singleton] at hterm
  change (TypedPresentation.game E X Z ℓ P (questionCheck L X Z projectPauli D DP)).μ
    (.inr (.hide k, w), 0) (.inr (.hide j, w), 0) * Ψ.condFail G MA MB q r ≤ ε at hterm
  rw [TypedPresentation.mu_aux E X Z P (questionCheck L X Z projectPauli D DP)
    (.hide k) (.hide j) w w (TypeGraph.adj_hide_next E X Z w k j hk), inv_mul_eq_div] at hterm
  have hc : (0 : ℝ) < (TypeGraph.edges E X Z ℓ).card := by
    exact_mod_cast (TypeGraph.edges_nonempty E X Z ℓ).card_pos
  have hcond := (div_le_iff₀ hc).mp hterm
  unfold BipartiteModel.condFail at hcond
  change 1 - _ ≤ Ψ.condWin G MA MB q r
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
    (Ψ : BipartiteModel 𝒞 𝒜 ℬ) (hΨ : ‖Ψ.ψ‖ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) 𝒜)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) ℬ)
    {ε : ℝ} (hfail : 1 - Ψ.povmValue (parsedGame E X Z P L projectPauli D DP) MA MB ≤ ε)
    (w : Bool) (k j : Fin ℓ) (hk : k.val + 1 = j.val)
    (hL : (L w).SupportedOn univ)
    (hMB : IsPVMIn (MB (QuestionType.hide w j, 0)).op) :
    conditionalCoarseDistance Ψ
      ((MA (QuestionType.hide w k, 0)).map (hidingCoarse (L w) k.val))
      (MB (QuestionType.hide w j, 0))
      (hidingNextGuarded (L w) k.val) (hidingNextLater (L w) k.val) ≤
        2 * (TypeGraph.edges E X Z ℓ).card * ε := by
  have hwin := hiding_next_condWin_lower E X Z P L projectPauli D DP Ψ hΨ
    MA MB hfail w k j hk
  have h := conditional_coarse_consistency Ψ hΨ
    (MA (QuestionType.hide w k, 0)) (MB (QuestionType.hide w j, 0)) hMB
    (fun y a => hidingNextGuarded (L w) k.val y (hidingCoarse (L w) k.val a))
    (hidingNextLater (L w) k.val)
    (TypedPredicate.check L X Z projectPauli D (fun p s => DP p s 0 0)
      (QuestionType.hide w k) (QuestionType.hide w j))
    (δ := (TypeGraph.edges E X Z ℓ).card * ε) hwin
    (fun a b hab => hiding_next_accepts_guarded L X Z projectPauli D
      (fun p s => DP p s 0 0) w k j hk hL hab)
  simpa only [conditionalCoarseDistance, povmIn_map_map, mul_assoc] using h

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
    (Ψ : BipartiteModel 𝒞 𝒜 ℬ) (hΨ : ‖Ψ.ψ‖ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) 𝒜)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) ℬ)
    {ε η εfine : ℝ}
    (hfail : 1 - Ψ.povmValue (parsedGame E X Z P L projectPauli D DP) MA MB ≤ ε)
    (w : Bool) (k j : Fin ℓ) (hk : k.val + 1 = j.val)
    (hL : (L w).SupportedOn univ)
    (hMA : IsPVMIn (MA (QuestionType.hide w k, 0)).op)
    (hMB : IsPVMIn (MB (QuestionType.hide w j, 0)).op)
    (ideal : Option ((ι → F) × (ι → F) × (ι → F)) → ℬ)
    (Q : Option (ι → F) → ℬ)
    (hideal : IsPVMIn ideal) (hprefix : IsPVMIn Q)
    (hcomm : ∀ y i, Commute (Q y) (ideal i))
    (hfine : ∑ i, Ψ.xSqNorm
      (((MA (QuestionType.hide w k, 0)).map (hidingCoarse (L w) k.val)).op i)
      (ideal i) ≤ εfine)
    (hnorm : ∑ y, Ψ.snorm (Ψ.πB
      ((∑ z, ((MB (QuestionType.hide w j, 0)).map
        (hidingNextLater (L w) k.val)).op (y, z)) - Q y)) ^ 2 ≤ η) :
    (∑ p, Ψ.snorm
      (Ψ.πB (((MB (QuestionType.hide w j, 0)).map
        (hidingNextLater (L w) k.val)).op p) -
        Ψ.πB (conditionalIdeal ideal Q (hidingNextGuarded (L w) k.val) p)) ^ 2) ≤
      6 * (TypeGraph.edges E X Z ℓ).card * ε + 3 * η + 3 * εfine := by
  let M : POVMIn (Option ((ι → F) × (ι → F) × (ι → F))) 𝒜 :=
    (MA (QuestionType.hide w k, 0)).map (hidingCoarse (L w) k.val)
  let N : POVMIn (Option (ι → F) × Option ((ι → F) × (ι → F) × (ι → F))) ℬ :=
    (MB (QuestionType.hide w j, 0)).map (hidingNextLater (L w) k.val)
  have hm : IsPVMIn M.op := by
    rw [show M.op = _ from funext (POVMIn.map_op (hidingCoarse (L w) k.val)
      (MA (QuestionType.hide w k, 0)))]
    exact hMA.coarse _
  have hc := hiding_next_guarded_estimate E X Z P L projectPauli D DP Ψ hΨ
    MA MB hfail w k j hk hL hMB
  change conditionalCoarseDistance Ψ M (MB (QuestionType.hide w j, 0))
    (hidingNextGuarded (L w) k.val) (hidingNextLater (L w) k.val) ≤ _ at hc
  rw [conditionalCoarseDistance_fibSum] at hc
  have hN (dec : DecidableEq
      (Option (ι → F) × Option ((ι → F) × (ι → F) × (ι → F))))
      (p : Option (ι → F) × Option ((ι → F) × (ι → F) × (ι → F))) :
      (@POVMIn.map ℬ (ParsedAnswer (ι → F) A PauliAnswer) _ _ _ _ _
        (Option (ι → F) × Option ((ι → F) × (ι → F) × (ι → F))) _ dec
        (hidingNextLater (L w) k.val) (MB (QuestionType.hide w j, 0))).op p = N.op p := by
    simp only [N, POVMIn.map_op, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : hidingNextLater (L w) k.val a = p
    · simp only [ite_eq_left ha]
    · simp only [ite_eq_right ha]
  simp only [hN] at hc
  have h := conditional_coarse_ideal_replacement Ψ hΨ
    M.op ideal Q N.op (hidingNextGuarded (L w) k.val)
    (α := 2 * (TypeGraph.edges E X Z ℓ).card * ε) (η := η) (ε := εfine)
    hm hideal hprefix hcomm hfine hnorm hc
  exact h.trans_eq (by ring)

end MIPRE.Introspection.TypedEstimates

end

end
