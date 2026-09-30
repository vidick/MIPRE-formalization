/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.AdaptiveTwoSidedIteration
public import MIPRE.Foundations.Introspection.AdaptivePowerBudget
public import MIPRE.Foundations.Introspection.PrimitivePauliTransfer
public import MIPRE.Foundations.Introspection.TerminalOptionExtraction
public import MIPRE.Foundations.Introspection.HidingRigidityGame

@[expose] public section

/-! # Finite-game introspection soundness from primitive Pauli estimates

The only operator estimates assumed here are the extracted Alice-X and
Bob-Z guarantees. Actual game success supplies all hiding estimates and
Alice-Z consistency. Both adaptive inductions and terminal extraction are
then constructed. The explicit power bound covers every nonnegative input
error, including errors outside the smallness threshold of the induction.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the extracted register state
is the register model `Ξ.reg (ι → F)` of a normalized auxiliary model `Ξ`, and the value is that of
any value model `ω` dominating the POVM strategies of `Ξ`. The strategy terminal extraction builds
lives in the model the two iterations return, which reduces to `Ξ`
(`BipartiteModel.POVMReduces`), so `ω` dominates it too.
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Matrix Classical
set_option linter.unusedSectionVars false

/-- A common budget for game failure, both Z estimates, and both hiding
estimates, depending only on the fixed depth and type-graph size. -/
def primitiveBudgetCoefficient (r : ℕ) (edges : ℝ) : ℝ :=
  3 + 8 * edges + 2 * TypedEstimates.hidingPauliBudget r edges 1 1

theorem primitiveBudgetCoefficient_bounds (r : ℕ) {edges : ℝ} (hE : 0 ≤ edges) :
    1 ≤ primitiveBudgetCoefficient r edges ∧
    4 * edges + 2 ≤ primitiveBudgetCoefficient r edges ∧
    TypedEstimates.hidingPauliBudget r edges 1 1 ≤ primitiveBudgetCoefficient r edges ∧
    4 * edges + 2 * TypedEstimates.hidingPauliBudget r edges 1 1 ≤
      primitiveBudgetCoefficient r edges := by
  have hB : 0 ≤ TypedEstimates.hidingPauliBudget r edges 1 1 := by
    unfold TypedEstimates.hidingPauliBudget
    positivity
  unfold primitiveBudgetCoefficient
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem hidingPauliBudget_common (r : ℕ) (edges t : ℝ) :
    TypedEstimates.hidingPauliBudget r (edges * t) t t =
      TypedEstimates.hidingPauliBudget r edges 1 1 * t := by
  unfold TypedEstimates.hidingPauliBudget
  ring

/-- This coefficient includes terminal edge loss and the trivial large-error
regime, so no smallness premise remains in the soundness conclusion. -/
def primitiveSoundnessCoefficient (r : ℕ) (edges : ℝ) : ℝ :=
  (1 + edges) * adaptiveSoundnessCoefficient r edges (2 * r) *
    primitiveBudgetCoefficient r edges

theorem primitiveSoundnessCoefficient_one_le (r : ℕ) {edges : ℝ} (hE : 0 ≤ edges) :
    1 ≤ primitiveSoundnessCoefficient r edges := by
  have hC := adaptiveSoundnessCoefficient_one_le r (2 * r) hE
  have hc := (primitiveBudgetCoefficient_bounds r hE).1
  have hfirst : 1 ≤ (1 + edges) * adaptiveSoundnessCoefficient r edges (2 * r) := by
    nlinarith [mul_nonneg hE (show 0 ≤ adaptiveSoundnessCoefficient r edges (2 * r) by linarith)]
  unfold primitiveSoundnessCoefficient
  nlinarith [mul_nonneg (sub_nonneg.mpr hfirst) (sub_nonneg.mpr hc)]

theorem primitiveSoundness_power_bounds (r : ℕ) {edges t : ℝ}
    (hE : 0 ≤ edges) (ht : 0 ≤ t) :
    let p := adaptiveSoundnessCoefficient r edges (2 * r) *
      iteratedRoot (3 * (2 * r)) (primitiveBudgetCoefficient r edges * t)
    p ≤ primitiveSoundnessCoefficient r edges * iteratedRoot (6 * r) t ∧
    edges * p ≤ primitiveSoundnessCoefficient r edges * iteratedRoot (6 * r) t := by
  dsimp only
  have hC := adaptiveSoundnessCoefficient_one_le r (2 * r) hE
  have hc := (primitiveBudgetCoefficient_bounds r hE).1
  have hR := iteratedRoot_nonneg (6 * r) ht
  have hroot := iteratedRoot_scale_le (6 * r) (t := t) hc
  have hn : 3 * (2 * r) = 6 * r := by omega
  rw [hn]
  have hp := mul_le_mul_of_nonneg_left hroot (by linarith :
    0 ≤ adaptiveSoundnessCoefficient r edges (2 * r))
  have hbase : 0 ≤ adaptiveSoundnessCoefficient r edges (2 * r) *
      (primitiveBudgetCoefficient r edges * iteratedRoot (6 * r) t) := by positivity
  unfold primitiveSoundnessCoefficient
  constructor
  · calc
      _ ≤ _ := hp
      _ ≤ (1 + edges) * (adaptiveSoundnessCoefficient r edges (2 * r) *
          (primitiveBudgetCoefficient r edges * iteratedRoot (6 * r) t)) :=
        le_mul_of_one_le_left hbase (by linarith)
      _ = _ := by ring
  · calc
      _ ≤ edges * (adaptiveSoundnessCoefficient r edges (2 * r) *
          (primitiveBudgetCoefficient r edges * iteratedRoot (6 * r) t)) :=
        mul_le_mul_of_nonneg_left hp hE
      _ ≤ (1 + edges) * (adaptiveSoundnessCoefficient r edges (2 * r) *
          (primitiveBudgetCoefficient r edges * iteratedRoot (6 * r) t)) :=
        mul_le_mul_of_nonneg_right (by linarith) hbase
      _ = _ := by ring

/-- The finite-game soundness loss has the paper's two-term error profile,
with constants uniform in the source game and the register dimension. -/
theorem exists_primitiveSoundness_errorProfile (r : ℕ) {edges a b : ℝ}
    (hE : 0 ≤ edges) (ha : 0 ≤ a) (hb0 : 0 < b) (hb1 : b ≤ 1) :
    ∃ a' b' : ℝ, 1 ≤ a' ∧ 0 < b' ∧ b' ≤ 1 ∧
      ∀ x ε : ℝ, 1 ≤ x → 0 ≤ ε →
        primitiveSoundnessCoefficient r edges *
          iteratedRoot (6 * r) (errorProfile a b x ε) ≤ errorProfile a' b' x ε := by
  refine ⟨powerCoefficient (primitiveSoundnessCoefficient r edges) a (rootExponent (6 * r)),
    b * rootExponent (6 * r), one_le_powerCoefficient _ _ _,
    (power_exponent_bounds hb0 hb1 (rootExponent_pos _) (rootExponent_le_one _)).1,
    (power_exponent_bounds hb0 hb1 (rootExponent_pos _) (rootExponent_le_one _)).2, ?_⟩
  intro x ε hx hε
  exact errorProfile_iteratedRoot (6 * r)
    (by linarith [primitiveSoundnessCoefficient_one_le r hE]) ha hx hε

namespace TypedEstimates
universe u v
variable {F ι A : Type} {PauliType PauliAnswer κ : Type*}
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [Nonempty A]
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Fintype κ] [DecidableEq κ] {ℓ : ℕ}
variable {𝒞 𝒜 ℬ : Type u} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [StarModule ℂ 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜]
  [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [StarModule ℂ ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
  [StarProper ℬ]

set_option maxHeartbeats 800000 in
/-- Complete finite-game soundness on an extracted register model, in every value model
dominating its POVM strategies. No hiding, prefix invariant, future measurement, or small-error
hypothesis is assumed. -/
theorem quantumValue_ge_of_primitive_pauli
    (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (hL : ∀ w, (L w).ExactlyOn univ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (ω : ValueModel) (G : Game (ι → F) (ι → F) A A)
    (hμ : ∀ x y, G.μ x y = CL.clDist (L false).eval (L true).eval x y)
    (hD : G.D = D) (Ξ : BipartiteModel.{v} 𝒞 𝒜 ℬ) (hΞ : ‖Ξ.ψ‖ = 1)
    (hω : ω.DominatesPOVM Ξ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) 𝒜))
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) ℬ))
    (hMA : ∀ q, IsPVMIn (MA q).op) (hMB : ∀ q, IsPVMIn (MB q).op)
    (qX qZ : κ → ZMod 2)
    (hqX : ∀ z, (P X).eval z = qX) (hqZ : ∀ z, (P Z).eval z = qZ)
    {t : ℝ} (ht : 0 ≤ t)
    (hfail : 1 - (Ξ.reg (ι → F)).povmValue (parsedGame E X Z P L projectPauli D DP) MA MB ≤ t)
    (hX : ∑ x, (Ξ.reg (ι → F)).stateSqNorm
      (((MA (QuestionType.pauli X, qX)).map (pauliProjection projectPauli)).op x -
        smulKron 1 (Honest.pauliXReadout x)) ≤ t)
    (hZ : introBobZError projectPauli Z qZ Ξ MB ≤ t) :
    1 - primitiveSoundnessCoefficient ℓ (TypeGraph.edges E X Z ℓ).card *
      iteratedRoot (6 * ℓ) t ≤ ω.val G := by
  let edges : ℝ := (TypeGraph.edges E X Z ℓ).card
  have hE : 0 ≤ edges := Nat.cast_nonneg _
  let c := primitiveBudgetCoefficient ℓ edges
  let s := c * t
  have hc := primitiveBudgetCoefficient_bounds ℓ hE
  have hs : 0 ≤ s := mul_nonneg (by linarith [hc.1]) ht
  have hts : t ≤ s := le_mul_of_one_le_left ht hc.1
  have hpay := primitiveSoundness_power_bounds ℓ hE ht
  rcases adaptiveSoundness_power_cases ℓ (2 * ℓ) hE hs
    (le_refl s) (le_refl s) (le_refl s) with ⟨hsmall, hbound⟩ | hlarge
  · have hZA : introAliceZError projectPauli Z qZ Ξ MA ≤ s := by
      apply (introAliceZError_le_of_bob E X Z P L projectPauli D DP
        Ξ hΞ MA MB qZ hqZ hfail hZ).trans
      calc
        _ = (4 * edges + 2) * t := by dsimp [edges]; ring
        _ ≤ s := mul_le_mul_of_nonneg_right hc.2.1 ht
    have hhide (w : Bool) (j : Fin ℓ) := hiding_register_rigidity_of_pauli
      E X Z P L projectPauli D DP Ξ hΞ MA MB hfail qX qZ hqX hqZ
      (hMA _) hX hZ w (hL w).supportedOn (hMA _) (fun j => hMA _) (fun j => hMB _) j
    have hhA (j : Fin ℓ) : hidingAliceError L false (hL false).supportedOn Ξ MA j ≤ s := by
      apply (hhide false j).2.trans
      rw [hidingPauliBudget_common]
      calc
        _ = (4 * edges + 2 * hidingPauliBudget ℓ edges 1 1) * t := by dsimp [edges]; ring
        _ ≤ s := mul_le_mul_of_nonneg_right hc.2.2.2 ht
    have hhB (j : Fin ℓ) : hidingBobError L true (hL true).supportedOn Ξ MB j ≤ s := by
      apply (hhide true j).1.trans
      rw [hidingPauliBudget_common]
      exact mul_le_mul_of_nonneg_right hc.2.2.1 ht
    obtain ⟨N₁, N₂, MAN, MBN, IA, IB, hN₂, _, _, hf, hred⟩ := exists_intro_two_sided_iteration
      E X Z P L projectPauli D DP Ξ hΞ MA MB hMA hMB qZ hqZ
      (fun w => (hL w).supportedOn) hs hs hs (hfail.trans hts) hZA
      (hZ.trans hts) hhA hhB hsmall hsmall hsmall
    obtain ⟨S, hS⟩ := TypedExtraction.exists_strategy_of_terminal_invariants
      E X Z P L hL projectPauli D DP G hμ hD N₂.Ξ.swap hN₂ MAN MBN IA IB hf
    have hbudget := (mul_le_mul_of_nonneg_left hbound hE).trans hpay.2
    have hvalue : S.value ≤ ω.val G :=
      ValueModel.DominatesPOVM.dominates (ValueModel.DominatesPOVM.of_povmReduces hred hω) G S
    exact (by linarith : 1 - primitiveSoundnessCoefficient ℓ edges *
      iteratedRoot (6 * ℓ) t ≤ S.value).trans hvalue
  · have htotal := hlarge.trans hpay.1
    exact (by linarith : 1 - primitiveSoundnessCoefficient ℓ edges *
      iteratedRoot (6 * ℓ) t ≤ 0).trans (ω.nonneg G)

/-- The composed soundness theorem in the original two-term profile. Its
exponent and coefficient depend only on depth, graph size, and the primitive
QLD profile constants. -/
theorem quantumValue_ge_of_primitive_profile
    (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (hL : ∀ w, (L w).ExactlyOn univ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (ω : ValueModel) (G : Game (ι → F) (ι → F) A A)
    (hμ : ∀ x y, G.μ x y = CL.clDist (L false).eval (L true).eval x y)
    (hD : G.D = D) (Ξ : BipartiteModel.{v} 𝒞 𝒜 ℬ) (hΞ : ‖Ξ.ψ‖ = 1)
    (hω : ω.DominatesPOVM Ξ)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) 𝒜))
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) ℬ))
    (hMA : ∀ q, IsPVMIn (MA q).op) (hMB : ∀ q, IsPVMIn (MB q).op)
    (qX qZ : κ → ZMod 2)
    (hqX : ∀ z, (P X).eval z = qX) (hqZ : ∀ z, (P Z).eval z = qZ)
    {a b x ε : ℝ} (ha : 0 ≤ a) (hx : 1 ≤ x) (hε : 0 ≤ ε)
    (hfail : 1 - (Ξ.reg (ι → F)).povmValue (parsedGame E X Z P L projectPauli D DP) MA MB ≤
      errorProfile a b x ε)
    (hX : ∑ z, (Ξ.reg (ι → F)).stateSqNorm
      (((MA (QuestionType.pauli X, qX)).map (pauliProjection projectPauli)).op z -
        smulKron 1 (Honest.pauliXReadout z)) ≤ errorProfile a b x ε)
    (hZ : introBobZError projectPauli Z qZ Ξ MB ≤ errorProfile a b x ε) :
    1 - errorProfile
      (powerCoefficient (primitiveSoundnessCoefficient ℓ (TypeGraph.edges E X Z ℓ).card)
        a (rootExponent (6 * ℓ)))
      (b * rootExponent (6 * ℓ)) x ε ≤ ω.val G := by
  have hv := quantumValue_ge_of_primitive_pauli E X Z P L hL projectPauli D DP
    ω G hμ hD Ξ hΞ hω MA MB hMA hMB qX qZ hqX hqZ
    (errorProfile_nonneg ha (by linarith) hε) hfail hX hZ
  have hC := primitiveSoundnessCoefficient_one_le ℓ
    (Nat.cast_nonneg (α := ℝ) (TypeGraph.edges E X Z ℓ).card)
  have hp := errorProfile_iteratedRoot (C := primitiveSoundnessCoefficient ℓ
    (TypeGraph.edges E X Z ℓ).card) (b := b) (6 * ℓ)
    (by linarith) ha hx hε
  linarith

end TypedEstimates
end MIPRE.Introspection
end

end
