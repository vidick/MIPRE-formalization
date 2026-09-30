/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.Readout
public import MIPRE.Foundations.Verifier
public import MIPRE.Foundations.LocalIsometry
public import MIPRE.Foundations.ModelStrategy

@[expose] public section

/-! # Extracting the original strategy from introspective readouts

This proves the final game-value calculation in the soundness proof of
`introspection.tex`. Once the induction has produced a question readout tensored
with an auxiliary measurement depending on that question, the original strategy
uses precisely those auxiliary measurements and the auxiliary state. The value
identity below is exact, including the question-distribution normalization.

In the register model `Ξ.reg I` (Phase 4 of `planning/mipco-track.md`): the readout of the
question tensored with an auxiliary operator `P` of the ancilla is `smulKron P (readout f x)`, and
the extracted strategy is a projective strategy of the ancillary model `Ξ` itself.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder

variable {I X Y A B : Type*}
  [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B]
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]

set_option linter.unusedSectionVars false

/-- Read the question from the EPR seed and then measure the auxiliary system. -/
def conditionalReadout {R : Type*} [Ring R] [Algebra ℂ R] (f : I → X) (P : X → A → R)
    (xa : X × A) : Matrix I I R := smulKron (P xa.1 xa.2) (readout f xa.1)

/-- The question-dependent auxiliary family gives an actual joint PVM. -/
theorem conditionalReadout_isPVM {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
    [StarModule ℂ R] (f : I → X) (P : X → A → R) (hP : ∀ x, IsPVMIn (P x)) :
    IsPVMIn (conditionalReadout f P) where
  star_eq xa := by
    rw [conditionalReadout, star_smulKron, (hP xa.1).star_eq, ← star_eq_conjTranspose,
      (readout_isPVM f).toIn.star_eq]
  idem xa := by
    rw [conditionalReadout, smulKron_mul, (readout_isPVM f).idem, (hP xa.1).idem]
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp only [conditionalReadout]
    simp_rw [← smulKron_sum_left, (hP _).sum_eq_one, ← smulKron_sum_right,
      (readout_isPVM f).sum_eq_one, smulKron_one_one]
  orthogonal {xa xa'} h := by
    rw [conditionalReadout, conditionalReadout, smulKron_mul]
    by_cases hx : xa.1 = xa'.1
    · have ha : xa.2 ≠ xa'.2 := fun ha => h (Prod.ext hx ha)
      rw [← hx, (hP xa.1).orthogonal ha, smulKron_zero_left]
    · rw [(readout_isPVM f).toIn.orthogonal hx, smulKron_zero_right]

/-- The full joint answer probability factors into the original question law and
the auxiliary strategy's conditional answer probability. -/
theorem bornProb_conditionalReadout (f : I → X) (g : I → Y) (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
    (P : X → A → 𝒜) (Q : Y → B → ℬ) (xa : X × A) (yb : Y × B) :
    (Ξ.reg I).bornProb (conditionalReadout f P xa) (conditionalReadout g Q yb) =
      SampledGame.dist f g xa.1 yb.1 * Ξ.bornProb (P xa.1 xa.2) (Q yb.1 yb.2) := by
  rw [conditionalReadout, conditionalReadout,
    BipartiteModel.bornProb_expand_smulKron _ _ _ _ ((readout_isPVM f).posSemidef _)
      ((readout_isPVM g).posSemidef _), bornProb_registerEPR_readout]

/-- Acceptance probability of the introspective test on the terminal measurements. -/
def readoutAcceptance (f : I → X) (g : I → Y) (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
    (P : X → A → 𝒜) (Q : Y → B → ℬ) (D : X → Y → A → B → Bool) : ℝ :=
  ∑ xa : X × A, ∑ yb : Y × B,
    (if D xa.1 yb.1 xa.2 yb.2 then 1 else 0) *
      (Ξ.reg I).bornProb (conditionalReadout f P xa) (conditionalReadout g Q yb)

variable [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- The terminal readout acceptance is the value of the actual auxiliary strategy. -/
theorem readoutAcceptance_eq_value (G : Game X Y A B) (f : I → X) (g : I → Y)
    (hμ : ∀ x y, G.μ x y = SampledGame.dist f g x y) (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
    (S : Ξ.ProjStrat G) :
    readoutAcceptance f g Ξ (fun x a => (S.PA x).op a) (fun y b => (S.PB y).op b) G.D =
      S.value := by
  unfold readoutAcceptance
  simp_rw [bornProb_conditionalReadout f g Ξ]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  unfold BipartiteModel.ProjStrat.value BipartiteModel.povmValue BipartiteModel.condWin
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hμ]
  ring

/-- No further error or dimension factor is lost in the final extraction step: the value of a
value model dominating the auxiliary model is at least the acceptance. -/
theorem val_ge_of_readoutAcceptance {X Y A B : Type} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (G : Game X Y A B) (f : I → X) (g : I → Y)
    (hμ : ∀ x y, G.μ x y = SampledGame.dist f g x y) {ω : ValueModel}
    (Ξ : BipartiteModel 𝒞 𝒜 ℬ) (hω : ω.Dominates Ξ) (S : Ξ.ProjStrat G) (ε : ℝ)
    (h : 1 - ε ≤ readoutAcceptance f g Ξ (fun x a => (S.PA x).op a)
      (fun y b => (S.PB y).op b) G.D) :
    1 - ε ≤ ω.val G := by
  rw [readoutAcceptance_eq_value G f g hμ Ξ S] at h
  exact h.trans (hω G S)

/-- The extracted strategy keeps the auxiliary model and its question-indexed
measurements, discarding the EPR register used to generate the questions. -/
def extractedStrategy (G : Game X Y A B) (Ξ : BipartiteModel 𝒞 𝒜 ℬ) (hΞ : ‖Ξ.ψ‖ = 1)
    (P : X → A → 𝒜) (Q : Y → B → ℬ) (hP : ∀ x, IsPVMIn (P x)) (hQ : ∀ y, IsPVMIn (Q y)) :
    Ξ.ProjStrat G where
  PA x := (hP x).toPOVMIn
  PB y := (hQ y).toPOVMIn
  projA x := hP x
  projB y := hQ y
  ψ_unit := hΞ

/-- The final introspection test directly certifies an equally good projective strategy
for the original game, in the auxiliary model. -/
theorem exists_strategy_of_readoutAcceptance (G : Game X Y A B)
    (f : I → X) (g : I → Y) (hμ : ∀ x y, G.μ x y = SampledGame.dist f g x y)
    (Ξ : BipartiteModel 𝒞 𝒜 ℬ) (hΞ : ‖Ξ.ψ‖ = 1) (P : X → A → 𝒜) (Q : Y → B → ℬ)
    (hP : ∀ x, IsPVMIn (P x)) (hQ : ∀ y, IsPVMIn (Q y)) :
    ∃ S : Ξ.ProjStrat G, S.value = readoutAcceptance f g Ξ P Q G.D :=
  ⟨extractedStrategy G Ξ hΞ P Q hP hQ,
    (readoutAcceptance_eq_value G f g hμ Ξ (extractedStrategy G Ξ hΞ P Q hP hQ)).symm⟩

/-- Specialization to the actual game of a normal-form verifier: there is no
unproved distribution-identification hypothesis at this interface. -/
theorem verifier_readoutAcceptance_eq_value {ℓ : ℕ} (V : Verifier ℓ) (n T : ℕ)
    (Ξ : BipartiteModel 𝒞 𝒜 ℬ) (S : Ξ.ProjStrat (V.game n T)) :
    readoutAcceptance (V.sampler.cl n .alice).eval (V.sampler.cl n .bob).eval
      Ξ (fun x a => (S.PA x).op a) (fun y b => (S.PB y).op b) (V.game n T).D = S.value := by
  apply readoutAcceptance_eq_value
  intro x y
  exact (sampled_dist_eq_clDist _ _ x y).symm

end MIPRE.Introspection

end

end
