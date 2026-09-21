/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.Readout
import MIPRE.Foundations.Verifier

/-! # Extracting the original strategy from introspective readouts

This proves the final game-value calculation in the soundness proof of
`introspection.tex`. Once the induction has produced a question readout tensored
with an auxiliary measurement depending on that question, the original strategy
uses precisely those auxiliary measurements and the auxiliary state. The value
identity below is exact, including the question-distribution normalization.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder

variable {I X Y A B H K : Type*}
  [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K]

set_option linter.unusedSectionVars false

/-- Read the question from the EPR seed and then measure the auxiliary system. -/
def conditionalReadout (f : I → X) (P : X → A → Matrix H H ℂ)
    (xa : X × A) : Matrix (I × H) (I × H) ℂ := readout f xa.1 ⊗ₖ P xa.1 xa.2

/-- The question-dependent auxiliary family gives an actual joint PVM. -/
theorem conditionalReadout_isPVM (f : I → X) (P : X → A → Matrix H H ℂ)
    (hP : ∀ x, IsPVM (P x)) : IsPVM (conditionalReadout f P) where
  isSelfAdjoint xa := by
    rw [conditionalReadout, Matrix.conjTranspose_kronecker,
      (readout_isPVM f).isSelfAdjoint, (hP xa.1).isSelfAdjoint]
  idem xa := by
    rw [conditionalReadout, ← Matrix.mul_kronecker_mul,
      (readout_isPVM f).idem, (hP xa.1).idem]
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp only [conditionalReadout]
    have hs (x : X) : (∑ a, readout f x ⊗ₖ P x a) = readout f x ⊗ₖ (1 : Matrix H H ℂ) := by
      rw [← kronecker_sum_right, (hP x).sum_eq_one]
    simp_rw [hs]
    rw [← sum_kronecker_left, (readout_isPVM f).sum_eq_one, Matrix.one_kronecker_one]

/-- The full joint answer probability factors into the original question law and
the auxiliary strategy's conditional answer probability. -/
theorem bornProb_conditionalReadout (f : I → X) (g : I → Y) (ξ : H × K → ℂ)
    (P : X → A → Matrix H H ℂ) (Q : Y → B → Matrix K K ℂ)
    (hP : ∀ x a, (P x a).PosSemidef) (hQ : ∀ y b, (Q y b).PosSemidef)
    (xa : X × A) (yb : Y × B) :
    bornProb (registerState I ξ) (conditionalReadout f P xa) (conditionalReadout g Q yb) =
      SampledGame.dist f g xa.1 yb.1 * bornProb ξ (P xa.1 xa.2) (Q yb.1 yb.2) := by
  rw [registerState, conditionalReadout, conditionalReadout,
    bornProb_expVec_kron _ _ (hP _ _) (hQ _ _), bornProb_registerEPR_readout]

/-- Acceptance probability of the introspective test on the terminal measurements. -/
def readoutAcceptance (f : I → X) (g : I → Y) (ξ : H × K → ℂ)
    (P : X → A → Matrix H H ℂ) (Q : Y → B → Matrix K K ℂ)
    (D : X → Y → A → B → Bool) : ℝ :=
  ∑ xa : X × A, ∑ yb : Y × B,
    (if D xa.1 yb.1 xa.2 yb.2 then 1 else 0) *
      bornProb (registerState I ξ) (conditionalReadout f P xa) (conditionalReadout g Q yb)

/-- The terminal readout acceptance is the value of the actual auxiliary strategy. -/
theorem readoutAcceptance_eq_value (G : Game X Y A B) (f : I → X) (g : I → Y)
    (hμ : ∀ x y, G.μ x y = SampledGame.dist f g x y)
    (S : TensorProductStrategy G) :
    readoutAcceptance f g S.ψ S.PA.M S.PB.M G.D = S.value := by
  have hPA (x : X) (a : A) : (S.PA.M x a).PosSemidef := (S.PA.toPOVM x).posSemidef a
  have hPB (y : Y) (b : B) : (S.PB.M y b).PosSemidef := (S.PB.toPOVM y).posSemidef b
  unfold readoutAcceptance
  simp_rw [bornProb_conditionalReadout f g S.ψ S.PA.M S.PB.M hPA hPB]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  unfold TensorProductStrategy.value
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => ?_
  rw [hμ]
  unfold bornProb
  ring

/-- No further error or dimension factor is lost in the final extraction step. -/
theorem quantumValue_ge_of_readoutAcceptance (G : Game X Y A B)
    (f : I → X) (g : I → Y) (hμ : ∀ x y, G.μ x y = SampledGame.dist f g x y)
    (S : TensorProductStrategy G) (ε : ℝ)
    (h : 1 - ε ≤ readoutAcceptance f g S.ψ S.PA.M S.PB.M G.D) :
    1 - ε ≤ quantumValue G := by
  rw [readoutAcceptance_eq_value G f g hμ S] at h
  exact h.trans (le_ciSup (TensorProductStrategy.bddAbove_range_value G) S)

/-- The extracted strategy keeps the auxiliary state and its question-indexed
measurements, discarding the EPR register used to generate the questions. -/
def extractedStrategy (G : Game X Y A B) {dA dB : ℕ}
    (ξ : Fin dA × Fin dB → ℂ) (hξ : star ξ ⬝ᵥ ξ = 1)
    (P : X → A → Matrix (Fin dA) (Fin dA) ℂ)
    (Q : Y → B → Matrix (Fin dB) (Fin dB) ℂ)
    (hP : ∀ x, IsPVM (P x)) (hQ : ∀ y, IsPVM (Q y)) : TensorProductStrategy G where
  dA := dA
  dB := dB
  ψ := ξ
  ψ_unit := hξ
  PA :=
    { M := P
      selfAdjoint := fun x a => by rw [Matrix.star_eq_conjTranspose]; exact (hP x).isSelfAdjoint a
      projective := fun x a => (hP x).idem a
      normalized := fun x => (hP x).sum_eq_one }
  PB :=
    { M := Q
      selfAdjoint := fun y b => by rw [Matrix.star_eq_conjTranspose]; exact (hQ y).isSelfAdjoint b
      projective := fun y b => (hQ y).idem b
      normalized := fun y => (hQ y).sum_eq_one }

/-- The final introspection test directly certifies an equally good legal strategy
for the original game, with exactly the auxiliary local dimensions. -/
theorem exists_strategy_of_readoutAcceptance (G : Game X Y A B)
    (f : I → X) (g : I → Y) (hμ : ∀ x y, G.μ x y = SampledGame.dist f g x y)
    {dA dB : ℕ} (ξ : Fin dA × Fin dB → ℂ) (hξ : star ξ ⬝ᵥ ξ = 1)
    (P : X → A → Matrix (Fin dA) (Fin dA) ℂ)
    (Q : Y → B → Matrix (Fin dB) (Fin dB) ℂ)
    (hP : ∀ x, IsPVM (P x)) (hQ : ∀ y, IsPVM (Q y)) :
    ∃ S : TensorProductStrategy G,
      S.dA = dA ∧ S.dB = dB ∧ S.value = readoutAcceptance f g ξ P Q G.D := by
  exact ⟨extractedStrategy G ξ hξ P Q hP hQ, rfl, rfl,
    (readoutAcceptance_eq_value G f g hμ (extractedStrategy G ξ hξ P Q hP hQ)).symm⟩

/-- Specialization to the actual game of a normal-form verifier: there is no
unproved distribution-identification hypothesis at this interface. -/
theorem verifier_readoutAcceptance_eq_value {ℓ : ℕ} (V : Verifier ℓ) (n T : ℕ)
    (S : TensorProductStrategy (V.game n T)) :
    readoutAcceptance (V.sampler.cl n .alice).eval (V.sampler.cl n .bob).eval
      S.ψ S.PA.M S.PB.M (V.game n T).D = S.value := by
  apply readoutAcceptance_eq_value
  intro x y
  exact (sampled_dist_eq_clDist _ _ x y).symm

end MIPRE.Introspection

end
