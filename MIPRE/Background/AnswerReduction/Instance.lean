/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.AnswerReduction.SoundFinal
import MIPRE.TM.CookLevin.ClassicalPcp

/-!
# Answer reduction, supplied

Piece AR-6 of `planning/answer-reduction.md` (`thm:answer-reduction`): the `AnswerReduction 5`
contract, inhabited by `arVerifier` over the classical PCP decider
(`TM.CookLevin.Pad.classicalPcpDecider`). The three hypotheses the construction and its analysis
ask of the PCP decider hold for it:

* its field is the Shoup field (`shoupField_classical`), by definition;
* its parameters are polynomial in `(log n, log T, Q, σ)` (`exists_paramsBound_classical`): the
  padded dimension is, and the field degree is polylogarithmic in `Q m'`;
* its field is eventually larger than every fixed power of `8 (Q + 1) m'`
  (`fieldLarge_classical`), from the field degree's square term.

The contract's clauses are then `arVerifier_bounds` (the complexity clause and the answer cut
below the output bound), `arVerifier_hasPerfectPCC` (completeness at the cut, hence at the bound)
and `arVerifier_soundness` (at the output bound).
-/

noncomputable section

namespace MIPRE.AnswerReduction

open Cost SAT TM.CookLevin.Pad TM.CookLevin.Desc Polynomial

/-! ## The classical PCP decider's hypotheses -/

/-- **The classical PCP decider uses the Shoup field.** -/
theorem shoupField_classical : ShoupField classicalPcpDecider := fun _ _ => rfl

/-- **The classical PCP decider's parameters are polynomial.** -/
theorem exists_paramsBound_classical : ∃ R : Polynomial ℕ, ParamsBound classicalPcpDecider R := by
  obtain ⟨P, hP⟩ := outerDim_polynomial
  refine ⟨2 * ((X + P + 3) ^ 2 + P) + 7 + P, fun n T Q σ => ?_⟩
  have hk := fieldDegree_le n T Q σ
  have ho := hP n T Q σ
  have hQ : Q ≤ LOf n T Q σ := by unfold LOf; omega
  have h2 : (Q + outerDim n T Q σ + 3) ^ 2 ≤ (LOf n T Q σ + P.eval (LOf n T Q σ) + 3) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hms : (pcpParams n T Q σ).m + (pcpParams n T Q σ).s ≤ outerDim n T Q σ := by
    rw [← pcpParams_outer]
    change _ ≤ 5 * _ + 5 + _
    omega
  change fieldDegree n T Q σ + (pcpParams n T Q σ).m + (pcpParams n T Q σ).s
    ≤ _
  change _ ≤ Polynomial.eval (LOf n T Q σ) _
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_ofNat, Polynomial.eval_X]
  omega

/-- **The classical PCP decider's field is eventually large.** -/
theorem fieldLarge_classical : FieldLarge classicalPcpDecider := fun e =>
  ⟨2 ^ e, fun n T Q σ h => pcpParams_field_eventually_large e n T Q σ h⟩

/-! ## The constants -/

/-- The parameter polynomial of the classical PCP decider. -/
def classicalR : Polynomial ℕ := exists_paramsBound_classical.choose

theorem classicalR_spec : ParamsBound classicalPcpDecider classicalR :=
  exists_paramsBound_classical.choose_spec

theorem exists_bounds : ∃ (bound : Polynomial ℕ) (deg : ℕ),
    (∀ (V : Verifier (4 + 1)) (lam mu sigma n : ℕ), V.Within n (inBudget lam mu n) →
      V.size ≤ sigma → (arVerifier classicalPcpDecider lam mu sigma V).Within n
        (Budget.uniform (outBound bound lam mu sigma n) (outDegree deg mu))) ∧
    ∀ lam mu sigma n, cutVal (arPar classicalPcpDecider lam mu sigma n)
      ≤ outBound bound lam mu sigma n :=
  arVerifier_bounds classicalPcpDecider classicalR 4 classicalR_spec

/-- The output bound's polynomial. -/
def arBound : Polynomial ℕ := exists_bounds.choose

/-- The output bound's degree. -/
def arDeg : ℕ := exists_bounds.choose_spec.choose

theorem arBounds_spec :
    (∀ (V : Verifier (4 + 1)) (lam mu sigma n : ℕ), V.Within n (inBudget lam mu n) →
      V.size ≤ sigma → (arVerifier classicalPcpDecider lam mu sigma V).Within n
        (Budget.uniform (outBound arBound lam mu sigma n) (outDegree arDeg mu))) ∧
    ∀ lam mu sigma n, cutVal (arPar classicalPcpDecider lam mu sigma n)
      ≤ outBound arBound lam mu sigma n :=
  exists_bounds.choose_spec.choose_spec

theorem exists_sound : ∃ (a b : ℝ) (C : ℕ), 1 ≤ a ∧ 0 < b ∧ b ≤ 1 ∧
    ∀ (V : Verifier (4 + 1)) (lam mu sigma n : ℕ) (ε : ℝ) (B : ℕ), C ≤ n → 2 ≤ n →
      1 ≤ lam → V.Within n (inBudget lam mu n) → V.decider.size ≤ sigma → 0 < ε →
      cutVal (arPar classicalPcpDecider lam mu sigma n) ≤ B →
      1 - ε < (arVerifier classicalPcpDecider lam mu sigma V).valStar n B →
      1 - delta a b lam mu sigma n ε ≤ V.valStar n (inAns lam mu n) :=
  arVerifier_soundness (ℓ := 4) classicalPcpDecider classicalR shoupField_classical classicalR_spec
    fieldLarge_classical

/-- The constant `a` of the soundness loss. -/
def arA : ℝ := exists_sound.choose

/-- The exponent `b` of the soundness loss. -/
def arB : ℝ := exists_sound.choose_spec.choose

/-- The threshold. -/
def arC : ℕ := exists_sound.choose_spec.choose_spec.choose

theorem arSound_spec : 1 ≤ arA ∧ 0 < arB ∧ arB ≤ 1 ∧
    ∀ (V : Verifier (4 + 1)) (lam mu sigma n : ℕ) (ε : ℝ) (B : ℕ), arC ≤ n → 2 ≤ n →
      1 ≤ lam → V.Within n (inBudget lam mu n) → V.decider.size ≤ sigma → 0 < ε →
      cutVal (arPar classicalPcpDecider lam mu sigma n) ≤ B →
      1 - ε < (arVerifier classicalPcpDecider lam mu sigma V).valStar n B →
      1 - delta arA arB lam mu sigma n ε ≤ V.valStar n (inAns lam mu n) :=
  exists_sound.choose_spec.choose_spec.choose_spec

/-! ## The instance -/

/-- **Answer reduction** (`thm:answer-reduction`), for `5`-level inputs: `arVerifier` over the
classical PCP decider. -/
def answerReduction : MIPRE.AnswerReduction 5 where
  a := arA
  b := arB
  one_le_a := arSound_spec.1
  b_pos := arSound_spec.2.1
  b_le_one := arSound_spec.2.2.1
  C := arC
  bound := arBound
  deg := arDeg
  sampler S lam mu sigma :=
    CL.Detyping.sampler graph (typedSampler S classicalPcpDecider lam mu sigma)
      (by norm_num)
  samplerProg := arSamplerProg classicalPcpDecider 4
  samplerProg_eq _ _ _ _ := rfl
  compute := arCompute classicalPcpDecider 4
  output V lam mu sigma := arVerifier classicalPcpDecider lam mu sigma V
  output_sampler _ _ _ _ := rfl
  output_decider _ _ _ _ := rfl
  within V lam mu sigma n hV hsz := arBounds_spec.1 V lam mu sigma n hV hsz
  completeness V lam mu sigma n _ hlam hmu hV hsz h :=
    Verifier.hasPerfectPCC_of_le _ (arBounds_spec.2 lam mu sigma n)
      (arVerifier_hasPerfectPCC classicalPcpDecider lam mu sigma V n shoupField_classical hlam hmu
        hV hsz h)
  soundness V lam mu sigma n ε hC hn2 hlam hV hsz hε h :=
    arSound_spec.2.2.2 V lam mu sigma n ε _ hC hn2 hlam hV hsz hε
      (arBounds_spec.2 lam mu sigma n) h

end MIPRE.AnswerReduction

end
