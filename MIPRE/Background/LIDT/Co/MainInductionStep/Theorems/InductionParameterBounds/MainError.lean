/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
MainInductionStep/Theorems/InductionParameterBounds/MainError.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.MainInductionStep.Theorems.InductionParameterBounds.Preliminaries
public import MIPRE.Background.LIDT.MIPStarRE.LDT.MainInductionStep.Theorems.InductionParameterBounds.MainError

@[expose] public section

/-!
# Section 6 — Main-induction error bounds

The scalar consequences of the non-vacuous hypothesis `mainInductionError < 1`: the bounds
`eps ≤ 1`, `delta ≤ 1`, `gamma ≤ 1`, `params.d ≤ params.q` and `3 ≤ k² · m_next` for a good
strategy. This is the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/MainInductionStep/Theorems/InductionParameterBounds/MainError.lean`
in the port of `planning/c6b-plan.md` (milestone M12, section "Port conventions").

Ten declarations read a strategy and are ported: the five bounds for a good
`SymStrat params.next 𝔓 K` and their five answer-valued analogues for a good
`AnswerSymStrat params.next 𝔓 K`. A strategy enters only through the nonnegativity of
`eps`, `delta` and `gamma` that its `IsGood` gives (`eps_nonneg_of_isGood` and its siblings of
`Co/Test/StrategyFailures.lean`), so each ported lemma applies one of two private scalar
theorems, `le_one_of_mainInductionError_lt_one_of_nonneg` and
`three_le_k_sq_mul_next_m_of_nonneg`, which take those three nonnegativity facts in place of the
strategy. No lemma of the file has a swap, density or normalization hypothesis.

The other six declarations are arithmetic on the classical error functions `mainInductionError`
and `mainInductionNu`: this file imports the vendored file and names them through an explicit
`open MIPStarRE.LDT.MainInductionStep (…)` list. Importing it adds no operator content, since the
vendored file's only import is the vendored `InductionParameterBounds/Preliminaries`, which the
ported `Preliminaries` already imports.

## Not ported

- `k_ne_zero_of_mainInductionError_lt_one`: classical, imported.
- `one_le_k_of_mainInductionError_lt_one`: classical, imported.
- `mainInductionNu_lt_one_of_mainInductionError_lt_one`: classical, imported.
- `le_one_of_mainInductionError_lt_one_of_scaled_bound`: classical, imported.
- `mainInductionNu_scaled_component_le`: classical, imported.
- `mainInductionSuccessorBound_pred`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `blueprint/src/chapter/ch10_induction.tex`
- `references/ldt-paper/inductive_step.tex`
-/

namespace MIPRE.LIDT.Co.MainInductionStep

open MIPStarRE.LDT (Parameters FieldModel)
open MIPStarRE.LDT.MainInductionStep (mainInductionError mainInductionNu
  one_le_k_of_mainInductionError_lt_one le_one_of_mainInductionError_lt_one_of_scaled_bound)
open MIPRE.LIDT.Co (SymStrat AnswerSymStrat eps_nonneg_of_isGood delta_nonneg_of_isGood
  gamma_nonneg_of_isGood answer_eps_nonneg_of_isGood answer_delta_nonneg_of_isGood
  answer_gamma_nonneg_of_isGood)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The scalar core of the `≤ 1` bounds: with `eps`, `delta`, `gamma` nonnegative and
`mainInductionError params.next k eps delta gamma < 1`, each of `eps`, `delta`, `gamma` and
`d / q` is at most `1`, since each `x^{1/1024}` is a summand of `mainInductionNu`. -/
private theorem le_one_of_mainInductionError_lt_one_of_nonneg
    (params : Parameters) {k : ℕ} {eps delta gamma : ℝ}
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta) (hgamma : 0 ≤ gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    eps ≤ 1 ∧ delta ≤ 1 ∧ gamma ≤ 1 ∧ params.d ≤ params.q := by
  have ha := Real.rpow_nonneg heps (1 / (1024 : ℝ))
  have hb := Real.rpow_nonneg hdelta (1 / (1024 : ℝ))
  have hc := Real.rpow_nonneg hgamma (1 / (1024 : ℝ))
  have hr := Real.rpow_nonneg
    (div_nonneg (Nat.cast_nonneg params.d) (Nat.cast_nonneg params.q) : (0 : ℝ) ≤ _)
    (1 / (1024 : ℝ))
  have hle : ∀ x : ℝ,
      x ^ (1 / (1024 : ℝ)) ≤
        eps ^ (1 / (1024 : ℝ)) + delta ^ (1 / (1024 : ℝ)) + gamma ^ (1 / (1024 : ℝ)) +
          ((params.d : ℝ) / (params.q : ℝ)) ^ (1 / (1024 : ℝ)) → x ≤ 1 :=
    fun x hx => le_one_of_mainInductionError_lt_one_of_scaled_bound params hsmall
      (mul_le_mul_of_nonneg_left hx (by positivity))
  set a := eps ^ (1 / (1024 : ℝ))
  set b := delta ^ (1 / (1024 : ℝ))
  set c := gamma ^ (1 / (1024 : ℝ))
  set r := ((params.d : ℝ) / (params.q : ℝ)) ^ (1 / (1024 : ℝ))
  have hdq := hle ((params.d : ℝ) / (params.q : ℝ)) (show r ≤ a + b + c + r by linarith)
  have hq : (0 : ℝ) < params.q := by exact_mod_cast params.hq
  exact ⟨hle eps (show a ≤ a + b + c + r by linarith),
    hle delta (show b ≤ a + b + c + r by linarith),
    hle gamma (show c ≤ a + b + c + r by linarith),
    by exact_mod_cast (div_le_one hq).1 hdq⟩

/-- The scalar core of `three_le_k_sq_mul_next_m_of_hsmall`: with `eps`, `delta`, `gamma`
nonnegative and `mainInductionError params.next k eps delta gamma < 1`,
`3 ≤ k² · m_next`. -/
private theorem three_le_k_sq_mul_next_m_of_nonneg
    (params : Parameters) {k : ℕ} {eps delta gamma : ℝ}
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta) (hgamma : 0 ≤ gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    (3 : ℝ) ≤ ((k : ℝ) ^ (2 : ℕ)) * (params.next.m : ℝ) := by
  have hk1 := one_le_k_of_mainInductionError_lt_one params.next k eps delta gamma hsmall
  have hm : params.next.m = params.m + 1 := rfl
  have hm1 := params.hm
  have hm2 : (2 : ℝ) ≤ params.next.m := by rw [hm]; exact_mod_cast Nat.succ_le_succ hm1
  rcases (show k = 1 ∨ 2 ≤ k by omega) with rfl | hk2
  · rcases (show params.next.m = 2 ∨ 3 ≤ params.next.m by omega) with hm2' | hm3
    · exfalso
      have hnu : 0 ≤ mainInductionNu params.next 1 eps delta gamma :=
        mul_nonneg (by positivity) (add_nonneg (add_nonneg (add_nonneg
          (Real.rpow_nonneg heps _) (Real.rpow_nonneg hdelta _)) (Real.rpow_nonneg hgamma _))
          (Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _))
      have hexp := Real.add_one_le_exp (-((1 : ℕ) : ℝ) / (80000 * (2 : ℝ) ^ (2 : ℕ)))
      have heq : mainInductionError params.next 1 eps delta gamma =
          (2 : ℝ) ^ (2 : ℕ) * (mainInductionNu params.next 1 eps delta gamma +
            Real.exp (-((1 : ℕ) : ℝ) / (80000 * (2 : ℝ) ^ (2 : ℕ)))) := by
        simp only [mainInductionError, hm2', Nat.cast_ofNat, neg_div]
      norm_num at hexp heq
      linarith
    · have : (3 : ℝ) ≤ params.next.m := by exact_mod_cast hm3
      simpa using this
  · have hk : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    have := mul_le_mul (pow_le_pow_left₀ (by norm_num) hk 2) hm2 (by norm_num) (by positivity)
    norm_num at this
    linarith

/-- Under `mainInductionError < 1`, the axis-parallel error of a good strategy satisfies
`eps ≤ 1`. -/
lemma eps_le_one_of_mainInductionError_lt_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    {eps delta gamma : ℝ} {k : ℕ}
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    eps ≤ 1 :=
  (le_one_of_mainInductionError_lt_one_of_nonneg params
    (eps_nonneg_of_isGood params.next strategy hgood)
    (delta_nonneg_of_isGood params.next strategy hgood)
    (gamma_nonneg_of_isGood params.next strategy hgood) hsmall).1

/-- Under `mainInductionError < 1`, the self-consistency error of a good strategy satisfies
`delta ≤ 1`. -/
lemma delta_le_one_of_mainInductionError_lt_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    {eps delta gamma : ℝ} {k : ℕ}
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    delta ≤ 1 :=
  (le_one_of_mainInductionError_lt_one_of_nonneg params
    (eps_nonneg_of_isGood params.next strategy hgood)
    (delta_nonneg_of_isGood params.next strategy hgood)
    (gamma_nonneg_of_isGood params.next strategy hgood) hsmall).2.1

/-- `3 ≤ k² · m_next` in the small-parameter regime of a good strategy. -/
lemma three_le_k_sq_mul_next_m_of_hsmall
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    {eps delta gamma : ℝ} {k : ℕ}
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    (3 : ℝ) ≤ ((k : ℝ) ^ (2 : ℕ)) * (params.next.m : ℝ) :=
  three_le_k_sq_mul_next_m_of_nonneg params
    (eps_nonneg_of_isGood params.next strategy hgood)
    (delta_nonneg_of_isGood params.next strategy hgood)
    (gamma_nonneg_of_isGood params.next strategy hgood) hsmall

/-- Under `mainInductionError < 1`, the diagonal error of a good strategy satisfies
`gamma ≤ 1`. -/
lemma gamma_le_one_of_mainInductionError_lt_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    {eps delta gamma : ℝ} {k : ℕ}
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    gamma ≤ 1 :=
  (le_one_of_mainInductionError_lt_one_of_nonneg params
    (eps_nonneg_of_isGood params.next strategy hgood)
    (delta_nonneg_of_isGood params.next strategy hgood)
    (gamma_nonneg_of_isGood params.next strategy hgood) hsmall).2.2.1

/-- Under `mainInductionError < 1` for a good strategy, `params.d ≤ params.q`. -/
lemma dq_le_q_of_mainInductionError_lt_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    {eps delta gamma : ℝ} {k : ℕ}
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    params.d ≤ params.q :=
  (le_one_of_mainInductionError_lt_one_of_nonneg params
    (eps_nonneg_of_isGood params.next strategy hgood)
    (delta_nonneg_of_isGood params.next strategy hgood)
    (gamma_nonneg_of_isGood params.next strategy hgood) hsmall).2.2.2

/-! ### Answer-valued small-error scalar consequences -/

/-- Answer-valued analogue of `eps_le_one_of_mainInductionError_lt_one`. -/
lemma answer_eps_le_one_of_mainInductionError_lt_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K)
    {eps delta gamma : ℝ} {k : ℕ}
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    eps ≤ 1 :=
  (le_one_of_mainInductionError_lt_one_of_nonneg params
    (answer_eps_nonneg_of_isGood params.next strategy hgood)
    (answer_delta_nonneg_of_isGood params.next strategy hgood)
    (answer_gamma_nonneg_of_isGood params.next strategy hgood) hsmall).1

/-- Answer-valued analogue of `delta_le_one_of_mainInductionError_lt_one`. -/
lemma answer_delta_le_one_of_mainInductionError_lt_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K)
    {eps delta gamma : ℝ} {k : ℕ}
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    delta ≤ 1 :=
  (le_one_of_mainInductionError_lt_one_of_nonneg params
    (answer_eps_nonneg_of_isGood params.next strategy hgood)
    (answer_delta_nonneg_of_isGood params.next strategy hgood)
    (answer_gamma_nonneg_of_isGood params.next strategy hgood) hsmall).2.1

/-- Answer-valued analogue of `gamma_le_one_of_mainInductionError_lt_one`. -/
lemma answer_gamma_le_one_of_mainInductionError_lt_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K)
    {eps delta gamma : ℝ} {k : ℕ}
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    gamma ≤ 1 :=
  (le_one_of_mainInductionError_lt_one_of_nonneg params
    (answer_eps_nonneg_of_isGood params.next strategy hgood)
    (answer_delta_nonneg_of_isGood params.next strategy hgood)
    (answer_gamma_nonneg_of_isGood params.next strategy hgood) hsmall).2.2.1

/-- Answer-valued analogue of `dq_le_q_of_mainInductionError_lt_one`. -/
lemma answer_dq_le_q_of_mainInductionError_lt_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K)
    {eps delta gamma : ℝ} {k : ℕ}
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    params.d ≤ params.q :=
  (le_one_of_mainInductionError_lt_one_of_nonneg params
    (answer_eps_nonneg_of_isGood params.next strategy hgood)
    (answer_delta_nonneg_of_isGood params.next strategy hgood)
    (answer_gamma_nonneg_of_isGood params.next strategy hgood) hsmall).2.2.2

/-- Answer-valued analogue of `three_le_k_sq_mul_next_m_of_hsmall`. -/
lemma answer_three_le_k_sq_mul_next_m_of_hsmall
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K)
    {eps delta gamma : ℝ} {k : ℕ}
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    (3 : ℝ) ≤ ((k : ℝ) ^ (2 : ℕ)) * (params.next.m : ℝ) :=
  three_le_k_sq_mul_next_m_of_nonneg params
    (answer_eps_nonneg_of_isGood params.next strategy hgood)
    (answer_delta_nonneg_of_isGood params.next strategy hgood)
    (answer_gamma_nonneg_of_isGood params.next strategy hgood) hsmall

end MIPRE.LIDT.Co.MainInductionStep

end
