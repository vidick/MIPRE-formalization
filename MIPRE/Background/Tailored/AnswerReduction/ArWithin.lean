/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.AnswerReduction.ArLpCost

@[expose] public section

/-!
# The complexity clause of the answer reduction

Slice P4h of `planning/aldous-lyons-track.md`, concluded: the output verifier of the answer
reduction (`ArRoutine.output`) is within the contract's output budget
(`TailoredAnswerReduction.within`): an input within `inBudget λ μ n` with `|𝒱| ≤ σ` gives an
output whose sampler, calculator and processor run within `outBound bound λ μ σ n` at degree
`outDegree deg μ`, whose questions have dimension and whose lengths are at most the same bound,
for a polynomial `bound` and a degree `deg` depending only on the routine (`output_within`), under
the one hypothesis that the routine's parameter program runs in polynomial time
(`ArRoutine.ParTime`). The calculator halting on every input, the contract's `len_total`, is
`ArRoutine.lenD_total`.
-/

noncomputable section

namespace MIPRE.Tailored.AnsRed.Typed

open Cost MIPRE.CL MIPRE.Pipeline

/-- A monomial bound below a larger one. -/
theorem pow_le_pow_of_le' {W K c m C M : ℕ} (hc : c ≤ C) (hm : m ≤ M) :
    (c * (W + 1) ^ m) ^ (K + 1) ≤ (C * (W + 1) ^ M) ^ (K + 1) :=
  Nat.pow_le_pow_left (Nat.mul_le_mul hc (Nat.pow_le_pow_right (by omega) hm)) _

namespace ArRoutine

variable {R : ArRoutine}

/-- **The complexity clause of the answer reduction** (`TailoredAnswerReduction.within`): an input
within `inBudget λ μ n` with `|𝒱| ≤ σ` gives an output within `outBound bound λ μ σ n` at degree
`outDegree deg μ`, for a polynomial `bound` and a degree `deg` depending only on the routine. -/
theorem output_within (hR : R.ParTime) (ℓ : ℕ) : ∃ (bound : Polynomial ℕ) (deg : ℕ),
    ∀ (V : TailoredVerifier (ℓ + 1)) (lam mu sigma n : ℕ),
      V.Within n (AnswerReduction.inBudget lam mu n) → V.size ≤ sigma →
      (R.output V lam mu sigma).Within n
        (Budget.uniform (AnswerReduction.outBound bound lam mu sigma n)
          (AnswerReduction.outDegree deg mu)) := by
  obtain ⟨cS, mS, eS, hS⟩ := arSampler_time hR ℓ
  obtain ⟨cm, mm, em, hdim⟩ := arSampler_dim_pdom hR ℓ
  obtain ⟨cL, mL, eL, hL⟩ := lenD_time hR
  obtain ⟨cP, mP, eP, hP⟩ := lpD_time ℓ hR
  obtain ⟨cB, mB, eB, hB⟩ := lenD_len_pdom hR
  set C := cS + cm + cL + cP + cB
  set M := mS + mm + mL + mP + mB
  refine ⟨Polynomial.C C * (Polynomial.X + 1) ^ M, eS + eL + eP,
    fun V lam mu sigma n hV hsz => ?_⟩
  set W := AnswerReduction.arg lam mu sigma n with hWdef
  have hW : AnswerReduction.arg lam mu sigma n ≤ W := le_rfl
  obtain ⟨hQ, hs, -, -⟩ := le_of_arg_le hW
  have hbd : AnswerReduction.outBound (Polynomial.C C * (Polynomial.X + 1) ^ M) lam mu sigma n =
      (C * (W + 1) ^ M) ^ (mu + 1) := by
    simp [AnswerReduction.outBound, hWdef]
  have hSz : esize V.sampler.prog ≤ W := ((le_max_left _ _).trans hsz).trans hs
  have hVS : V.sampler.TimeBoundAt n ((lam * n + 1) ^ mu) mu := hV.1
  have hVd : V.sampler.dim n ≤ W := hV.2.1.trans hQ
  -- a run dominated at `X = |d| + 1` is within the output bound
  have hrun : ∀ {c m e : ℕ} (p : Prog) (d : Data), c ≤ C → m ≤ M → e ≤ eS + eL + eP →
      (∃ r t, PDom W (d.size + 1) mu c m e t ∧ p.Runs (.cons (encode n) d) r t) →
      HaltsWithin p (.cons (encode n) d)
        ((C * (W + 1) ^ M) ^ (mu + 1) * (d.size + 1) ^ ((eS + eL + eP) * (mu + 1))) := by
    intro c m e p d hc hm he ⟨r, t, ht, hr⟩
    refine ⟨r, t, ht.le_final.trans ?_, hr⟩
    exact Nat.mul_le_mul (pow_le_pow_of_le' hc hm)
      (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ he))
  -- a dominated number at `X = 1` is below the output bound
  have hnum : ∀ {c m e v : ℕ}, c ≤ C → m ≤ M → PDom W 1 mu c m e v →
      v ≤ (C * (W + 1) ^ M) ^ (mu + 1) := by
    intro c m e v hc hm h
    have h' := h.le_final
    simp only [one_pow, Nat.mul_one] at h'
    exact h'.trans (pow_le_pow_of_le' hc hm)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- the sampler's time
    simp only [Budget.uniform_S, Budget.uniform_k, hbd, AnswerReduction.outDegree]
    exact (hS V.sampler lam mu sigma n hW hSz hVS).mono (pow_le_pow_of_le' (by omega) (by omega))
      (Nat.mul_le_mul_right _ (by omega))
  · -- the dimension
    simp only [Budget.uniform_d, hbd]
    exact hnum (by omega) (by omega) (hdim V.sampler lam mu sigma n le_rfl hW hVd)
  · -- the calculator's time
    simp only [Budget.uniform_D, Budget.uniform_k, hbd, AnswerReduction.outDegree]
    intro d
    exact hrun _ d (by omega) (by omega) (by omega)
      (hL lam mu sigma n d (by omega) hW le_rfl)
  · -- the processor's time
    simp only [Budget.uniform_D, Budget.uniform_k, hbd, AnswerReduction.outDegree]
    intro d
    exact hrun _ d (by omega) (by omega) (by omega)
      (hP V lam mu sigma n d (by omega) hW hsz hVS le_rfl)
  · -- the lengths
    simp only [Budget.uniform_B, hbd]
    intro x κ k hk
    exact hnum (by omega) (by omega) (hB lam mu sigma n le_rfl hW x κ k hk)

end ArRoutine

end MIPRE.Tailored.AnsRed.Typed

end
