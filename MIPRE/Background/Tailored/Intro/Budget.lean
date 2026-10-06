/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Introspection.Compiler

@[expose] public section

/-!
# The output's sampler within the budget at `λ`

The output tailored verifier at `λ` has the introspection verifier's sampler at `Cλ`, which is
within `seven`'s budget at `Cλ` (`sevenC_spec`). Since `C λ n + 1 ≤ (λ n + 1)^C`, that budget is
within the budget at `λ` with the exponent multiplied by `C` (`sampler_within`).
-/

namespace MIPRE.Tailored.Intro.Budget

open Cost MIPRE.Introspection

/-- Bernoulli's inequality, on the naturals. -/
theorem mul_add_one_le_pow (C x : ℕ) : C * x + 1 ≤ (x + 1) ^ C := by
  induction C with
  | zero => simp
  | succ C ih =>
    rw [pow_succ]
    nlinarith [Nat.one_le_pow C (x + 1) (by omega)]

theorem budget_pow_le (C lam n s : ℕ) :
    (C * lam * n + 1) ^ s ≤ (lam * n + 1) ^ (C * s) := by
  rw [pow_mul]
  apply Nat.pow_le_pow_left
  rw [mul_assoc]
  exact mul_add_one_le_pow C (lam * n)

/-- **The output's sampler at `Cλ` is within the budget at `λ`**, with the exponent
`C · sevenC`. -/
theorem sampler_within (source : Prog × Prog) {C : ℕ} (hC : 1 ≤ C) (lam n : ℕ) :
    (PauliSampler.finalSampler sevenConstant one_le_sevenConstant sevenConstant_spec.2.1 7
        (C * lam)).TimeBoundAt n ((lam * n + 1) ^ (C * sevenC)) (C * sevenC) ∧
      (PauliSampler.finalSampler sevenConstant one_le_sevenConstant sevenConstant_spec.2.1 7
        (C * lam)).dim n ≤ (lam * n + 1) ^ (C * sevenC) := by
  obtain ⟨hS, hd, -⟩ := sevenC_spec.1 source (C * lam) n
  refine ⟨hS.mono (budget_pow_le C lam n sevenC) (Nat.le_mul_of_pos_left _ hC), ?_⟩
  exact hd.trans (budget_pow_le C lam n sevenC)

end MIPRE.Tailored.Intro.Budget

end
