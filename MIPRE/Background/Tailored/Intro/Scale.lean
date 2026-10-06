/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.Intro.Budget
public import MIPRE.Background.Tailored.Intro.LenIntro
public import MIPRE.Background.Tailored.Intro.Output
public import MIPRE.Foundations.Introspection.SourceCompilerGuard

@[expose] public section

/-!
# The output at `C λ`, read at `λ`

The tailored presentation of `Introspection.seven` at `λ` runs `seven`'s construction at `C λ`,
where `C` is the constant of `TailoredVerifier.ofTNFVT_isBounded` (the input's normal form
verifier is `C λ`-bounded). This file collects what that rescaling needs:

* `λ ↦ 2^k λ` as a polynomial-time function (`mulPow2F`), the constant being rounded up to a
  power of two;
* budgets at `C λ` are budgets at `λ` with the exponent multiplied by `C` (`ansBound_scale`,
  `lenIntro_within`);
* at index `0` an output whose calculator outputs `0` and whose processor outputs no constraint
  has a perfect ZPC strategy, the trivial one (`hasPerfectZPC_of_zero`).
-/

namespace MIPRE.Tailored.Intro.Scale

open Cost Cost.Prog Cost.PolyTimeFun MIPRE.Introspection

/-! ## Multiplication by a power of two -/

/-- `n ↦ 2 n`. -/
noncomputable def doubleF : PolyTimeFun ℕ ℕ := ap₂ natBit (const false) (PolyTimeFun.id ℕ)

@[simp] theorem doubleF_apply (n : ℕ) : doubleF n = 2 * n := by
  simp [doubleF, Nat.bit_val]

/-- `n ↦ 2^k n`. -/
noncomputable def mulPow2F : ℕ → PolyTimeFun ℕ ℕ
  | 0 => PolyTimeFun.id ℕ
  | k + 1 => doubleF.comp (mulPow2F k)

@[simp] theorem mulPow2F_apply (k n : ℕ) : mulPow2F k n = 2 ^ k * n := by
  induction k with
  | zero => simp [mulPow2F]
  | succ k ih => simp [mulPow2F, ih, pow_succ]; ring

/-! ## Budgets at `C λ` -/

/-- `2^{(C λ n + 1)^{C'}} ≤ 2^{(λ n + 1)^{C C'}}`. -/
theorem ansBound_scale (C C' lam n : ℕ) : ansBound C' (C * lam) n ≤ ansBound (C * C') lam n :=
  Nat.pow_le_pow_right (by norm_num) (Budget.budget_pow_le C lam n C')

theorem LenBound.mono {L : Decider} {n B B' : ℕ} (h : LenBound L n B) (hB : B ≤ B') :
    LenBound L n B' :=
  fun x κ k hk => (h x κ k hk).trans hB

/-- **The answer-length calculator at `C λ` is within the budget at `λ`**, with the exponent
multiplied by `C`. -/
theorem lenIntro_within : ∃ C' : ℕ, ∀ C : ℕ, 1 ≤ C → ∀ lam n : ℕ,
    (LenIntro.lenIntro (C * lam)).TimeBoundAt n (ansBound (C * C') lam n) (C * C') ∧
      LenBound (LenIntro.lenIntro (C * lam)) n (ansBound (C * C') lam n) := by
  obtain ⟨C', hC'⟩ := LenIntro.lenIntro_budget
  refine ⟨C', fun C hC lam n => ?_⟩
  obtain ⟨hT, hB⟩ := hC' (C * lam) n
  exact ⟨hT.mono (ansBound_scale C C' lam n) (Nat.le_mul_of_pos_left _ hC),
    LenBound.mono hB (ansBound_scale C C' lam n)⟩

/-! ## Index zero -/

/-- **An output that is empty at index `n` has a perfect ZPC strategy there**: when the
calculator outputs `0` and the processor no constraint, every pair of empty answers is
accepted, and the trivial strategy is perfect. -/
theorem hasPerfectZPC_of_zero {ℓ : ℕ} (W : TailoredVerifier ℓ) (n : ℕ)
    (hlen : ∀ x κ, LenIs W.len n x κ 0) (hlp : ∀ x y aR bR, LpIs W.lp n x y aR bR []) :
    W.HasPerfectZPC n := by
  have hdef : ∀ x, W.LenDefined n x := fun x κ => ⟨0, hlen x κ⟩
  have hl0 : ∀ x κ, W.lenOf n x κ = 0 := fun x κ => Output.lenOf_eq_of (hlen x κ)
  apply hasPerfectZPC_of_accepts_zero
  intro p q _
  refine ⟨?_, ?_, ?_⟩
  · simp
  · simp
  · intro c hc
    change c ∈ W.consOf n _ _ _ _ at hc
    rw [W.consOf_eq_of (hdef _) (hdef _) (hlp _ _ _ _)] at hc
    simp at hc

end MIPRE.Tailored.Intro.Scale

end
