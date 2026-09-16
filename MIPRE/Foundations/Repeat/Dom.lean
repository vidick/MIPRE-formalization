/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import Mathlib.Tactic

/-!
# Domination by a monomial in the parameters and the input size

The time bounds of the repeated verifier (`thm:parallel-repetition`) have the shape
`c (W + 1)^m X^{e (K + 1)}`: `W` a number dominating all the parameters at index `n` (the
argument `MIPRE.Repetition.arg`), `X = |d| + 1` the size of the input and `K` the input's
degree. `Dom W X K c m e v` says `v` is below such a monomial. The costs of the programs are
sums and products of quantities each of which is below `W`, below `X`, or a constant, and the
combinators here — `add`, `mul`, `pow`, `ofLeW`, `ofLeX`, `const` — assemble the exponents,
so that the final `c, m, e` are produced by the chain rather than computed by hand. The
exponent of `X` is counted in units of `K + 1`, so that a bound `X^{e (K + 1)}` with `e`
independent of `K` is what comes out, as the degree clause of the theorem needs.
-/

namespace MIPRE.Repeat

/-- `v ≤ c (W + 1)^m X^{e (K + 1)}`. -/
def Dom (W X K c m e v : ℕ) : Prop := v ≤ c * (W + 1) ^ m * X ^ (e * (K + 1))

namespace Dom

variable {W X K : ℕ}

theorem le {c m e v : ℕ} (h : Dom W X K c m e v) : v ≤ c * (W + 1) ^ m * X ^ (e * (K + 1)) := h

theorem of_le {c m e v v' : ℕ} (h : Dom W X K c m e v) (hv : v' ≤ v) : Dom W X K c m e v' :=
  hv.trans h

theorem const (c : ℕ) : Dom W X K c 0 0 c := by simp [Dom]

theorem ofLeW {v : ℕ} (h : v ≤ W) : Dom W X K 1 1 0 v := by simp [Dom]; omega

theorem ofLeX (hX : 1 ≤ X) {v : ℕ} (h : v ≤ X) : Dom W X K 1 0 1 v := by
  simp only [Dom, one_mul, pow_zero, one_mul]
  exact h.trans (Nat.le_self_pow (by omega) X)

theorem mono (hX : 1 ≤ X) {c c' m m' e e' v : ℕ} (h : Dom W X K c m e v) (hc : c ≤ c') (hm : m ≤ m')
    (he : e ≤ e') : Dom W X K c' m' e' v := by
  unfold Dom at h ⊢
  refine h.trans ?_
  gcongr <;> first | omega | exact Nat.mul_le_mul_right _ he

theorem add (hX : 1 ≤ X) {c₁ c₂ m₁ m₂ e₁ e₂ v₁ v₂ : ℕ} (h₁ : Dom W X K c₁ m₁ e₁ v₁)
    (h₂ : Dom W X K c₂ m₂ e₂ v₂) : Dom W X K (c₁ + c₂) (max m₁ m₂) (max e₁ e₂) (v₁ + v₂) := by
  have h₁' := h₁.mono hX (c' := c₁) (m' := max m₁ m₂) (e' := max e₁ e₂) le_rfl (le_max_left _ _)
    (le_max_left _ _)
  have h₂' := h₂.mono hX (c' := c₂) (m' := max m₁ m₂) (e' := max e₁ e₂) le_rfl (le_max_right _ _)
    (le_max_right _ _)
  unfold Dom at h₁' h₂' ⊢
  rw [Nat.add_mul, Nat.add_mul]
  omega

theorem mul {c₁ c₂ m₁ m₂ e₁ e₂ v₁ v₂ : ℕ} (h₁ : Dom W X K c₁ m₁ e₁ v₁) (h₂ : Dom W X K c₂ m₂ e₂ v₂) :
    Dom W X K (c₁ * c₂) (m₁ + m₂) (e₁ + e₂) (v₁ * v₂) := by
  unfold Dom at h₁ h₂ ⊢
  calc v₁ * v₂ ≤ (c₁ * (W + 1) ^ m₁ * X ^ (e₁ * (K + 1))) * (c₂ * (W + 1) ^ m₂ * X ^ (e₂ * (K + 1))) :=
        Nat.mul_le_mul h₁ h₂
    _ = c₁ * c₂ * (W + 1) ^ (m₁ + m₂) * X ^ ((e₁ + e₂) * (K + 1)) := by
        rw [pow_add, Nat.add_mul, pow_add]; ring

theorem pow {c m e v : ℕ} (h : Dom W X K c m e v) (p : ℕ) :
    Dom W X K (c ^ p) (m * p) (e * p) (v ^ p) := by
  induction p with
  | zero => simpa using const 1
  | succ p ih =>
    have := ih.mul h
    simpa [pow_succ, Nat.mul_succ] using this

/-- `X^K` itself: one unit of the exponent. -/
theorem powK (hX : 1 ≤ X) : Dom W X K 1 0 1 (X ^ K) := by
  simp only [Dom, one_mul, pow_zero]
  exact Nat.pow_le_pow_right hX (by omega)

/-- `X^{K+1}`. -/
theorem powK1 : Dom W X K 1 0 1 (X ^ (K + 1)) := by
  simp [Dom]

end Dom

end MIPRE.Repeat
