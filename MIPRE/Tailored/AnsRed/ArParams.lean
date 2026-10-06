/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.AnsRed.Pcp
public import MIPRE.TM.CookLevin.Decoupled6Prog

@[expose] public section

/-!
# The parameters of the answer reduction

Slice P4i of `planning/aldous-lyons-track.md`: the parameters at which the output verifier of the
answer reduction runs at an index `n`, from `(λ, μ, σ)` (II:10846–11074, in the form the
formalization needs). With `Q = (λn + 1)^μ` the input's budget:

* the PCP's window width `ℓ = Q`: the input's answers have length at most `2^Q`;
* its copy width `◇ = (μ + 2)(Q + 4)`: the input's processor runs within `2^Q (|d| + 1)^μ`, so it
  outputs fewer than `2^{◇ - Q - 2}` constraints on the answers the PCP reads;
* the output indicator's description time `T = 2^K`, `K = E₁ (μ + 1)(oW + Q + 4)`, with
  `oW = 2ℓ + 3◇ + 6` the width of the table `O`: `L*` accepts the honest strings within `T`;
* the size bound `σ' = c₀ + 5σ + 4(ℓ + ◇) + 8` of the description of `L*`;
* the witness index width `r = r₀(T, σ')` and the gate count `s = s₀(n, T, Q, σ')` of the
  window describer (`MIPRE.SAT.windowDescriber`);
* the selector width `j = size m`, `m = nIn + s` the number of the PCP's variables, so `m < 2^j`;
* the degree `d = 17`;
* the field width `t = E₂ (j + r + Q + 1)`, large enough for the soundness error.

The constants `E₁`, `E₂` and `c₀` are arguments (`ArConsts`); the bounds that fix them come
later (the running time of `L*`, the error of the soundness, the size of `L*`'s program).
-/

noncomputable section

namespace MIPRE.Tailored.AnsRed.Params

open MIPRE.SAT

/-- The constants of the parameters: `E₁` scales the description time's exponent, `E₂` the field
width, `c₀` is the fixed part of the size of the output indicator's program. -/
structure ArConsts where
  E₁ : ℕ
  E₂ : ℕ
  c₀ : ℕ

variable (κ : ArConsts) (lam mu sigma n : ℕ)

/-- The input's budget `Q = (λn + 1)^μ`. -/
abbrev pQ : ℕ := (lam * n + 1) ^ mu

/-- The window width `ℓ = Q`. -/
abbrev pEll : ℕ := pQ lam mu n

/-- The copy width `◇ = (μ + 2)(Q + 4)`. -/
abbrev pDm : ℕ := (mu + 2) * (pQ lam mu n + 4)

/-- The width `oW = 2ℓ + 3◇ + 6` of an index of the table `O`. -/
abbrev pOW : ℕ := pEll lam mu n + pEll lam mu n + 3 * pDm lam mu n + 6

/-- The exponent `K = E₁ (μ + 1)(oW + Q + 4)` of the description time. -/
abbrev pK : ℕ := κ.E₁ * (mu + 1) * (pOW lam mu n + pQ lam mu n + 4)

/-- The description time `T = 2^K` of the output indicator. -/
abbrev pT : ℕ := 2 ^ pK κ lam mu n

/-- The size bound `σ' = c₀ + 5σ + 4(ℓ + ◇) + 8` of the output indicator's program. -/
abbrev pSig : ℕ := κ.c₀ + 5 * sigma + 4 * (pEll lam mu n + pDm lam mu n) + 8

/-- The witness index width `r = r₀(T, σ')`. -/
abbrev pR : ℕ := windowDescriber.r₀ (pT κ lam mu n) (pSig κ lam mu sigma n)

/-- The gate count `s = s₀(n, T, Q, σ')`. -/
abbrev pS : ℕ := windowDescriber.s₀ n (pT κ lam mu n) (pQ lam mu n) (pSig κ lam mu sigma n)

/-- **The dimensions of the PCP**. -/
def pL : PcpDims := ⟨pEll lam mu n, pDm lam mu n, pR κ lam mu sigma n, pS κ lam mu sigma n⟩

@[simp] theorem pL_ℓ : (pL κ lam mu sigma n).ℓ = pEll lam mu n := rfl
@[simp] theorem pL_dm : (pL κ lam mu sigma n).dm = pDm lam mu n := rfl
@[simp] theorem pL_r : (pL κ lam mu sigma n).r = pR κ lam mu sigma n := rfl
@[simp] theorem pL_s : (pL κ lam mu sigma n).s = pS κ lam mu sigma n := rfl

theorem pL_oW : (pL κ lam mu sigma n).oW = pOW lam mu n := rfl

/-- The selector width `j = size m`. -/
abbrev pJ : ℕ := (pL κ lam mu sigma n).m.size

/-- The degree `d = 17`. -/
abbrev pD : ℕ := 17

/-- The field width `t = E₂ (j + r + Q + 1)`. -/
abbrev pTw : ℕ := κ.E₂ * (pJ κ lam mu sigma n + pR κ lam mu sigma n + pQ lam mu n + 1)

/-- **The data of the circuit function**: `K` and `σ'`, in unary. -/
def pExtra : Cost.Data :=
  Cost.encode ((Cost.unary (pK κ lam mu n), Cost.unary (pSig κ lam mu sigma n)) :
    Cost.Unary × Cost.Unary)

/-! ## Basic facts -/

theorem one_le_pQ : 1 ≤ pQ lam mu n := Nat.one_le_pow _ _ (by omega)

/-- `m < 2^j`. -/
theorem pL_m_lt : (pL κ lam mu sigma n).m < 2 ^ pJ κ lam mu sigma n := Nat.lt_size_self _

/-- `m ≤ 2^j`. -/
theorem pL_m_le : (pL κ lam mu sigma n).m ≤ 2 ^ pJ κ lam mu sigma n :=
  (pL_m_lt κ lam mu sigma n).le

/-- `j ≤ t` once `E₂ ≥ 1`. -/
theorem pJ_le_pTw (h : 1 ≤ κ.E₂) : pJ κ lam mu sigma n ≤ pTw κ lam mu sigma n := by
  unfold pTw
  nlinarith [Nat.zero_le (pR κ lam mu sigma n), Nat.zero_le (pQ lam mu n)]

/-- `1 ≤ t` once `E₂ ≥ 1`. -/
theorem one_le_pTw (h : 1 ≤ κ.E₂) : 1 ≤ pTw κ lam mu sigma n := by
  unfold pTw
  nlinarith [Nat.zero_le (pJ κ lam mu sigma n), Nat.zero_le (pR κ lam mu sigma n),
    Nat.zero_le (pQ lam mu n)]

/-- `Q ≤ K` once `E₁ ≥ 1`. -/
theorem pQ_le_pK (h : 1 ≤ κ.E₁) : pQ lam mu n ≤ pK κ lam mu n := by
  unfold pK
  have : 1 ≤ κ.E₁ * (mu + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  calc pQ lam mu n ≤ pOW lam mu n + pQ lam mu n + 4 := by omega
    _ = 1 * (pOW lam mu n + pQ lam mu n + 4) := (one_mul _).symm
    _ ≤ _ := Nat.mul_le_mul_right _ this

/-- `oW ≤ K` once `E₁ ≥ 1`. -/
theorem pOW_le_pK (h : 1 ≤ κ.E₁) : pOW lam mu n ≤ pK κ lam mu n := by
  unfold pK
  have : 1 ≤ κ.E₁ * (mu + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  calc pOW lam mu n ≤ pOW lam mu n + pQ lam mu n + 4 := by omega
    _ = 1 * (pOW lam mu n + pQ lam mu n + 4) := (one_mul _).symm
    _ ≤ _ := Nat.mul_le_mul_right _ this

end MIPRE.Tailored.AnsRed.Params

end

end
