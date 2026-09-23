/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Repeat.Dom
import MIPRE.Foundations.Cost.Growth

/-!
# Domination by a power of a monomial

The time bounds of the answer-reduced verifier (`thm:answer-reduction`) have the shape
`(c (W + 1)^m X^e)^{K + 1}`: `W` a number dominating the parameters at index `n`, `X = |d| + 1`
the size of the input and `K = μ` the input sampler's degree. It is the shape of the contract's
`outBound bound λ μ σ n = P(L + σ)^{μ + 1}` at degree `d (μ + 1)`: one call to a sampler of
coefficient `B ≤ W` and degree `K` on a query of size below `c (W + 1)^m X^e` costs
`B (c (W + 1)^m X^e)^K`, which is of this shape (`ofCall`), and so is any fixed polynomial of
such a cost (`poly`). `MIPRE.Repeat.Dom` is the unpowered shape `c (W + 1)^m X^{e (K + 1)}`,
which suffices when the coefficient of the simulated program does not depend on `K`; here the
powered coefficient carries the constants that a query larger than the input by a constant
factor raises to the power `K`, and the index-independent `K + 1 ≤ 2^{K + 1}` (`ofLeK`).

`PDom W X K c m e v` says `v` is below `(c (W + 1)^m X^e)^{K + 1}`; the combinators assemble the
constants, and `le_final` reads off the coefficient `(c (W + 1)^m)^{K + 1}` and degree
`e (K + 1)`.
-/

namespace MIPRE.Pipeline

open Cost

/-- `v ≤ (c (W + 1)^m X^e)^{K + 1}`. -/
def PDom (W X K c m e v : ℕ) : Prop := v ≤ (c * (W + 1) ^ m * X ^ e) ^ (K + 1)

namespace PDom

variable {W X K : ℕ}

theorem le {c m e v : ℕ} (h : PDom W X K c m e v) : v ≤ (c * (W + 1) ^ m * X ^ e) ^ (K + 1) := h

theorem of_le {c m e v v' : ℕ} (h : PDom W X K c m e v) (hv : v' ≤ v) : PDom W X K c m e v' :=
  hv.trans h

/-- The coefficient and the degree. -/
theorem le_final {c m e v : ℕ} (h : PDom W X K c m e v) :
    v ≤ (c * (W + 1) ^ m) ^ (K + 1) * X ^ (e * (K + 1)) := by
  refine h.trans (le_of_eq ?_)
  rw [mul_pow, pow_mul]

theorem mono (hX : 1 ≤ X) {c c' m m' e e' v : ℕ} (h : PDom W X K c m e v) (hc : c ≤ c')
    (hm : m ≤ m') (he : e ≤ e') : PDom W X K c' m' e' v := by
  refine h.trans (Nat.pow_le_pow_left ?_ _)
  exact Nat.mul_le_mul (Nat.mul_le_mul hc (Nat.pow_le_pow_right (by omega) hm))
    (Nat.pow_le_pow_right hX he)

/-- A base of at least one is below its `(K + 1)`-st power. -/
theorem le_pow_succ {a : ℕ} : a ≤ a ^ (K + 1) :=
  Nat.le_self_pow (by omega) a

theorem const (c : ℕ) : PDom W X K (c + 1) 0 0 c := by
  simp only [PDom, pow_zero, Nat.mul_one]
  exact (Nat.le_succ c).trans (le_pow_succ)

theorem ofLeW {v : ℕ} (h : v ≤ W) : PDom W X K 1 1 0 v := by
  simp only [PDom, pow_one, pow_zero, Nat.mul_one, Nat.one_mul]
  exact (h.trans (Nat.le_succ W)).trans (le_pow_succ)

/-- An affine function of `W`. -/
theorem ofAffine {a b v : ℕ} (h : v ≤ a * W + b) : PDom W X K (a + b + 1) 1 0 v := by
  simp only [PDom, pow_one, pow_zero, Nat.mul_one]
  refine h.trans ((?_ : a * W + b ≤ (a + b + 1) * (W + 1)).trans le_pow_succ)
  nlinarith

theorem ofLeX {v : ℕ} (h : v ≤ X) : PDom W X K 1 0 1 v := by
  simp only [PDom, pow_zero, pow_one, Nat.mul_one, Nat.one_mul]
  exact h.trans (le_pow_succ)

/-- An affine function of `X`. -/
theorem ofAffineX (hX : 1 ≤ X) {a b v : ℕ} (h : v ≤ a * X + b) : PDom W X K (a + b) 0 1 v := by
  simp only [PDom, pow_zero, pow_one, Nat.mul_one]
  by_cases hab : a + b = 0
  · have : a = 0 := by omega
    have : b = 0 := by omega
    subst_vars
    simpa using h
  refine h.trans ((?_ : a * X + b ≤ (a + b) * X).trans le_pow_succ)
  nlinarith

/-- `K + 1 ≤ 2^{K + 1}`: the input sampler's degree itself is dominated. -/
theorem ofLeK {v : ℕ} (h : v ≤ K + 1) : PDom W X K 2 0 0 v := by
  simp only [PDom, pow_zero, Nat.mul_one]
  exact h.trans (Nat.lt_two_pow_self).le

theorem add (hX : 1 ≤ X) {c₁ c₂ m₁ m₂ e₁ e₂ v₁ v₂ : ℕ} (h₁ : PDom W X K c₁ m₁ e₁ v₁)
    (h₂ : PDom W X K c₂ m₂ e₂ v₂) :
    PDom W X K (c₁ + c₂) (max m₁ m₂) (max e₁ e₂) (v₁ + v₂) := by
  have h₁' := h₁.mono hX (c' := c₁) (m' := max m₁ m₂) (e' := max e₁ e₂) le_rfl (le_max_left _ _)
    (le_max_left _ _)
  have h₂' := h₂.mono hX (c' := c₂) (m' := max m₁ m₂) (e' := max e₁ e₂) le_rfl (le_max_right _ _)
    (le_max_right _ _)
  unfold PDom at h₁' h₂' ⊢
  refine (Nat.add_le_add h₁' h₂').trans ?_
  rw [Nat.add_mul, Nat.add_mul]
  exact pow_add_pow_le (Nat.zero_le _) (Nat.zero_le _) (by omega)

theorem mul {c₁ c₂ m₁ m₂ e₁ e₂ v₁ v₂ : ℕ} (h₁ : PDom W X K c₁ m₁ e₁ v₁)
    (h₂ : PDom W X K c₂ m₂ e₂ v₂) : PDom W X K (c₁ * c₂) (m₁ + m₂) (e₁ + e₂) (v₁ * v₂) := by
  unfold PDom at h₁ h₂ ⊢
  refine (Nat.mul_le_mul h₁ h₂).trans (le_of_eq ?_)
  rw [← mul_pow, pow_add, pow_add]
  ring_nf

theorem pow {c m e v : ℕ} (h : PDom W X K c m e v) (p : ℕ) :
    PDom W X K (c ^ p) (m * p) (e * p) (v ^ p) := by
  unfold PDom at h ⊢
  refine (Nat.pow_le_pow_left h p).trans (le_of_eq ?_)
  rw [← pow_mul, Nat.mul_comm (K + 1) p, pow_mul]
  simp only [mul_pow, ← pow_mul]

/-- The unpowered domination of `MIPRE.Repeat.Dom` is powered domination. -/
theorem ofDom {c m e v : ℕ} (h : Repeat.Dom W X K c m e v) : PDom W X K c m e v := by
  unfold Repeat.Dom at h
  unfold PDom
  refine h.trans ?_
  rw [mul_pow, pow_mul]
  by_cases h0 : c * (W + 1) ^ m = 0
  · rw [h0]; simp
  · exact Nat.mul_le_mul_right _ (le_pow_succ)

/-- **A fixed polynomial of a dominated quantity.** -/
theorem poly (hX : 1 ≤ X) (P : Polynomial ℕ) {c m e y : ℕ} (h : PDom W X K c m e y) :
    PDom W X K ((∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i + 1) * (c + 2) ^ P.natDegree)
      (m * P.natDegree) (e * P.natDegree) (P.eval y) := by
  have h1 : PDom W X K (c + 2) m e (y + 1) :=
    (h.add hX (const 1)).mono hX (by omega) (by omega) (by omega)
  have hP : P.eval y ≤ (∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i + 1) *
      (y + 1) ^ P.natDegree :=
    (polynomial_eval_mono P (Nat.le_succ y)).trans ((polynomial_eval_le_sum_coeff_mul_pow P
      (by omega)).trans (Nat.mul_le_mul_right _ (Nat.le_succ _)))
  refine PDom.of_le ?_ hP
  have hS : PDom W X K (∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i + 1) 0 0
      (∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i + 1) := by
    unfold PDom; simp only [pow_zero, Nat.mul_one]; exact le_pow_succ
  simpa using hS.mul (h1.pow P.natDegree)

/-- **One call to a sampler** of coefficient `B ≤ W` and degree `K`, on a query of size below the
unpowered monomial `c (W + 1)^m X^e`. -/
theorem ofCall {B q t c m e : ℕ} (hB : B ≤ W) (hq : q + 1 ≤ c * (W + 1) ^ m * X ^ e)
    (ht : t ≤ B * (q + 1) ^ K) : PDom W X K c (m + 1) e t := by
  unfold PDom
  refine ht.trans ?_
  have hA : 1 ≤ c * (W + 1) ^ m * X ^ e := by omega
  calc B * (q + 1) ^ K ≤ (W + 1) * (c * (W + 1) ^ m * X ^ e) ^ K :=
        Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hq K)
    _ ≤ (W + 1) ^ (K + 1) * (c * (W + 1) ^ m * X ^ e) ^ (K + 1) :=
        Nat.mul_le_mul (le_pow_succ) (Nat.pow_le_pow_right hA (by omega))
    _ = (c * (W + 1) ^ (m + 1) * X ^ e) ^ (K + 1) := by
        rw [← mul_pow]; congr 1; ring

/-- **One call to a program** of coefficient `B ≤ c₀ (W + 1)^{m₀}` and degree `e' (K + 1)`, on a
query of size below the unpowered monomial `c₁ (W + 1)^{m₁} X^{e₁}`. -/
theorem ofCallPow {B q t c₀ m₀ c₁ m₁ e₁ e' : ℕ} (hB : B ≤ c₀ * (W + 1) ^ m₀)
    (hq : q + 1 ≤ c₁ * (W + 1) ^ m₁ * X ^ e₁) (ht : t ≤ B * (q + 1) ^ (e' * (K + 1))) :
    PDom W X K (c₀ * c₁ ^ e') (m₀ + m₁ * e') (e₁ * e') t := by
  unfold PDom
  refine ht.trans ?_
  calc B * (q + 1) ^ (e' * (K + 1))
      ≤ c₀ * (W + 1) ^ m₀ * ((c₁ * (W + 1) ^ m₁ * X ^ e₁) ^ e') ^ (K + 1) := by
        rw [← pow_mul]
        exact Nat.mul_le_mul hB (Nat.pow_le_pow_left hq _)
    _ ≤ (c₀ * (W + 1) ^ m₀) ^ (K + 1) * ((c₁ * (W + 1) ^ m₁ * X ^ e₁) ^ e') ^ (K + 1) :=
        Nat.mul_le_mul_right _ le_pow_succ
    _ = (c₀ * c₁ ^ e' * (W + 1) ^ (m₀ + m₁ * e') * X ^ (e₁ * e')) ^ (K + 1) := by
        rw [← mul_pow]
        congr 1
        rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, pow_add]
        ring

/-- **A run of a program whose coefficient is already powered**, `B ≤ (c₀ (W + 1)^{m₀})^{K + 1}`,
at degree `e' (K + 1)`, on an input of size below the unpowered monomial `c₁ (W + 1)^{m₁} X^{e₁}`. -/
theorem ofPoweredCall {B q t c₀ m₀ c₁ m₁ e₁ e' : ℕ} (hB : B ≤ (c₀ * (W + 1) ^ m₀) ^ (K + 1))
    (hq : q ≤ c₁ * (W + 1) ^ m₁ * X ^ e₁) (ht : t ≤ B * q ^ (e' * (K + 1))) :
    PDom W X K (c₀ * c₁ ^ e') (m₀ + m₁ * e') (e₁ * e') t := by
  unfold PDom
  refine ht.trans ?_
  calc B * q ^ (e' * (K + 1))
      ≤ (c₀ * (W + 1) ^ m₀) ^ (K + 1) * ((c₁ * (W + 1) ^ m₁ * X ^ e₁) ^ e') ^ (K + 1) := by
        rw [← pow_mul]
        exact Nat.mul_le_mul hB (Nat.pow_le_pow_left hq _)
    _ = (c₀ * c₁ ^ e' * (W + 1) ^ (m₀ + m₁ * e') * X ^ (e₁ * e')) ^ (K + 1) := by
        rw [← mul_pow]
        congr 1
        rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, pow_add]
        ring

/-- Below the unpowered monomial. -/
theorem ofMono {c m e v : ℕ} (h : v ≤ c * (W + 1) ^ m * X ^ e) : PDom W X K c m e v :=
  h.trans le_pow_succ

/-- A linear function of `W` and `K + 1`. -/
theorem ofLin (hX : 1 ≤ X) {a b c v : ℕ} (h : v ≤ a * W + b * (K + 1) + c) :
    PDom W X K (a + 2 * b + c + 3) 1 0 v := by
  have h1 : PDom W X K (a + c + 1) 1 0 (a * W + c) := ofAffine le_rfl
  have h2 : PDom W X K ((b + 1) * 2) 0 0 (b * (K + 1)) := (const b).mul (ofLeK le_rfl)
  refine ((h1.add hX h2).mono hX (by nlinarith) (by simp) (by simp)).of_le ?_
  omega

end PDom

end MIPRE.Pipeline
