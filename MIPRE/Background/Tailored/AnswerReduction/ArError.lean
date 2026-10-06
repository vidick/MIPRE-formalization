/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.AnswerReduction.Sound
public import MIPRE.Background.AnswerReduction.SoundFinal
public import MIPRE.Tailored.AnsRed.ArParams

@[expose] public section

/-!
# Soundness of the answer reduction: the error chain

Slice P4i of `planning/aldous-lyons-track.md`: the soundness error `24 √(errAR (16⁹ ε))` of the
answer-reduced verifier (`valStar_sound_output`), at the parameters of `ArParams`, is below the
contract's loss `δ(ε, n) = σ^a ((λn)^{μa} ε^b + (λn)^{-μb})` (`exists_errAR_le_delta`), and the
field-size hypotheses of `valStar_sound_output` hold (`field_hyps`).

The chain, with `j` the selector width, `t` the field width and `m` the PCP's variable count:

1. every role's number of codewords is at most `11 m + 11` (`length_slotsOf_le`), and `m < 2^j`;
2. `errAR(θ) ≤ 2^j (250 D + 25920 θ + 4 d / q)` for `D` above the three roles' `δ_sim`
   (`errAR_le_of_dS`), and each `δ_sim` is at most `P (9 · 16⁹ ε^{clB} + q^{-clB} + 2^{-clB Q})`
   with `P = 2^{3A (j + 5)}`, `A = ⌈simA⌉` (`dS_le_of`), since `Q ≤ m < 2^j`;
3. when `t ≥ e2Min (j + Q + 1)`, `e2Min = 400000 (3A + 2)`, the field terms `2^j P q^{-clB}` and
   `2^j / q` are at most `2^{-(2Q + 9)}` (`field_term_le`), so (`errAR_le_shape`)

     `errAR(16⁹ ε) ≤ 7 (39204 · 16⁹ G ε^{clB} + (Q + 1)^{-2} + 22 G 2^{-clB Q})`,  `G = 2 · 2^j P`,

   which is the shape `MIPRE.AnswerReduction.sqrt_le_delta` compares with the loss;
4. at the parameters, `m ≤ cM (Q σ)^{pM}` (`pL_m_le`), from the window describer's bounds on
   `r₀` and `s₀`, so `G ≤ (96 m)^{3A + 1} ≤ errCc (Q σ)^{errPp}` (`gN_le_poly`), and the
   threshold of `exists_threshold_clB` gives `C`.

The field-width constant `e2Min` depends only on `simA`, while `a` and `C` depend on `E₁` and
`c₀` through `cM`. The case `ε ≥ 1` or `μ = 0` is the trivial one: the loss is then at least `1`
(`one_le_delta_of_trivial'`); `errAR_le_delta_or` packages both.
-/

noncomputable section

namespace MIPRE.Tailored.AnsRed.Typed

open Finset MIPRE.CL MIPRE.SAT MIPRE.LIDT MIPRE.Tailored.AnsRed.Params
open MIPRE.AnswerReduction (simAN simA_mul_rpow_le deltaSim_le_of coeffSum aOf one_le_aOf
  exists_threshold_clB sqrt_le_delta)

/-! ## The number of codewords -/

/-- **Every role has at most `11 m + 11` codewords.** -/
theorem length_slotsOf_le (L : PcpDims) (r : Role) : (slotsOf L r).length ≤ 11 * L.m + 11 := by
  cases r <;>
    simp only [slotsOf, rOf, lOf, List.length_append, length_rSlots, length_lSlots,
      List.length_singleton] <;>
    unfold PcpDims.m PcpDims.nIn PcpDims.oW <;> omega

/-! ## The error, in terms of the extractions' errors -/

/-- **The error is `2^j` times the extractions' errors**, up to constants. -/
theorem errAR_le_of_dS {t : ℕ} {ht : 1 ≤ t} {j d : ℕ} {L : PcpDims} {θ D : ℝ} (hθ : 0 ≤ θ)
    (hD : ∀ r, dS t ht j d L r (9 * θ) ≤ D) :
    errAR t ht j d L θ ≤
      (2 : ℝ) ^ j * (250 * D + 25920 * θ + 4 * ((d : ℝ) / Fintype.card (Fq t ht))) := by
  have hO := hD .oracle
  have hA := hD .alice
  have hB := hD .bob
  have h90 : 0 ≤ 9 * θ := by linarith
  have hO0 := dS_nonneg ht j d L .oracle h90
  have hA0 := dS_nonneg ht j d L .alice h90
  have hB0 := dS_nonneg ht j d L .bob h90
  have hJ : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have e : ((2 ^ j : ℕ) : ℝ) * d / Fintype.card (Fq t ht)
      = (2 : ℝ) ^ j * ((d : ℝ) / Fintype.card (Fq t ht)) := by
    push_cast; ring
  unfold errAR errP
  rw [e]
  set J : ℝ := (2 : ℝ) ^ j
  set dO := dS t ht j d L .oracle (9 * θ)
  set dA := dS t ht j d L .alice (9 * θ)
  set dB := dS t ht j d L .bob (9 * θ)
  have p1 := mul_nonneg (by linarith : (0 : ℝ) ≤ J) (by linarith : 0 ≤ D - dO)
  have p2 := mul_nonneg (by linarith : (0 : ℝ) ≤ J) (by linarith : 0 ≤ D - dA)
  have p3 := mul_nonneg (by linarith : (0 : ℝ) ≤ J) (by linarith : 0 ≤ D - dB)
  have p4 := mul_nonneg (by linarith : (0 : ℝ) ≤ J - 1) hO0
  have p5 := mul_nonneg (by linarith : (0 : ℝ) ≤ J - 1) hA0
  have p6 := mul_nonneg (by linarith : (0 : ℝ) ≤ J - 1) hB0
  have p7 := mul_nonneg (by linarith : (0 : ℝ) ≤ J - 1) hθ
  nlinarith

/-! ## One extraction's error -/

/-- The prefactor bound `P = 2^{3A (j + 5)}`, as a real number. -/
abbrev pwR (j : ℕ) : ℝ := ((2 ^ (j + 5) : ℕ) : ℝ) ^ (3 * simAN)

theorem one_le_pwR (j : ℕ) : 1 ≤ pwR j :=
  one_le_pow₀ (by exact_mod_cast Nat.one_le_two_pow)

/-- **One extraction's error**, at the typed failure `16⁹ ε` and degree `17`, when the PCP's
variables fit the selector (`m < 2^j`) and `Q ≤ 2^j`. -/
theorem dS_le_of {t : ℕ} {ht : 1 ≤ t} {j : ℕ} {L : PcpDims} (r : Role) {Q : ℕ}
    (hQ : Q ≤ 2 ^ j) (hm : L.m < 2 ^ j) {ε : ℝ} (hε : 0 ≤ ε) :
    dS t ht j 17 L r (9 * (16 ^ 9 * ε)) ≤
      pwR j * (9 * 16 ^ 9 * ε ^ clB) + pwR j * (Fintype.card (Fq t ht) : ℝ) ^ (-clB)
        + pwR j * (2 : ℝ) ^ (-(clB * Q)) := by
  have hlen := length_slotsOf_le L r
  set len := (slotsOf L r).length
  have hlen1 := one_le_length_slotsOf L r
  have hP : Simul.simA * ((17 * 2 ^ j * len : ℕ) : ℝ) ^ Simul.simA ≤ pwR j := by
    refine simA_mul_rpow_le (Nat.mul_pos (Nat.mul_pos (by norm_num) (Nat.two_pow_pos _)) hlen1)
      ?_ ?_
    · have := Nat.one_le_two_pow (n := j)
      rw [pow_add]; omega
    · rw [pow_add, mul_pow]
      have h1 : len ≤ 11 * 2 ^ j := by omega
      have h2 : 17 * 2 ^ j * len ≤ 17 * 2 ^ j * (11 * 2 ^ j) := Nat.mul_le_mul_left _ h1
      nlinarith
  have hx : (9 * (16 ^ 9 * ε)) ^ clB ≤ 9 * 16 ^ 9 * ε ^ clB := by
    rw [← mul_assoc, Real.mul_rpow (by norm_num) hε]
    have h2 : ((9 : ℝ) * 16 ^ 9) ^ clB ≤ 9 * 16 ^ 9 := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 9 * 16 ^ 9)
        clB_lt_one.le
      rwa [Real.rpow_one] at this
    exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hε _)
  have hc : (2 : ℝ) ^ (-(clB * ((2 ^ j : ℕ) : ℝ) * ((17 : ℕ) : ℝ))) ≤ (2 : ℝ) ^ (-(clB * Q)) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hQ' : (Q : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) * 17 := by
      exact_mod_cast (by omega : Q ≤ 2 ^ j * 17)
    have := clB_pos
    push_cast at hQ' ⊢
    nlinarith
  exact deltaSim_le_of (by positivity) hP hx le_rfl hc

/-! ## The field terms -/

/-- **The field-width constant**: `t ≥ e2Min (j + Q + 1)` makes the field terms negligible. It
depends only on `simA`. -/
irreducible_def e2Min : ℕ := 400000 * (3 * simAN + 2)

theorem seven_le_e2Min : 7 ≤ e2Min := by rw [e2Min_def]; omega

/-- **The field terms**: when `t ≥ e2Min (j + Q + 1)`, `2^j P q^{-clB} ≤ 2^{-(2Q + 9)}` and
`2^j / q ≤ 2^{-(2Q + 9)}`, at `q = 2^t`. -/
theorem field_term_le {t j Q : ℕ} (hT : e2Min * (j + Q + 1) ≤ t) :
    (2 : ℝ) ^ j * pwR j * ((2 ^ t : ℕ) : ℝ) ^ (-clB) ≤ 1 / (2 : ℝ) ^ (2 * Q + 9) ∧
      (2 : ℝ) ^ j * (1 / ((2 ^ t : ℕ) : ℝ)) ≤ 1 / (2 : ℝ) ^ (2 * Q + 9) := by
  set A := simAN
  have hpw : (2 : ℝ) ^ j * pwR j = (2 : ℝ) ^ (j + (j + 5) * (3 * A)) := by
    rw [pwR, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, ← pow_add]
  -- `q^{clB} = 2^{t clB}`
  have hqc : ((2 ^ t : ℕ) : ℝ) ^ clB = (2 : ℝ) ^ ((t : ℝ) * clB) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have hexp : ((2 * Q + 9 + (j + (j + 5) * (3 * A)) : ℕ) : ℝ) ≤ (t : ℝ) * clB := by
    have h1 : ((e2Min * (j + Q + 1) : ℕ) : ℝ) ≤ t := Nat.cast_le.mpr hT
    have h2 : ((e2Min * (j + Q + 1) : ℕ) : ℝ) = 400000 * (3 * A + 2) * (j + Q + 1) := by
      rw [e2Min_def]; push_cast; ring
    rw [h2] at h1
    rw [clB_eq]
    push_cast
    have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg _
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
    nlinarith [mul_nonneg hA0 hj0, mul_nonneg hA0 hQ0]
  have hkey : (2 : ℝ) ^ (2 * Q + 9) * (2 : ℝ) ^ (j + (j + 5) * (3 * A)) ≤
      ((2 ^ t : ℕ) : ℝ) ^ clB := by
    rw [hqc, ← pow_add, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hq1 : (1 : ℝ) ≤ ((2 ^ t : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_two_pow
  have hqpos : (0 : ℝ) < ((2 ^ t : ℕ) : ℝ) ^ clB := by positivity
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (2 * Q + 9) := by positivity
  have hfirst : (2 : ℝ) ^ j * pwR j * ((2 ^ t : ℕ) : ℝ) ^ (-clB) ≤ 1 / (2 : ℝ) ^ (2 * Q + 9) := by
    rw [Real.rpow_neg (by positivity), hpw, ← div_eq_mul_inv,
      div_le_div_iff₀ hqpos h2pos, one_mul, mul_comm]
    exact hkey
  refine ⟨hfirst, le_trans ?_ hfirst⟩
  -- `1 / q ≤ P q^{-clB}`
  have hqq : ((2 ^ t : ℕ) : ℝ) ^ clB ≤ ((2 ^ t : ℕ) : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_le hq1 clB_lt_one.le
    rwa [Real.rpow_one] at this
  have h1 : 1 / ((2 ^ t : ℕ) : ℝ) ≤ ((2 ^ t : ℕ) : ℝ) ^ (-clB) := by
    rw [Real.rpow_neg (by positivity), one_div]
    exact inv_anti₀ hqpos hqq
  have hJ : (0 : ℝ) ≤ 2 ^ j := by positivity
  have hP1 := one_le_pwR j
  have hqn : 0 ≤ ((2 ^ t : ℕ) : ℝ) ^ (-clB) := by positivity
  calc (2 : ℝ) ^ j * (1 / ((2 ^ t : ℕ) : ℝ)) ≤ (2 : ℝ) ^ j * ((2 ^ t : ℕ) : ℝ) ^ (-clB) :=
        mul_le_mul_of_nonneg_left h1 hJ
    _ ≤ (2 : ℝ) ^ j * pwR j * ((2 ^ t : ℕ) : ℝ) ^ (-clB) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hqn hP1) hJ

/-! ## The shape of the error -/

/-- `G = 2 · 2^j · 2^{3A (j + 5)}`, the factor of the error's shape. -/
def gN (j : ℕ) : ℕ := 2 * 2 ^ j * (2 ^ (j + 5)) ^ (3 * simAN)

/-- `318 · 2^{-(2Q + 9)} ≤ 7 / (Q + 1)²`. -/
theorem shape_Q (Q : ℕ) : 318 * (1 / (2 : ℝ) ^ (2 * Q + 9)) ≤ 7 * (1 / ((Q : ℝ) + 1) ^ 2) := by
  have hQl : (Q : ℝ) + 1 ≤ 2 ^ Q := by
    have : Q + 1 ≤ 2 ^ Q := Nat.lt_two_pow_self
    exact_mod_cast this
  have hsq : ((Q : ℝ) + 1) ^ 2 ≤ (2 : ℝ) ^ (2 * Q) := by
    rw [mul_comm, pow_mul]
    exact pow_le_pow_left₀ (by positivity) hQl 2
  rw [pow_add, mul_one_div, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have h0 : (0 : ℝ) < (2 : ℝ) ^ (2 * Q) := by positivity
  nlinarith

/-- The arithmetic of the error's shape. -/
theorem shape_arith {X J P w E F ε qc q R : ℝ}
    (hX : X ≤ J * (250 * (P * (9 * 16 ^ 9 * w) + P * qc + P * E) + 25920 * (16 ^ 9 * ε)
      + 4 * (17 / q)))
    (hJ1 : 1 ≤ J) (hP1 : 1 ≤ P) (hw0 : 0 ≤ w) (hεw : ε ≤ w) (hE0 : 0 ≤ E)
    (hqc : J * P * qc ≤ F) (hqi : J * (1 / q) ≤ F) (hF : 318 * F ≤ 7 * R) :
    X ≤ 7 * (39204 * 16 ^ 9 * (2 * J * P) * w + R + 22 * (2 * J * P) * E) := by
  have hPw : ε ≤ P * w := by nlinarith
  have hJε : J * ε ≤ J * (P * w) := mul_le_mul_of_nonneg_left hPw (by linarith)
  have hJPE : 0 ≤ J * P * E := by have : 0 ≤ J * P := by nlinarith
                                  positivity
  have hJPw : 0 ≤ J * P * w := by have : 0 ≤ J * P := by nlinarith
                                  positivity
  have e1 : J * (4 * (17 / q)) = 68 * (J * (1 / q)) := by ring
  have e2 : J * (250 * (P * (9 * 16 ^ 9 * w) + P * qc + P * E) + 25920 * (16 ^ 9 * ε)
      + 4 * (17 / q)) = 2250 * 16 ^ 9 * (J * P * w) + 250 * (J * P * qc) + 250 * (J * P * E)
        + 25920 * 16 ^ 9 * (J * ε) + J * (4 * (17 / q)) := by ring
  rw [e2, e1] at hX
  have e3 : J * (P * w) = J * P * w := by ring
  rw [e3] at hJε
  linarith

/-- **The shape of the error**: at degree `17`, when the PCP's variables fit the selector, `Q ≤ m`,
and the field is wide (`t ≥ e2Min (j + Q + 1)`), `errAR(16⁹ ε)` has the shape
`MIPRE.AnswerReduction.sqrt_le_delta` compares with the loss, with `K = 16⁹` and `G = gN j`. -/
theorem errAR_le_shape {t : ℕ} {ht : 1 ≤ t} {j : ℕ} {L : PcpDims} {Q : ℕ} (hm : L.m < 2 ^ j)
    (hQ : Q ≤ L.m) (hT : e2Min * (j + Q + 1) ≤ t) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    errAR t ht j 17 L (16 ^ 9 * ε) ≤
      7 * (39204 * ((16 ^ 9 : ℕ) : ℝ) * (gN j : ℝ) * ε ^ clB + 1 / ((Q : ℝ) + 1) ^ 2
        + 22 * (gN j : ℝ) * (2 : ℝ) ^ (-(clB * Q))) := by
  have hq : (Fintype.card (Fq t ht) : ℝ) = ((2 ^ t : ℕ) : ℝ) := by rw [card_fq]
  have hθ : 0 ≤ 16 ^ 9 * ε := by positivity
  have hD := fun r => dS_le_of (t := t) (ht := ht) r (by omega : Q ≤ 2 ^ j) hm hε
  rw [hq] at hD
  have h1 := errAR_le_of_dS (t := t) (ht := ht) (j := j) (d := 17) (L := L) hθ hD
  rw [hq, Nat.cast_ofNat] at h1
  obtain ⟨hf1, hf2⟩ := field_term_le (t := t) (j := j) (Q := Q) hT
  have hG : (gN j : ℝ) = 2 * (2 : ℝ) ^ j * pwR j := by
    rw [gN, pwR]; push_cast; ring
  have hK : ((16 ^ 9 : ℕ) : ℝ) = 16 ^ 9 := by push_cast; ring
  rw [hG, hK]
  exact shape_arith h1 (one_le_pow₀ (by norm_num)) (one_le_pwR j) (Real.rpow_nonneg hε _)
    (Real.self_le_rpow_of_le_one hε hε1 clB_lt_one.le) (Real.rpow_nonneg (by norm_num) _)
    hf1 hf2 (shape_Q Q)

/-! ## The field-size hypotheses -/

/-- **The field-size hypotheses of `valStar_sound_output`** hold at the parameters once `E₂ ≥ 7`:
both sides are at most `2^{j + 8}`, and `t ≥ 7 (j + 2)`. -/
theorem field_hyps (κ : ArConsts) (hE : 7 ≤ κ.E₂) (lam mu sigma n : ℕ) :
    2 * ((2 ^ pJ κ lam mu sigma n + 1) * pD) ≤
        Fintype.card (Fq (pTw κ lam mu sigma n) (one_le_pTw κ lam mu sigma n (by omega))) ∧
      2 * ((pL κ lam mu sigma n).m * chkDeg 5 pD) ≤
        Fintype.card (Fq (pTw κ lam mu sigma n) (one_le_pTw κ lam mu sigma n (by omega))) := by
  rw [card_fq]
  have hm := pL_m_lt κ lam mu sigma n
  have hQ := one_le_pQ lam mu n
  have ht : pJ κ lam mu sigma n + 8 ≤ pTw κ lam mu sigma n := by
    have : 7 * (pJ κ lam mu sigma n + 2) ≤
        κ.E₂ * (pJ κ lam mu sigma n + pR κ lam mu sigma n + pQ lam mu n + 1) :=
      Nat.mul_le_mul hE (by omega)
    show _ ≤ κ.E₂ * (pJ κ lam mu sigma n + pR κ lam mu sigma n + pQ lam mu n + 1)
    omega
  have h8 : 2 ^ (pJ κ lam mu sigma n + 8) ≤ 2 ^ pTw κ lam mu sigma n :=
    Nat.pow_le_pow_right (by norm_num) ht
  have h1 : 1 ≤ 2 ^ pJ κ lam mu sigma n := Nat.one_le_two_pow
  rw [pow_add] at h8
  have hc : chkDeg 5 pD = 113 := rfl
  have hd : pD = 17 := rfl
  rw [hc, hd]
  constructor <;> omega

/-! ## The size of the parameters -/

/-- The constant of the window describer's bound on `r₀`. -/
def wdC : ℕ := windowDescriber.r₀_le.choose

/-- The polynomial of the window describer's bound on `s₀`. -/
def wdP : Polynomial ℕ := windowDescriber.s₀_le.choose

theorem r₀_le_wdC (T σ : ℕ) :
    windowDescriber.r₀ T σ ≤ wdC * (Nat.size T + Nat.size σ + 1) :=
  windowDescriber.r₀_le.choose_spec T σ

theorem s₀_le_wdP (n T Q σ : ℕ) :
    windowDescriber.s₀ n T Q σ ≤ wdP.eval (Nat.size n + Nat.size T + Q + σ) :=
  windowDescriber.s₀_le.choose_spec n T Q σ

/-- The constant of the bound on the window describer's arguments. -/
def cW (κ : ArConsts) : ℕ := 43 * κ.E₁ + κ.c₀ + 60

/-- **The constant of the bound on `m`.** -/
def cM (κ : ArConsts) : ℕ := 49 + 3 * wdC * cW κ + coeffSum wdP * cW κ ^ wdP.natDegree

/-- **The exponent of the bound on `m`.** -/
def pM : ℕ := 3 * wdP.natDegree + 3

/-- `n < Q` and `μ < Q`. -/
theorem pQ_facts {lam mu n : ℕ} (hlam : 1 ≤ lam) (hmu : 1 ≤ mu) (hn : 1 ≤ n) :
    n + 1 ≤ pQ lam mu n ∧ mu + 1 ≤ pQ lam mu n := by
  show n + 1 ≤ (lam * n + 1) ^ mu ∧ mu + 1 ≤ (lam * n + 1) ^ mu
  have h2 : n ≤ lam * n := Nat.le_mul_of_pos_left _ hlam
  constructor
  · have h1 : lam * n + 1 ≤ (lam * n + 1) ^ mu := Nat.le_self_pow (by omega) _
    omega
  · have h1 : mu < 2 ^ mu := Nat.lt_two_pow_self
    have h3 : 2 ^ mu ≤ (lam * n + 1) ^ mu := Nat.pow_le_pow_left (by omega) _
    omega

theorem size_le_self (x : ℕ) : Nat.size x ≤ x := Nat.size_le.mpr Nat.lt_two_pow_self

/-- The PCP's variable count, unfolded. -/
theorem pL_m_eq (κ : ArConsts) (lam mu sigma n : ℕ) :
    (pL κ lam mu sigma n).m = (pQ lam mu n + 1) + (pQ lam mu n + 1) + (pOW lam mu n + 1)
      + 3 * pR κ lam mu sigma n + 6 + pS κ lam mu sigma n := rfl

/-- **The PCP's variable count is polynomial**: `m ≤ cM (Q σ)^{pM}`. -/
theorem pL_m_le (κ : ArConsts) {lam mu sigma n : ℕ} (hlam : 1 ≤ lam) (hmu : 1 ≤ mu)
    (hs : 1 ≤ sigma) (hn : 1 ≤ n) :
    (pL κ lam mu sigma n).m ≤ cM κ * (pQ lam mu n * sigma) ^ pM := by
  obtain ⟨hnQ, hμQ⟩ := pQ_facts hlam hmu hn
  rw [pL_m_eq]
  set Q := pQ lam mu n with hQ
  set Y := Q * sigma with hY
  have hQY : Q ≤ Y := Nat.le_mul_of_pos_right _ hs
  have hY1 : 1 ≤ Y := by omega
  have hY12 : Y ≤ Y ^ 2 := Nat.le_self_pow (by norm_num) _
  have hY23 : Y ^ 2 ≤ Y ^ 3 := Nat.pow_le_pow_right hY1 (by norm_num)
  have hσY : sigma ≤ Y := Nat.le_mul_of_pos_left _ (by omega)
  have hQ2 : Q * Q ≤ Y ^ 2 := by rw [sq]; exact Nat.mul_le_mul hQY hQY
  -- the copy width and the table width
  have hdm : pDm lam mu n ≤ 10 * Y ^ 2 := by
    have : (mu + 2) * (Q + 4) ≤ (Q + 1) * (Q + 4) := Nat.mul_le_mul_right _ (by omega)
    show (mu + 2) * (Q + 4) ≤ _
    nlinarith
  have hoW : pOW lam mu n ≤ 38 * Y ^ 2 := by
    show Q + Q + 3 * pDm lam mu n + 6 ≤ _
    omega
  -- the exponent of the description time and the size bound
  have hK : pK κ lam mu n ≤ 43 * κ.E₁ * Y ^ 3 := by
    show κ.E₁ * (mu + 1) * (pOW lam mu n + Q + 4) ≤ _
    have h1 : (mu + 1) * (pOW lam mu n + Q + 4) ≤ Y * (43 * Y ^ 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    calc κ.E₁ * (mu + 1) * (pOW lam mu n + Q + 4)
        = κ.E₁ * ((mu + 1) * (pOW lam mu n + Q + 4)) := by ring
      _ ≤ κ.E₁ * (Y * (43 * Y ^ 2)) := Nat.mul_le_mul_left _ h1
      _ = 43 * κ.E₁ * Y ^ 3 := by ring
  have hsig : pSig κ lam mu sigma n ≤ (κ.c₀ + 57) * Y ^ 2 := by
    show κ.c₀ + 5 * sigma + 4 * (Q + pDm lam mu n) + 8 ≤ _
    have : κ.c₀ ≤ κ.c₀ * Y ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
    nlinarith
  have hsT : Nat.size (pT κ lam mu n) = pK κ lam mu n + 1 := Nat.size_pow
  have hc3 : (κ.c₀ + 57) * Y ^ 2 ≤ (κ.c₀ + 57) * Y ^ 3 := Nat.mul_le_mul_left _ hY23
  have hcW : cW κ * Y ^ 3 = 43 * κ.E₁ * Y ^ 3 + (κ.c₀ + 57) * Y ^ 3 + 3 * Y ^ 3 := by
    unfold cW; ring
  -- the witness index width
  have hr : pR κ lam mu sigma n ≤ wdC * (cW κ * Y ^ 3) := by
    refine (r₀_le_wdC _ _).trans (Nat.mul_le_mul_left _ ?_)
    have := size_le_self (pSig κ lam mu sigma n)
    rw [hsT, hcW]
    omega
  -- the gate count
  have hs0 : pS κ lam mu sigma n ≤
      coeffSum wdP * (cW κ ^ wdP.natDegree * Y ^ (3 * wdP.natDegree)) := by
    have hW : Nat.size n + Nat.size (pT κ lam mu n) + Q + pSig κ lam mu sigma n
        ≤ cW κ * Y ^ 3 := by
      have := size_le_self n
      rw [hsT, hcW]
      omega
    have hW1 : 1 ≤ Nat.size n + Nat.size (pT κ lam mu n) + Q + pSig κ lam mu sigma n := by
      omega
    refine (s₀_le_wdP _ _ _ _).trans
      ((MIPRE.Cost.polynomial_eval_le_sum_coeff_mul_pow wdP hW1).trans ?_)
    rw [pow_mul, ← mul_pow]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hW _)
  -- assembling
  set Z := Y ^ pM with hZ
  have hYZ : Y ≤ Z := Nat.le_self_pow (by unfold pM; omega) _
  have hY2Z : Y ^ 2 ≤ Z := Nat.pow_le_pow_right hY1 (by unfold pM; omega)
  have hY3Z : Y ^ 3 ≤ Z := Nat.pow_le_pow_right hY1 (by unfold pM; omega)
  have hYDZ : Y ^ (3 * wdP.natDegree) ≤ Z := Nat.pow_le_pow_right hY1 (by unfold pM; omega)
  have hZ1 : 1 ≤ Z := hY1.trans hYZ
  have e1 : wdC * (cW κ * Y ^ 3) ≤ wdC * cW κ * Z := by
    rw [← mul_assoc]; exact Nat.mul_le_mul_left _ hY3Z
  have e2 : coeffSum wdP * (cW κ ^ wdP.natDegree * Y ^ (3 * wdP.natDegree))
      ≤ coeffSum wdP * cW κ ^ wdP.natDegree * Z := by
    rw [← mul_assoc]; exact Nat.mul_le_mul_left _ hYDZ
  have e3 : cM κ * Z =
      49 * Z + 3 * (wdC * cW κ * Z) + coeffSum wdP * cW κ ^ wdP.natDegree * Z := by
    unfold cM; ring
  rw [e3]
  omega

/-- `2^j ≤ 2 m + 1`. -/
theorem two_pow_pJ_le (κ : ArConsts) (lam mu sigma n : ℕ) :
    2 ^ pJ κ lam mu sigma n ≤ 2 * (pL κ lam mu sigma n).m + 1 :=
  MIPRE.Cost.two_pow_size_le _

/-- **The factor of the error's shape is polynomial in `m`.** -/
theorem gN_le {j m : ℕ} (hm1 : 1 ≤ m) (hj : 2 ^ j ≤ 2 * m + 1) :
    gN j ≤ (96 * m) ^ (3 * simAN + 1) := by
  have h1 : 2 ^ (j + 5) ≤ 96 * m := by rw [pow_add]; omega
  have h2 : (2 ^ (j + 5)) ^ (3 * simAN) ≤ (96 * m) ^ (3 * simAN) := Nat.pow_le_pow_left h1 _
  unfold gN
  calc 2 * 2 ^ j * (2 ^ (j + 5)) ^ (3 * simAN) ≤ (96 * m) * (96 * m) ^ (3 * simAN) :=
        Nat.mul_le_mul (by omega) h2
    _ = (96 * m) ^ (3 * simAN + 1) := (pow_succ' _ _).symm

/-! ## The constants of the loss -/

/-- The constant `c` of the polynomial bound `G ≤ c Q^p σ^p`. -/
def errCc (κ : ArConsts) : ℕ := (96 * cM κ) ^ (3 * simAN + 1)

/-- The exponent `p` of the polynomial bound `G ≤ c Q^p σ^p`. -/
def errPp : ℕ := pM * (3 * simAN + 1)

/-- **The exponent `a` of the soundness loss.** It depends on `E₁` and `c₀`, not on `E₂`. -/
def errA (κ : ArConsts) : ℕ := aOf (errCc κ) errPp (16 ^ 9)

theorem one_le_errA (κ : ArConsts) : 1 ≤ errA κ := one_le_aOf _ _ _

/-- **The threshold `C` of the soundness loss**: past it, `2^{clB Q}` beats the polynomial. -/
def errC (κ : ArConsts) : ℕ := (exists_threshold_clB (errCc κ) errPp).choose

theorem gN_le_poly (κ : ArConsts) {lam mu sigma n : ℕ} (hlam : 1 ≤ lam) (hmu : 1 ≤ mu)
    (hs : 1 ≤ sigma) (hn : 1 ≤ n) :
    (gN (pJ κ lam mu sigma n) : ℝ) ≤
      (errCc κ : ℝ) * (pQ lam mu n : ℝ) ^ errPp * (sigma : ℝ) ^ errPp := by
  have hm1 : 1 ≤ (pL κ lam mu sigma n).m := by rw [pL_m_eq]; omega
  have h1 := gN_le hm1 (two_pow_pJ_le κ lam mu sigma n)
  have h2 : (96 * (pL κ lam mu sigma n).m) ^ (3 * simAN + 1)
      ≤ (96 * (cM κ * (pQ lam mu n * sigma) ^ pM)) ^ (3 * simAN + 1) :=
    Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (pL_m_le κ hlam hmu hs hn)) _
  have h3 : (96 * (cM κ * (pQ lam mu n * sigma) ^ pM)) ^ (3 * simAN + 1)
      = errCc κ * pQ lam mu n ^ errPp * sigma ^ errPp := by
    rw [errCc, errPp, mul_pow, mul_pow, ← pow_mul, mul_pow]; ring
  have := h1.trans (h2.trans_eq h3)
  exact_mod_cast this

/-! ## The error below the loss -/

/-- **The soundness error is below the loss** (`ε ≤ 1`, `μ ≥ 1`), past the threshold `errC κ`,
with `a = errA κ` and `b = clB / 2`, when `E₂ ≥ e2Min`. -/
theorem errAR_le_delta (κ : ArConsts) (hE : e2Min ≤ κ.E₂) {lam mu sigma n : ℕ} {ε : ℝ}
    (hC : errC κ ≤ n) (hn2 : 2 ≤ n) (hlam : 1 ≤ lam) (hmu : 1 ≤ mu) (hs : 1 ≤ sigma)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    24 * √(errAR (pTw κ lam mu sigma n)
        (one_le_pTw κ lam mu sigma n (by have := seven_le_e2Min; omega))
        (pJ κ lam mu sigma n) pD (pL κ lam mu sigma n) (16 ^ 9 * ε)) ≤
      AnswerReduction.delta (errA κ) (clB / 2) lam mu sigma n ε := by
  obtain ⟨hnQ, hμQ⟩ := pQ_facts hlam hmu (by omega : 1 ≤ n)
  have hm := pL_m_lt κ lam mu sigma n
  have hQm : pQ lam mu n ≤ (pL κ lam mu sigma n).m := by rw [pL_m_eq]; omega
  have hT : e2Min * (pJ κ lam mu sigma n + pQ lam mu n + 1) ≤ pTw κ lam mu sigma n := by
    unfold pTw
    exact Nat.mul_le_mul hE (by omega)
  have herr := errAR_le_shape
    (ht := one_le_pTw κ lam mu sigma n (by have := seven_le_e2Min; omega)) hm hQm hT hε.le hε1
  have hG := gN_le_poly κ hlam hmu hs (by omega : 1 ≤ n)
  have hN2 : 2 ≤ lam * n := le_trans hn2 (Nat.le_mul_of_pos_left _ hlam)
  have hQN : pQ lam mu n ≤ (lam * n) ^ (2 * mu) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (by nlinarith) _
  have hNQ : (lam * n) ^ mu ≤ pQ lam mu n := Nat.pow_le_pow_left (by omega) _
  obtain ⟨hQ8, hthr⟩ := (exists_threshold_clB (errCc κ) errPp).choose_spec (pQ lam mu n)
    (by unfold errC at hC; omega)
  have hfin := sqrt_le_delta (K := 16 ^ 9) hN2 hmu hs hQN hNQ hQ8 hthr hG hε.le
    (e := errAR (pTw κ lam mu sigma n)
        (one_le_pTw κ lam mu sigma n (by have := seven_le_e2Min; omega))
        (pJ κ lam mu sigma n) pD (pL κ lam mu sigma n) (16 ^ 9 * ε) / 7)
    (by linarith)
  rw [mul_div_cancel₀ _ (by norm_num : (7 : ℝ) ≠ 0)] at hfin
  have hNr : (lam : ℝ) * n = ((lam * n : ℕ) : ℝ) := by push_cast; ring
  rw [AnswerReduction.delta, hNr]
  exact hfin

/-- **The loss is at least `1` when `μ = 0` or `ε ≥ 1`**, at `a = errA κ`, `b = clB / 2`. -/
theorem one_le_delta_of_trivial' (κ : ArConsts) {lam mu sigma n : ℕ} {ε : ℝ} (hlam : 1 ≤ lam)
    (hn : 1 ≤ n) (hs : 1 ≤ sigma) (hε : 0 < ε) (h : mu = 0 ∨ 1 ≤ ε) :
    1 ≤ AnswerReduction.delta (errA κ) (clB / 2) lam mu sigma n ε := by
  have hN1 : (1 : ℝ) ≤ (lam : ℝ) * n := by
    have : 1 ≤ lam * n := le_trans hn (Nat.le_mul_of_pos_left _ hlam)
    exact_mod_cast this
  exact AnswerReduction.one_le_delta_of_trivial (one_le_errA κ) hs hN1 hε h

/-- **The soundness error against the loss, for every `ε > 0` and `μ`**: either the error is below
the loss, or the loss is at least `1` (and the contract's conclusion is trivial). -/
theorem errAR_le_delta_or (κ : ArConsts) (hE : e2Min ≤ κ.E₂) {lam mu sigma n : ℕ} {ε : ℝ}
    (hC : errC κ ≤ n) (hn2 : 2 ≤ n) (hlam : 1 ≤ lam) (hs : 1 ≤ sigma) (hε : 0 < ε) :
    24 * √(errAR (pTw κ lam mu sigma n)
        (one_le_pTw κ lam mu sigma n (by have := seven_le_e2Min; omega))
        (pJ κ lam mu sigma n) pD (pL κ lam mu sigma n) (16 ^ 9 * ε)) ≤
      AnswerReduction.delta (errA κ) (clB / 2) lam mu sigma n ε ∨
    1 ≤ AnswerReduction.delta (errA κ) (clB / 2) lam mu sigma n ε := by
  by_cases h : mu = 0 ∨ 1 ≤ ε
  · exact Or.inr (one_le_delta_of_trivial' κ hlam (by omega) hs hε h)
  · push Not at h
    exact Or.inl (errAR_le_delta κ hE hC hn2 hlam (by omega) hs hε h.2.le)

/-- **The soundness error chain** (P4i): a field-width threshold `E₂₀` independent of `κ`, and
for every `κ` past it, constants `a ≥ 1`, `0 < b ≤ 1` and a threshold `C` such that the error of
`valStar_sound_output` is below the contract's loss `δ(ε, n)` for `ε ≤ 1` and `μ ≥ 1`, and the
loss is at least `1` otherwise. -/
theorem exists_errAR_le_delta : ∃ E₂₀ : ℕ, 7 ≤ E₂₀ ∧ ∀ κ : ArConsts, ∀ hE1 : 1 ≤ κ.E₂,
    E₂₀ ≤ κ.E₂ → ∃ (a b : ℝ) (C : ℕ), 1 ≤ a ∧ 0 < b ∧ b ≤ 1 ∧
      (∀ (lam mu sigma n : ℕ) (ε : ℝ), C ≤ n → 2 ≤ n → 1 ≤ lam → 1 ≤ mu → 1 ≤ sigma →
        0 < ε → ε ≤ 1 →
        24 * √(errAR (pTw κ lam mu sigma n) (one_le_pTw κ lam mu sigma n hE1)
            (pJ κ lam mu sigma n) pD (pL κ lam mu sigma n) (16 ^ 9 * ε)) ≤
          AnswerReduction.delta a b lam mu sigma n ε) ∧
      (∀ (lam mu sigma n : ℕ) (ε : ℝ), 1 ≤ n → 1 ≤ lam → 1 ≤ sigma → 0 < ε →
        (mu = 0 ∨ 1 ≤ ε) → 1 ≤ AnswerReduction.delta a b lam mu sigma n ε) :=
  ⟨e2Min, seven_le_e2Min, fun κ _ hE => ⟨errA κ, clB / 2, errC κ,
    by exact_mod_cast one_le_errA κ, by have := clB_pos; linarith,
    by have := clB_lt_one; linarith,
    fun _ _ _ _ _ hC hn2 hlam hmu hs hε hε1 => errAR_le_delta κ hE hC hn2 hlam hmu hs hε hε1,
    fun _ _ _ _ _ hn hlam hs hε h => one_le_delta_of_trivial' κ hlam hn hs hε h⟩⟩

end MIPRE.Tailored.AnsRed.Typed

end

end
