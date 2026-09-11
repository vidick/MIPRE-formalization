/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/MainTheorem/Constants.lean
-/
/-
# Parameter choice and the contradiction (Section 7.3, predicate case)

Statement skeleton for audit nodes 1.5, 1.5.1–1.5.4.
Anchors: 07_main_theorem.tex sec 7.3, eqs universal-c-choice,
gamma-xi-choice, gamma-greedy-condition, alleged-repeated-counterexample,
main-q-eta-delta, explicit-one-shot-lower-bound,
strict-one-shot-contradiction.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Game.Basic
import MIPRE.Background.Repetition.CommutingRepetition.Game.Value
import MIPRE.Background.Repetition.CommutingRepetition.Tracial.Reduction
import MIPRE.Background.Repetition.CommutingRepetition.Prerounding.Main
import MIPRE.Background.Repetition.CommutingRepetition.MainTheorem.OneShot

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped BigOperators

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- **Constant choice** (node 1.5.1; 07_main_theorem.tex, eqs
universal-c-choice, gamma-xi-choice, gamma-greedy-condition): for
`C ≥ 1`, `c ≤ min{1/8, 1/(8192 C⁶), 1/19200}`, `0 < ε ≤ 1`, `ℓ ≥ 0`, the
choices `γ = c ε⁷/(ε + ℓ)` and `ξ = ε/(4C)` satisfy the downstream
hypotheses: `γ ≤ c ε⁶ ≤ ε/8` and `0 < ξ ≤ 1`. -/
theorem constant_choice {C c ε ℓ : ℝ} (hC : 1 ≤ C) (hc0 : 0 < c)
    (hc : c ≤ min (1 / 8) (min (1 / (8192 * C ^ 6)) (1 / 19200)))
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hℓ : 0 ≤ ℓ) :
    c * ε ^ 7 / (ε + ℓ) ≤ c * ε ^ 6 ∧
    c * ε ^ 7 / (ε + ℓ) ≤ ε / 8 ∧
    0 < ε / (4 * C) ∧ ε / (4 * C) ≤ 1 := by
  have hεℓ : 0 < ε + ℓ := by linarith
  have hc8 : c ≤ 1 / 8 := le_trans hc (min_le_left _ _)
  have hε6 : ε ^ 6 ≤ ε := by
    calc ε ^ 6 ≤ ε ^ 1 :=
        pow_le_pow_of_le_one hε0.le hε1 (by norm_num)
      _ = ε := pow_one ε
  have h1 : c * ε ^ 7 / (ε + ℓ) ≤ c * ε ^ 6 := by
    rw [div_le_iff₀ hεℓ]
    have hkey : c * ε ^ 6 * (ε + ℓ) = c * ε ^ 7 + c * ε ^ 6 * ℓ := by ring
    rw [hkey]
    have : 0 ≤ c * ε ^ 6 * ℓ :=
      mul_nonneg (mul_nonneg hc0.le (pow_nonneg hε0.le 6)) hℓ
    linarith
  have h2 : c * ε ^ 6 ≤ ε / 8 := by nlinarith
  have hC0 : (0 : ℝ) < 4 * C := by linarith
  refine ⟨h1, le_trans h1 h2, div_pos hε0 hC0, ?_⟩
  rw [div_le_one hC0]
  linarith

/-- **Counterexample extraction** (node 1.5.2; 07_main_theorem.tex, eq
alleged-repeated-counterexample and following): if the repeated value
exceeds `e^{−γn}`, the strict tracial reduction at `H = G^{⊗n}`,
`λ = e^{−γn}` yields an exact tracially embeddable repeated strategy with
success still above `e^{−γn}`. No attainment is used. -/
theorem counterexample_extraction
    [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
    (G : Game X Y A B) (n : ℕ) {γ : ℝ}
    (hsup : Real.exp (-(γ * n)) < (G.«repeat» n).omegaCO) :
    ∃ Trep : TracialStrategy.{0}
        (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B),
      Real.exp (-(γ * n)) < (G.«repeat» n).win Trep.correlation :=
  strict_tracial_reduction (G.«repeat» n) hsup

/-- **Pre-rounding parameter arithmetic** (node 1.5.3; 07_main_theorem.tex,
eq main-q-eta-delta): with `γ = c ε⁷/(ε + ℓ)` and `c ≤ 1/8`, the
pre-rounding outputs satisfy `η ≤ 8cε⁶ ≤ 1` and `Δ ≤ 128cε⁶`. -/
theorem eta_delta_bounds {c ε ℓ η Δ : ℝ} (hc0 : 0 < c) (hc : c ≤ 1 / 8)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hℓ : 0 ≤ ℓ)
    (hη : η ≤ 8 * (c * ε ^ 7 / (ε + ℓ)) * ((ε + ℓ) / ε))
    (hΔ : Δ ≤ 16 * η) :
    η ≤ 8 * c * ε ^ 6 ∧ 8 * c * ε ^ 6 ≤ 1 ∧ Δ ≤ 128 * c * ε ^ 6 := by
  have hεℓ : 0 < ε + ℓ := by linarith
  have heq : 8 * (c * ε ^ 7 / (ε + ℓ)) * ((ε + ℓ) / ε) = 8 * c * ε ^ 6 := by
    field_simp
    try ring
  rw [heq] at hη
  have hε6 : ε ^ 6 ≤ 1 := pow_le_one₀ hε0.le hε1
  refine ⟨hη, by nlinarith, by linarith⟩

/-- **Arithmetic contradiction** (node 1.5.4; 07_main_theorem.tex, eqs
explicit-one-shot-lower-bound, strict-one-shot-contradiction): inserting
`η ≤ 8cε⁶`, `Δ ≤ 128cε⁶`, `ξ = ε/(4C)` into the one-shot payoff bound
`w ≥ 1 − ε/4 − (C/2)(Δ^{1/6} + ξ) − 5√(3η/2)` forces `w ≥ 1 − 3ε/4`:
the three displayed losses are at most `ε/4`, `ε/8`, `ε/8` by the
constraints `(128c)^{1/6} ≤ 1/(2C)`, `(C/2)ξ = ε/8`, `5√(12c) ≤ 1/8`. -/
theorem contradiction_arithmetic {C c ε η Δ w : ℝ}
    (hC : 1 ≤ C)
    (hc0 : 0 < c)
    (hc : c ≤ min (1 / 8) (min (1 / (8192 * C ^ 6)) (1 / 19200)))
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hη0 : 0 ≤ η) (hη : η ≤ 8 * c * ε ^ 6)
    (hΔ0 : 0 ≤ Δ) (hΔ : Δ ≤ 128 * c * ε ^ 6)
    (hw : 1 - ε / 4 - C / 2 * (Δ ^ ((1 : ℝ) / 6) + ε / (4 * C)) -
        5 * Real.sqrt (3 * η / 2) ≤ w) :
    1 - 3 * ε / 4 ≤ w := by
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC
  have hcC : c ≤ 1 / (8192 * C ^ 6) :=
    le_trans hc (le_trans (min_le_right _ _) (min_le_left _ _))
  have hc19 : c ≤ 1 / 19200 :=
    le_trans hc (le_trans (min_le_right _ _) (min_le_right _ _))
  have hΔ6 : Δ ^ ((1 : ℝ) / 6) ≤ 1 / (2 * C) * ε := by
    have hC6 : (0 : ℝ) < C ^ 6 := by positivity
    have hup : Δ ≤ (1 / (2 * C) * ε) ^ (6 : ℕ) := by
      have hpow : ((1 : ℝ) / (2 * C) * ε) ^ (6 : ℕ) = ε ^ 6 / (64 * C ^ 6) := by
        field_simp
        ring
      rw [hpow, le_div_iff₀ (by positivity : (0 : ℝ) < 64 * C ^ 6)]
      have hc' : c * (8192 * C ^ 6) ≤ 1 :=
        (le_div_iff₀ (by positivity : (0 : ℝ) < 8192 * C ^ 6)).mp hcC
      nlinarith [mul_le_mul_of_nonneg_right hΔ
          (by positivity : (0 : ℝ) ≤ 64 * C ^ 6),
        mul_le_mul_of_nonneg_left hc' (pow_nonneg hε0.le 6)]
    calc Δ ^ ((1 : ℝ) / 6)
        ≤ ((1 / (2 * C) * ε) ^ (6 : ℕ)) ^ ((1 : ℝ) / 6) :=
          Real.rpow_le_rpow hΔ0 hup (by norm_num)
      _ = 1 / (2 * C) * ε := by
          have ha : (0 : ℝ) ≤ 1 / (2 * C) * ε := by positivity
          rw [← Real.rpow_natCast (1 / (2 * C) * ε) 6, ← Real.rpow_mul ha]
          norm_num
  have hsq : Real.sqrt (3 * η / 2) ≤ 1 / 40 * ε ^ 3 := by
    have h12 : 3 * η / 2 ≤ (1 / 40 * ε ^ 3) ^ 2 := by
      have hsq' : ((1 : ℝ) / 40 * ε ^ 3) ^ 2 = ε ^ 6 / 1600 := by ring
      rw [hsq']
      nlinarith [pow_nonneg hε0.le 6]
    calc Real.sqrt (3 * η / 2)
        ≤ Real.sqrt ((1 / 40 * ε ^ 3) ^ 2) := Real.sqrt_le_sqrt h12
      _ = 1 / 40 * ε ^ 3 := Real.sqrt_sq (by positivity)
  have hloss1 : C / 2 * (Δ ^ ((1 : ℝ) / 6)) ≤ ε / 4 := by
    calc C / 2 * (Δ ^ ((1 : ℝ) / 6))
        ≤ C / 2 * (1 / (2 * C) * ε) :=
          mul_le_mul_of_nonneg_left hΔ6 (by positivity)
      _ = ε / 4 := by field_simp; ring
  have hloss2 : C / 2 * (ε / (4 * C)) = ε / 8 := by field_simp; ring
  have hloss3 : 5 * Real.sqrt (3 * η / 2) ≤ ε / 8 := by
    have hε3 : ε ^ 3 ≤ ε := by
      calc ε ^ 3 ≤ ε ^ 1 :=
          pow_le_pow_of_le_one hε0.le hε1 (by norm_num)
        _ = ε := pow_one ε
    calc 5 * Real.sqrt (3 * η / 2) ≤ 5 * (1 / 40 * ε ^ 3) :=
        mul_le_mul_of_nonneg_left hsq (by norm_num)
      _ = ε ^ 3 / 8 := by ring
      _ ≤ ε / 8 := by linarith
  have hsplit : C / 2 * (Δ ^ ((1 : ℝ) / 6) + ε / (4 * C))
      = C / 2 * (Δ ^ ((1 : ℝ) / 6)) + C / 2 * (ε / (4 * C)) := by ring
  rw [hsplit, hloss2] at hw
  linarith

/-- **The predicate case** (node 1.5; 07_main_theorem.tex sec 7.3): the
uniform repetition bound for games whose payoff is a predicate. If
`ω^co(G^{⊗n}) > e^{−γn}` then nodes 1.1, 1.2, 1.3, 1.4 produce a legal
one-shot strategy with `win_G ≥ 1 − 3ε/4 > 1 − ε = ω^co(G)`, contradicting
the definition of the supremum (attainment of neither value is needed). -/
theorem predicate_case :
    ∃ c : ℝ, 0 < c ∧
      ∀ (X Y A B : Type) [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
        [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
        (G : Game X Y A B), G.IsPredicate → ∀ n : ℕ, 1 ≤ n →
        (G.«repeat» n).omegaCO ≤
          Real.exp
            (-(c * ((1 - G.omegaCO) ^ 7 /
              ((1 - G.omegaCO) +
                Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)))))
              * (n : ℝ)) := by
  obtain ⟨C, hC1, hC⟩ := otqcs_sampling
  have hc0 : 0 < min (1 / 8 : ℝ) (min (1 / (8192 * C ^ 6)) (1 / 19200)) := by
    have h1 : (0 : ℝ) < 1 / (8192 * C ^ 6) := by positivity
    simp only [lt_min_iff]
    refine ⟨by norm_num, h1, by norm_num⟩
  refine ⟨min (1 / 8) (min (1 / (8192 * C ^ 6)) (1 / 19200)), hc0, ?_⟩
  intro X Y A B _ _ _ _ _ _ _ _ G hV n hn
  set c := min (1 / 8 : ℝ) (min (1 / (8192 * C ^ 6)) (1 / 19200)) with hcdef
  set ε := 1 - G.omegaCO with hεdef
  set ℓ := Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)) with hℓdef
  have hℓ0 : 0 ≤ ℓ := by
    rw [hℓdef]
    apply Real.log_nonneg
    have hA : (1 : ℝ) ≤ (Fintype.card A : ℝ) := by
      exact_mod_cast Fintype.card_pos
    have hB : (1 : ℝ) ≤ (Fintype.card B : ℝ) := by
      exact_mod_cast Fintype.card_pos
    nlinarith
  have hε1 : ε ≤ 1 := by
    have := G.omegaCO_nonneg
    rw [hεdef]
    linarith
  have hε0' : 0 ≤ ε := by
    have := G.omegaCO_le_one
    rw [hεdef]
    linarith
  rcases eq_or_lt_of_le hε0' with hε | hε0
  · -- Degenerate case ε = 0: the bound is exp 0 = 1.
    rw [← hε]
    have h1 : (-(c * ((0 : ℝ) ^ 7 / (0 + ℓ))) * (n : ℝ)) = 0 := by
      norm_num
    rw [h1, Real.exp_zero]
    exact Game.omegaCO_le_one _
  · -- Main case 0 < ε ≤ 1: contradiction with the one-shot strategy.
    by_contra hcon
    push_neg at hcon
    obtain ⟨hγ6, hγ8, hξ0, hξ1⟩ :=
      constant_choice hC1 hc0 hcdef.le hε0 hε1 hℓ0
    set γ := c * (ε ^ 7 / (ε + ℓ)) with hγdef
    have hγeq : γ = c * ε ^ 7 / (ε + ℓ) := by
      rw [hγdef, mul_div_assoc]
    have hcon' : Real.exp (-(γ * (n : ℝ))) < (G.«repeat» n).omegaCO := by
      rw [show -(γ * (n : ℝ)) = -γ * (n : ℝ) by ring, hγdef]
      exact hcon
    obtain ⟨Trep, hTrep⟩ := counterexample_extraction G n hcon'
    have hγε : γ ≤ ε / 8 := by
      rw [hγeq]
      exact hγ8
    obtain ⟨P, η, hη0, hηb, hsucc, hΔ, _hACA, _hACB, _hKLA, _hKLB,
      hTVA, _hTVB, hmis⟩ :=
      tracial_prerounding G hV n hn Trep hε0 hε1 hγε hTrep
    obtain ⟨R, hR⟩ := hC (P.Hist × X) (P.Hist × Y) A B P.N P.labelLaw
      P.labelLaw_nonneg P.labelLaw_sum P.xvec P.yvec P.u
      P.xvec_norm P.yvec_norm P.u_norm P.A_ P.B_ P.A_pos P.B_pos
      P.A_sum P.B_sum (ε / (4 * C)) hξ0 hξ1
    have herr : P.samplingError R
        ≤ C * (P.alignment ^ ((1 : ℝ) / 6) + ε / (4 * C)) := by
      rw [P.samplingError_eq_labelLaw R, ← P.piAlignment_labelLaw]
      exact hR
    obtain ⟨Sc, hSc⟩ := one_shot_strategy G P R
    have hwin_le : G.win Sc.correlation ≤ 1 - ε := by
      have := G.le_omegaCO Sc
      rw [hεdef]
      linarith
    have hηb' : η ≤ 8 * (c * ε ^ 7 / (ε + ℓ)) * ((ε + ℓ) / ε) := by
      rw [← hγeq]
      exact hηb
    obtain ⟨hη8, _h81, hΔ128⟩ :=
      eta_delta_bounds hc0 (hcdef.le.trans (min_le_left _ _)) hε0 hε1 hℓ0
        hηb' hΔ
    have hw : 1 - ε / 4 -
        C / 2 * (P.alignment ^ ((1 : ℝ) / 6) + ε / (4 * C)) -
        5 * Real.sqrt (3 * η / 2) ≤ G.win Sc.correlation := by
      have hhalf : C * (P.alignment ^ ((1 : ℝ) / 6) + ε / (4 * C)) / 2
          = C / 2 * (P.alignment ^ ((1 : ℝ) / 6) + ε / (4 * C)) := by
        ring
      linarith [hSc, hsucc, herr, hTVA, hmis, hhalf.symm.le, hhalf.le]
    have hcontra := contradiction_arithmetic hC1 hc0 hcdef.le hε0 hε1
      hη0 hη8 P.alignment_nonneg hΔ128 hw
    linarith [hwin_le, hcontra, hε0]

end CommutingRepetition
