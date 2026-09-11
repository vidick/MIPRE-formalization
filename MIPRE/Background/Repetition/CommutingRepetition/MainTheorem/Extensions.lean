/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/MainTheorem/Extensions.lean
-/
/-
# Bounded payoffs (Section 7.4)

Statement skeleton for audit node 1.6.2 (the rational-payoff case via
private referee coins). Node 1.6.1 (marginal monotonicity) and the
perturbation half of 1.6.3 live in Game/Monotone.lean; the real-payoff
limit and the power-13 corollary are assembled in MainTheorem/Main.lean.
Anchors: 07_main_theorem.tex sec 7.4, eqs private-coin-core-weight,
weighted-accepted-word-entropy, payoff-rational-approximation.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.MainTheorem.Constants
import MIPRE.Background.Repetition.CommutingRepetition.Game.Monotone

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped BigOperators

/-- **The rational-payoff case** (node 1.6.2; 07_main_theorem.tex sec 7.4):
the uniform repetition bound for games with rational payoff tables in
`[0,1]`, for some universal constant. (The manuscript's constant-sharing
with the predicate case is not encoded by this second `∃ c` — the same
weaker-but-true packaging as DIFFERENCES.md D2; the predicate case's
constant does work, since the private-coin argument keeps every estimate's
constants unchanged.) The
referee declares acceptance per coordinate with a fresh private coin of
bias `V(aᵢ, bᵢ | xᵢ, yᵢ)`; the coins are never revealed, so no effect,
sampler, or label may depend on them, and the predicate machinery runs
with the core indicator replaced by the weight `w_D ∈ [0,1]` (eq
private-coin-core-weight), the accepted-word budget by the weighted
entropy inequality `w·H₁(a) ≤ H₁(w·a)` plus log-sum (eq
weighted-accepted-word-entropy), and the history budget by data processing
from the private-coin space. -/
theorem rational_case :
    ∃ c : ℝ, 0 < c ∧
      ∀ (X Y A B : Type) [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
        [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
        (G : Game X Y A B),
        (∀ x y a b, ∃ r : ℚ, G.payoff x y a b = (r : ℝ)) →
        ∀ n : ℕ, 1 ≤ n →
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
  intro X Y A B _ _ _ _ _ _ _ _ G hQ n hn
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
      weighted_tracial_prerounding G hQ n hn Trep hε0 hε1 hγε hTrep
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
