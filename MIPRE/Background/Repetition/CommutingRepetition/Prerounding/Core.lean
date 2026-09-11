/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Prerounding/Core.lean
-/
/-
# The greedy core and its parameters (Section 5.2)

Statement skeleton for audit nodes 1.2.1 and 1.2.2.
Anchors: 05_prerounding.tex, lem greedy-core (eq greedy-core) and eqs
p-q-m, eta-definition, core-basic-bounds, eta-gamma-bound.

The probability carrier is the ported `FiniteEventLaw` (Prelim/FiniteProb,
from the ten-proofs artifact); `winEvent wins D` is the event `W_D` and
`eventMass` its probability. The proof of 1.2.1 will go through the ported
greedy engine `exists_conditioned_win_set`.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Prelim.FiniteProb

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped BigOperators
open FiniteEventLaw

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]

/-- **Greedy core** (node 1.2.1; 05_prerounding.tex, lem greedy-core).
With `θ = P(W_[n]) > 0`, `0 < δ < 1`, and `log(1/θ)/δ < n`, there is a
proper subset `D ⊊ [n]` with `|D| ≤ log(1/θ)/δ`, `P(W_D) ≥ θ`, and
average conditional success `(1/(n−|D|)) ∑_{i∉D} P(W_i | W_D) ≥ 1 − δ`.
All conditionals are defined because `W_[n] ⊆ W_D` gives
`P(W_D) ≥ θ > 0`. -/
theorem greedy_core (law : FiniteEventLaw Ω) (wins : ι → Ω → Bool)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hθ : 0 < law.eventMass (winEvent wins Finset.univ))
    (hn : Real.log (1 / law.eventMass (winEvent wins Finset.univ)) / δ
      < (Fintype.card ι : ℝ)) :
    ∃ D : Finset ι, D ⊂ Finset.univ ∧
      (D.card : ℝ)
        ≤ Real.log (1 / law.eventMass (winEvent wins Finset.univ)) / δ ∧
      law.eventMass (winEvent wins Finset.univ)
        ≤ law.eventMass (winEvent wins D) ∧
      1 - δ ≤
        (1 / ((Fintype.card ι : ℝ) - D.card)) *
          ∑ i ∈ Finset.univ \ D,
            law.eventMass (winEvent wins (insert i D)) /
              law.eventMass (winEvent wins D) := by
  classical
  set θ := law.eventMass (winEvent wins Finset.univ) with hθdef
  have hθ1 : θ ≤ 1 := by
    calc θ ≤ law.eventMass Finset.univ :=
        law.eventMass_mono (Finset.subset_univ _)
      _ = 1 := law.eventMass_univ
  have hL0 : 0 ≤ Real.log (1 / θ) / δ := by
    apply div_nonneg _ hδ0.le
    rw [one_div, Real.log_inv]
    have := Real.log_nonpos hθ.le hθ1
    linarith
  set T : ℕ := ⌊Real.log (1 / θ) / δ⌋₊ + 1 with hTdef
  have hfloorle : (⌊Real.log (1 / θ) / δ⌋₊ : ℝ) ≤ Real.log (1 / θ) / δ :=
    Nat.floor_le hL0
  have hTgt : Real.log (1 / θ) / δ < (T : ℝ) := by
    rw [hTdef]
    push_cast
    exact Nat.lt_floor_add_one _
  have hfloorlt : ⌊Real.log (1 / θ) / δ⌋₊ < Fintype.card ι := by
    have h1 : (⌊Real.log (1 / θ) / δ⌋₊ : ℝ) < (Fintype.card ι : ℝ) :=
      lt_of_le_of_lt hfloorle hn
    exact_mod_cast h1
  have hT : T ≤ Fintype.card ι := by
    rw [hTdef]
    omega
  have hterm : (1 - δ) ^ T < θ := by
    have hexp1 : (1 - δ : ℝ) ≤ Real.exp (-δ) := by
      have := Real.add_one_le_exp (-δ)
      linarith
    have hpow : (1 - δ : ℝ) ^ T ≤ Real.exp (-δ) ^ T :=
      pow_le_pow_left₀ (by linarith) hexp1 T
    have hexppow : Real.exp (-δ) ^ T = Real.exp (-(δ * T)) := by
      rw [← Real.exp_nat_mul]
      ring_nf
    have hstrict : Real.exp (-(δ * T)) < θ := by
      have harg : -(δ * T) < Real.log θ := by
        rw [one_div, Real.log_inv] at hTgt
        have h2 : -Real.log θ < δ * T := by
          rw [div_lt_iff₀ hδ0] at hTgt
          linarith [hTgt]
        linarith
      calc Real.exp (-(δ * T)) < Real.exp (Real.log θ) :=
          Real.exp_lt_exp.mpr harg
        _ = θ := Real.exp_log hθ
    calc (1 - δ : ℝ) ^ T ≤ Real.exp (-δ) ^ T := hpow
      _ = Real.exp (-(δ * T)) := hexppow
      _ < θ := hstrict
  obtain ⟨D, hDcard, hDmass, hDfail⟩ :=
    exists_conditioned_win_set law wins hθ hδ0 hδ1.le hT
      (le_refl θ) hterm
  have hDcardR : (D.card : ℝ) ≤ Real.log (1 / θ) / δ := by
    have h1 : D.card ≤ ⌊Real.log (1 / θ) / δ⌋₊ := by
      omega
    calc (D.card : ℝ) ≤ (⌊Real.log (1 / θ) / δ⌋₊ : ℝ) := by exact_mod_cast h1
      _ ≤ Real.log (1 / θ) / δ := hfloorle
  have hproper : D ⊂ Finset.univ := by
    rw [Finset.ssubset_univ_iff]
    intro hcon
    have : D.card = Fintype.card ι := by rw [hcon, Finset.card_univ]
    omega
  refine ⟨D, hproper, hDcardR, hDmass, ?_⟩
  -- Convert the failure-mass bound into the conditional-average form.
  have hPD : 0 < law.eventMass (winEvent wins D) := lt_of_lt_of_le hθ hDmass
  have hmcard : D.card < Fintype.card ι := by
    have := Finset.card_lt_card hproper
    simpa [Finset.card_univ] using this
  have hm0 : (0 : ℝ) < (Fintype.card ι : ℝ) - D.card := by
    have : (D.card : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hmcard
    linarith
  have hsdcard : ((Finset.univ \ D).card : ℝ)
      = (Fintype.card ι : ℝ) - D.card := by
    have h := Finset.card_sdiff_of_subset (Finset.subset_univ D)
    rw [Finset.card_univ] at h
    rw [h]
    exact Nat.cast_sub hmcard.le
  -- hDfail : ∑ failureMass < m·(δ·P_D), i.e. m·P_D − ∑ P_{D∪i} < m·δ·P_D.
  have hsum : (∑ i ∈ Finset.univ \ D, law.eventMass (winEvent wins D)) -
      (∑ i ∈ Finset.univ \ D,
        law.eventMass (winEvent wins (insert i D)))
      < ((Finset.univ \ D).card : ℝ) *
        (δ * law.eventMass (winEvent wins D)) := by
    rw [← Finset.sum_sub_distrib]
    exact hDfail
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  -- ∑ P_{D∪i} > m·(1−δ)·P_D.
  have hlower : ((Finset.univ \ D).card : ℝ) * (1 - δ) *
      law.eventMass (winEvent wins D)
      < ∑ i ∈ Finset.univ \ D,
          law.eventMass (winEvent wins (insert i D)) := by
    nlinarith [hsum]
  -- Divide by m·P_D.
  rw [← Finset.sum_div, one_div, ← div_eq_inv_mul, div_div]
  rw [le_div_iff₀ (mul_pos hPD hm0)]
  rw [hsdcard] at hlower
  nlinarith [hlower]

/-- **Core parameters and bounds** (node 1.2.2; 05_prerounding.tex, eqs
p-q-m, eta-definition, core-basic-bounds, eta-gamma-bound). With
`δ = ε/4`, `m = n − |D|`, `p = P(W_D) ∈ [θ, 1]`, `t₀ = log(1/p)`,
`s₀ = |D|·ℓ`, `η = (t₀ + s₀)/m`, the pre-rounding hypotheses
`θ > e^{−γn}`, `0 < ε ≤ 1`, `γ ≤ ε/8` give
`|D| < 4γn/ε ≤ n/2` (so `m > n/2`), `t₀ < γn`, and
`η < 2γ(1 + 4ℓ/ε) ≤ 8γ(ε + ℓ)/ε`. The `q ≥ 1 − ε/4` part of eq
core-basic-bounds is not restated here: it is verbatim the third conjunct
of `greedy_core` at `δ = ε/4` (node 1.2.2 lists it as a "put" item) and
is consumed directly from there. -/
theorem core_parameters {ε γ ℓ θ p : ℝ} {n Dcard : ℕ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hγ : γ ≤ ε / 8) (hℓ : 0 ≤ ℓ)
    (hn : 1 ≤ n)
    (hθ : Real.exp (-(γ * n)) < θ)
    (hθp : θ ≤ p) (hp1 : p ≤ 1)
    (hD : (Dcard : ℝ) ≤ Real.log (1 / θ) / (ε / 4)) :
    (Dcard : ℝ) < 4 * γ * n / ε ∧
    4 * γ * n / ε ≤ (n : ℝ) / 2 ∧
    (n : ℝ) / 2 < (n : ℝ) - Dcard ∧
    Real.log (1 / p) < γ * n ∧
    (Real.log (1 / p) + Dcard * ℓ) / ((n : ℝ) - Dcard)
        < 2 * γ * (1 + 4 * ℓ / ε) ∧
    2 * γ * (1 + 4 * ℓ / ε) ≤ 8 * γ * ((ε + ℓ) / ε) := by
  have hθ0 : 0 < θ := lt_trans (Real.exp_pos _) hθ
  have hp0 : 0 < p := lt_of_lt_of_le hθ0 hθp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  -- θ > e^{−γn} with θ ≤ 1 forces γn > 0, hence γ > 0.
  have hγn : 0 < γ * n := by
    by_contra hcon
    push_neg at hcon
    have h1 : (1 : ℝ) ≤ Real.exp (-(γ * n)) := by
      rw [Real.one_le_exp_iff]
      linarith
    linarith [hθ.trans_le (hθp.trans hp1)]
  have hγ0 : 0 < γ := by
    by_contra hcon
    push_neg at hcon
    nlinarith
  -- t₀' := log(1/θ) < γn (from θ > e^{−γn}), and log(1/θ) ≥ 0 (θ ≤ 1).
  have hθ1 : θ ≤ 1 := le_trans hθp hp1
  have hlogθ : Real.log (1 / θ) < γ * n := by
    rw [one_div, Real.log_inv]
    have h := Real.log_lt_log (Real.exp_pos (-(γ * n))) hθ
    rw [Real.log_exp] at h
    linarith
  have hlogθ0 : 0 ≤ Real.log (1 / θ) := by
    rw [one_div, Real.log_inv]
    have := Real.log_nonpos hθ0.le hθ1
    linarith
  -- |D| < 4γn/ε.
  have hD4 : (Dcard : ℝ) < 4 * γ * n / ε := by
    have hε4 : (0 : ℝ) < ε / 4 := by linarith
    calc (Dcard : ℝ) ≤ Real.log (1 / θ) / (ε / 4) := hD
      _ < (γ * n) / (ε / 4) := by gcongr
      _ = 4 * γ * n / ε := by
          field_simp
          try ring
  have hD2 : 4 * γ * n / ε ≤ (n : ℝ) / 2 := by
    rw [div_le_div_iff₀ hε0 (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have hm : (n : ℝ) / 2 < (n : ℝ) - Dcard := by linarith
  -- t₀ = log(1/p) < γn.
  have hlogp : Real.log (1 / p) < γ * n := by
    rw [one_div, Real.log_inv]
    rw [one_div, Real.log_inv] at hlogθ
    have := Real.log_le_log hθ0 hθp
    linarith
  have hlogp0 : 0 ≤ Real.log (1 / p) := by
    rw [one_div, Real.log_inv]
    have := Real.log_nonpos hp0.le hp1
    linarith
  -- η < 2γ(1 + 4ℓ/ε).
  have hη : (Real.log (1 / p) + Dcard * ℓ) / ((n : ℝ) - Dcard)
      < 2 * γ * (1 + 4 * ℓ / ε) := by
    have hm0 : 0 < (n : ℝ) - Dcard := lt_trans (by linarith) hm
    rw [div_lt_iff₀ hm0]
    -- LHS < γn + (4γn/ε)·ℓ = γn(1 + 4ℓ/ε) = (2γ(1+4ℓ/ε))·(n/2)
    --     ≤ RHS since n − Dcard > n/2 and the factor is positive.
    have hfac : 0 < 2 * γ * (1 + 4 * ℓ / ε) := by positivity
    have hDℓ : Dcard * ℓ ≤ (4 * γ * n / ε) * ℓ :=
      mul_le_mul_of_nonneg_right hD4.le hℓ
    have hgrow : 2 * γ * (1 + 4 * ℓ / ε) * ((n : ℝ) / 2)
        ≤ 2 * γ * (1 + 4 * ℓ / ε) * ((n : ℝ) - Dcard) :=
      mul_le_mul_of_nonneg_left hm.le hfac.le
    have hexpand : 2 * γ * (1 + 4 * ℓ / ε) * ((n : ℝ) / 2)
        = γ * n + (4 * γ * n / ε) * ℓ := by
      field_simp
      try ring
    linarith
  have hfinal : 2 * γ * (1 + 4 * ℓ / ε) ≤ 8 * γ * ((ε + ℓ) / ε) := by
    have h1 : 2 * γ * (1 + 4 * ℓ / ε) = (2 * γ * ε + 8 * γ * ℓ) / ε := by
      field_simp
      try ring
    have h2 : 8 * γ * ((ε + ℓ) / ε) = (8 * γ * ε + 8 * γ * ℓ) / ε := by
      field_simp
      try ring
    rw [h1, h2]
    gcongr
    nlinarith
  exact ⟨hD4, hD2, hm, hlogp, hη, hfinal⟩

end CommutingRepetition
