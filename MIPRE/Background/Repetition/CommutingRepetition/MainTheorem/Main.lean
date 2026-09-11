/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/MainTheorem/Main.lean
-/
/-
# The uniform direct parallel repetition theorem (root statement)

Encoding decision D6; the root statements. Lin's density theorem is
*proved* in this development — `Density.tracialDensity`
(Tracial/Density/Main.lean, audit node 1.1.1, stage E7 of the density
programme) — and is never an axiom, so the root statements below and the
intermediates they rest on (Tracial/Reduction, MainTheorem/Constants,
MainTheorem/Extensions) carry no hypothesis at all.
Anchors: 07_main_theorem.tex, thm uniform-direct-repetition-proof
(eq uniform-U7) and cor uniform-U13; 01_introduction.tex thm main-intro;
audit nodes 1 (root), 1.6.3.

Conventions recorded for the fidelity ledger:
- ε = 1 − ω^co(G), ℓ = log(|A|·|B|); the degenerate case ε = ℓ = 0 is
  covered automatically by Lean's `0 / 0 = 0` (matching the manuscript's
  zero-ratio convention);
- the universal constant is quantified BEFORE the game and `n`
  (∃ c > 0, ∀ G n — the paper's quantifier order);
- `omegaCO` is the universe-0 supremum (see Game/Value.lean);
- Lin's density theorem is discharged by `Density.tracialDensity`, so
  these statements are unconditional; the `TracialDensityHypothesis` Prop
  survives only as the frozen encoding of Lin's statement (decision D5).
  No axiom keyword exists in this development, and the axiom gate in CI
  enforces that the closed proofs depend on nothing beyond propext,
  Classical.choice, Quot.sound.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Game.Basic
import MIPRE.Background.Repetition.CommutingRepetition.Game.Value
import MIPRE.Background.Repetition.CommutingRepetition.Game.Monotone
import MIPRE.Background.Repetition.CommutingRepetition.Tracial.Density
import MIPRE.Background.Repetition.CommutingRepetition.Tracial.Density.Main
import MIPRE.Background.Repetition.CommutingRepetition.MainTheorem.Extensions

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped BigOperators

/-- **Uniform direct parallel repetition for commuting-operator
strategies** (07_main_theorem.tex, Theorem 7.1): there is a universal
`c > 0` such that for every finite game `G` with payoffs in `[0,1]` and
every `n ≥ 1`,
`ω^co(G^{⊗n}) ≤ exp(−c·n·ε⁷/(ε + log(|A||B|)))` where `ε = 1 − ω^co(G)`. -/
theorem uniform_parallel_repetition :
    ∃ c : ℝ, 0 < c ∧
      ∀ (X Y A B : Type) [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
        [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
        (G : Game X Y A B) (n : ℕ), 1 ≤ n →
        (G.«repeat» n).omegaCO ≤
          Real.exp
            (-(c * ((1 - G.omegaCO) ^ 7 /
              ((1 - G.omegaCO) +
                Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)))))
              * (n : ℝ)) := by
  obtain ⟨c, hc0, hrat⟩ := rational_case
  refine ⟨c, hc0, ?_⟩
  intro X Y A B _ _ _ _ _ _ _ _ G n hn
  set ε := 1 - G.omegaCO with hεdef
  set ℓ := Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)) with hℓdef
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
  · -- Main case: approximate by rational payoff tables and pass to the
    -- limit through continuity of the bound at ε > 0.
    have hεℓ : (0 : ℝ) < ε + ℓ := by
      have hℓ0 : 0 ≤ ℓ := by
        rw [hℓdef]
        apply Real.log_nonneg
        have hA : (1 : ℝ) ≤ (Fintype.card A : ℝ) := by
          exact_mod_cast Fintype.card_pos
        have hB : (1 : ℝ) ≤ (Fintype.card B : ℝ) := by
          exact_mod_cast Fintype.card_pos
        nlinarith
      linarith
    refine le_of_forall_pos_le_add ?_
    intro e he
    -- Continuity of the bound in ε at ε > 0.
    have hcont : ContinuousAt
        (fun t : ℝ => Real.exp (-(c * (t ^ 7 / (t + ℓ))) * (n : ℝ))) ε := by
      have h1 : ContinuousAt (fun t : ℝ => t ^ 7) ε := by fun_prop
      have h2 : ContinuousAt (fun t : ℝ => t + ℓ) ε := by fun_prop
      have h3 : ContinuousAt (fun t : ℝ => t ^ 7 / (t + ℓ)) ε :=
        h1.div h2 hεℓ.ne'
      exact Real.continuous_exp.continuousAt.comp
        (((h3.const_mul c).neg).mul_const (n : ℝ))
    obtain ⟨δ₀, hδ₀0, hδ₀⟩ := Metric.continuousAt_iff.mp hcont (e / 2)
      (by positivity)
    -- Pick the approximation scale.
    set δ := min (δ₀ / 2) (e / (2 * ((n : ℝ) + 1))) with hδdef
    have hδ0 : 0 < δ := by
      rw [hδdef]
      have : (0 : ℝ) < e / (2 * ((n : ℝ) + 1)) := by positivity
      simp only [lt_min_iff]
      exact ⟨by positivity, this⟩
    -- Entrywise rational approximation of the payoff table, kept in [0,1].
    have hchoice : ∀ (x : X) (y : Y) (a : A) (b : B),
        ∃ q : ℚ, 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ 1 ∧
          |(q : ℝ) - G.payoff x y a b| ≤ δ := by
      intro x y a b
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn
        (show G.payoff x y a b - δ < G.payoff x y a b by linarith)
      refine ⟨max q 0, ?_, ?_, ?_⟩
      · exact_mod_cast le_max_right q 0
      · have hq1' : (q : ℝ) ≤ 1 :=
          le_trans hq2.le (G.payoff_le_one x y a b)
        have hmax : max q 0 ≤ (1 : ℚ) :=
          max_le (by exact_mod_cast hq1') (by norm_num)
        exact_mod_cast hmax
      · rcases le_total q 0 with h | h
        · rw [max_eq_right h]
          push_cast
          rw [abs_sub_comm, sub_zero,
            abs_of_nonneg (G.payoff_nonneg x y a b)]
          have hq0' : (q : ℝ) ≤ 0 := by exact_mod_cast h
          linarith
        · rw [max_eq_left h]
          rw [abs_le]
          constructor
          · linarith
          · have hq0' : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast h
            linarith [G.payoff_nonneg x y a b]
    choose Vq hq0 hq1 hqd using hchoice
    set G' : Game X Y A B :=
      { questionWeight := G.questionWeight
        weight_nonneg := G.weight_nonneg
        weight_normalized := G.weight_normalized
        payoff := fun x y a b => (Vq x y a b : ℝ)
        payoff_nonneg := hq0
        payoff_le_one := hq1 } with hG'def
    have hVd : ∀ x y a b, |G.payoff x y a b - G'.payoff x y a b| ≤ δ := by
      intro x y a b
      rw [abs_sub_comm]
      exact hqd x y a b
    have hμ : G.questionWeight = G'.questionWeight := rfl
    have hd1 := Game.abs_repeat_omegaCO_sub_le hδ0.le hμ hVd n
    have hd2 := Game.abs_omegaCO_sub_omegaCO_le hδ0.le hμ hVd
    have hb := hrat X Y A B G' (fun x y a b => ⟨Vq x y a b, rfl⟩) n hn
    -- The approximated gap is within δ₀ of ε, so the bound moves by ≤ e/2.
    have hεdist : dist (1 - G'.omegaCO) ε < δ₀ := by
      rw [Real.dist_eq, hεdef]
      have h1 : |G.omegaCO - G'.omegaCO| ≤ δ := hd2
      have h2 : δ ≤ δ₀ / 2 := by
        rw [hδdef]
        exact min_le_left _ _
      have h3 : |1 - G'.omegaCO - (1 - G.omegaCO)| = |G.omegaCO - G'.omegaCO| := by
        rw [show (1 - G'.omegaCO - (1 - G.omegaCO)) = (G.omegaCO - G'.omegaCO) by ring]
      rw [h3]
      linarith
    have hf := hδ₀ hεdist
    rw [Real.dist_eq] at hf
    have hf' : Real.exp (-(c * ((1 - G'.omegaCO) ^ 7 /
        ((1 - G'.omegaCO) + ℓ))) * (n : ℝ))
        ≤ Real.exp (-(c * (ε ^ 7 / (ε + ℓ))) * (n : ℝ)) + e / 2 := by
      have := (abs_le.mp hf.le).2
      linarith
    have hnδ : (n : ℝ) * δ ≤ e / 2 := by
      have h1 : δ ≤ e / (2 * ((n : ℝ) + 1)) := by
        rw [hδdef]
        exact min_le_right _ _
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have h2 : (n : ℝ) * δ ≤ (n : ℝ) * (e / (2 * ((n : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left h1 hn0
      have h3 : (n : ℝ) * (e / (2 * ((n : ℝ) + 1))) ≤ e / 2 := by
        rw [show (n : ℝ) * (e / (2 * ((n : ℝ) + 1)))
          = ((n : ℝ) * e) / (2 * ((n : ℝ) + 1)) by ring]
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [he.le, Nat.cast_nonneg (α := ℝ) n]
      linarith
    calc (G.«repeat» n).omegaCO
        ≤ (G'.«repeat» n).omegaCO + (n : ℝ) * δ := by
          linarith [(abs_le.mp hd1).2]
      _ ≤ Real.exp (-(c * ((1 - G'.omegaCO) ^ 7 /
            ((1 - G'.omegaCO) + ℓ))) * (n : ℝ)) + (n : ℝ) * δ := by
          linarith [hb]
      _ ≤ Real.exp (-(c * (ε ^ 7 / (ε + ℓ))) * (n : ℝ)) + e / 2 +
            (n : ℝ) * δ := by linarith [hf']
      _ ≤ Real.exp (-(c * (ε ^ 7 / (ε + ℓ))) * (n : ℝ)) + e := by
          linarith [hnδ]

/-- Power-thirteen corollary (07_main_theorem.tex, Corollary 7.2): some
universal constant gives the ε¹³ bound. The paper's "with the same
universal constant" is not encoded by this second `∃ c` (a deliberate
weaker-but-true rendering recorded in DIFFERENCES.md); the main theorem's
constant does work, since `ε⁷ ≥ ε¹³` on `[0,1]`. -/
theorem uniform_parallel_repetition_pow13 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (X Y A B : Type) [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
        [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
        (G : Game X Y A B) (n : ℕ), 1 ≤ n →
        (G.«repeat» n).omegaCO ≤
          Real.exp
            (-(c * ((1 - G.omegaCO) ^ 13 /
              ((1 - G.omegaCO) +
                Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)))))
              * (n : ℝ)) := by
  obtain ⟨c, hc0, hbound⟩ := uniform_parallel_repetition
  refine ⟨c, hc0, ?_⟩
  intro X Y A B _ _ _ _ _ _ _ _ G n hn
  refine (hbound X Y A B G n hn).trans (Real.exp_le_exp.mpr ?_)
  have hε0 : 0 ≤ 1 - G.omegaCO := by
    have := G.omegaCO_le_one
    linarith
  have hε1 : 1 - G.omegaCO ≤ 1 := by
    have := G.omegaCO_nonneg
    linarith
  have hℓ0 : 0 ≤ Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)) := by
    apply Real.log_nonneg
    have hA : (1 : ℝ) ≤ (Fintype.card A : ℝ) := by
      exact_mod_cast Fintype.card_pos
    have hB : (1 : ℝ) ≤ (Fintype.card B : ℝ) := by
      exact_mod_cast Fintype.card_pos
    nlinarith
  have hpow : (1 - G.omegaCO) ^ 13 ≤ (1 - G.omegaCO) ^ 7 :=
    pow_le_pow_of_le_one hε0 hε1 (by norm_num)
  have hdiv : (1 - G.omegaCO) ^ 13 /
      ((1 - G.omegaCO) +
        Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)))
      ≤ (1 - G.omegaCO) ^ 7 /
      ((1 - G.omegaCO) +
        Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ))) := by
    rcases eq_or_lt_of_le (add_nonneg hε0 hℓ0) with hz | hpos
    · rw [← hz]
      simp
    · gcongr
  have h1 := mul_le_mul_of_nonneg_left hdiv hc0.le
  have h2 := mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg (α := ℝ) n)
  linarith

end CommutingRepetition
