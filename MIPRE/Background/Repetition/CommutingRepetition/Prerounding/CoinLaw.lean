/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Prerounding/CoinLaw.lean
-/
/-
# Pre-rounding assembly: rational payoffs and the private-coin law (node 1.2.11)

The weighted run of 07_main_theorem.tex sec 7.4: a rational payoff table
`V = num/den` is realized by fresh finite private coins, one per coordinate,
declaring acceptance with probability `V(aᵢ, bᵢ ∣ xᵢ, yᵢ)`. The greedy core
(node 1.2.1) is applied to the genuine acceptance events on this larger
private probability space; integrating the coins out, the event masses are
the coin-free weighted sums `∑ Πμ · q(a,b∣x,y) · ∏_{j∈S} V_j`, so
`P(W_[n])` is the repeated win probability and `P(W_D)` the weighted core
mass `p` of eq private-coin-core-weight. Nothing here is a manuscript
statement.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Game.Value
import MIPRE.Background.Repetition.CommutingRepetition.Tracial.Strategy
import MIPRE.Background.Repetition.CommutingRepetition.Prelim.FiniteProb
import MIPRE.Background.Repetition.CommutingRepetition.Prerounding.Core

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped BigOperators

set_option linter.unusedSectionVars false

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-! ### A common denominator for a rational payoff table -/

/-- A rational `[0,1]`-payoff table has a common denominator: `V = num/den`
with `num ≤ den`. -/
theorem Game.exists_common_denominator (G : Game X Y A B)
    (hQ : ∀ x y a b, ∃ r : ℚ, G.payoff x y a b = (r : ℝ)) :
    ∃ (den : ℕ) (num : X → Y → A → B → ℕ), 0 < den ∧
      (∀ x y a b, G.payoff x y a b = (num x y a b : ℝ) / den) ∧
      (∀ x y a b, num x y a b ≤ den) := by
  classical
  choose r hr using hQ
  set den : ℕ := ∏ t : X × Y × A × B, (r t.1 t.2.1 t.2.2.1 t.2.2.2).den with hden
  have hden_pos : 0 < den := Finset.prod_pos fun t _ => Rat.den_pos _
  have hdvd : ∀ x y a b, (r x y a b).den ∣ den := fun x y a b =>
    Finset.dvd_prod_of_mem (fun t : X × Y × A × B => (r t.1 t.2.1 t.2.2.1 t.2.2.2).den)
      (Finset.mem_univ (x, y, a, b))
  have hr0 : ∀ x y a b, 0 ≤ r x y a b := fun x y a b =>
    Rat.cast_nonneg.mp (hr x y a b ▸ G.payoff_nonneg x y a b)
  refine ⟨den, fun x y a b => (r x y a b).num.toNat * (den / (r x y a b).den), hden_pos,
    fun x y a b => ?_, fun x y a b => ?_⟩
  · show G.payoff x y a b
      = ((((r x y a b).num.toNat * (den / (r x y a b).den) : ℕ)) : ℝ) / den
    obtain ⟨k, hk⟩ := hdvd x y a b
    have hk' : den / (r x y a b).den = k := by
      rw [hk, Nat.mul_div_cancel_left _ (Rat.den_pos _)]
    have hnum : (((r x y a b).num.toNat : ℤ)) = (r x y a b).num :=
      Int.toNat_of_nonneg (Rat.num_nonneg.mpr (hr0 x y a b))
    have hnumR : (((r x y a b).num.toNat : ℕ) : ℝ) = ((r x y a b).num : ℝ) := by
      exact_mod_cast hnum
    have hdenR : (den : ℝ) = ((r x y a b).den : ℝ) * (k : ℝ) := by
      rw [hk]; push_cast; ring
    have hk0 : (0 : ℝ) < k := by
      have : 0 < k := Nat.pos_of_ne_zero fun h => by
        rw [h, mul_zero] at hk
        exact hden_pos.ne' hk
      exact_mod_cast this
    have hrden : (0 : ℝ) < (r x y a b).den := by exact_mod_cast Rat.den_pos _
    rw [hr x y a b, Rat.cast_def, hk']
    push_cast
    rw [hnumR, hdenR]
    field_simp
  · show (r x y a b).num.toNat * (den / (r x y a b).den) ≤ den
    have h1 := G.payoff_le_one x y a b
    obtain ⟨k, hk⟩ := hdvd x y a b
    have hk' : den / (r x y a b).den = k := by
      rw [hk, Nat.mul_div_cancel_left _ (Rat.den_pos _)]
    have hnum : (((r x y a b).num.toNat : ℤ)) = (r x y a b).num :=
      Int.toNat_of_nonneg (Rat.num_nonneg.mpr (hr0 x y a b))
    have hle : ((r x y a b).num : ℚ) ≤ (r x y a b).den := by
      have h2 : (r x y a b) ≤ 1 := by
        have := hr x y a b ▸ h1
        exact_mod_cast this
      have h3 := Rat.num_div_den (r x y a b)
      have hd : (0 : ℚ) < (r x y a b).den := by exact_mod_cast Rat.den_pos _
      rw [← h3, div_le_one hd] at h2
      exact h2
    have hle' : (r x y a b).num.toNat ≤ (r x y a b).den := by
      have : ((r x y a b).num.toNat : ℤ) ≤ ((r x y a b).den : ℤ) := by
        rw [hnum]; exact_mod_cast hle
      exact_mod_cast this
    rw [hk', hk]
    exact Nat.mul_le_mul_right k hle'

/-! ### The private-coin probability space -/

variable (G : Game X Y A B) {n : ℕ}
variable (Trep : TracialStrategy.{0} (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B))

/-- Questions, answers, and one private coin per coordinate. -/
abbrev CoinSpace (n den : ℕ) (X Y A B : Type) : Type :=
  (Fin n → X) × (Fin n → Y) × (Fin n → A) × (Fin n → B) × (Fin n → Fin den)

/-- The tracial correlation sums to one over the answer words. -/
theorem TracialStrategy.correlation_sum' (xw : Fin n → X) (yw : Fin n → Y) :
    (∑ as : Fin n → A, ∑ bs : Fin n → B, Trep.correlation xw yw as bs) = 1 := by
  unfold TracialStrategy.correlation
  have hexp : star Trep.σ * ((∑ as : Fin n → A, Trep.E xw as) * Trep.σ *
      (∑ bs : Fin n → B, Trep.F yw bs))
      = ∑ as : Fin n → A, ∑ bs : Fin n → B,
          star Trep.σ * (Trep.E xw as * Trep.σ * Trep.F yw bs) := by
    rw [Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun as _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
  have h := congrArg (fun z => (Trep.M.τ z).re) hexp
  simp only [map_sum, Complex.re_sum] at h
  rw [← h, Trep.E_sum, Trep.F_sum, one_mul, mul_one, Trep.σ_normalized, Complex.one_re]

/-- The private-coin weight: product prior, strategy correlation, uniform
coins. -/
noncomputable def coinWeight (den : ℕ) (ω : CoinSpace n den X Y A B) : ℝ :=
  (∏ j : Fin n, G.questionWeight (ω.1 j) (ω.2.1 j)) *
    Trep.correlation ω.1 ω.2.1 ω.2.2.1 ω.2.2.2.1 * (1 / (den : ℝ)) ^ n

theorem coinWeight_nonneg (den : ℕ) (ω : CoinSpace n den X Y A B) :
    0 ≤ coinWeight G Trep den ω :=
  mul_nonneg (mul_nonneg (Finset.prod_nonneg fun j _ => G.weight_nonneg _ _)
    (Trep.correlation_nonneg _ _ _ _)) (pow_nonneg (by positivity) n)

/-- Sums over the coin space, unfolded. -/
theorem sum_coinSpace (den : ℕ) (f : CoinSpace n den X Y A B → ℝ) :
    (∑ ω : CoinSpace n den X Y A B, f ω)
      = ∑ xw : Fin n → X, ∑ yw : Fin n → Y, ∑ as : Fin n → A, ∑ bs : Fin n → B,
          ∑ c : Fin n → Fin den, f (xw, yw, as, bs, c) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun xw _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun yw _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun as _ => ?_
  rw [Fintype.sum_prod_type]

theorem sum_coin_uniform (den : ℕ) (hden : 0 < den) :
    (∑ _c : Fin n → Fin den, (1 / (den : ℝ)) ^ n) = 1 := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    nsmul_eq_mul]
  have : (den : ℝ) ≠ 0 := by exact_mod_cast hden.ne'
  push_cast
  rw [one_div, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ this)]

theorem coinWeight_sum (den : ℕ) (hden : 0 < den) :
    (∑ ω : CoinSpace n den X Y A B, coinWeight G Trep den ω) = 1 := by
  rw [sum_coinSpace]
  have hinner : ∀ (xw : Fin n → X) (yw : Fin n → Y),
      (∑ as : Fin n → A, ∑ bs : Fin n → B, ∑ _c : Fin n → Fin den,
        coinWeight G Trep den (xw, yw, as, bs, _c))
        = ∏ j : Fin n, G.questionWeight (xw j) (yw j) := by
    intro xw yw
    simp only [coinWeight]
    have h1 : ∀ (as : Fin n → A) (bs : Fin n → B),
        (∑ _c : Fin n → Fin den,
          (∏ j : Fin n, G.questionWeight (xw j) (yw j)) * Trep.correlation xw yw as bs *
            (1 / (den : ℝ)) ^ n)
        = (∏ j : Fin n, G.questionWeight (xw j) (yw j)) * Trep.correlation xw yw as bs := by
      intro as bs
      rw [← Finset.mul_sum, sum_coin_uniform den hden, mul_one]
    simp only [h1]
    simp only [← Finset.mul_sum]
    rw [Trep.correlation_sum' xw yw, mul_one]
  simp only [hinner]
  exact G.weight_normalized.symm ▸ (Game.repeat G n).weight_normalized

/-- The private-coin law. -/
noncomputable def coinLaw (den : ℕ) (hden : 0 < den) : FiniteEventLaw (CoinSpace n den X Y A B) where
  weight := coinWeight G Trep den
  weight_nonneg := coinWeight_nonneg G Trep den
  weight_sum := coinWeight_sum G Trep den hden

/-- Coordinate `i` accepts when its coin falls below the payoff numerator. -/
def coinWins (den : ℕ) (num : X → Y → A → B → ℕ) (i : Fin n) (ω : CoinSpace n den X Y A B) :
    Bool :=
  decide ((ω.2.2.2.2 i : ℕ) < num (ω.1 i) (ω.2.1 i) (ω.2.2.1 i) (ω.2.2.2.1 i))

/-- The number of coin values accepting at threshold `k ≤ den`. -/
theorem sum_coin_accept (den k : ℕ) (hk : k ≤ den) :
    (∑ v : Fin den, (if (v : ℕ) < k then (1 : ℝ) else 0)) = k := by
  rw [Finset.sum_boole]
  have := Fin.card_filter_val_lt (n := den) (m := k)
  rw [this, min_eq_right hk]

/-- **Integrating out the coins**: the mass of the acceptance event on a set
of coordinates is the coin-free weighted sum. -/
theorem coinLaw_eventMass (den : ℕ) (hden : 0 < den) (num : X → Y → A → B → ℕ)
    (hnum : ∀ x y a b, num x y a b ≤ den) (S : Finset (Fin n)) :
    (coinLaw G Trep den hden).eventMass
        (FiniteEventLaw.winEvent (coinWins den num) S)
      = ∑ xw : Fin n → X, ∑ yw : Fin n → Y, ∑ as : Fin n → A, ∑ bs : Fin n → B,
          (∏ j : Fin n, G.questionWeight (xw j) (yw j)) * Trep.correlation xw yw as bs *
            ∏ j ∈ S, (num (xw j) (yw j) (as j) (bs j) : ℝ) / den := by
  classical
  unfold FiniteEventLaw.eventMass FiniteEventLaw.winEvent
  rw [Finset.sum_filter, sum_coinSpace]
  refine Finset.sum_congr rfl fun xw _ => Finset.sum_congr rfl fun yw _ =>
    Finset.sum_congr rfl fun as _ => Finset.sum_congr rfl fun bs _ => ?_
  -- The coin sum.
  have hind : ∀ (c : Fin n → Fin den)
      (inst : Decidable (∀ i ∈ S, coinWins den num i (xw, yw, as, bs, c) = true)),
      (@ite _ (∀ i ∈ S, coinWins den num i (xw, yw, as, bs, c) = true) inst
          ((coinLaw G Trep den hden).weight (xw, yw, as, bs, c)) 0)
        = (∏ j : Fin n, G.questionWeight (xw j) (yw j)) * Trep.correlation xw yw as bs *
            ∏ j : Fin n, ((1 / (den : ℝ)) *
              if j ∈ S then (if ((c j : ℕ) < num (xw j) (yw j) (as j) (bs j)) then 1 else 0)
              else 1) := by
    intro c inst
    simp only [coinLaw, coinWins, decide_eq_true_eq, coinWeight]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    by_cases h : ∀ i ∈ S, (c i : ℕ) < num (xw i) (yw i) (as i) (bs i)
    · rw [if_pos h]
      have : (∏ j : Fin n, if j ∈ S then
          (if ((c j : ℕ) < num (xw j) (yw j) (as j) (bs j)) then (1 : ℝ) else 0) else 1) = 1 := by
        refine Finset.prod_eq_one fun j _ => ?_
        by_cases hj : j ∈ S
        · rw [if_pos hj, if_pos (h j hj)]
        · rw [if_neg hj]
      rw [this, mul_one]
    · rw [if_neg h]
      have h' : ∃ j ∈ S, ¬ ((c j : ℕ) < num (xw j) (yw j) (as j) (bs j)) := by
        by_contra hc
        exact h fun j hj => by
          by_contra hne
          exact hc ⟨j, hj, hne⟩
      obtain ⟨j, hj, hne⟩ := h'
      have hz : (∏ j : Fin n, if j ∈ S then
          (if ((c j : ℕ) < num (xw j) (yw j) (as j) (bs j)) then (1 : ℝ) else 0) else 1) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ j) (by rw [if_pos hj, if_neg hne])
      rw [hz]
      ring
  simp only [hind]
  rw [← Finset.mul_sum]
  congr 1
  have hps := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset (Fin den)))
    (fun j v => (1 / (den : ℝ)) *
      if j ∈ S then (if ((v : ℕ) < num (xw j) (yw j) (as j) (bs j)) then (1 : ℝ) else 0) else 1)
  rw [Fintype.piFinset_univ] at hps
  rw [← hps, ← Finset.prod_ite_mem_eq S]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hj : j ∈ S
  · simp only [if_pos hj, ← Finset.mul_sum]
    rw [sum_coin_accept den _ (hnum _ _ _ _)]
    ring
  · simp only [if_neg hj, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have : (den : ℝ) ≠ 0 := by exact_mod_cast hden.ne'
    field_simp

/-- The all-coordinates acceptance mass is the repeated win probability. -/
theorem coinLaw_eventMass_univ (den : ℕ) (hden : 0 < den) (num : X → Y → A → B → ℕ)
    (hnum : ∀ x y a b, num x y a b ≤ den)
    (hV : ∀ x y a b, G.payoff x y a b = (num x y a b : ℝ) / den) :
    (coinLaw G Trep den hden).eventMass
        (FiniteEventLaw.winEvent (coinWins den num) Finset.univ)
      = (G.«repeat» n).win Trep.correlation := by
  rw [coinLaw_eventMass G Trep den hden num hnum]
  unfold Game.win
  refine Finset.sum_congr rfl fun xw _ => Finset.sum_congr rfl fun yw _ =>
    Finset.sum_congr rfl fun as _ => Finset.sum_congr rfl fun bs _ => ?_
  show (∏ j : Fin n, G.questionWeight (xw j) (yw j)) * Trep.correlation xw yw as bs *
      ∏ j ∈ Finset.univ, (num (xw j) (yw j) (as j) (bs j) : ℝ) / den
    = (∏ j : Fin n, G.questionWeight (xw j) (yw j)) *
      (∏ j : Fin n, G.payoff (xw j) (yw j) (as j) (bs j)) * Trep.correlation xw yw as bs
  simp only [hV]
  ring

end CommutingRepetition
