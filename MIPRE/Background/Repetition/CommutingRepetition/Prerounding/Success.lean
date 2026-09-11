/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Prerounding/Success.lean
-/
/-
# Pre-rounding assembly: the ideal success via the private-coin core (node 1.2.11)

The core weight `w_D = ∏_{j∈D} V(a_j, b_j | x_j, y_j)` (eq
private-coin-core-weight) is the coin-free form of the acceptance event
`W_D` of the private-coin law: summing the core word out of `w_D · coreSucc_i`
gives the mass of `W_{D∪{i}}`, and `p = 𝔼[w_D]` is the mass of `W_D`. Together
with `sum_flatQ_idealPayoff`, the `Q`-averaged ideal payoff is the greedy
core's average conditional success `(1/m) ∑_{i∉D} P(W_{D∪{i}}) / P(W_D)`.
Nothing here is a manuscript statement.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Prerounding.IdealSuccess

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped BigOperators

set_option linter.unusedSectionVars false

variable {n : ℕ} {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]

/-- Moving the first of three finite sums to the back. -/
theorem sum_comm3 {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] (F : α → β → γ → ℝ) :
    (∑ a, ∑ b, ∑ c, F a b c) = ∑ b, ∑ c, ∑ a, F a b c := by
  calc (∑ a, ∑ b, ∑ c, F a b c) = ∑ b, ∑ a, ∑ c, F a b c := Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ a, F a b c := Finset.sum_congr rfl fun b _ => Finset.sum_comm

/-! ### Core words and their canonical extensions -/

theorem agreesOn_extendCoreA_restrict [Nonempty A] (D : Finset (Fin n)) (as : Fin n → A) :
    agreesOn D as (extendCoreA D fun j => as j.1) := by
  intro j hj
  simp [extendCoreA, hj]

theorem agreesOn_extendCoreB_restrict [Nonempty B] (D : Finset (Fin n)) (bs : Fin n → B) :
    agreesOn D bs (extendCoreB D fun j => bs j.1) := by
  intro j hj
  simp [extendCoreB, hj]

theorem eq_restrict_of_agreesOn_extendCoreA [Nonempty A] (D : Finset (Fin n))
    {as : Fin n → A} {zA : {j : Fin n // j ∈ D} → A} (h : agreesOn D as (extendCoreA D zA)) :
    zA = fun j => as j.1 := by
  funext ⟨j, hj⟩
  have := h j hj
  simp [extendCoreA, hj] at this
  exact this.symm

theorem eq_restrict_of_agreesOn_extendCoreB [Nonempty B] (D : Finset (Fin n))
    {bs : Fin n → B} {zB : {j : Fin n // j ∈ D} → B} (h : agreesOn D bs (extendCoreB D zB)) :
    zB = fun j => bs j.1 := by
  funext ⟨j, hj⟩
  have := h j hj
  simp [extendCoreB, hj] at this
  exact this.symm

/-- **Summing out the core word**: a core-indexed sum of `w(z) · (agreement
indicator)` collapses to the restriction of the answer words. -/
theorem sum_core_collapse [Nonempty A] [Nonempty B] (D : Finset (Fin n))
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (xw : Fin n → X) (yw : Fin n → Y) (T : (Fin n → A) → (Fin n → B) → ℝ) :
    (∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
        w xw yw zD.1 zD.2 * ∑ as : Fin n → A, ∑ bs : Fin n → B,
          if agreesOn D as (extendCoreA D zD.1) ∧ agreesOn D bs (extendCoreB D zD.2) then
            T as bs else 0)
      = ∑ as : Fin n → A, ∑ bs : Fin n → B,
          w xw yw (fun j => as j.1) (fun j => bs j.1) * T as bs := by
  classical
  simp only [Finset.mul_sum]
  rw [sum_comm3]
  refine Finset.sum_congr rfl fun as _ => Finset.sum_congr rfl fun bs _ => ?_
  rw [Finset.sum_eq_single ((fun j => as j.1, fun j => bs j.1) :
    ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B))]
  · rw [if_pos ⟨agreesOn_extendCoreA_restrict D as, agreesOn_extendCoreB_restrict D bs⟩]
  · intro zD _ hne
    rw [if_neg, mul_zero]
    rintro ⟨h1, h2⟩
    exact hne (Prod.ext (eq_restrict_of_agreesOn_extendCoreA D h1)
      (eq_restrict_of_agreesOn_extendCoreB D h2))
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ### The core weight of a payoff table -/

/-- The private-coin core weight `w_D(x, y, z) = ∏_{j ∈ D} V(z_j | x_j, y_j)`
(eq private-coin-core-weight). -/
noncomputable def coreW (G : Game X Y A B) (D : Finset (Fin n)) (xw : Fin n → X) (yw : Fin n → Y)
    (zA : {j : Fin n // j ∈ D} → A) (zB : {j : Fin n // j ∈ D} → B) : ℝ :=
  ∏ j : {j : Fin n // j ∈ D}, G.payoff (xw j.1) (yw j.1) (zA j) (zB j)

theorem coreW_nonneg (G : Game X Y A B) (D : Finset (Fin n)) (xw : Fin n → X) (yw : Fin n → Y)
    (zA : {j : Fin n // j ∈ D} → A) (zB : {j : Fin n // j ∈ D} → B) :
    0 ≤ coreW G D xw yw zA zB :=
  Finset.prod_nonneg fun j _ => G.payoff_nonneg _ _ _ _

theorem coreW_le_one (G : Game X Y A B) (D : Finset (Fin n)) (xw : Fin n → X) (yw : Fin n → Y)
    (zA : {j : Fin n // j ∈ D} → A) (zB : {j : Fin n // j ∈ D} → B) :
    coreW G D xw yw zA zB ≤ 1 :=
  Finset.prod_le_one (fun j _ => G.payoff_nonneg _ _ _ _) (fun j _ => G.payoff_le_one _ _ _ _)

/-- The core weight reads the question words only on `D`. -/
theorem coreW_agree (G : Game X Y A B) (D : Finset (Fin n)) :
    ∀ (xw xw' : Fin n → X) (yw yw' : Fin n → Y) zA zB,
      agreesOn D xw xw' → agreesOn D yw yw' →
      coreW G D xw yw zA zB = coreW G D xw' yw' zA zB := by
  intro xw xw' yw yw' zA zB hx hy
  unfold coreW
  exact Finset.prod_congr rfl fun j _ => by rw [hx j.1 j.2, hy j.1 j.2]

/-- The core weight at the restriction of full answer words. -/
theorem coreW_restrict (G : Game X Y A B) (D : Finset (Fin n)) (xw : Fin n → X) (yw : Fin n → Y)
    (as : Fin n → A) (bs : Fin n → B) :
    coreW G D xw yw (fun j => as j.1) (fun j => bs j.1)
      = ∏ j ∈ D, G.payoff (xw j) (yw j) (as j) (bs j) := by
  unfold coreW
  exact Finset.prod_coe_sort D fun j => G.payoff (xw j) (yw j) (as j) (bs j)

namespace TracialStrategy

variable [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
variable (S : TracialStrategy.{0}
  (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B))
variable (G : Game X Y A B)

/-- The core pairing expanded over the answer words. -/
theorem re_corePair_expand (D : Finset (Fin n)) (xw : Fin n → X) (yw : Fin n → Y)
    (zA : {j : Fin n // j ∈ D} → A) (zB : {j : Fin n // j ∈ D} → B) :
    (S.M.τ (star S.σ * (S.coreEffectA D xw (extendCoreA D zA) * S.σ *
        S.coreEffectB D yw (extendCoreB D zB)))).re
      = ∑ as : Fin n → A, ∑ bs : Fin n → B,
          if agreesOn D as (extendCoreA D zA) ∧ agreesOn D bs (extendCoreB D zB) then
            S.correlation xw yw as bs else 0 := by
  unfold coreEffectA coreEffectB
  have hexp : star S.σ *
      ((∑ as : Fin n → A, if agreesOn D as (extendCoreA D zA) then S.E xw as else 0) * S.σ *
        (∑ bs : Fin n → B, if agreesOn D bs (extendCoreB D zB) then S.F yw bs else 0))
      = ∑ as : Fin n → A, ∑ bs : Fin n → B,
          star S.σ * ((if agreesOn D as (extendCoreA D zA) then S.E xw as else 0) * S.σ *
            (if agreesOn D bs (extendCoreB D zB) then S.F yw bs else 0)) := by
    rw [Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun as _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
  rw [hexp, map_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun as _ => ?_
  rw [map_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun bs _ => ?_
  unfold correlation
  by_cases h1 : agreesOn D as (extendCoreA D zA)
  · by_cases h2 : agreesOn D bs (extendCoreB D zB)
    · simp only [if_pos h1, if_pos h2, if_pos (And.intro h1 h2)]
    · simp only [if_pos h1, if_neg h2, if_neg (fun h : _ ∧ _ => h2 h.2), mul_zero, map_zero,
        Complex.zero_re]
  · simp only [if_neg h1, if_neg (fun h : _ ∧ _ => h1 h.1), zero_mul, mul_zero, map_zero,
      Complex.zero_re]

variable {den : ℕ} {num : X → Y → A → B → ℕ}

/-- **The weighted core mass is the private-coin acceptance mass** `P(W_D)`. -/
theorem coreMass_eq_eventMass (hden : 0 < den) (hnum : ∀ x y a b, num x y a b ≤ den)
    (hV : ∀ x y a b, G.payoff x y a b = (num x y a b : ℝ) / den) (D : Finset (Fin n)) :
    S.coreMass D G.questionWeight (coreW G D)
      = (coinLaw G S den hden).eventMass
          (FiniteEventLaw.winEvent (coinWins den num) D) := by
  rw [coinLaw_eventMass G S den hden num hnum]
  unfold coreMass
  refine Finset.sum_congr rfl fun xw _ => Finset.sum_congr rfl fun yw _ => ?_
  simp only [S.re_corePair_expand]
  rw [sum_core_collapse, Finset.mul_sum]
  refine Finset.sum_congr rfl fun as _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun bs _ => ?_
  rw [coreW_restrict]
  simp only [hV]
  ring

/-- **The live success is the private-coin acceptance mass** `P(W_{D∪{i}})`. -/
theorem liveSucc_eq_eventMass (hden : 0 < den) (hnum : ∀ x y a b, num x y a b ≤ den)
    (hV : ∀ x y a b, G.payoff x y a b = (num x y a b : ℝ) / den) (D : Finset (Fin n))
    (i : Fin n) (hi : i ∉ D) :
    S.liveSucc G.questionWeight G.payoff (coreW G D) i
      = (coinLaw G S den hden).eventMass
          (FiniteEventLaw.winEvent (coinWins den num) (insert i D)) := by
  rw [coinLaw_eventMass G S den hden num hnum]
  unfold liveSucc coreSucc
  refine Finset.sum_congr rfl fun xw _ => Finset.sum_congr rfl fun yw _ => ?_
  rw [sum_core_collapse, Finset.mul_sum]
  refine Finset.sum_congr rfl fun as _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun bs _ => ?_
  rw [coreW_restrict, Finset.prod_insert hi]
  simp only [hV]
  ring

/-- **The ideal success of the package is the greedy core's average
conditional success** (05_prerounding.tex, end of the proof of prop
tracial-prerounding: "has payoff `q` by the tower property"). -/
theorem flatQ_idealPayoff_ge (hden : 0 < den) (hnum : ∀ x y a b, num x y a b ≤ den)
    (hV : ∀ x y a b, G.payoff x y a b = (num x y a b : ℝ) / den) (D : Finset (Fin n))
    (hDn : D.card ≤ n) {δ : ℝ}
    (hgreedy : 1 - δ ≤
      (1 / ((n : ℝ) - D.card)) *
        ∑ i ∈ Finset.univ \ D,
          (coinLaw G S den hden).eventMass
              (FiniteEventLaw.winEvent (coinWins den num) (insert i D)) /
            (coinLaw G S den hden).eventMass (FiniteEventLaw.winEvent (coinWins den num) D))
    (R : ResolverArena S.M (S.refinedA D G.questionWeight) (S.refinedB D G.questionWeight)) :
    1 - δ ≤ ∑ u : PostTuple n X Y A B D × X × Y,
      S.flatQ R D G.questionWeight (coreW G D)
          ((coinLaw G S den hden).eventMass (FiniteEventLaw.winEvent (coinWins den num) D)) u *
        S.idealPayoffFlat G.questionWeight G.payoff R u := by
  rw [S.sum_flatQ_idealPayoff G.questionWeight G.payoff R G.weight_nonneg G.payoff_nonneg
    G.payoff_le_one (coreW G D) (coreW_agree G D), S.sum_tupleCore,
    RevealDatum.sum_revealLaw_mul, Nat.cast_sub hDn]
  refine hgreedy.trans (le_of_eq ?_)
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [S.liveSucc_eq_eventMass G hden hnum hV D i (Finset.mem_sdiff.mp hi).2]
  ring

end TracialStrategy

end CommutingRepetition
