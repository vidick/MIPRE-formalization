/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Prerounding/HistoryA.lean
-/
/-
# Pre-rounding: the history relative-entropy bound, Alice side (node 1.2.10)

Proof-side layer for the first conjunct of `history_relative_entropy`
(05_prerounding.tex, eqs JA-chain-rule, first-history-chain-term,
bob-block-conditioning-budget, bob-block-chain-rule,
second-history-chain-term). The flattened posterior `ℚ` and the locally
generated law `J_A` are compared through the log-sum, which splits pointwise
into the live-question term (bounded through tensorization of the core
posterior's question marginals by `t₀/m`) and the conditional live-answer
term (the Bob reverse experiment: the reveal datum re-read as a Bob base and
an interior cut, the cut sum telescoping into one conditional relative
entropy at the full Alice block, bounded by `t₀ + s₀`, with the size-biased
factor `2/m`). Nothing here is a manuscript statement.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Prerounding.HistoryCore

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped BigOperators InnerProductSpace

set_option linter.unusedSectionVars false

variable {n : ℕ} {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]

/-! ### Order prefixes: the full block and position sums -/

theorem ordPrefix_card {L : Finset (Fin n)} (π : Fin L.card ≃ {j : Fin n // j ∈ L}) :
    ordPrefix π L.card = L := by
  ext c
  simp only [ordPrefix, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨t, -, rfl⟩
    exact (π t).2
  · intro hc
    exact ⟨π.symm ⟨c, hc⟩, (π.symm ⟨c, hc⟩).isLt, by simp⟩

/-- A sum over the positions of an order is a sum over the block. -/
theorem sum_ordPositions {L : Finset (Fin n)} (π : Fin L.card ≃ {j : Fin n // j ∈ L})
    (f : Fin n → ℝ) :
    (∑ k : Fin L.card, f (π k)) = ∑ j ∈ L, f j := by
  rw [Equiv.sum_comp π (fun c : {j : Fin n // j ∈ L} => f c)]
  exact Finset.sum_coe_sort L f

namespace AliceBase

variable {D : Finset (Fin n)} (b : AliceBase n D)

theorem SA_union_LYp : b.SA ∪ b.LYp = Finset.univ := by
  ext j
  simp only [Finset.mem_univ, iff_true, Finset.mem_union, Finset.mem_sdiff, Finset.mem_compl]
  by_cases hD : j ∈ D
  · exact Or.inl (Or.inl hD)
  · by_cases hL : j ∈ b.1.1
    · exact Or.inl (Or.inr hL)
    · exact Or.inr ⟨hD, hL⟩

theorem SB_sdiff_SA : b.SB \ b.SA = b.LYp := by
  ext j
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_compl]
  constructor
  · rintro ⟨h1, h2⟩
    rcases h1 with (hD | hL) | hp
    · exact absurd (Or.inl hD) h2
    · exact hL
    · exact absurd (Or.inr (ordPrefix_subset _ _ hp)) h2
  · rintro ⟨hD, hL⟩
    exact ⟨Or.inl (Or.inr ⟨hD, hL⟩), fun h => h.elim hD hL⟩

end AliceBase

namespace TracialStrategy

variable [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
variable (S : TracialStrategy.{0}
  (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B))
variable {D : Finset (Fin n)}
variable {Af Bf : Type} [Fintype Af] [Fintype Bf]

/-- The Alice question marginal `μ_X`. -/
noncomputable def margX (μ : X → Y → ℝ) (x : X) : ℝ := ∑ y : Y, μ x y

theorem margX_nonneg (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y) (x : X) : 0 ≤ margX μ x :=
  Finset.sum_nonneg fun y _ => hμ x y

theorem mu_le_margX (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y) (x : X) (y : Y) :
    μ x y ≤ margX μ x :=
  Finset.single_le_sum (f := fun y => μ x y) (fun y _ => hμ x y) (Finset.mem_univ y)

theorem sum_margX (μ : X → Y → ℝ) (hμsum : (∑ x : X, ∑ y : Y, μ x y) = 1) :
    (∑ x : X, margX μ x) = 1 := hμsum

/-! ### The Bob-block conditional bound (eqs bob-block-conditioning-budget,
bob-block-chain-rule) -/

/-- The total prior mass over core tuples is the number of core words. -/
theorem sum_prodPrior (μ : X → Y → ℝ) (hμsum : (∑ x : X, ∑ y : Y, μ x y) = 1) :
    (∑ s : CoreTuple n X Y A B D, prodPrior D μ s)
      = ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)) ^ D.card := by
  have hz : ∀ (xw : Fin n → X) (yw : Fin n → Y),
      (∑ _zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
        ∏ j, μ (xw j) (yw j))
        = ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)) ^ D.card * ∏ j, μ (xw j) (yw j) := by
    intro xw yw
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod, Fintype.card_fun,
      Fintype.card_fun, Fintype.card_coe]
    push_cast
    ring
  calc (∑ s : CoreTuple n X Y A B D, prodPrior D μ s)
      = ∑ xw : Fin n → X, ∑ yw : Fin n → Y,
          ∑ _zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
            ∏ j, μ (xw j) (yw j) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun xw _ => ?_
        rw [Fintype.sum_prod_type]
        rfl
    _ = ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)) ^ D.card *
          ∑ xw : Fin n → X, ∑ yw : Fin n → Y, ∏ j, μ (xw j) (yw j) := by
        simp only [hz, Finset.mul_sum]
    _ = _ := by rw [sum_prod_mu_eq_one μ hμsum, mul_one]

theorem cardZ_pos : (0 : ℝ) < ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)) ^ D.card := by
  have hA : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos (α := A)
  have hB : (0 : ℝ) < Fintype.card B := by exact_mod_cast Fintype.card_pos (α := B)
  positivity

/-- **The block conditional bound**: at a fixed Alice set `SX` and a Bob
background `SY` covering the rest, the core-posterior expectation of the
log-ratio of the class masses at the full Bob word against the background,
minus the product-prior conditional, is at most `t₀ + s₀` — the chain rule
`D(ℚ⁰_{class} ‖ P_{class}) − D(ℚ⁰_{background} ‖ P_{background})`, the
first term bounded pointwise by `log(1/p)` and the second by Gibbs. -/
theorem blockBound (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (hμsum : (∑ x : X, ∑ y : Y, μ x y) = 1)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB)
    (hw1 : ∀ xw yw zA zB, w xw yw zA zB ≤ 1)
    {p : ℝ} (hp : p = S.coreMass D μ w) (hppos : 0 < p)
    (SX SY : Finset (Fin n)) (hcov : SX ∪ SY = Finset.univ)
    (L : Finset (Fin n)) (hL : L = SX \ SY) (π : Fin L.card ≃ {j : Fin n // j ∈ L}) :
    (∑ s : CoreTuple n X Y A B D, S.corePost D μ w p s *
      (Real.log (classMass SX Finset.univ (S.corePost D μ w p) s /
          classMass SX SY (S.corePost D μ w p) s)
        - ∑ k : Fin L.card,
            Real.log (μ (s.1 (π k)) (s.2.1 (π k)) / margX μ (s.1 (π k)))))
      ≤ Real.log p⁻¹ + (D.card : ℝ) *
          Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)) := by
  classical
  set Q := S.corePost D μ w p with hQ
  have hQ0 : ∀ s, 0 ≤ Q s := S.corePost_nonneg D μ hμ w hw0 hppos
  have hQ1 : (∑ s, Q s) = 1 := S.sum_corePost D μ w hp hppos
  have hP0 : ∀ s : CoreTuple n X Y A B D, 0 ≤ prodPrior D μ s := prodPrior_nonneg D μ hμ
  have hQP : ∀ s, Q s ≤ p⁻¹ * prodPrior D μ s := S.corePost_le D μ hμ w hw0 hw1 hppos
  have hcard := sum_prodPrior (D := D) (A := A) (B := B) μ hμsum
  have hZpos : (0 : ℝ) < ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)) ^ D.card :=
    cardZ_pos (D := D)
  have hG1 : (∑ s, Q s * Real.log (classMass SX Finset.univ Q s /
      classMass SX Finset.univ (prodPrior D μ) s)) ≤ Real.log p⁻¹ := by
    have := HistoryKL.sum_mul_log_class_le (classMap SX Finset.univ) Q (prodPrior D μ)
      (inv_pos.mpr hppos) hQ0 hQP hQ1
    simpa only [classMass_eq_sum_ite] using this
  have hG2 : - Real.log (∑ s : CoreTuple n X Y A B D, prodPrior D μ s)
      ≤ ∑ s, Q s * Real.log (classMass SX SY Q s / classMass SX SY (prodPrior D μ) s) := by
    have habs : ∀ s, prodPrior D μ s = 0 → Q s = 0 := by
      intro s hs
      simp only [hQ, corePost, hs, zero_mul, zero_div]
    have := HistoryKL.neg_log_le_sum_mul_log_class (classMap SX SY) Q (prodPrior D μ)
      hQ0 hP0 habs hQ1 (by rw [hcard]; exact hZpos)
    simpa only [classMass_eq_sum_ite] using this
  have hterm : ∀ s, Q s * (Real.log (classMass SX Finset.univ Q s / classMass SX SY Q s)
        - ∑ k : Fin L.card, Real.log (μ (s.1 (π k)) (s.2.1 (π k)) / margX μ (s.1 (π k))))
      = Q s * Real.log (classMass SX Finset.univ Q s /
          classMass SX Finset.univ (prodPrior D μ) s)
        - Q s * Real.log (classMass SX SY Q s / classMass SX SY (prodPrior D μ) s) := by
    intro s
    rcases (hQ0 s).lt_or_eq with hs | hs
    · have hPs : 0 < prodPrior D μ s := S.prodPrior_pos_of_corePost_pos D μ hμ w p s hs
      have hN1 : 0 < classMass SX Finset.univ Q s :=
        lt_of_lt_of_le hs (le_classMass _ _ Q hQ0 s)
      have hN2 : 0 < classMass SX SY Q s := lt_of_lt_of_le hs (le_classMass _ _ Q hQ0 s)
      have hP1 : 0 < classMass SX Finset.univ (prodPrior D μ) s :=
        lt_of_lt_of_le hPs (le_classMass _ _ _ hP0 s)
      have hP2 : 0 < classMass SX SY (prodPrior D μ) s :=
        lt_of_lt_of_le hPs (le_classMass _ _ _ hP0 s)
      have hμj : ∀ j, 0 < μ (s.1 j) (s.2.1 j) := S.mu_pos_of_corePost_pos D μ hμ w p s hs
      have hμX : ∀ j, 0 < margX μ (s.1 j) := fun j =>
        lt_of_lt_of_le (hμj j) (mu_le_margX μ hμ _ _)
      have hratio : classMass SX Finset.univ (prodPrior D μ) s
          = classMass SX SY (prodPrior D μ) s *
              ∏ j ∈ SX \ SY, μ (s.1 j) (s.2.1 j) / margX μ (s.1 j) :=
        classMass_prodPrior_univ_eq SX SY hcov μ s (fun j _ => (hμX j).ne')
      have hprod : (∏ j ∈ SX \ SY, μ (s.1 j) (s.2.1 j) / margX μ (s.1 j)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun j _ => (div_pos (hμj j) (hμX j)).ne'
      have hsum : (∑ k : Fin L.card, Real.log (μ (s.1 (π k)) (s.2.1 (π k)) / margX μ (s.1 (π k))))
          = Real.log (∏ j ∈ SX \ SY, μ (s.1 j) (s.2.1 j) / margX μ (s.1 j)) := by
        rw [sum_ordPositions π (fun j => Real.log (μ (s.1 j) (s.2.1 j) / margX μ (s.1 j))), hL,
          Real.log_prod (fun j _ => (div_pos (hμj j) (hμX j)).ne')]
      rw [← mul_sub]
      congr 1
      rw [hsum, Real.log_div hN1.ne' hN2.ne', Real.log_div hN1.ne' hP1.ne',
        Real.log_div hN2.ne' hP2.ne', hratio, Real.log_mul hP2.ne' hprod]
      ring
    · rw [← hs]
      simp
  calc (∑ s, Q s * (Real.log (classMass SX Finset.univ Q s / classMass SX SY Q s)
        - ∑ k : Fin L.card, Real.log (μ (s.1 (π k)) (s.2.1 (π k)) / margX μ (s.1 (π k)))))
      = (∑ s, Q s * Real.log (classMass SX Finset.univ Q s /
            classMass SX Finset.univ (prodPrior D μ) s))
          - ∑ s, Q s * Real.log (classMass SX SY Q s / classMass SX SY (prodPrior D μ) s) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun s _ => hterm s
    _ ≤ Real.log p⁻¹ - (- Real.log (∑ s : CoreTuple n X Y A B D, prodPrior D μ s)) := sub_le_sub hG1 hG2
    _ = Real.log p⁻¹ + (D.card : ℝ) * Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)) := by
        rw [hcard, Real.log_pow]
        ring

/-! ### The second chain term (Alice side): the Bob reverse experiment -/

/-- The integrand of the second chain term at datum `r`:
`log ℚ⁰(y_i ∣ X_{{i}∪C_X}, Y_{C_Y}, Z) − log μ(y_i ∣ x_i)`. -/
noncomputable def histLogA (μ : X → Y → ℝ)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (p : ℝ) (r : RevealDatum n D) (s : CoreTuple n X Y A B D) : ℝ :=
  Real.log (classMass (insert r.i r.CX) (insert r.i r.CY) (S.corePost D μ w p) s /
      classMass (insert r.i r.CX) r.CY (S.corePost D μ w p) s)
    - Real.log (μ (s.1 r.i) (s.2.1 r.i) / margX μ (s.1 r.i))

/-- **Per-base telescoped bound** (eq bob-block-chain-rule): at a fixed Bob
base the cut sum of the conditional log-ratios telescopes to the full-block
conditional, bounded by `t₀ + s₀`. -/
theorem cutSumHist_le (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (hμsum : (∑ x : X, ∑ y : Y, μ x y) = 1)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB)
    (hw1 : ∀ xw yw zA zB, w xw yw zA zB ≤ 1)
    {p : ℝ} (hp : p = S.coreMass D μ w) (hppos : 0 < p) (b : AliceBase n D) :
    (∑ k : Fin (Dᶜ \ b.1.1).card, ∑ s : CoreTuple n X Y A B D, S.corePost D μ w p s *
      (Real.log (classMass b.SB (b.SA ∪ ordPrefix b.πY ((k : ℕ) + 1)) (S.corePost D μ w p) s /
          classMass b.SB (b.SA ∪ ordPrefix b.πY (k : ℕ)) (S.corePost D μ w p) s)
        - Real.log (μ (s.1 (b.πY k)) (s.2.1 (b.πY k)) / margX μ (s.1 (b.πY k)))))
      ≤ Real.log p⁻¹ + (D.card : ℝ) *
          Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)) := by
  classical
  set Q := S.corePost D μ w p with hQ
  have hQ0 : ∀ s, 0 ≤ Q s := S.corePost_nonneg D μ hμ w hw0 hppos
  have htel : ∀ s, (∑ k : Fin (Dᶜ \ b.1.1).card, Q s *
      (Real.log (classMass b.SB (b.SA ∪ ordPrefix b.πY ((k : ℕ) + 1)) Q s /
          classMass b.SB (b.SA ∪ ordPrefix b.πY (k : ℕ)) Q s)
        - Real.log (μ (s.1 (b.πY k)) (s.2.1 (b.πY k)) / margX μ (s.1 (b.πY k)))))
      = Q s * (Real.log (classMass b.SB Finset.univ Q s / classMass b.SB b.SA Q s)
        - ∑ k : Fin (Dᶜ \ b.1.1).card,
            Real.log (μ (s.1 (b.πY k)) (s.2.1 (b.πY k)) / margX μ (s.1 (b.πY k)))) := by
    intro s
    rcases (hQ0 s).lt_or_eq with hs | hs
    · have hN : ∀ j : ℕ, 0 < classMass b.SB (b.SA ∪ ordPrefix b.πY j) Q s := fun j =>
        lt_of_lt_of_le hs (le_classMass _ _ Q hQ0 s)
      have hsum : (∑ k : Fin (Dᶜ \ b.1.1).card,
          Real.log (classMass b.SB (b.SA ∪ ordPrefix b.πY ((k : ℕ) + 1)) Q s /
            classMass b.SB (b.SA ∪ ordPrefix b.πY (k : ℕ)) Q s))
          = Real.log (classMass b.SB Finset.univ Q s / classMass b.SB b.SA Q s) := by
        have h1 := Fin.sum_univ_eq_sum_range (fun j =>
          Real.log (classMass b.SB (b.SA ∪ ordPrefix b.πY (j + 1)) Q s)
            - Real.log (classMass b.SB (b.SA ∪ ordPrefix b.πY j) Q s)) (Dᶜ \ b.1.1).card
        have h2 := Finset.sum_range_sub (fun j =>
          Real.log (classMass b.SB (b.SA ∪ ordPrefix b.πY j) Q s)) (Dᶜ \ b.1.1).card
        rw [Finset.sum_congr rfl fun k _ => Real.log_div (hN _).ne' (hN _).ne', h1, h2,
          ordPrefix_zero, Finset.union_empty, ordPrefix_card, b.SA_union_LYp,
          Real.log_div (lt_of_lt_of_le hs (le_classMass _ _ Q hQ0 s)).ne'
            (lt_of_lt_of_le hs (le_classMass _ _ Q hQ0 s)).ne']
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, hsum]
    · rw [← hs]
      simp
  rw [Finset.sum_comm, Finset.sum_congr rfl fun s _ => htel s]
  exact S.blockBound μ hμ hμsum w hw0 hw1 hp hppos b.SB b.SA
    (by rw [Finset.union_comm]; exact b.SA_union_SB) (Dᶜ \ b.1.1) b.SB_sdiff_SA.symm b.πY

/-- **The second chain term is at most `2(t₀ + s₀)/m`** (eqs
bob-block-conditioning-budget through second-history-chain-term): the reveal
datum re-read as (Bob base, interior cut), the size-biased law `(2/m)·β`, the
cut sum telescoped per base. -/
theorem secondTermA_le (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (hμsum : (∑ x : X, ∑ y : Y, μ x y) = 1)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB)
    (hw1 : ∀ xw yw zA zB, w xw yw zA zB ≤ 1)
    {p : ℝ} (hp : p = S.coreMass D μ w) (hppos : 0 < p) (hm : D.card < n) :
    (∑ r : RevealDatum n D, r.revealLaw *
      ∑ s : CoreTuple n X Y A B D, S.corePost D μ w p s * S.histLogA μ w p r s)
      ≤ 2 * (Real.log p⁻¹ + (D.card : ℝ) *
          Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ))) / ((n : ℝ) - D.card) := by
  classical
  obtain ⟨e, hlaw, hwire⟩ := bobReveal_pushforward_strong n D
  set Φ : RevealDatum n D → ℝ := fun r =>
    ∑ s : CoreTuple n X Y A B D, S.corePost D μ w p s * S.histLogA μ w p r s with hΦ
  set m : ℝ := ((n - D.card : ℕ) : ℝ) with hmdef
  have hm0 : 0 < m := by rw [hmdef]; exact_mod_cast Nat.sub_pos_of_lt hm
  set C : ℝ := Real.log p⁻¹ + (D.card : ℝ) *
    Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)) with hC
  have hΦ' : ∀ (b : AliceBase n D) (k : Fin (Dᶜ \ b.1.1).card),
      Φ (e (mkBobDatum b k)) = ∑ s : CoreTuple n X Y A B D, S.corePost D μ w p s *
        (Real.log (classMass b.SB (b.SA ∪ ordPrefix b.πY ((k : ℕ) + 1)) (S.corePost D μ w p) s /
            classMass b.SB (b.SA ∪ ordPrefix b.πY (k : ℕ)) (S.corePost D μ w p) s)
          - Real.log (μ (s.1 (b.πY k)) (s.2.1 (b.πY k)) / margX μ (s.1 (b.πY k)))) := by
    intro b k
    obtain ⟨hi, hLY, hLX, -, -, hpre, hpy⟩ := hwire (mkBobDatum b k)
    simp only [hΦ, histLogA]
    rw [(e (mkBobDatum b k)).insert_CY_of_bob b k hi hLY hpre,
      (e (mkBobDatum b k)).CY_of_bob b k hLY hpre,
      (e (mkBobDatum b k)).insert_CX_of_bob b k hi hLX hpy, hi, mkBobDatum_liveIdx,
      ordPrefix_succ, Finset.union_insert]
  calc (∑ r : RevealDatum n D, r.revealLaw * Φ r)
      = ∑ d : BobRevealDatum n D, (e d).revealLaw * Φ (e d) :=
        (Equiv.sum_comp e fun r => r.revealLaw * Φ r).symm
    _ = ∑ t : Σ b : AliceBase n D, Fin (Dᶜ \ b.1.1).card,
          (e (bobSigmaEquiv D t)).revealLaw * Φ (e (bobSigmaEquiv D t)) :=
        (Fintype.sum_equiv (bobSigmaEquiv D) _ _ fun t => rfl).symm
    _ = ∑ b : AliceBase n D, ∑ k : Fin (Dᶜ \ b.1.1).card,
          (2 / m * AliceBase.β b) * Φ (e (mkBobDatum b k)) := by
        rw [Fintype.sum_sigma]
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
        show (e (mkBobDatum b k)).revealLaw * Φ (e (mkBobDatum b k)) = _
        rw [← hlaw, mkBobDatum_law hm]
    _ = ∑ b : AliceBase n D, (2 / m * AliceBase.β b) *
          ∑ k : Fin (Dᶜ \ b.1.1).card, Φ (e (mkBobDatum b k)) :=
        Finset.sum_congr rfl fun b _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ b : AliceBase n D, (2 / m * AliceBase.β b) * C := by
        refine Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (by positivity) (AliceBase.β_nonneg b))
        rw [Finset.sum_congr rfl fun k _ => hΦ' b k]
        exact S.cutSumHist_le μ hμ hμsum w hw0 hw1 hp hppos b
    _ = 2 / m * C := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, AliceBase.sum_β D hm, mul_one]
    _ = 2 * C / ((n : ℝ) - D.card) := by
        rw [hmdef, Nat.cast_sub hm.le]
        ring

/-! ### The flattened laws: histories, live marginals, and the first chain
term -/

/-- `ℚ(h, x) = ∑_y ℚ(h, x, y)`. -/
noncomputable def histX
    {Ffam : ALabel n X Y A → Af → S.M.A}
    {Gfam : BLabel n X Y B → Bf → S.M.A}
    (R : ResolverArena S.M Ffam Gfam) (D : Finset (Fin n))
    (μ : X → Y → ℝ)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (p : ℝ) (h : PostTuple n X Y A B D) (x : X) : ℝ :=
  ∑ y : Y, S.flatQ R D μ w p (h, x, y)

/-- `ℚ(i, X_i = x) = ∑_{h : h.i = i} ℚ(h, x)`. -/
noncomputable def liveX
    {Ffam : ALabel n X Y A → Af → S.M.A}
    {Gfam : BLabel n X Y B → Bf → S.M.A}
    (R : ResolverArena S.M Ffam Gfam) (D : Finset (Fin n))
    (μ : X → Y → ℝ)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (p : ℝ) (i₀ : Fin n) (x : X) : ℝ :=
  ∑ h : PostTuple n X Y A B D, if h.1.i = i₀ then S.histX R D μ w p h x else 0

variable {Ffam : ALabel n X Y A → Af → S.M.A}
variable {Gfam : BLabel n X Y B → Bf → S.M.A}

theorem condQA_eq (R : ResolverArena S.M Ffam Gfam) (μ : X → Y → ℝ)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (p : ℝ) (i₀ : Fin n) (x : X) (h : PostTuple n X Y A B D) :
    S.condQA R D μ w p i₀ x h
      = if h.1.i = i₀ then S.histX R D μ w p h x / S.liveX R D μ w p i₀ x else 0 := rfl

theorem flatJA_eq (R : ResolverArena S.M Ffam Gfam) (μ : X → Y → ℝ)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (p : ℝ) (u : PostTuple n X Y A B D × X × Y) :
    S.flatJA R D μ w p u
      = (((n - D.card : ℕ) : ℝ))⁻¹ * μ u.2.1 u.2.2 *
          (S.histX R D μ w p u.1 u.2.1 / S.liveX R D μ w p u.1.1.i u.2.1) := by
  unfold flatJA
  rw [S.condQA_eq, if_pos rfl]

theorem histX_nonneg (R : ResolverArena S.M Ffam Gfam) (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB) {p : ℝ} (hppos : 0 < p)
    (h : PostTuple n X Y A B D) (x : X) : 0 ≤ S.histX R D μ w p h x :=
  Finset.sum_nonneg fun y _ => S.flatQ_nonneg μ hμ R w hw0 hppos _

theorem flatQ_le_histX (R : ResolverArena S.M Ffam Gfam) (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB) {p : ℝ} (hppos : 0 < p)
    (h : PostTuple n X Y A B D) (x : X) (y : Y) :
    S.flatQ R D μ w p (h, x, y) ≤ S.histX R D μ w p h x :=
  Finset.single_le_sum (f := fun y => S.flatQ R D μ w p (h, x, y))
    (fun y _ => S.flatQ_nonneg μ hμ R w hw0 hppos _) (Finset.mem_univ y)

theorem liveX_nonneg (R : ResolverArena S.M Ffam Gfam) (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB) {p : ℝ} (hppos : 0 < p)
    (i₀ : Fin n) (x : X) : 0 ≤ S.liveX R D μ w p i₀ x :=
  Finset.sum_nonneg fun h _ => by
    split_ifs
    · exact S.histX_nonneg R μ hμ w hw0 hppos h x
    · exact le_rfl

theorem histX_le_liveX (R : ResolverArena S.M Ffam Gfam) (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB) {p : ℝ} (hppos : 0 < p)
    (h : PostTuple n X Y A B D) (x : X) :
    S.histX R D μ w p h x ≤ S.liveX R D μ w p h.1.i x := by
  unfold liveX
  have := Finset.single_le_sum (f := fun h' : PostTuple n X Y A B D =>
    if h'.1.i = h.1.i then S.histX R D μ w p h' x else 0)
    (fun h' _ => by
      split_ifs
      · exact S.histX_nonneg R μ hμ w hw0 hppos h' x
      · exact le_rfl) (Finset.mem_univ h)
  simpa using this

/-- Live-coordinate mass vanishes on the core. -/
theorem liveX_eq_zero_of_mem (R : ResolverArena S.M Ffam Gfam) (μ : X → Y → ℝ)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (p : ℝ) (i₀ : Fin n) (hi₀ : i₀ ∈ D) (x : X) : S.liveX R D μ w p i₀ x = 0 :=
  Finset.sum_eq_zero fun h _ => if_neg fun (hh : h.1.i = i₀) => h.1.i_notMem (hh ▸ hi₀)

/-- Sums over the flattened space grouped by the live coordinate and the
live Alice question. -/
theorem sum_flatQ_group (R : ResolverArena S.M Ffam Gfam) (μ : X → Y → ℝ)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (p : ℝ) (F : Fin n → X → ℝ) :
    (∑ u : PostTuple n X Y A B D × X × Y, S.flatQ R D μ w p u * F u.1.1.i u.2.1)
      = ∑ i₀ : Fin n, ∑ x : X, S.liveX R D μ w p i₀ x * F i₀ x := by
  classical
  have hL : (∑ u : PostTuple n X Y A B D × X × Y, S.flatQ R D μ w p u * F u.1.1.i u.2.1)
      = ∑ h : PostTuple n X Y A B D, ∑ x : X, S.histX R D μ w p h x * F h.1.i x := by
    rw [Fintype.sum_prod_type (f := fun u : PostTuple n X Y A B D × X × Y =>
      S.flatQ R D μ w p u * F u.1.1.i u.2.1)]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Fintype.sum_prod_type (f := fun q : X × Y => S.flatQ R D μ w p (h, q) * F h.1.i q.1)]
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold histX
    rw [Finset.sum_mul]
  have hR : (∑ i₀ : Fin n, ∑ x : X, S.liveX R D μ w p i₀ x * F i₀ x)
      = ∑ x : X, ∑ h : PostTuple n X Y A B D, S.histX R D μ w p h x * F h.1.i x := by
    unfold liveX
    simp only [Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.sum_ite_eq]
    simp
  rw [hL, hR]
  exact Finset.sum_comm

/-- The Alice question marginal of the core posterior. -/
noncomputable def coreMargX (μ : X → Y → ℝ)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (p : ℝ) (xw : Fin n → X) : ℝ :=
  ∑ q : (Fin n → Y) × (({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B)),
    S.corePost D μ w p (xw, q)

theorem coreMargX_nonneg (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB) {p : ℝ} (hppos : 0 < p) (xw : Fin n → X) :
    0 ≤ S.coreMargX μ w p xw :=
  Finset.sum_nonneg fun q _ => S.corePost_nonneg D μ hμ w hw0 hppos _

theorem sum_coreMargX (μ : X → Y → ℝ)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    {p : ℝ} (hp : p = S.coreMass D μ w) (hppos : 0 < p) :
    (∑ xw : Fin n → X, S.coreMargX μ w p xw) = 1 := by
  rw [← S.sum_corePost D μ w hp hppos, Fintype.sum_prod_type]
  rfl

/-- `ℚ⁰_X ≤ p⁻¹ · μ_X^{⊗n}` (the conditioning budget for the question
marginal). -/
theorem coreMargX_le (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB)
    (hw1 : ∀ xw yw zA zB, w xw yw zA zB ≤ 1) {p : ℝ} (hppos : 0 < p) (xw : Fin n → X) :
    S.coreMargX μ w p xw ≤ p⁻¹ * ∏ j : Fin n, margX μ (xw j) := by
  unfold coreMargX
  rw [Fintype.sum_prod_type]
  calc (∑ yw : Fin n → Y, ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
        S.corePost D μ w p (xw, yw, zD))
      ≤ ∑ yw : Fin n → Y, p⁻¹ * ∏ j : Fin n, μ (xw j) (yw j) :=
        Finset.sum_le_sum fun yw _ => S.sum_zD_corePost_le D μ hμ w hw0 hw1 hppos xw yw
    _ = p⁻¹ * ∏ j : Fin n, margX μ (xw j) := by
        rw [← Finset.mul_sum]
        congr 1
        have h := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset Y))
          (fun j y => μ (xw j) y)
        rw [Fintype.piFinset_univ] at h
        unfold margX
        rw [h]

/-- The core marginal at a coordinate, as a coordinate marginal of `ℚ⁰_X`. -/
theorem sum_corePost_coord (μ : X → Y → ℝ)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (p : ℝ) (i₀ : Fin n) (x : X) :
    (∑ s : CoreTuple n X Y A B D, if s.1 i₀ = x then S.corePost D μ w p s else 0)
      = HistoryKL.coordMarginal (S.coreMargX μ w p) i₀ x := by
  unfold HistoryKL.coordMarginal coreMargX
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun xw _ => ?_
  split_ifs
  · rfl
  · exact Finset.sum_eq_zero fun _ _ => rfl

/-- **The first chain term is at most `t₀/m`** (eq first-history-chain-term):
the live marginal is `m⁻¹` times the core question marginal, and the
marginals tensorize against `μ_X`. -/
theorem firstTermA_le (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (hμsum : (∑ x : X, ∑ y : Y, μ x y) = 1)
    (R : ResolverArena S.M Ffam Gfam)
    (htotF : ∀ s : ALabel n X Y A,
      (∑ a : Af, Ffam s a) = S.setEffectA D s.1 μ s.2.1 s.2.2.1 s.2.2.2)
    (htotG : ∀ t : BLabel n X Y B,
      (∑ b : Bf, Gfam t b) = S.setEffectB D t.1 μ t.2.1 t.2.2.1 t.2.2.2)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB)
    (hw1 : ∀ xw yw zA zB, w xw yw zA zB ≤ 1)
    (hwD : ∀ (xw xw' : Fin n → X) (yw yw' : Fin n → Y) zA zB,
      agreesOn D xw xw' → agreesOn D yw yw' →
      w xw yw zA zB = w xw' yw' zA zB)
    {p : ℝ} (hp : p = S.coreMass D μ w) (hppos : 0 < p) (hm : D.card < n) :
    (∑ u : PostTuple n X Y A B D × X × Y, S.flatQ R D μ w p u *
        Real.log (S.liveX R D μ w p u.1.1.i u.2.1 * ((n - D.card : ℕ) : ℝ) / margX μ u.2.1))
      ≤ Real.log p⁻¹ / ((n : ℝ) - D.card) := by
  classical
  set m : ℝ := ((n - D.card : ℕ) : ℝ) with hmdef
  have hm0 : 0 < m := by rw [hmdef]; exact_mod_cast Nat.sub_pos_of_lt hm
  set q := S.coreMargX μ w p with hq
  have hq0 : ∀ xw, 0 ≤ q xw := S.coreMargX_nonneg μ hμ w hw0 hppos
  have hq1 : (∑ xw, q xw) = 1 := S.sum_coreMargX μ w hp hppos
  have hqK : ∀ xw, q xw ≤ p⁻¹ * ∏ j, margX μ (xw j) := S.coreMargX_le μ hμ w hw0 hw1 hppos
  -- Each coordinate marginal is absolutely continuous w.r.t. `μ_X`.
  have habs : ∀ (i₀ : Fin n) (x : X), margX μ x = 0 → HistoryKL.coordMarginal q i₀ x = 0 := by
    intro i₀ x hx
    unfold HistoryKL.coordMarginal
    refine Finset.sum_eq_zero fun xw _ => ?_
    split_ifs with hxw
    · refine le_antisymm ?_ (hq0 xw)
      refine (hqK xw).trans (le_of_eq ?_)
      rw [Finset.prod_eq_zero (Finset.mem_univ i₀) (by rw [hxw, hx]), mul_zero]
    · rfl
  -- The per-coordinate log-sums are nonnegative (Gibbs).
  have hGibbs : ∀ i₀ : Fin n, 0 ≤ ∑ x : X,
      HistoryKL.coordMarginal q i₀ x * Real.log (HistoryKL.coordMarginal q i₀ x / margX μ x) := by
    intro i₀
    have := HistoryKL.neg_log_sum_le_sum_mul_log (HistoryKL.coordMarginal q i₀) (margX μ)
      (HistoryKL.coordMarginal_nonneg q hq0 i₀) (margX_nonneg μ hμ) (habs i₀)
      (by rw [HistoryKL.sum_coordMarginal, hq1]) (by rw [sum_margX μ hμsum]; exact one_pos)
    rwa [sum_margX μ hμsum, Real.log_one, neg_zero] at this
  -- The live marginal at a non-core coordinate.
  have hlive : ∀ (i₀ : Fin n) (x : X), i₀ ∉ D →
      S.liveX R D μ w p i₀ x = m⁻¹ * HistoryKL.coordMarginal q i₀ x := by
    intro i₀ x hi₀
    unfold liveX histX
    rw [S.sum_flatQ_live μ hμ R htotF htotG w hwD p i₀ x, RevealDatum.revealLaw_sum_fiber i₀ hi₀,
      S.sum_corePost_coord μ w p i₀ x, one_div]
  rw [S.sum_flatQ_group R μ w p (fun i₀ x => Real.log (S.liveX R D μ w p i₀ x * m / margX μ x))]
  calc (∑ i₀ : Fin n, ∑ x : X, S.liveX R D μ w p i₀ x *
        Real.log (S.liveX R D μ w p i₀ x * m / margX μ x))
      ≤ ∑ i₀ : Fin n, m⁻¹ * ∑ x : X, HistoryKL.coordMarginal q i₀ x *
          Real.log (HistoryKL.coordMarginal q i₀ x / margX μ x) := by
        refine Finset.sum_le_sum fun i₀ _ => ?_
        by_cases hi₀ : i₀ ∈ D
        · rw [Finset.sum_eq_zero fun x _ => by
            rw [S.liveX_eq_zero_of_mem R μ w p i₀ hi₀ x, zero_mul]]
          exact mul_nonneg (inv_nonneg.mpr hm0.le) (hGibbs i₀)
        · rw [Finset.mul_sum]
          refine le_of_eq (Finset.sum_congr rfl fun x _ => ?_)
          rw [hlive i₀ x hi₀, show m⁻¹ * HistoryKL.coordMarginal q i₀ x * m / margX μ x
            = HistoryKL.coordMarginal q i₀ x / margX μ x from by field_simp]
          ring
    _ = m⁻¹ * ∑ i₀ : Fin n, ∑ x : X, HistoryKL.coordMarginal q i₀ x *
          Real.log (HistoryKL.coordMarginal q i₀ x / margX μ x) := by rw [Finset.mul_sum]
    _ ≤ m⁻¹ * Real.log p⁻¹ :=
        mul_le_mul_of_nonneg_left
          (HistoryKL.sum_coordMarginal_log_le q (margX μ) (inv_pos.mpr hppos) hq0 hq1
            (margX_nonneg μ hμ) hqK) (inv_nonneg.mpr hm0.le)
    _ = Real.log p⁻¹ / ((n : ℝ) - D.card) := by
        rw [hmdef, Nat.cast_sub hm.le]
        ring

/-- **The second chain term in core form**: the `ℚ`-expectation of
`log(ℚ(h,x,y) μ_X(x) / (ℚ(h,x) μ(x,y)))` is the reveal-law average of the
core integrand `histLogA`. -/
theorem secondTermA_eq (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (R : ResolverArena S.M Ffam Gfam)
    (htotF : ∀ s : ALabel n X Y A,
      (∑ a : Af, Ffam s a) = S.setEffectA D s.1 μ s.2.1 s.2.2.1 s.2.2.2)
    (htotG : ∀ t : BLabel n X Y B,
      (∑ b : Bf, Gfam t b) = S.setEffectB D t.1 μ t.2.1 t.2.2.1 t.2.2.2)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB)
    (hwD : ∀ (xw xw' : Fin n → X) (yw yw' : Fin n → Y) zA zB,
      agreesOn D xw xw' → agreesOn D yw yw' →
      w xw yw zA zB = w xw' yw' zA zB)
    {p : ℝ} (hppos : 0 < p) :
    (∑ u : PostTuple n X Y A B D × X × Y, S.flatQ R D μ w p u *
        Real.log (S.flatQ R D μ w p u * margX μ u.2.1 /
          (S.histX R D μ w p u.1 u.2.1 * μ u.2.1 u.2.2)))
      = ∑ r : RevealDatum n D, r.revealLaw *
          ∑ s : CoreTuple n X Y A B D, S.corePost D μ w p s * S.histLogA μ w p r s := by
  classical
  set φ : PostTuple n X Y A B D × X × Y → ℝ := fun u =>
    Real.log (S.flatQ R D μ w p u * margX μ u.2.1 /
      (S.histX R D μ w p u.1 u.2.1 * μ u.2.1 u.2.2)) with hφ
  have hQ0 : ∀ s, 0 ≤ S.corePost D μ w p s := S.corePost_nonneg D μ hμ w hw0 hppos
  rw [Finset.sum_congr rfl fun u _ =>
    congrArg (· * φ u) (S.flatQ_eq μ hμ R htotF htotG w hwD p u)]
  rw [HistoryKL.sum_groupedMass_mul (flattenPost (D := D))
    (fun t : PostTuple n X Y A B D => t.1.revealLaw * S.corePost D μ w p t.2) φ,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rcases (hQ0 s).lt_or_eq with hs | hs
  · have h1 := S.flatQ_flattenPost μ hμ R htotF htotG w hwD p (r, s)
    have h2 := S.sum_flatQ_hist μ hμ R htotF htotG w hwD p (r, s)
    have hrl : 0 < r.revealLaw := r.revealLaw_pos
    have hN1 : 0 < classMass (insert r.i r.CX) (insert r.i r.CY) (S.corePost D μ w p) s :=
      lt_of_lt_of_le hs (le_classMass _ _ _ hQ0 s)
    have hN2 : 0 < classMass (insert r.i r.CX) r.CY (S.corePost D μ w p) s :=
      lt_of_lt_of_le hs (le_classMass _ _ _ hQ0 s)
    have hμi : 0 < μ (s.1 r.i) (s.2.1 r.i) := S.mu_pos_of_corePost_pos D μ hμ w p s hs r.i
    have hμX : 0 < margX μ (s.1 r.i) := lt_of_lt_of_le hμi (mu_le_margX μ hμ _ _)
    simp only [hφ, histLogA]
    dsimp only [flattenPost] at h1 ⊢
    rw [h1]
    unfold histX
    rw [h2]
    rw [show r.revealLaw * classMass (insert r.i r.CX) (insert r.i r.CY) (S.corePost D μ w p) s *
        margX μ (s.1 r.i) /
        (r.revealLaw * classMass (insert r.i r.CX) r.CY (S.corePost D μ w p) s *
          μ (s.1 r.i) (s.2.1 r.i))
        = (classMass (insert r.i r.CX) (insert r.i r.CY) (S.corePost D μ w p) s /
            classMass (insert r.i r.CX) r.CY (S.corePost D μ w p) s) /
          (μ (s.1 r.i) (s.2.1 r.i) / margX μ (s.1 r.i)) from by
      field_simp]
    rw [Real.log_div (div_pos hN1 hN2).ne' (div_pos hμi hμX).ne']
    ring
  · rw [← hs]
    simp


/-! ### The Alice conjunct: absolute continuity, subnormalization, log split -/

theorem flatJA_nonneg (R : ResolverArena S.M Ffam Gfam) (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB) {p : ℝ} (hppos : 0 < p)
    (u : PostTuple n X Y A B D × X × Y) : 0 ≤ S.flatJA R D μ w p u := by
  rw [S.flatJA_eq]
  exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (hμ _ _))
    (div_nonneg (S.histX_nonneg R μ hμ w hw0 hppos _ _) (S.liveX_nonneg R μ hμ w hw0 hppos _ _))

/-- A vanishing live-question factor kills the flattened posterior. -/
theorem flatQ_eq_zero_of_mu (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (R : ResolverArena S.M Ffam Gfam)
    (htotF : ∀ s : ALabel n X Y A,
      (∑ a : Af, Ffam s a) = S.setEffectA D s.1 μ s.2.1 s.2.2.1 s.2.2.2)
    (htotG : ∀ t : BLabel n X Y B,
      (∑ b : Bf, Gfam t b) = S.setEffectB D t.1 μ t.2.1 t.2.2.1 t.2.2.2)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hwD : ∀ (xw xw' : Fin n → X) (yw yw' : Fin n → Y) zA zB,
      agreesOn D xw xw' → agreesOn D yw yw' →
      w xw yw zA zB = w xw' yw' zA zB)
    (p : ℝ) (u : PostTuple n X Y A B D × X × Y) (hu : μ u.2.1 u.2.2 = 0) :
    S.flatQ R D μ w p u = 0 := by
  classical
  rw [S.flatQ_eq μ hμ R htotF htotG w hwD p, HistoryKL.groupedMass_eq_sum_ite]
  refine Finset.sum_eq_zero fun t _ => ?_
  split_ifs with ht
  · have hx : t.2.1 t.1.i = u.2.1 := congrArg (fun v => v.2.1) ht
    have hy : t.2.2.1 t.1.i = u.2.2 := congrArg (fun v => v.2.2) ht
    rw [S.corePost_eq_zero_of_mu D μ w p t.2 t.1.i (by rw [hx, hy]; exact hu), mul_zero]
  · rfl

theorem flatQ_eq_zero_of_flatJA (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (R : ResolverArena S.M Ffam Gfam)
    (htotF : ∀ s : ALabel n X Y A,
      (∑ a : Af, Ffam s a) = S.setEffectA D s.1 μ s.2.1 s.2.2.1 s.2.2.2)
    (htotG : ∀ t : BLabel n X Y B,
      (∑ b : Bf, Gfam t b) = S.setEffectB D t.1 μ t.2.1 t.2.2.1 t.2.2.2)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB)
    (hwD : ∀ (xw xw' : Fin n → X) (yw yw' : Fin n → Y) zA zB,
      agreesOn D xw xw' → agreesOn D yw yw' →
      w xw yw zA zB = w xw' yw' zA zB)
    {p : ℝ} (hppos : 0 < p) (hm : D.card < n)
    (u : PostTuple n X Y A B D × X × Y) (hu : S.flatJA R D μ w p u = 0) :
    S.flatQ R D μ w p u = 0 := by
  obtain ⟨h, x, y⟩ := u
  rw [S.flatJA_eq] at hu
  have hm0 : (((n - D.card : ℕ) : ℝ))⁻¹ ≠ 0 := by
    have : (0 : ℝ) < ((n - D.card : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hm
    exact inv_ne_zero this.ne'
  have hQ0 := S.flatQ_nonneg μ hμ R w hw0 hppos (h, x, y)
  have hQh := S.flatQ_le_histX R μ hμ w hw0 hppos h x y
  have hhl := S.histX_le_liveX R μ hμ w hw0 hppos h x
  have hh0 := S.histX_nonneg R μ hμ w hw0 hppos h x
  rcases mul_eq_zero.mp hu with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 hm0
    · exact S.flatQ_eq_zero_of_mu μ hμ R htotF htotG w hwD p (h, x, y) h2
  · rcases div_eq_zero_iff.mp h1 with h2 | h2
    · exact le_antisymm (h2 ▸ hQh) hQ0
    · have : S.histX R D μ w p h x = 0 := le_antisymm (h2 ▸ hhl) hh0
      exact le_antisymm (this ▸ hQh) hQ0

/-- **`J_A` is subnormalized**: its total mass is `m⁻¹ ∑_x μ_X(x) · #{i ∉ D :
ℚ(i, x) > 0} ≤ 1`. -/
theorem sum_flatJA_le_one (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (hμsum : (∑ x : X, ∑ y : Y, μ x y) = 1)
    (R : ResolverArena S.M Ffam Gfam)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB) {p : ℝ} (hppos : 0 < p) (hm : D.card < n) :
    (∑ u : PostTuple n X Y A B D × X × Y, S.flatJA R D μ w p u) ≤ 1 := by
  classical
  set m : ℝ := ((n - D.card : ℕ) : ℝ) with hmdef
  have hm0 : 0 < m := by rw [hmdef]; exact_mod_cast Nat.sub_pos_of_lt hm
  have h1 : (∑ u : PostTuple n X Y A B D × X × Y, S.flatJA R D μ w p u)
      = m⁻¹ * ∑ x : X, margX μ x *
          ∑ h : PostTuple n X Y A B D, S.histX R D μ w p h x / S.liveX R D μ w p h.1.i x := by
    have hL : (∑ u : PostTuple n X Y A B D × X × Y, S.flatJA R D μ w p u)
        = ∑ h : PostTuple n X Y A B D, ∑ x : X,
            m⁻¹ * margX μ x * (S.histX R D μ w p h x / S.liveX R D μ w p h.1.i x) := by
      simp only [S.flatJA_eq]
      rw [Fintype.sum_prod_type (f := fun u : PostTuple n X Y A B D × X × Y =>
        m⁻¹ * μ u.2.1 u.2.2 * (S.histX R D μ w p u.1 u.2.1 / S.liveX R D μ w p u.1.1.i u.2.1))]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [Fintype.sum_prod_type (f := fun q : X × Y =>
        m⁻¹ * μ q.1 q.2 * (S.histX R D μ w p h q.1 / S.liveX R D μ w p h.1.i q.1))]
      refine Finset.sum_congr rfl fun x _ => ?_
      unfold margX
      rw [Finset.mul_sum, Finset.sum_mul]
    have hR : m⁻¹ * (∑ x : X, margX μ x *
          ∑ h : PostTuple n X Y A B D, S.histX R D μ w p h x / S.liveX R D μ w p h.1.i x)
        = ∑ x : X, ∑ h : PostTuple n X Y A B D,
            m⁻¹ * margX μ x * (S.histX R D μ w p h x / S.liveX R D μ w p h.1.i x) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      ring
    rw [hL, hR]
    exact Finset.sum_comm
  have hgroup : ∀ x : X, (∑ h : PostTuple n X Y A B D,
      S.histX R D μ w p h x / S.liveX R D μ w p h.1.i x)
      = ∑ i₀ : Fin n, ∑ h : PostTuple n X Y A B D,
          if h.1.i = i₀ then S.histX R D μ w p h x / S.liveX R D μ w p i₀ x else 0 := by
    intro x
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.sum_ite_eq]
    simp
  have hbound : ∀ (x : X) (i₀ : Fin n),
      (∑ h : PostTuple n X Y A B D,
        if h.1.i = i₀ then S.histX R D μ w p h x / S.liveX R D μ w p i₀ x else 0)
        ≤ if i₀ ∈ D then 0 else 1 := by
    intro x i₀
    have : (∑ h : PostTuple n X Y A B D,
        if h.1.i = i₀ then S.histX R D μ w p h x / S.liveX R D μ w p i₀ x else 0)
        = S.liveX R D μ w p i₀ x / S.liveX R D μ w p i₀ x := by
      unfold liveX
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun h _ => ?_
      split_ifs <;> simp
    rw [this]
    split_ifs with hi
    · rw [S.liveX_eq_zero_of_mem R μ w p i₀ hi x]
      simp
    · by_cases hz : S.liveX R D μ w p i₀ x = 0
      · rw [hz]; simp
      · rw [div_self hz]
  have hcount : (∑ i₀ : Fin n, (if i₀ ∈ D then (0 : ℝ) else 1)) = m := by
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul, mul_one]
    have : (Finset.univ.filter fun i₀ : Fin n => ¬ i₀ ∈ D) = Dᶜ := by
      ext i₀
      simp
    rw [this, Finset.card_compl, Fintype.card_fin, hmdef]
  have hinner : ∀ x : X, (∑ h : PostTuple n X Y A B D,
      S.histX R D μ w p h x / S.liveX R D μ w p h.1.i x) ≤ m := by
    intro x
    rw [hgroup x, ← hcount]
    exact Finset.sum_le_sum fun i₀ _ => hbound x i₀
  rw [h1]
  calc m⁻¹ * ∑ x : X, margX μ x *
        ∑ h : PostTuple n X Y A B D, S.histX R D μ w p h x / S.liveX R D μ w p h.1.i x
      ≤ m⁻¹ * ∑ x : X, margX μ x * m := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => ?_)
          (inv_nonneg.mpr hm0.le)
        exact mul_le_mul_of_nonneg_left (hinner x) (margX_nonneg μ hμ x)
    _ = 1 := by
        rw [← Finset.sum_mul, sum_margX μ hμsum, one_mul, inv_mul_cancel₀ hm0.ne']

/-- **The pointwise log split** (eq JA-chain-rule): `log(ℚ/J_A)` is the
conditional live-answer term plus the live-question term. -/
theorem logSplitA (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (R : ResolverArena S.M Ffam Gfam)
    (htotF : ∀ s : ALabel n X Y A,
      (∑ a : Af, Ffam s a) = S.setEffectA D s.1 μ s.2.1 s.2.2.1 s.2.2.2)
    (htotG : ∀ t : BLabel n X Y B,
      (∑ b : Bf, Gfam t b) = S.setEffectB D t.1 μ t.2.1 t.2.2.1 t.2.2.2)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB)
    (hwD : ∀ (xw xw' : Fin n → X) (yw yw' : Fin n → Y) zA zB,
      agreesOn D xw xw' → agreesOn D yw yw' →
      w xw yw zA zB = w xw' yw' zA zB)
    {p : ℝ} (hppos : 0 < p) (hm : D.card < n)
    (u : PostTuple n X Y A B D × X × Y) :
    S.flatQ R D μ w p u * Real.log (S.flatQ R D μ w p u / S.flatJA R D μ w p u)
      = S.flatQ R D μ w p u * Real.log (S.flatQ R D μ w p u * margX μ u.2.1 /
            (S.histX R D μ w p u.1 u.2.1 * μ u.2.1 u.2.2))
        + S.flatQ R D μ w p u *
            Real.log (S.liveX R D μ w p u.1.1.i u.2.1 * ((n - D.card : ℕ) : ℝ) / margX μ u.2.1) := by
  obtain ⟨h, x, y⟩ := u
  set m : ℝ := ((n - D.card : ℕ) : ℝ) with hmdef
  have hm0 : 0 < m := by rw [hmdef]; exact_mod_cast Nat.sub_pos_of_lt hm
  rcases (S.flatQ_nonneg μ hμ R w hw0 hppos (h, x, y)).lt_or_eq with hQ | hQ
  · have hhist : 0 < S.histX R D μ w p h x :=
      lt_of_lt_of_le hQ (S.flatQ_le_histX R μ hμ w hw0 hppos h x y)
    have hlive : 0 < S.liveX R D μ w p h.1.i x :=
      lt_of_lt_of_le hhist (S.histX_le_liveX R μ hμ w hw0 hppos h x)
    have hμxy : 0 < μ x y := by
      rcases (hμ x y).lt_or_eq with h' | h'
      · exact h'
      · exact absurd (S.flatQ_eq_zero_of_mu μ hμ R htotF htotG w hwD p (h, x, y) h'.symm) hQ.ne'
    have hμX : 0 < margX μ x := lt_of_lt_of_le hμxy (mu_le_margX μ hμ x y)
    rw [← mul_add]
    congr 1
    rw [S.flatJA_eq]
    dsimp only
    rw [show S.flatQ R D μ w p (h, x, y) /
        (m⁻¹ * μ x y * (S.histX R D μ w p h x / S.liveX R D μ w p h.1.i x))
        = (S.flatQ R D μ w p (h, x, y) * margX μ x / (S.histX R D μ w p h x * μ x y)) *
          (S.liveX R D μ w p h.1.i x * m / margX μ x) from by
      field_simp]
    rw [Real.log_mul (div_pos (mul_pos hQ hμX) (mul_pos hhist hμxy)).ne'
      (div_pos (mul_pos hlive hm0) hμX).ne']
  · rw [← hQ]
    simp

/-- **The log-sum form of the Alice conjunct**: the `ℚ`-weighted log-ratio
against the defaultless `J_A` is at most `(3t₀ + 2s₀)/m`. Consumed at assembly
(node 1.2.11) where the sampler's law dominates `J_A` up to a rounding factor. -/
theorem logSumA_le (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (hμsum : (∑ x : X, ∑ y : Y, μ x y) = 1)
    (R : ResolverArena S.M Ffam Gfam)
    (htotF : ∀ s : ALabel n X Y A,
      (∑ a : Af, Ffam s a) = S.setEffectA D s.1 μ s.2.1 s.2.2.1 s.2.2.2)
    (htotG : ∀ t : BLabel n X Y B,
      (∑ b : Bf, Gfam t b) = S.setEffectB D t.1 μ t.2.1 t.2.2.1 t.2.2.2)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB)
    (hw1 : ∀ xw yw zA zB, w xw yw zA zB ≤ 1)
    (hwD : ∀ (xw xw' : Fin n → X) (yw yw' : Fin n → Y) zA zB,
      agreesOn D xw xw' → agreesOn D yw yw' →
      w xw yw zA zB = w xw' yw' zA zB)
    {p : ℝ} (hp : p = S.coreMass D μ w) (hppos : 0 < p) (hm : D.card < n) :
    (∑ u : PostTuple n X Y A B D × X × Y,
        S.flatQ R D μ w p u * Real.log (S.flatQ R D μ w p u / S.flatJA R D μ w p u))
      ≤ (3 * Real.log p⁻¹ + 2 * ((D.card : ℝ) *
          Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)))) /
        ((n : ℝ) - D.card) := by
  have hsplit := Finset.sum_congr rfl fun u (_ : u ∈ Finset.univ) =>
    S.logSplitA μ hμ R htotF htotG w hw0 hwD hppos hm u
  rw [hsplit, Finset.sum_add_distrib, S.secondTermA_eq μ hμ R htotF htotG w hw0 hwD hppos]
  have hT2 := S.secondTermA_le μ hμ hμsum w hw0 hw1 hp hppos hm
  have hT1 := S.firstTermA_le μ hμ hμsum R htotF htotG w hw0 hw1 hwD hp hppos hm
  have hmpos : (0 : ℝ) < (n : ℝ) - D.card := by
    rw [← Nat.cast_sub hm.le]
    exact_mod_cast Nat.sub_pos_of_lt hm
  calc _
      ≤ 2 * (Real.log p⁻¹ + (D.card : ℝ) *
          Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ))) / ((n : ℝ) - D.card)
        + Real.log p⁻¹ / ((n : ℝ) - D.card) := add_le_add hT2 hT1
    _ = _ := by
        field_simp
        ring
/-- **The Alice conjunct** of `history_relative_entropy`:
`D(ℚ ‖ J_A) ≤ (3t₀ + 2s₀)/m`. -/
theorem klA_le (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (hμsum : (∑ x : X, ∑ y : Y, μ x y) = 1)
    (R : ResolverArena S.M Ffam Gfam)
    (htotF : ∀ s : ALabel n X Y A,
      (∑ a : Af, Ffam s a) = S.setEffectA D s.1 μ s.2.1 s.2.2.1 s.2.2.2)
    (htotG : ∀ t : BLabel n X Y B,
      (∑ b : Bf, Gfam t b) = S.setEffectB D t.1 μ t.2.1 t.2.2.1 t.2.2.2)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB)
    (hw1 : ∀ xw yw zA zB, w xw yw zA zB ≤ 1)
    (hwD : ∀ (xw xw' : Fin n → X) (yw yw' : Fin n → Y) zA zB,
      agreesOn D xw xw' → agreesOn D yw yw' →
      w xw yw zA zB = w xw' yw' zA zB)
    {p : ℝ} (hp : p = S.coreMass D μ w) (hppos : 0 < p) (hm : D.card < n) :
    Pinsker.finiteRelativeEntropy (S.flatQ R D μ w p) (S.flatJA R D μ w p)
      ≤ (3 * Real.log p⁻¹ + 2 * ((D.card : ℝ) *
          Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)))) /
        ((n : ℝ) - D.card) := by
  have hkl := HistoryKL.finiteRelativeEntropy_le_log_sum (S.flatQ R D μ w p) (S.flatJA R D μ w p)
    (S.flatQ_nonneg μ hμ R w hw0 hppos) (S.flatJA_nonneg R μ hμ w hw0 hppos)
    (S.flatQ_eq_zero_of_flatJA μ hμ R htotF htotG w hw0 hwD hppos hm)
    (S.sum_flatQ μ hμ R htotF htotG w hwD hp hppos hm)
    (S.sum_flatJA_le_one μ hμ hμsum R w hw0 hppos hm)
  exact hkl.trans (S.logSumA_le μ hμ hμsum R htotF htotG w hw0 hw1 hwD hp hppos hm)

end TracialStrategy

end CommutingRepetition
