/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Prerounding/HistoryB.lean
-/
/-
# Pre-rounding: the history relative-entropy bound, Bob side (node 1.2.10)

The mirror of `Prerounding/HistoryA.lean` for the second conjunct of
`history_relative_entropy` (05_prerounding.tex, "the same argument with the
roles exchanged"): `J_B` conditions on the live Bob question, the first chain
term tensorizes the core posterior's Bob question marginals against `μ_Y`,
and the second chain term runs the Alice reverse experiment (the reveal datum
as an Alice base and an interior cut in the Bob block, Alice's revealed set
growing along the Bob-block order, Bob's fixed at `S_B`). Nothing here is a
manuscript statement.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Prerounding.HistoryA

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped BigOperators InnerProductSpace

set_option linter.unusedSectionVars false

variable {n : ℕ} {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]

namespace TracialStrategy

variable [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
variable (S : TracialStrategy.{0}
  (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B))
variable {D : Finset (Fin n)}
variable {Af Bf : Type} [Fintype Af] [Fintype Bf]

/-- The Bob question marginal `μ_Y`. -/
noncomputable def margY (μ : X → Y → ℝ) (y : Y) : ℝ := ∑ x : X, μ x y

theorem margY_nonneg (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y) (y : Y) : 0 ≤ margY μ y :=
  Finset.sum_nonneg fun x _ => hμ x y

theorem mu_le_margY (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y) (x : X) (y : Y) :
    μ x y ≤ margY μ y :=
  Finset.single_le_sum (f := fun x => μ x y) (fun x _ => hμ x y) (Finset.mem_univ x)

theorem sum_margY (μ : X → Y → ℝ) (hμsum : (∑ x : X, ∑ y : Y, μ x y) = 1) :
    (∑ y : Y, margY μ y) = 1 := by
  unfold margY
  rw [Finset.sum_comm]
  exact hμsum

/-- The prior class-mass ratio with the Alice set enlarged to everything:
the pinned-to-marginal ratios on `SY \ SX`. -/
theorem classMass_prodPrior_univ_eq' (SX SY : Finset (Fin n)) (hcov : SX ∪ SY = Finset.univ)
    (μ : X → Y → ℝ) (s : CoreTuple n X Y A B D)
    (hμY : ∀ j ∈ SY \ SX, (∑ x : X, μ x (s.2.1 j)) ≠ 0) :
    classMass Finset.univ SY (prodPrior D μ) s
      = classMass SX SY (prodPrior D μ) s *
          ∏ j ∈ SY \ SX, μ (s.1 j) (s.2.1 j) / ∑ x : X, μ x (s.2.1 j) := by
  rw [classMass_prodPrior, classMass_prodPrior, ← Finset.univ_inter (SY \ SX),
    ← Finset.prod_ite_mem, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hcov' : j ∉ SX → j ∈ SY := fun h => by
    have : j ∈ SX ∪ SY := by rw [hcov]; exact Finset.mem_univ j
    exact (Finset.mem_union.mp this).resolve_left h
  by_cases hY : j ∈ SY
  · by_cases hX : j ∈ SX
    · have : j ∉ SY \ SX := fun h => (Finset.mem_sdiff.mp h).2 hX
      simp [hX, hY, this]
    · have hmem : j ∈ SY \ SX := Finset.mem_sdiff.mpr ⟨hY, hX⟩
      have h0 := hμY j hmem
      simp only [hX, hY, hmem, Finset.mem_univ, if_true, if_false]
      field_simp
  · have hX : j ∈ SX := by
      by_contra h
      exact hY (hcov' h)
    have : j ∉ SY \ SX := fun h => hY (Finset.mem_sdiff.mp h).1
    simp [hX, hY, this]

/-- **The block conditional bound, Bob side**: Bob's set fixed, Alice's
enlarged to everything against the background `SX`. -/
theorem blockBoundB (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (hμsum : (∑ x : X, ∑ y : Y, μ x y) = 1)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB)
    (hw1 : ∀ xw yw zA zB, w xw yw zA zB ≤ 1)
    {p : ℝ} (hp : p = S.coreMass D μ w) (hppos : 0 < p)
    (SX SY : Finset (Fin n)) (hcov : SX ∪ SY = Finset.univ)
    (L : Finset (Fin n)) (hL : L = SY \ SX) (π : Fin L.card ≃ {j : Fin n // j ∈ L}) :
    (∑ s : CoreTuple n X Y A B D, S.corePost D μ w p s *
      (Real.log (classMass Finset.univ SY (S.corePost D μ w p) s /
          classMass SX SY (S.corePost D μ w p) s)
        - ∑ k : Fin L.card,
            Real.log (μ (s.1 (π k)) (s.2.1 (π k)) / margY μ (s.2.1 (π k)))))
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
  have hG1 : (∑ s, Q s * Real.log (classMass Finset.univ SY Q s /
      classMass Finset.univ SY (prodPrior D μ) s)) ≤ Real.log p⁻¹ := by
    have := HistoryKL.sum_mul_log_class_le (classMap Finset.univ SY) Q (prodPrior D μ)
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
  have hterm : ∀ s, Q s * (Real.log (classMass Finset.univ SY Q s / classMass SX SY Q s)
        - ∑ k : Fin L.card, Real.log (μ (s.1 (π k)) (s.2.1 (π k)) / margY μ (s.2.1 (π k))))
      = Q s * Real.log (classMass Finset.univ SY Q s /
          classMass Finset.univ SY (prodPrior D μ) s)
        - Q s * Real.log (classMass SX SY Q s / classMass SX SY (prodPrior D μ) s) := by
    intro s
    rcases (hQ0 s).lt_or_eq with hs | hs
    · have hPs : 0 < prodPrior D μ s := S.prodPrior_pos_of_corePost_pos D μ hμ w p s hs
      have hN1 : 0 < classMass Finset.univ SY Q s :=
        lt_of_lt_of_le hs (le_classMass _ _ Q hQ0 s)
      have hN2 : 0 < classMass SX SY Q s := lt_of_lt_of_le hs (le_classMass _ _ Q hQ0 s)
      have hP1 : 0 < classMass Finset.univ SY (prodPrior D μ) s :=
        lt_of_lt_of_le hPs (le_classMass _ _ _ hP0 s)
      have hP2 : 0 < classMass SX SY (prodPrior D μ) s :=
        lt_of_lt_of_le hPs (le_classMass _ _ _ hP0 s)
      have hμj : ∀ j, 0 < μ (s.1 j) (s.2.1 j) := S.mu_pos_of_corePost_pos D μ hμ w p s hs
      have hμY : ∀ j, 0 < margY μ (s.2.1 j) := fun j =>
        lt_of_lt_of_le (hμj j) (mu_le_margY μ hμ _ _)
      have hratio : classMass Finset.univ SY (prodPrior D μ) s
          = classMass SX SY (prodPrior D μ) s *
              ∏ j ∈ SY \ SX, μ (s.1 j) (s.2.1 j) / margY μ (s.2.1 j) :=
        classMass_prodPrior_univ_eq' SX SY hcov μ s (fun j _ => (hμY j).ne')
      have hprod : (∏ j ∈ SY \ SX, μ (s.1 j) (s.2.1 j) / margY μ (s.2.1 j)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun j _ => (div_pos (hμj j) (hμY j)).ne'
      have hsum : (∑ k : Fin L.card, Real.log (μ (s.1 (π k)) (s.2.1 (π k)) / margY μ (s.2.1 (π k))))
          = Real.log (∏ j ∈ SY \ SX, μ (s.1 j) (s.2.1 j) / margY μ (s.2.1 j)) := by
        rw [sum_ordPositions π (fun j => Real.log (μ (s.1 j) (s.2.1 j) / margY μ (s.2.1 j))), hL,
          Real.log_prod (fun j _ => (div_pos (hμj j) (hμY j)).ne')]
      rw [← mul_sub]
      congr 1
      rw [hsum, Real.log_div hN1.ne' hN2.ne', Real.log_div hN1.ne' hP1.ne',
        Real.log_div hN2.ne' hP2.ne', hratio, Real.log_mul hP2.ne' hprod]
      ring
    · rw [← hs]
      simp
  calc (∑ s, Q s * (Real.log (classMass Finset.univ SY Q s / classMass SX SY Q s)
        - ∑ k : Fin L.card, Real.log (μ (s.1 (π k)) (s.2.1 (π k)) / margY μ (s.2.1 (π k)))))
      = (∑ s, Q s * Real.log (classMass Finset.univ SY Q s /
            classMass Finset.univ SY (prodPrior D μ) s))
          - ∑ s, Q s * Real.log (classMass SX SY Q s / classMass SX SY (prodPrior D μ) s) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun s _ => hterm s
    _ ≤ Real.log p⁻¹ - (- Real.log (∑ s : CoreTuple n X Y A B D, prodPrior D μ s)) :=
        sub_le_sub hG1 hG2
    _ = Real.log p⁻¹ + (D.card : ℝ) * Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)) := by
        rw [hcard, Real.log_pow]
        ring

/-! ### The second chain term (Bob side): the Alice reverse experiment -/

/-- The integrand of the Bob-side second chain term at datum `r`:
`log ℚ⁰(x_i ∣ X_{C_X}, Y_{{i}∪C_Y}, Z) − log μ(x_i ∣ y_i)`. -/
noncomputable def histLogB (μ : X → Y → ℝ)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (p : ℝ) (r : RevealDatum n D) (s : CoreTuple n X Y A B D) : ℝ :=
  Real.log (classMass (insert r.i r.CX) (insert r.i r.CY) (S.corePost D μ w p) s /
      classMass r.CX (insert r.i r.CY) (S.corePost D μ w p) s)
    - Real.log (μ (s.1 r.i) (s.2.1 r.i) / margY μ (s.2.1 r.i))

/-- **Per-base telescoped bound, Bob side**: Alice's set grows along the
Bob-block order at a fixed Alice base. -/
theorem cutSumHistB_le (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (hμsum : (∑ x : X, ∑ y : Y, μ x y) = 1)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB)
    (hw1 : ∀ xw yw zA zB, w xw yw zA zB ≤ 1)
    {p : ℝ} (hp : p = S.coreMass D μ w) (hppos : 0 < p) (b : AliceBase n D) :
    (∑ k : Fin (Dᶜ \ b.1.1).card, ∑ s : CoreTuple n X Y A B D, S.corePost D μ w p s *
      (Real.log (classMass (b.SA ∪ ordPrefix b.πY ((k : ℕ) + 1)) b.SB (S.corePost D μ w p) s /
          classMass (b.SA ∪ ordPrefix b.πY (k : ℕ)) b.SB (S.corePost D μ w p) s)
        - Real.log (μ (s.1 (b.πY k)) (s.2.1 (b.πY k)) / margY μ (s.2.1 (b.πY k)))))
      ≤ Real.log p⁻¹ + (D.card : ℝ) *
          Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)) := by
  classical
  set Q := S.corePost D μ w p with hQ
  have hQ0 : ∀ s, 0 ≤ Q s := S.corePost_nonneg D μ hμ w hw0 hppos
  have htel : ∀ s, (∑ k : Fin (Dᶜ \ b.1.1).card, Q s *
      (Real.log (classMass (b.SA ∪ ordPrefix b.πY ((k : ℕ) + 1)) b.SB Q s /
          classMass (b.SA ∪ ordPrefix b.πY (k : ℕ)) b.SB Q s)
        - Real.log (μ (s.1 (b.πY k)) (s.2.1 (b.πY k)) / margY μ (s.2.1 (b.πY k)))))
      = Q s * (Real.log (classMass Finset.univ b.SB Q s / classMass b.SA b.SB Q s)
        - ∑ k : Fin (Dᶜ \ b.1.1).card,
            Real.log (μ (s.1 (b.πY k)) (s.2.1 (b.πY k)) / margY μ (s.2.1 (b.πY k)))) := by
    intro s
    rcases (hQ0 s).lt_or_eq with hs | hs
    · have hN : ∀ j : ℕ, 0 < classMass (b.SA ∪ ordPrefix b.πY j) b.SB Q s := fun j =>
        lt_of_lt_of_le hs (le_classMass _ _ Q hQ0 s)
      have hsum : (∑ k : Fin (Dᶜ \ b.1.1).card,
          Real.log (classMass (b.SA ∪ ordPrefix b.πY ((k : ℕ) + 1)) b.SB Q s /
            classMass (b.SA ∪ ordPrefix b.πY (k : ℕ)) b.SB Q s))
          = Real.log (classMass Finset.univ b.SB Q s / classMass b.SA b.SB Q s) := by
        have h1 := Fin.sum_univ_eq_sum_range (fun j =>
          Real.log (classMass (b.SA ∪ ordPrefix b.πY (j + 1)) b.SB Q s)
            - Real.log (classMass (b.SA ∪ ordPrefix b.πY j) b.SB Q s)) (Dᶜ \ b.1.1).card
        have h2 := Finset.sum_range_sub (fun j =>
          Real.log (classMass (b.SA ∪ ordPrefix b.πY j) b.SB Q s)) (Dᶜ \ b.1.1).card
        rw [Finset.sum_congr rfl fun k _ => Real.log_div (hN _).ne' (hN _).ne', h1, h2,
          ordPrefix_zero, Finset.union_empty, ordPrefix_card, b.SA_union_LYp,
          Real.log_div (lt_of_lt_of_le hs (le_classMass _ _ Q hQ0 s)).ne'
            (lt_of_lt_of_le hs (le_classMass _ _ Q hQ0 s)).ne']
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, hsum]
    · rw [← hs]
      simp
  rw [Finset.sum_comm, Finset.sum_congr rfl fun s _ => htel s]
  exact S.blockBoundB μ hμ hμsum w hw0 hw1 hp hppos b.SA b.SB b.SA_union_SB
    (Dᶜ \ b.1.1) b.SB_sdiff_SA.symm b.πY

/-- **The Bob-side second chain term is at most `2(t₀ + s₀)/m`**: the reveal
datum as (Alice base, interior cut), the size-biased law `(2/m)·β`. -/
theorem secondTermB_le (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (hμsum : (∑ x : X, ∑ y : Y, μ x y) = 1)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB)
    (hw1 : ∀ xw yw zA zB, w xw yw zA zB ≤ 1)
    {p : ℝ} (hp : p = S.coreMass D μ w) (hppos : 0 < p) (hm : D.card < n) :
    (∑ r : RevealDatum n D, r.revealLaw *
      ∑ s : CoreTuple n X Y A B D, S.corePost D μ w p s * S.histLogB μ w p r s)
      ≤ 2 * (Real.log p⁻¹ + (D.card : ℝ) *
          Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ))) / ((n : ℝ) - D.card) := by
  classical
  obtain ⟨e, hlaw, hwire⟩ := aliceReveal_pushforward_strong n D
  set Φ : RevealDatum n D → ℝ := fun r =>
    ∑ s : CoreTuple n X Y A B D, S.corePost D μ w p s * S.histLogB μ w p r s with hΦ
  set m : ℝ := ((n - D.card : ℕ) : ℝ) with hmdef
  have hm0 : 0 < m := by rw [hmdef]; exact_mod_cast Nat.sub_pos_of_lt hm
  set C : ℝ := Real.log p⁻¹ + (D.card : ℝ) *
    Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)) with hC
  have hΦ' : ∀ (b : AliceBase n D) (k : Fin (Dᶜ \ b.1.1).card),
      Φ (e (mkAliceDatum b k)) = ∑ s : CoreTuple n X Y A B D, S.corePost D μ w p s *
        (Real.log (classMass (b.SA ∪ ordPrefix b.πY ((k : ℕ) + 1)) b.SB (S.corePost D μ w p) s /
            classMass (b.SA ∪ ordPrefix b.πY (k : ℕ)) b.SB (S.corePost D μ w p) s)
          - Real.log (μ (s.1 (b.πY k)) (s.2.1 (b.πY k)) / margY μ (s.2.1 (b.πY k)))) := by
    intro b k
    obtain ⟨hi, hLX, hLY, -, -, hpre, hpx⟩ := hwire (mkAliceDatum b k)
    simp only [hΦ, histLogB]
    rw [(e (mkAliceDatum b k)).insert_CX_of_alice b k hi hLX hpre,
      (e (mkAliceDatum b k)).CX_of_alice b k hLX hpre,
      (e (mkAliceDatum b k)).insert_CY_of_alice b k hi hLY hpx, hi, mkAliceDatum_liveIdx,
      ordPrefix_succ, Finset.union_insert]
  calc (∑ r : RevealDatum n D, r.revealLaw * Φ r)
      = ∑ d : AliceRevealDatum n D, (e d).revealLaw * Φ (e d) :=
        (Equiv.sum_comp e fun r => r.revealLaw * Φ r).symm
    _ = ∑ t : Σ b : AliceBase n D, Fin (Dᶜ \ b.1.1).card,
          (e (aliceSigmaEquiv D t)).revealLaw * Φ (e (aliceSigmaEquiv D t)) :=
        (Fintype.sum_equiv (aliceSigmaEquiv D) _ _ fun t => rfl).symm
    _ = ∑ b : AliceBase n D, ∑ k : Fin (Dᶜ \ b.1.1).card,
          (2 / m * AliceBase.β b) * Φ (e (mkAliceDatum b k)) := by
        rw [Fintype.sum_sigma]
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
        show (e (mkAliceDatum b k)).revealLaw * Φ (e (mkAliceDatum b k)) = _
        rw [← hlaw, mkAliceDatum_law hm]
    _ = ∑ b : AliceBase n D, (2 / m * AliceBase.β b) *
          ∑ k : Fin (Dᶜ \ b.1.1).card, Φ (e (mkAliceDatum b k)) :=
        Finset.sum_congr rfl fun b _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ b : AliceBase n D, (2 / m * AliceBase.β b) * C := by
        refine Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (by positivity) (AliceBase.β_nonneg b))
        rw [Finset.sum_congr rfl fun k _ => hΦ' b k]
        exact S.cutSumHistB_le μ hμ hμsum w hw0 hw1 hp hppos b
    _ = 2 / m * C := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, AliceBase.sum_β D hm, mul_one]
    _ = 2 * C / ((n : ℝ) - D.card) := by
        rw [hmdef, Nat.cast_sub hm.le]
        ring

/-! ### The flattened laws, Bob side -/

/-- `ℚ(h, y) = ∑_x ℚ(h, x, y)`. -/
noncomputable def histY
    {Ffam : ALabel n X Y A → Af → S.M.A}
    {Gfam : BLabel n X Y B → Bf → S.M.A}
    (R : ResolverArena S.M Ffam Gfam) (D : Finset (Fin n))
    (μ : X → Y → ℝ)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (p : ℝ) (h : PostTuple n X Y A B D) (y : Y) : ℝ :=
  ∑ x : X, S.flatQ R D μ w p (h, x, y)

/-- `ℚ(i, Y_i = y)`. -/
noncomputable def liveY
    {Ffam : ALabel n X Y A → Af → S.M.A}
    {Gfam : BLabel n X Y B → Bf → S.M.A}
    (R : ResolverArena S.M Ffam Gfam) (D : Finset (Fin n))
    (μ : X → Y → ℝ)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (p : ℝ) (i₀ : Fin n) (y : Y) : ℝ :=
  ∑ h : PostTuple n X Y A B D, if h.1.i = i₀ then S.histY R D μ w p h y else 0

variable {Ffam : ALabel n X Y A → Af → S.M.A}
variable {Gfam : BLabel n X Y B → Bf → S.M.A}

theorem condQB_eq (R : ResolverArena S.M Ffam Gfam) (μ : X → Y → ℝ)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (p : ℝ) (i₀ : Fin n) (y : Y) (h : PostTuple n X Y A B D) :
    S.condQB R D μ w p i₀ y h
      = if h.1.i = i₀ then S.histY R D μ w p h y / S.liveY R D μ w p i₀ y else 0 := rfl

theorem flatJB_eq (R : ResolverArena S.M Ffam Gfam) (μ : X → Y → ℝ)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (p : ℝ) (u : PostTuple n X Y A B D × X × Y) :
    S.flatJB R D μ w p u
      = (((n - D.card : ℕ) : ℝ))⁻¹ * μ u.2.1 u.2.2 *
          (S.histY R D μ w p u.1 u.2.2 / S.liveY R D μ w p u.1.1.i u.2.2) := by
  unfold flatJB
  rw [S.condQB_eq, if_pos rfl]

theorem histY_nonneg (R : ResolverArena S.M Ffam Gfam) (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB) {p : ℝ} (hppos : 0 < p)
    (h : PostTuple n X Y A B D) (y : Y) : 0 ≤ S.histY R D μ w p h y :=
  Finset.sum_nonneg fun x _ => S.flatQ_nonneg μ hμ R w hw0 hppos _

theorem flatQ_le_histY (R : ResolverArena S.M Ffam Gfam) (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB) {p : ℝ} (hppos : 0 < p)
    (h : PostTuple n X Y A B D) (x : X) (y : Y) :
    S.flatQ R D μ w p (h, x, y) ≤ S.histY R D μ w p h y :=
  Finset.single_le_sum (f := fun x => S.flatQ R D μ w p (h, x, y))
    (fun x _ => S.flatQ_nonneg μ hμ R w hw0 hppos _) (Finset.mem_univ x)

theorem liveY_nonneg (R : ResolverArena S.M Ffam Gfam) (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB) {p : ℝ} (hppos : 0 < p)
    (i₀ : Fin n) (y : Y) : 0 ≤ S.liveY R D μ w p i₀ y :=
  Finset.sum_nonneg fun h _ => by
    split_ifs
    · exact S.histY_nonneg R μ hμ w hw0 hppos h y
    · exact le_rfl

theorem histY_le_liveY (R : ResolverArena S.M Ffam Gfam) (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB) {p : ℝ} (hppos : 0 < p)
    (h : PostTuple n X Y A B D) (y : Y) :
    S.histY R D μ w p h y ≤ S.liveY R D μ w p h.1.i y := by
  unfold liveY
  have := Finset.single_le_sum (f := fun h' : PostTuple n X Y A B D =>
    if h'.1.i = h.1.i then S.histY R D μ w p h' y else 0)
    (fun h' _ => by
      split_ifs
      · exact S.histY_nonneg R μ hμ w hw0 hppos h' y
      · exact le_rfl) (Finset.mem_univ h)
  simpa using this

theorem liveY_eq_zero_of_mem (R : ResolverArena S.M Ffam Gfam) (μ : X → Y → ℝ)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (p : ℝ) (i₀ : Fin n) (hi₀ : i₀ ∈ D) (y : Y) : S.liveY R D μ w p i₀ y = 0 :=
  Finset.sum_eq_zero fun h _ => if_neg fun (hh : h.1.i = i₀) => h.1.i_notMem (hh ▸ hi₀)

/-- (F2, Bob) The flattened posterior summed over the live Alice question. -/
theorem sum_flatQ_histY (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
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
    (p : ℝ) (t : PostTuple n X Y A B D) :
    (∑ x : X, S.flatQ R D μ w p (histCore t, x, t.2.2.1 t.1.i))
      = t.1.revealLaw * classMass t.1.CX (insert t.1.i t.1.CY) (S.corePost D μ w p) t.2 := by
  classical
  obtain ⟨r, xw, yw, zD⟩ := t
  have hflat : ∀ x : X, (histCore (r, xw, yw, zD), x, yw r.i)
      = flattenPost (r, Function.update xw r.i x, yw, zD) := by
    intro x
    simp only [flattenPost, histCore, Function.update_self, Prod.mk.injEq, true_and, and_true]
    funext j
    unfold keepOn
    by_cases hj : j ∈ r.CX
    · rw [if_pos hj, if_pos hj, Function.update_of_ne]
      rintro rfl
      exact r.i_notMem_CX hj
    · rw [if_neg hj, if_neg hj]
  simp only [hflat, S.flatQ_flattenPost μ hμ R htotF htotG w hwD p]
  rw [← Finset.mul_sum]
  congr 1
  unfold classMass
  dsimp only
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun xw' _ => ?_
  have hiff : ∀ x : X, agreesOn (insert r.i r.CX) xw' (Function.update xw r.i x)
      ↔ xw' r.i = x ∧ agreesOn r.CX xw' xw := by
    intro x
    rw [agreesOn_insert_iff, Function.update_self]
    refine and_congr_right fun _ => ?_
    constructor
    · intro h j hj
      rw [h j hj, Function.update_of_ne]
      rintro rfl
      exact r.i_notMem_CX hj
    · intro h j hj
      rw [h j hj, Function.update_of_ne]
      rintro rfl
      exact r.i_notMem_CX hj
  simp only [hiff]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun yw' _ => ?_
  rw [Finset.sum_eq_single (xw' r.i)]
  · simp
  · intro x _ hne
    rw [if_neg]
    rintro ⟨⟨h, -⟩, -⟩
    exact hne h.symm
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- (F3, Bob) The flattened posterior mass of a live coordinate and live Bob
question. -/
theorem sum_flatQ_liveY (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
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
    (p : ℝ) (i₀ : Fin n) (y : Y) :
    (∑ h : PostTuple n X Y A B D,
      if h.1.i = i₀ then ∑ x : X, S.flatQ R D μ w p (h, x, y) else 0)
      = (∑ r : RevealDatum n D, if r.i = i₀ then r.revealLaw else 0) *
          ∑ s : CoreTuple n X Y A B D, if s.2.1 i₀ = y then S.corePost D μ w p s else 0 := by
  classical
  have hL : (∑ h : PostTuple n X Y A B D,
      if h.1.i = i₀ then ∑ x : X, S.flatQ R D μ w p (h, x, y) else 0)
      = ∑ u : PostTuple n X Y A B D × X × Y,
          S.flatQ R D μ w p u * (if u.1.1.i = i₀ ∧ u.2.2 = y then 1 else 0) := by
    rw [Fintype.sum_prod_type (f := fun u : PostTuple n X Y A B D × X × Y =>
      S.flatQ R D μ w p u * (if u.1.1.i = i₀ ∧ u.2.2 = y then (1 : ℝ) else 0))]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Fintype.sum_prod_type (f := fun q : X × Y =>
      S.flatQ R D μ w p (h, q) * (if h.1.i = i₀ ∧ q.2 = y then (1 : ℝ) else 0))]
    by_cases hi : h.1.i = i₀
    · rw [if_pos hi]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_eq_single y]
      · simp [hi]
      · intro y' _ hy'
        simp [hy']
      · intro h
        exact absurd (Finset.mem_univ y) h
    · rw [if_neg hi]
      symm
      exact Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y' _ => by simp [hi]
  rw [hL]
  simp only [S.flatQ_eq μ hμ R htotF htotG w hwD p]
  rw [HistoryKL.sum_groupedMass_mul (flattenPost (D := D))
    (fun t : PostTuple n X Y A B D => t.1.revealLaw * S.corePost D μ w p t.2)
    (fun u => if u.1.1.i = i₀ ∧ u.2.2 = y then (1 : ℝ) else 0)]
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hi : r.i = i₀
  · rw [if_pos hi, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [flattenPost, histCore, hi, true_and]
    split_ifs <;> ring
  · rw [if_neg hi, zero_mul]
    refine Finset.sum_eq_zero fun s _ => ?_
    simp [flattenPost, histCore, hi]

/-- Sums over the flattened space grouped by the live coordinate and the
live Bob question. -/
theorem sum_flatQ_groupY (R : ResolverArena S.M Ffam Gfam) (μ : X → Y → ℝ)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (p : ℝ) (F : Fin n → Y → ℝ) :
    (∑ u : PostTuple n X Y A B D × X × Y, S.flatQ R D μ w p u * F u.1.1.i u.2.2)
      = ∑ i₀ : Fin n, ∑ y : Y, S.liveY R D μ w p i₀ y * F i₀ y := by
  classical
  have hL : (∑ u : PostTuple n X Y A B D × X × Y, S.flatQ R D μ w p u * F u.1.1.i u.2.2)
      = ∑ h : PostTuple n X Y A B D, ∑ y : Y, S.histY R D μ w p h y * F h.1.i y := by
    rw [Fintype.sum_prod_type (f := fun u : PostTuple n X Y A B D × X × Y =>
      S.flatQ R D μ w p u * F u.1.1.i u.2.2)]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Fintype.sum_prod_type (f := fun q : X × Y => S.flatQ R D μ w p (h, q) * F h.1.i q.2),
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    unfold histY
    rw [Finset.sum_mul]
  have hR : (∑ i₀ : Fin n, ∑ y : Y, S.liveY R D μ w p i₀ y * F i₀ y)
      = ∑ y : Y, ∑ h : PostTuple n X Y A B D, S.histY R D μ w p h y * F h.1.i y := by
    unfold liveY
    simp only [Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.sum_ite_eq]
    simp
  rw [hL, hR]
  exact Finset.sum_comm

/-- The Bob question marginal of the core posterior. -/
noncomputable def coreMargY (μ : X → Y → ℝ)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (p : ℝ) (yw : Fin n → Y) : ℝ :=
  ∑ xw : Fin n → X, ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
    S.corePost D μ w p (xw, yw, zD)

theorem coreMargY_nonneg (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB) {p : ℝ} (hppos : 0 < p) (yw : Fin n → Y) :
    0 ≤ S.coreMargY μ w p yw :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    S.corePost_nonneg D μ hμ w hw0 hppos _

/-- The core posterior as a triple sum. -/
theorem sum_corePost_triple (f : CoreTuple n X Y A B D → ℝ) :
    (∑ s : CoreTuple n X Y A B D, f s)
      = ∑ xw : Fin n → X, ∑ yw : Fin n → Y,
          ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B), f (xw, yw, zD) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun xw _ => ?_
  rw [Fintype.sum_prod_type]

theorem sum_coreMargY (μ : X → Y → ℝ)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    {p : ℝ} (hp : p = S.coreMass D μ w) (hppos : 0 < p) :
    (∑ yw : Fin n → Y, S.coreMargY μ w p yw) = 1 := by
  rw [← S.sum_corePost D μ w hp hppos, sum_corePost_triple (S.corePost D μ w p)]
  unfold coreMargY
  exact Finset.sum_comm

/-- `ℚ⁰_Y ≤ p⁻¹ · μ_Y^{⊗n}`. -/
theorem coreMargY_le (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB)
    (hw1 : ∀ xw yw zA zB, w xw yw zA zB ≤ 1) {p : ℝ} (hppos : 0 < p) (yw : Fin n → Y) :
    S.coreMargY μ w p yw ≤ p⁻¹ * ∏ j : Fin n, margY μ (yw j) := by
  unfold coreMargY
  calc (∑ xw : Fin n → X, ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
        S.corePost D μ w p (xw, yw, zD))
      ≤ ∑ xw : Fin n → X, p⁻¹ * ∏ j : Fin n, μ (xw j) (yw j) :=
        Finset.sum_le_sum fun xw _ => S.sum_zD_corePost_le D μ hμ w hw0 hw1 hppos xw yw
    _ = p⁻¹ * ∏ j : Fin n, margY μ (yw j) := by
        rw [← Finset.mul_sum]
        congr 1
        have h := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset X))
          (fun j x => μ x (yw j))
        rw [Fintype.piFinset_univ] at h
        unfold margY
        rw [h]

theorem sum_corePost_coordY (μ : X → Y → ℝ)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (p : ℝ) (i₀ : Fin n) (y : Y) :
    (∑ s : CoreTuple n X Y A B D, if s.2.1 i₀ = y then S.corePost D μ w p s else 0)
      = HistoryKL.coordMarginal (S.coreMargY μ w p) i₀ y := by
  unfold HistoryKL.coordMarginal coreMargY
  rw [sum_corePost_triple (fun s => if s.2.1 i₀ = y then S.corePost D μ w p s else 0),
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun yw _ => ?_
  split_ifs
  · rfl
  · exact Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ => rfl

/-- **The Bob-side first chain term is at most `t₀/m`**. -/
theorem firstTermB_le (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
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
        Real.log (S.liveY R D μ w p u.1.1.i u.2.2 * ((n - D.card : ℕ) : ℝ) / margY μ u.2.2))
      ≤ Real.log p⁻¹ / ((n : ℝ) - D.card) := by
  classical
  set m : ℝ := ((n - D.card : ℕ) : ℝ) with hmdef
  have hm0 : 0 < m := by rw [hmdef]; exact_mod_cast Nat.sub_pos_of_lt hm
  set q := S.coreMargY μ w p with hq
  have hq0 : ∀ yw, 0 ≤ q yw := S.coreMargY_nonneg μ hμ w hw0 hppos
  have hq1 : (∑ yw, q yw) = 1 := S.sum_coreMargY μ w hp hppos
  have hqK : ∀ yw, q yw ≤ p⁻¹ * ∏ j, margY μ (yw j) := S.coreMargY_le μ hμ w hw0 hw1 hppos
  have habs : ∀ (i₀ : Fin n) (y : Y), margY μ y = 0 → HistoryKL.coordMarginal q i₀ y = 0 := by
    intro i₀ y hy
    unfold HistoryKL.coordMarginal
    refine Finset.sum_eq_zero fun yw _ => ?_
    split_ifs with hyw
    · refine le_antisymm ?_ (hq0 yw)
      refine (hqK yw).trans (le_of_eq ?_)
      rw [Finset.prod_eq_zero (Finset.mem_univ i₀) (by rw [hyw, hy]), mul_zero]
    · rfl
  have hGibbs : ∀ i₀ : Fin n, 0 ≤ ∑ y : Y,
      HistoryKL.coordMarginal q i₀ y * Real.log (HistoryKL.coordMarginal q i₀ y / margY μ y) := by
    intro i₀
    have := HistoryKL.neg_log_sum_le_sum_mul_log (HistoryKL.coordMarginal q i₀) (margY μ)
      (HistoryKL.coordMarginal_nonneg q hq0 i₀) (margY_nonneg μ hμ) (habs i₀)
      (by rw [HistoryKL.sum_coordMarginal, hq1]) (by rw [sum_margY μ hμsum]; exact one_pos)
    rwa [sum_margY μ hμsum, Real.log_one, neg_zero] at this
  have hlive : ∀ (i₀ : Fin n) (y : Y), i₀ ∉ D →
      S.liveY R D μ w p i₀ y = m⁻¹ * HistoryKL.coordMarginal q i₀ y := by
    intro i₀ y hi₀
    unfold liveY histY
    rw [S.sum_flatQ_liveY μ hμ R htotF htotG w hwD p i₀ y, RevealDatum.revealLaw_sum_fiber i₀ hi₀,
      S.sum_corePost_coordY μ w p i₀ y, one_div]
  rw [S.sum_flatQ_groupY R μ w p (fun i₀ y => Real.log (S.liveY R D μ w p i₀ y * m / margY μ y))]
  calc (∑ i₀ : Fin n, ∑ y : Y, S.liveY R D μ w p i₀ y *
        Real.log (S.liveY R D μ w p i₀ y * m / margY μ y))
      ≤ ∑ i₀ : Fin n, m⁻¹ * ∑ y : Y, HistoryKL.coordMarginal q i₀ y *
          Real.log (HistoryKL.coordMarginal q i₀ y / margY μ y) := by
        refine Finset.sum_le_sum fun i₀ _ => ?_
        by_cases hi₀ : i₀ ∈ D
        · rw [Finset.sum_eq_zero fun y _ => by
            rw [S.liveY_eq_zero_of_mem R μ w p i₀ hi₀ y, zero_mul]]
          exact mul_nonneg (inv_nonneg.mpr hm0.le) (hGibbs i₀)
        · rw [Finset.mul_sum]
          refine le_of_eq (Finset.sum_congr rfl fun y _ => ?_)
          rw [hlive i₀ y hi₀, show m⁻¹ * HistoryKL.coordMarginal q i₀ y * m / margY μ y
            = HistoryKL.coordMarginal q i₀ y / margY μ y from by field_simp]
          ring
    _ = m⁻¹ * ∑ i₀ : Fin n, ∑ y : Y, HistoryKL.coordMarginal q i₀ y *
          Real.log (HistoryKL.coordMarginal q i₀ y / margY μ y) := by rw [Finset.mul_sum]
    _ ≤ m⁻¹ * Real.log p⁻¹ :=
        mul_le_mul_of_nonneg_left
          (HistoryKL.sum_coordMarginal_log_le q (margY μ) (inv_pos.mpr hppos) hq0 hq1
            (margY_nonneg μ hμ) hqK) (inv_nonneg.mpr hm0.le)
    _ = Real.log p⁻¹ / ((n : ℝ) - D.card) := by
        rw [hmdef, Nat.cast_sub hm.le]
        ring

/-- **The Bob-side second chain term in core form**. -/
theorem secondTermB_eq (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
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
        Real.log (S.flatQ R D μ w p u * margY μ u.2.2 /
          (S.histY R D μ w p u.1 u.2.2 * μ u.2.1 u.2.2)))
      = ∑ r : RevealDatum n D, r.revealLaw *
          ∑ s : CoreTuple n X Y A B D, S.corePost D μ w p s * S.histLogB μ w p r s := by
  classical
  set φ : PostTuple n X Y A B D × X × Y → ℝ := fun u =>
    Real.log (S.flatQ R D μ w p u * margY μ u.2.2 /
      (S.histY R D μ w p u.1 u.2.2 * μ u.2.1 u.2.2)) with hφ
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
    have h2 := S.sum_flatQ_histY μ hμ R htotF htotG w hwD p (r, s)
    have hrl : 0 < r.revealLaw := r.revealLaw_pos
    have hN1 : 0 < classMass (insert r.i r.CX) (insert r.i r.CY) (S.corePost D μ w p) s :=
      lt_of_lt_of_le hs (le_classMass _ _ _ hQ0 s)
    have hN2 : 0 < classMass r.CX (insert r.i r.CY) (S.corePost D μ w p) s :=
      lt_of_lt_of_le hs (le_classMass _ _ _ hQ0 s)
    have hμi : 0 < μ (s.1 r.i) (s.2.1 r.i) := S.mu_pos_of_corePost_pos D μ hμ w p s hs r.i
    have hμY : 0 < margY μ (s.2.1 r.i) := lt_of_lt_of_le hμi (mu_le_margY μ hμ _ _)
    simp only [hφ, histLogB]
    dsimp only [flattenPost] at h1 ⊢
    rw [h1]
    unfold histY
    rw [h2]
    rw [show r.revealLaw * classMass (insert r.i r.CX) (insert r.i r.CY) (S.corePost D μ w p) s *
        margY μ (s.2.1 r.i) /
        (r.revealLaw * classMass r.CX (insert r.i r.CY) (S.corePost D μ w p) s *
          μ (s.1 r.i) (s.2.1 r.i))
        = (classMass (insert r.i r.CX) (insert r.i r.CY) (S.corePost D μ w p) s /
            classMass r.CX (insert r.i r.CY) (S.corePost D μ w p) s) /
          (μ (s.1 r.i) (s.2.1 r.i) / margY μ (s.2.1 r.i)) from by
      field_simp]
    rw [Real.log_div (div_pos hN1 hN2).ne' (div_pos hμi hμY).ne']
    ring
  · rw [← hs]
    simp

/-! ### The Bob conjunct -/

theorem flatJB_nonneg (R : ResolverArena S.M Ffam Gfam) (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB) {p : ℝ} (hppos : 0 < p)
    (u : PostTuple n X Y A B D × X × Y) : 0 ≤ S.flatJB R D μ w p u := by
  rw [S.flatJB_eq]
  exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (hμ _ _))
    (div_nonneg (S.histY_nonneg R μ hμ w hw0 hppos _ _) (S.liveY_nonneg R μ hμ w hw0 hppos _ _))

theorem flatQ_eq_zero_of_flatJB (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
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
    (u : PostTuple n X Y A B D × X × Y) (hu : S.flatJB R D μ w p u = 0) :
    S.flatQ R D μ w p u = 0 := by
  obtain ⟨h, x, y⟩ := u
  rw [S.flatJB_eq] at hu
  have hm0 : (((n - D.card : ℕ) : ℝ))⁻¹ ≠ 0 := by
    have : (0 : ℝ) < ((n - D.card : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hm
    exact inv_ne_zero this.ne'
  have hQ0 := S.flatQ_nonneg μ hμ R w hw0 hppos (h, x, y)
  have hQh := S.flatQ_le_histY R μ hμ w hw0 hppos h x y
  have hhl := S.histY_le_liveY R μ hμ w hw0 hppos h y
  have hh0 := S.histY_nonneg R μ hμ w hw0 hppos h y
  rcases mul_eq_zero.mp hu with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 hm0
    · exact S.flatQ_eq_zero_of_mu μ hμ R htotF htotG w hwD p (h, x, y) h2
  · rcases div_eq_zero_iff.mp h1 with h2 | h2
    · exact le_antisymm (h2 ▸ hQh) hQ0
    · have : S.histY R D μ w p h y = 0 := le_antisymm (h2 ▸ hhl) hh0
      exact le_antisymm (this ▸ hQh) hQ0

/-- **`J_B` is subnormalized**. -/
theorem sum_flatJB_le_one (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (hμsum : (∑ x : X, ∑ y : Y, μ x y) = 1)
    (R : ResolverArena S.M Ffam Gfam)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB) {p : ℝ} (hppos : 0 < p) (hm : D.card < n) :
    (∑ u : PostTuple n X Y A B D × X × Y, S.flatJB R D μ w p u) ≤ 1 := by
  classical
  set m : ℝ := ((n - D.card : ℕ) : ℝ) with hmdef
  have hm0 : 0 < m := by rw [hmdef]; exact_mod_cast Nat.sub_pos_of_lt hm
  have h1 : (∑ u : PostTuple n X Y A B D × X × Y, S.flatJB R D μ w p u)
      = m⁻¹ * ∑ y : Y, margY μ y *
          ∑ h : PostTuple n X Y A B D, S.histY R D μ w p h y / S.liveY R D μ w p h.1.i y := by
    have hL : (∑ u : PostTuple n X Y A B D × X × Y, S.flatJB R D μ w p u)
        = ∑ h : PostTuple n X Y A B D, ∑ y : Y,
            m⁻¹ * margY μ y * (S.histY R D μ w p h y / S.liveY R D μ w p h.1.i y) := by
      simp only [S.flatJB_eq]
      rw [Fintype.sum_prod_type (f := fun u : PostTuple n X Y A B D × X × Y =>
        m⁻¹ * μ u.2.1 u.2.2 * (S.histY R D μ w p u.1 u.2.2 / S.liveY R D μ w p u.1.1.i u.2.2))]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [Fintype.sum_prod_type (f := fun q : X × Y =>
        m⁻¹ * μ q.1 q.2 * (S.histY R D μ w p h q.2 / S.liveY R D μ w p h.1.i q.2)),
        Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => ?_
      unfold margY
      rw [Finset.mul_sum, Finset.sum_mul]
    have hR : m⁻¹ * (∑ y : Y, margY μ y *
          ∑ h : PostTuple n X Y A B D, S.histY R D μ w p h y / S.liveY R D μ w p h.1.i y)
        = ∑ y : Y, ∑ h : PostTuple n X Y A B D,
            m⁻¹ * margY μ y * (S.histY R D μ w p h y / S.liveY R D μ w p h.1.i y) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      ring
    rw [hL, hR]
    exact Finset.sum_comm
  have hgroup : ∀ y : Y, (∑ h : PostTuple n X Y A B D,
      S.histY R D μ w p h y / S.liveY R D μ w p h.1.i y)
      = ∑ i₀ : Fin n, ∑ h : PostTuple n X Y A B D,
          if h.1.i = i₀ then S.histY R D μ w p h y / S.liveY R D μ w p i₀ y else 0 := by
    intro y
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.sum_ite_eq]
    simp
  have hbound : ∀ (y : Y) (i₀ : Fin n),
      (∑ h : PostTuple n X Y A B D,
        if h.1.i = i₀ then S.histY R D μ w p h y / S.liveY R D μ w p i₀ y else 0)
        ≤ if i₀ ∈ D then 0 else 1 := by
    intro y i₀
    have : (∑ h : PostTuple n X Y A B D,
        if h.1.i = i₀ then S.histY R D μ w p h y / S.liveY R D μ w p i₀ y else 0)
        = S.liveY R D μ w p i₀ y / S.liveY R D μ w p i₀ y := by
      unfold liveY
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun h _ => ?_
      split_ifs <;> simp
    rw [this]
    split_ifs with hi
    · rw [S.liveY_eq_zero_of_mem R μ w p i₀ hi y]
      simp
    · by_cases hz : S.liveY R D μ w p i₀ y = 0
      · rw [hz]; simp
      · rw [div_self hz]
  have hcount : (∑ i₀ : Fin n, (if i₀ ∈ D then (0 : ℝ) else 1)) = m := by
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul, mul_one]
    have : (Finset.univ.filter fun i₀ : Fin n => ¬ i₀ ∈ D) = Dᶜ := by
      ext i₀
      simp
    rw [this, Finset.card_compl, Fintype.card_fin, hmdef]
  have hinner : ∀ y : Y, (∑ h : PostTuple n X Y A B D,
      S.histY R D μ w p h y / S.liveY R D μ w p h.1.i y) ≤ m := by
    intro y
    rw [hgroup y, ← hcount]
    exact Finset.sum_le_sum fun i₀ _ => hbound y i₀
  rw [h1]
  calc m⁻¹ * ∑ y : Y, margY μ y *
        ∑ h : PostTuple n X Y A B D, S.histY R D μ w p h y / S.liveY R D μ w p h.1.i y
      ≤ m⁻¹ * ∑ y : Y, margY μ y * m := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => ?_)
          (inv_nonneg.mpr hm0.le)
        exact mul_le_mul_of_nonneg_left (hinner y) (margY_nonneg μ hμ y)
    _ = 1 := by
        rw [← Finset.sum_mul, sum_margY μ hμsum, one_mul, inv_mul_cancel₀ hm0.ne']

/-- **The pointwise log split, Bob side**. -/
theorem logSplitB (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
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
    S.flatQ R D μ w p u * Real.log (S.flatQ R D μ w p u / S.flatJB R D μ w p u)
      = S.flatQ R D μ w p u * Real.log (S.flatQ R D μ w p u * margY μ u.2.2 /
            (S.histY R D μ w p u.1 u.2.2 * μ u.2.1 u.2.2))
        + S.flatQ R D μ w p u *
            Real.log (S.liveY R D μ w p u.1.1.i u.2.2 * ((n - D.card : ℕ) : ℝ) / margY μ u.2.2) := by
  obtain ⟨h, x, y⟩ := u
  set m : ℝ := ((n - D.card : ℕ) : ℝ) with hmdef
  have hm0 : 0 < m := by rw [hmdef]; exact_mod_cast Nat.sub_pos_of_lt hm
  rcases (S.flatQ_nonneg μ hμ R w hw0 hppos (h, x, y)).lt_or_eq with hQ | hQ
  · have hhist : 0 < S.histY R D μ w p h y :=
      lt_of_lt_of_le hQ (S.flatQ_le_histY R μ hμ w hw0 hppos h x y)
    have hlive : 0 < S.liveY R D μ w p h.1.i y :=
      lt_of_lt_of_le hhist (S.histY_le_liveY R μ hμ w hw0 hppos h y)
    have hμxy : 0 < μ x y := by
      rcases (hμ x y).lt_or_eq with h' | h'
      · exact h'
      · exact absurd (S.flatQ_eq_zero_of_mu μ hμ R htotF htotG w hwD p (h, x, y) h'.symm) hQ.ne'
    have hμY : 0 < margY μ y := lt_of_lt_of_le hμxy (mu_le_margY μ hμ x y)
    rw [← mul_add]
    congr 1
    rw [S.flatJB_eq]
    dsimp only
    rw [show S.flatQ R D μ w p (h, x, y) /
        (m⁻¹ * μ x y * (S.histY R D μ w p h y / S.liveY R D μ w p h.1.i y))
        = (S.flatQ R D μ w p (h, x, y) * margY μ y / (S.histY R D μ w p h y * μ x y)) *
          (S.liveY R D μ w p h.1.i y * m / margY μ y) from by
      field_simp]
    rw [Real.log_mul (div_pos (mul_pos hQ hμY) (mul_pos hhist hμxy)).ne'
      (div_pos (mul_pos hlive hm0) hμY).ne']
  · rw [← hQ]
    simp

/-- **The log-sum form of the Bob conjunct**: the `ℚ`-weighted log-ratio
against the defaultless `J_B` is at most `(3t₀ + 2s₀)/m`. Consumed at assembly
(node 1.2.11) where the sampler's law dominates `J_B` up to a rounding factor. -/
theorem logSumB_le (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
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
        S.flatQ R D μ w p u * Real.log (S.flatQ R D μ w p u / S.flatJB R D μ w p u))
      ≤ (3 * Real.log p⁻¹ + 2 * ((D.card : ℝ) *
          Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)))) /
        ((n : ℝ) - D.card) := by
  have hsplit := Finset.sum_congr rfl fun u (_ : u ∈ Finset.univ) =>
    S.logSplitB μ hμ R htotF htotG w hw0 hwD hppos hm u
  rw [hsplit, Finset.sum_add_distrib, S.secondTermB_eq μ hμ R htotF htotG w hw0 hwD hppos]
  have hT2 := S.secondTermB_le μ hμ hμsum w hw0 hw1 hp hppos hm
  have hT1 := S.firstTermB_le μ hμ hμsum R htotF htotG w hw0 hw1 hwD hp hppos hm
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

/-- **The Bob conjunct** of `history_relative_entropy`:
`D(ℚ ‖ J_B) ≤ (3t₀ + 2s₀)/m`. -/
theorem klB_le (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
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
    Pinsker.finiteRelativeEntropy (S.flatQ R D μ w p) (S.flatJB R D μ w p)
      ≤ (3 * Real.log p⁻¹ + 2 * ((D.card : ℝ) *
          Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)))) /
        ((n : ℝ) - D.card) := by
  have hkl := HistoryKL.finiteRelativeEntropy_le_log_sum (S.flatQ R D μ w p) (S.flatJB R D μ w p)
    (S.flatQ_nonneg μ hμ R w hw0 hppos) (S.flatJB_nonneg R μ hμ w hw0 hppos)
    (S.flatQ_eq_zero_of_flatJB μ hμ R htotF htotG w hw0 hwD hppos hm)
    (S.sum_flatQ μ hμ R htotF htotG w hwD hp hppos hm)
    (S.sum_flatJB_le_one μ hμ hμsum R w hw0 hppos hm)
  exact hkl.trans (S.logSumB_le μ hμ hμsum R htotF htotG w hw0 hw1 hwD hp hppos hm)

end TracialStrategy

end CommutingRepetition
