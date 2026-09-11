/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Prerounding/PackageAlignment.lean
-/
/-
# Pre-rounding assembly: the alignment defect of the package (node 1.2.11)

The package's vectors are the normalized branches at the labels of a history
(`uVec`, `xVec`, `yVec`). On the support of the posterior law the full branch
is nonzero, and the bar branches (one live coordinate less revealed) are
nonzero too: by the one-step reveal identity the bar effect is a
`μ(·∣x_i)`-average of full effects, one of which is the actual live branch
with positive weight. So on the support the package vectors are the arena's
candidates, and the alignment defect is the posterior-weighted candidate
distance bounded by `posterior_alignment_A/B` and `prior_alignment_bound`:
`Δ ≤ 16 (t₀ + s₀)/m`. Nothing here is a manuscript statement.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Prerounding.IdealSuccess

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
variable (μ : X → Y → ℝ)

/-! ### Positivity propagates one reveal back -/

/-- If the pairing against the effect revealed at one more coordinate `c`
(pinned at a value of positive conditional weight) is positive, so is the
pairing against the less revealed effect (Bob side). -/
theorem re_pairing_pos_of_revealB (hμ : ∀ x y, 0 ≤ μ x y) (H : S.M.A) (hH : IsPosElem H)
    (R₀ : Finset (Fin n)) (x₀ : Fin n → X) (y₀ : Fin n → Y) (zB : Fin n → B) (c : Fin n)
    (hc : c ∉ R₀) (y : Y) (hμc : 0 < μ (x₀ c) y)
    (hpos : 0 < (S.M.τ (star S.σ * (H * S.σ *
      S.setEffectB D (insert c R₀) μ x₀ (Function.update y₀ c y) zB))).re) :
    0 < (S.M.τ (star S.σ * (H * S.σ * S.setEffectB D R₀ μ x₀ y₀ zB))).re := by
  rw [S.setEffectB_reveal D R₀ μ hμ x₀ y₀ zB c hc, S.re_pairing_weightedAvg_right]
  have hnn : ∀ y' : Y, 0 ≤ μ (x₀ c) y' * (S.M.τ (star S.σ * (H * S.σ *
      S.setEffectB D (insert c R₀) μ x₀ (Function.update y₀ c y') zB))).re :=
    fun y' => mul_nonneg (hμ _ _)
      (S.M.pairing_nonneg S.σ hH (S.setEffectB_isPosElem D _ μ hμ _ _ _))
  have hsum : 0 < ∑ y' : Y, μ (x₀ c) y' * (S.M.τ (star S.σ * (H * S.σ *
      S.setEffectB D (insert c R₀) μ x₀ (Function.update y₀ c y') zB))).re :=
    lt_of_lt_of_le (mul_pos hμc hpos)
      (Finset.single_le_sum (fun y' _ => hnn y') (Finset.mem_univ y))
  have hw : 0 < ∑ y' : Y, μ (x₀ c) y' :=
    lt_of_lt_of_le hμc (Finset.single_le_sum (fun y' _ => hμ (x₀ c) y') (Finset.mem_univ y))
  exact mul_pos (inv_pos.mpr hw) hsum

/-- Alice-side mirror of `re_pairing_pos_of_revealB`. -/
theorem re_pairing_pos_of_revealA (hμ : ∀ x y, 0 ≤ μ x y) (K : S.M.A) (hK : IsPosElem K)
    (R₀ : Finset (Fin n)) (x₀ : Fin n → X) (y₀ : Fin n → Y) (zA : Fin n → A) (c : Fin n)
    (hc : c ∉ R₀) (x : X) (hμc : 0 < μ x (y₀ c))
    (hpos : 0 < (S.M.τ (star S.σ * (
      S.setEffectA D (insert c R₀) μ (Function.update x₀ c x) y₀ zA * S.σ * K))).re) :
    0 < (S.M.τ (star S.σ * (S.setEffectA D R₀ μ x₀ y₀ zA * S.σ * K))).re := by
  rw [S.setEffectA_reveal D R₀ μ hμ x₀ y₀ zA c hc, S.re_pairing_weightedAvg_left]
  have hnn : ∀ x' : X, 0 ≤ μ x' (y₀ c) * (S.M.τ (star S.σ * (
      S.setEffectA D (insert c R₀) μ (Function.update x₀ c x') y₀ zA * S.σ * K))).re :=
    fun x' => mul_nonneg (hμ _ _)
      (S.M.pairing_nonneg S.σ (S.setEffectA_isPosElem D _ μ hμ _ _ _) hK)
  have hsum : 0 < ∑ x' : X, μ x' (y₀ c) * (S.M.τ (star S.σ * (
      S.setEffectA D (insert c R₀) μ (Function.update x₀ c x') y₀ zA * S.σ * K))).re :=
    lt_of_lt_of_le (mul_pos hμc hpos)
      (Finset.single_le_sum (fun x' _ => hnn x') (Finset.mem_univ x))
  have hw : 0 < ∑ x' : X, μ x' (y₀ c) :=
    lt_of_lt_of_le hμc (Finset.single_le_sum (fun x' _ => hμ x' (y₀ c)) (Finset.mem_univ x))
  exact mul_pos (inv_pos.mpr hw) hsum

variable (R : ResolverArena S.M (S.refinedA D μ) (S.refinedB D μ))

/-! ### The bar branches are nonzero on the support -/

/-- The bar Bob branch (Bob's live coordinate unrevealed) is nonzero wherever
the full branch is nonzero and the live question pair has positive weight. -/
theorem barB_branch_ne_zero (hμ : ∀ x y, 0 ≤ μ x y) (r : RevealDatum n D)
    (xw : Fin n → X) (yw : Fin n → Y)
    (zA : {j : Fin n // j ∈ D} → A) (zB : {j : Fin n // j ∈ D} → B)
    (hμi : 0 < μ (xw r.i) (yw r.i))
    (hb : R.branch S.σ (aLabel D (insert r.i r.CX) xw yw zA)
      (bLabel D (insert r.i r.CY) xw yw zB) ≠ 0) :
    R.branch S.σ (aLabel D (insert r.i r.CX) xw yw zA) (bLabel D r.CY xw yw zB) ≠ 0 := by
  intro h0
  have hbar := S.re_pairing_setEffect μ R (aLabel D (insert r.i r.CX) xw yw zA)
    (bLabel D r.CY xw yw zB)
  rw [h0, norm_zero, zero_pow two_ne_zero] at hbar
  have hfull := S.re_pairing_setEffect μ R (aLabel D (insert r.i r.CX) xw yw zA)
    (bLabel D (insert r.i r.CY) xw yw zB)
  have hpos : 0 < ‖R.branch S.σ (aLabel D (insert r.i r.CX) xw yw zA)
      (bLabel D (insert r.i r.CY) xw yw zB)‖ ^ 2 := pow_pos (norm_pos_iff.mpr hb) 2
  rw [← hfull] at hpos
  simp only [bLabel] at hbar hpos
  have hcongr : S.setEffectB D (insert r.i r.CY) μ (keepOff r.CY xw)
      (Function.update (keepOn r.CY yw) r.i (yw r.i)) (extendCoreB D zB)
      = S.setEffectB D (insert r.i r.CY) μ (keepOff (insert r.i r.CY) xw)
          (keepOn (insert r.i r.CY) yw) (extendCoreB D zB) := by
    refine S.setEffectB_congr D _ μ _ (fun j hj => ?_) (fun j hj => ?_)
    · rw [Finset.mem_insert, not_or] at hj
      simp [keepOff, hj.1, hj.2]
    · rcases Finset.mem_insert.mp hj with rfl | hjC
      · simp [keepOn]
      · have hji : j ≠ r.i := fun h => r.i_notMem_CY (h ▸ hjC)
        simp [keepOn, Function.update_of_ne hji, hjC, hj]
  have hx0 : keepOff r.CY xw r.i = xw r.i := by simp [keepOff, r.i_notMem_CY]
  refine absurd hbar (ne_of_gt ?_)
  refine S.re_pairing_pos_of_revealB μ hμ _ (S.setEffectA_isPosElem D _ μ hμ _ _ _) r.CY
    (keepOff r.CY xw) (keepOn r.CY yw) (extendCoreB D zB) r.i r.i_notMem_CY (yw r.i)
    (by rw [hx0]; exact hμi) ?_
  rw [hcongr]
  exact hpos

/-- The bar Alice branch is nonzero wherever the full branch is nonzero and
the live question pair has positive weight. -/
theorem barA_branch_ne_zero (hμ : ∀ x y, 0 ≤ μ x y) (r : RevealDatum n D)
    (xw : Fin n → X) (yw : Fin n → Y)
    (zA : {j : Fin n // j ∈ D} → A) (zB : {j : Fin n // j ∈ D} → B)
    (hμi : 0 < μ (xw r.i) (yw r.i))
    (hb : R.branch S.σ (aLabel D (insert r.i r.CX) xw yw zA)
      (bLabel D (insert r.i r.CY) xw yw zB) ≠ 0) :
    R.branch S.σ (aLabel D r.CX xw yw zA) (bLabel D (insert r.i r.CY) xw yw zB) ≠ 0 := by
  intro h0
  have hbar := S.re_pairing_setEffect μ R (aLabel D r.CX xw yw zA)
    (bLabel D (insert r.i r.CY) xw yw zB)
  rw [h0, norm_zero, zero_pow two_ne_zero] at hbar
  have hfull := S.re_pairing_setEffect μ R (aLabel D (insert r.i r.CX) xw yw zA)
    (bLabel D (insert r.i r.CY) xw yw zB)
  have hpos : 0 < ‖R.branch S.σ (aLabel D (insert r.i r.CX) xw yw zA)
      (bLabel D (insert r.i r.CY) xw yw zB)‖ ^ 2 := pow_pos (norm_pos_iff.mpr hb) 2
  rw [← hfull] at hpos
  simp only [aLabel] at hbar hpos
  have hcongr : S.setEffectA D (insert r.i r.CX) μ
      (Function.update (keepOn r.CX xw) r.i (xw r.i)) (keepOff r.CX yw) (extendCoreA D zA)
      = S.setEffectA D (insert r.i r.CX) μ (keepOn (insert r.i r.CX) xw)
          (keepOff (insert r.i r.CX) yw) (extendCoreA D zA) := by
    refine S.setEffectA_congr D _ μ _ (fun j hj => ?_) (fun j hj => ?_)
    · rcases Finset.mem_insert.mp hj with rfl | hjC
      · simp [keepOn]
      · have hji : j ≠ r.i := fun h => r.i_notMem_CX (h ▸ hjC)
        simp [keepOn, Function.update_of_ne hji, hjC, hj]
    · rw [Finset.mem_insert, not_or] at hj
      simp [keepOff, hj.1, hj.2]
  have hy0 : keepOff r.CX yw r.i = yw r.i := by simp [keepOff, r.i_notMem_CX]
  refine absurd hbar (ne_of_gt ?_)
  refine S.re_pairing_pos_of_revealA μ hμ _ (S.setEffectB_isPosElem D _ μ hμ _ _ _) r.CX
    (keepOn r.CX xw) (keepOff r.CX yw) (extendCoreA D zA) r.i r.i_notMem_CX (xw r.i)
    (by rw [hy0]; exact hμi) ?_
  rw [hcongr]
  exact hpos

/-! ### The alignment defect -/

/-- The summand of the package's alignment defect at a flattened tuple. -/
noncomputable def alignTerm (u : PostTuple n X Y A B D × X × Y) : ℝ :=
  ‖S.uVec μ R (u.1, u.2.1) (u.1, u.2.2) - S.xVec μ R (u.1, u.2.1)‖ ^ 2 +
    ‖S.uVec μ R (u.1, u.2.1) (u.1, u.2.2) - S.yVec μ R (u.1, u.2.2)‖ ^ 2

/-- On the support of the posterior law the package vectors are the arena's
candidates, so the alignment summand is the candidate distance. -/
theorem posteriorQ_mul_alignTerm (hμ : ∀ x y, 0 ≤ μ x y)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (p : ℝ) (t : PostTuple n X Y A B D) :
    S.posteriorQ R D μ w p t * S.alignTerm μ R (flattenPost t)
      = S.posteriorQ R D μ w p t *
        (‖R.candidate S.σ (aLabel D (insert t.1.i t.1.CX) t.2.1 t.2.2.1 t.2.2.2.1)
            (bLabel D (insert t.1.i t.1.CY) t.2.1 t.2.2.1 t.2.2.2.2)
          - R.candidate S.σ (aLabel D (insert t.1.i t.1.CX) t.2.1 t.2.2.1 t.2.2.2.1)
            (bLabel D t.1.CY t.2.1 t.2.2.1 t.2.2.2.2)‖ ^ 2 +
        ‖R.candidate S.σ (aLabel D (insert t.1.i t.1.CX) t.2.1 t.2.2.1 t.2.2.2.1)
            (bLabel D (insert t.1.i t.1.CY) t.2.1 t.2.2.1 t.2.2.2.2)
          - R.candidate S.σ (aLabel D t.1.CX t.2.1 t.2.2.1 t.2.2.2.1)
            (bLabel D (insert t.1.i t.1.CY) t.2.1 t.2.2.1 t.2.2.2.2)‖ ^ 2) := by
  by_cases hq : S.posteriorQ R D μ w p t = 0
  · rw [hq, zero_mul, zero_mul]
  congr 1
  have hb : R.branch S.σ (aLabel D (insert t.1.i t.1.CX) t.2.1 t.2.2.1 t.2.2.2.1)
      (bLabel D (insert t.1.i t.1.CY) t.2.1 t.2.2.1 t.2.2.2.2) ≠ 0 := by
    intro h0
    apply hq
    unfold posteriorQ
    rw [h0, norm_zero]
    simp
  have hμi : 0 < μ (t.2.1 t.1.i) (t.2.2.1 t.1.i) := by
    have hprod : (∏ j : Fin n, μ (t.2.1 j) (t.2.2.1 j)) ≠ 0 := by
      intro h0
      apply hq
      unfold posteriorQ
      rw [h0]
      simp
    exact lt_of_le_of_ne (hμ _ _)
      (Ne.symm (Finset.prod_ne_zero_iff.mp hprod t.1.i (Finset.mem_univ _)))
  have hbB := S.barB_branch_ne_zero μ R hμ t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2 hμi hb
  have hbA := S.barA_branch_ne_zero μ R hμ t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2 hμi hb
  simp only [alignTerm, flattenPost, uVec, xVec, yVec, labelA_histCore, labelB_histCore,
    barLabelA_histCore, barLabelB_histCore]
  rw [R.unitOr_branch S.σ _ _ hb, R.unitOr_branch S.σ _ _ hbB, R.unitOr_branch S.σ _ _ hbA]

/-- **The alignment defect of the package** `Δ ≤ 16 (t₀ + s₀)/m`
(05_prerounding.tex, eqs two-alignment-bounds with prior-alignment-costs). -/
theorem sum_flatQ_alignTerm_le (hμ : ∀ x y, 0 ≤ μ x y)
    (hμsum : (∑ x : X, ∑ y : Y, μ x y) = 1)
    (hcol : R.ColEntropyBudget) (hrow : R.RowEntropyBudget)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB)
    (hw1 : ∀ xw yw zA zB, w xw yw zA zB ≤ 1)
    (hwD : ∀ (xw xw' : Fin n → X) (yw yw' : Fin n → Y) zA zB,
      agreesOn D xw xw' → agreesOn D yw yw' →
      w xw yw zA zB = w xw' yw' zA zB)
    {p : ℝ} (hp : p = S.coreMass D μ w) (hppos : 0 < p) (hm : D.card < n) :
    (∑ u : PostTuple n X Y A B D × X × Y, S.flatQ R D μ w p u * S.alignTerm μ R u)
      ≤ 16 * (Real.log p⁻¹ + (D.card : ℝ) *
          Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ))) / ((n : ℝ) - D.card) := by
  classical
  unfold flatQ
  rw [HistoryKL.sum_groupedMass_mul,
    Finset.sum_congr rfl fun t _ => S.posteriorQ_mul_alignTerm μ R hμ w p t]
  simp only [mul_add]
  rw [Finset.sum_add_distrib]
  have hA := S.posterior_alignment_A μ hμ R w hw0 hppos
  have hB := S.posterior_alignment_B μ hμ R w hw0 hppos
  obtain ⟨hIA, hIB⟩ := S.prior_alignment_bound μ hμ hμsum R (S.sum_refinedA D μ)
    (S.sum_refinedB D μ) hcol hrow w hw0 hw1 hwD hp hppos hm
  calc _ ≤ 4 * S.alignCostB R D μ w / p + 4 * S.alignCostA R D μ w / p := add_le_add hB hA
    _ ≤ 4 * (2 * p * (Real.log p⁻¹ + (D.card : ℝ) *
            Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ))) / ((n : ℝ) - D.card)) / p
        + 4 * (2 * p * (Real.log p⁻¹ + (D.card : ℝ) *
            Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ))) / ((n : ℝ) - D.card)) / p :=
        add_le_add (by gcongr) (by gcongr)
    _ = _ := by
        field_simp
        ring

end TracialStrategy

end CommutingRepetition
