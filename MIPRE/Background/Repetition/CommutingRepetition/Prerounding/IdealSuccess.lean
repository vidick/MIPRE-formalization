/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Prerounding/IdealSuccess.lean
-/
/-
# Pre-rounding assembly: the ideal success (node 1.2.11)

"Equation ideal-answer-law, averaged under label-law-pi, has payoff `q` by
the tower property" (05_prerounding.tex, end of the proof of prop
tracial-prerounding). The `π`-averaged ideal success is flattened to the
posterior tuples; on each flattening fiber the candidate's coarse-grained
answer pairing is the refined pairing mass divided by the branch mass, and
the refined pairing at the canonical labels is the `priorWeight`-average of
the word-level payoff-weighted correlations (the tower property, as in
`branch_probability_core`). Regrouping by the live coordinate gives
`(1/(pm)) ∑_{i∉D} P(W_{D∪{i}})`, the greedy core's average conditional
success. Nothing here is a manuscript statement.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Prerounding.Package
import MIPRE.Background.Repetition.CommutingRepetition.Prerounding.CoinLaw
import MIPRE.Background.Repetition.CommutingRepetition.OTQCS.PairLaw

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped BigOperators InnerProductSpace

set_option linter.unusedSectionVars false

variable {n : ℕ} {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]

/-! ### Canonical reference words in the one-sided weights -/

theorem setWeightX_canon [Nonempty X] [Nonempty Y] (R₀ : Finset (Fin n)) (μ : X → Y → ℝ)
    (xw : Fin n → X) (yw : Fin n → Y) :
    setWeightX R₀ μ (keepOn R₀ xw) (keepOff R₀ yw) = setWeightX R₀ μ xw yw := by
  funext u
  simp only [setWeightX]
  have hkeep : ∀ j ∈ R₀, keepOn R₀ xw j = xw j := fun j hj => by
    simp only [keepOn, if_pos hj]
  have hiff : agreesOn R₀ u (keepOn R₀ xw) ↔ agreesOn R₀ u xw :=
    ⟨fun h j hj => (h j hj).trans (hkeep j hj), fun h j hj => (h j hj).trans (hkeep j hj).symm⟩
  have hprod : (∏ j ∈ R₀ᶜ, μ (u j) (keepOff R₀ yw j)) = ∏ j ∈ R₀ᶜ, μ (u j) (yw j) :=
    Finset.prod_congr rfl fun j hj => by
      simp only [keepOff, if_neg (Finset.mem_compl.mp hj)]
  rw [if_congr hiff hprod rfl]

theorem setWeightY_canon [Nonempty X] [Nonempty Y] (R₀ : Finset (Fin n)) (μ : X → Y → ℝ)
    (xw : Fin n → X) (yw : Fin n → Y) :
    setWeightY R₀ μ (keepOff R₀ xw) (keepOn R₀ yw) = setWeightY R₀ μ xw yw := by
  funext v
  simp only [setWeightY]
  have hkeep : ∀ j ∈ R₀, keepOn R₀ yw j = yw j := fun j hj => by
    simp only [keepOn, if_pos hj]
  have hiff : agreesOn R₀ v (keepOn R₀ yw) ↔ agreesOn R₀ v yw :=
    ⟨fun h j hj => (h j hj).trans (hkeep j hj), fun h j hj => (h j hj).trans (hkeep j hj).symm⟩
  have hprod : (∏ j ∈ R₀ᶜ, μ (keepOff R₀ xw j) (v j)) = ∏ j ∈ R₀ᶜ, μ (xw j) (v j) :=
    Finset.prod_congr rfl fun j hj => by
      simp only [keepOff, if_neg (Finset.mem_compl.mp hj)]
  rw [if_congr hiff hprod rfl]

/-- Moving the last two of four finite sums to the front. -/
theorem sum_comm4 {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (F : α → β → γ → δ → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d) = ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := by
  calc (∑ a, ∑ b, ∑ c, ∑ d, F a b c d)
      = ∑ a, ∑ c, ∑ b, ∑ d, F a b c d := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, F a b c d := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, F a b c d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := Finset.sum_congr rfl fun c _ => Finset.sum_comm

namespace TracialStrategy

variable [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
variable (S : TracialStrategy.{0}
  (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B))
variable {D : Finset (Fin n)}
variable (μ : X → Y → ℝ) (V : X → Y → A → B → ℝ)

/-! ### Payoff-weighted pairings -/

/-- The word-level payoff-weighted core correlation at live payoff `V(·,·∣x,y)`
read at coordinate `i`. -/
noncomputable def coreSucc (D : Finset (Fin n)) (i : Fin n) (x : X) (y : Y)
    (xw : Fin n → X) (yw : Fin n → Y)
    (zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B)) : ℝ :=
  ∑ as : Fin n → A, ∑ bs : Fin n → B,
    if agreesOn D as (extendCoreA D zD.1) ∧ agreesOn D bs (extendCoreB D zD.2) then
      V x y (as i) (bs i) * S.correlation xw yw as bs else 0

/-- The refined pairing mass at a pair of labels, weighted by the live payoff. -/
noncomputable def refinedPayoff (D : Finset (Fin n)) (i : Fin n) (x : X) (y : Y)
    (s : ALabel n X Y A) (t : BLabel n X Y B) : ℝ :=
  ∑ as : Fin n → A, ∑ bs : Fin n → B,
    V x y (as i) (bs i) *
      (S.M.τ (star S.σ * (S.refinedA D μ s as * S.σ * S.refinedB D μ t bs))).re

theorem refinedPayoff_nonneg (hμ : ∀ x y, 0 ≤ μ x y) (hV0 : ∀ x y a b, 0 ≤ V x y a b)
    (D : Finset (Fin n)) (i : Fin n) (x : X) (y : Y) (s : ALabel n X Y A) (t : BLabel n X Y B) :
    0 ≤ S.refinedPayoff μ V D i x y s t :=
  Finset.sum_nonneg fun as _ => Finset.sum_nonneg fun bs _ => mul_nonneg (hV0 _ _ _ _)
    (S.M.pairing_nonneg S.σ (S.refinedA_isPosElem D μ hμ s as) (S.refinedB_isPosElem D μ hμ t bs))

/-- The payoff-weighted refined mass is at most the total branch mass. -/
theorem refinedPayoff_le (hμ : ∀ x y, 0 ≤ μ x y) (hV1 : ∀ x y a b, V x y a b ≤ 1)
    (D : Finset (Fin n)) (i : Fin n) (x : X) (y : Y) (s : ALabel n X Y A) (t : BLabel n X Y B) :
    S.refinedPayoff μ V D i x y s t
      ≤ (S.M.τ (star S.σ * (S.setEffectA D s.1 μ s.2.1 s.2.2.1 s.2.2.2 * S.σ *
          S.setEffectB D t.1 μ t.2.1 t.2.2.1 t.2.2.2))).re := by
  have hexp : star S.σ * (S.setEffectA D s.1 μ s.2.1 s.2.2.1 s.2.2.2 * S.σ *
      S.setEffectB D t.1 μ t.2.1 t.2.2.1 t.2.2.2)
      = ∑ as : Fin n → A, ∑ bs : Fin n → B,
          star S.σ * (S.refinedA D μ s as * S.σ * S.refinedB D μ t bs) := by
    rw [← S.sum_refinedA D μ s, ← S.sum_refinedB D μ t, Finset.sum_mul, Finset.sum_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun as _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
  have h := congrArg (fun z => (S.M.τ z).re) hexp
  simp only [map_sum, Complex.re_sum] at h
  rw [h]
  unfold refinedPayoff
  refine Finset.sum_le_sum fun as _ => Finset.sum_le_sum fun bs _ => ?_
  exact mul_le_of_le_one_left
    (S.M.pairing_nonneg S.σ (S.refinedA_isPosElem D μ hμ s as) (S.refinedB_isPosElem D μ hμ t bs))
    (hV1 _ _ _ _)

/-- The pairing of two refined effects at one answer pair. -/
theorem re_pairing_refined (D : Finset (Fin n)) (s : ALabel n X Y A) (t : BLabel n X Y B)
    (as : Fin n → A) (bs : Fin n → B) :
    (S.M.τ (star S.σ * (S.refinedA D μ s as * S.σ * S.refinedB D μ t bs))).re
      = (∑ w : Fin n → X, setWeightX s.1 μ s.2.1 s.2.2.1 w)⁻¹ *
        (∑ v : Fin n → Y, setWeightY t.1 μ t.2.1 t.2.2.1 v)⁻¹ *
        ∑ w : Fin n → X, ∑ v : Fin n → Y,
          setWeightX s.1 μ s.2.1 s.2.2.1 w * setWeightY t.1 μ t.2.1 t.2.2.1 v *
            (if agreesOn D as s.2.2.2 ∧ agreesOn D bs t.2.2.2 then
              S.correlation w v as bs else 0) := by
  unfold refinedA refinedB
  have hcorr : ∀ (w : Fin n → X) (v : Fin n → Y),
      (S.M.τ (star S.σ * ((if agreesOn D as s.2.2.2 then S.E w as else 0) * S.σ *
        (if agreesOn D bs t.2.2.2 then S.F v bs else 0)))).re
      = if agreesOn D as s.2.2.2 ∧ agreesOn D bs t.2.2.2 then S.correlation w v as bs else 0 := by
    intro w v
    unfold correlation
    by_cases h1 : agreesOn D as s.2.2.2
    · by_cases h2 : agreesOn D bs t.2.2.2
      · simp only [if_pos h1, if_pos h2, if_pos (And.intro h1 h2)]
      · simp only [if_pos h1, if_neg h2, if_neg (fun h : _ ∧ _ => h2 h.2), mul_zero, map_zero,
          Complex.zero_re]
    · simp only [if_neg h1, if_neg (fun h : _ ∧ _ => h1 h.1), zero_mul, mul_zero, map_zero,
        Complex.zero_re]
  rw [S.re_pairing_weightedAvg_left]
  simp only [S.re_pairing_weightedAvg_right, hcorr, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun v _ => ?_
  ring

/-- **The tower identity for the payoff-weighted refined pairing** (the
refined form of `branch_probability_core`): the conditioned-prior mass times
the refined pairing at the canonical labels is the prior-weighted sum of the
word-level payoff-weighted correlations over the fiber. -/
theorem priorWeight_refinedPayoff (hμ : ∀ x y, 0 ≤ μ x y) (r : RevealDatum n D)
    (xw : Fin n → X) (yw : Fin n → Y)
    (zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B)) :
    (∑ xw' : Fin n → X, ∑ yw' : Fin n → Y, priorWeight r μ xw yw xw' yw') *
        S.refinedPayoff μ V D r.i (xw r.i) (yw r.i)
          (aLabel D (insert r.i r.CX) xw yw zD.1) (bLabel D (insert r.i r.CY) xw yw zD.2)
      = ∑ xw' : Fin n → X, ∑ yw' : Fin n → Y,
          priorWeight r μ xw yw xw' yw' * S.coreSucc V D r.i (xw r.i) (yw r.i) xw' yw' zD := by
  classical
  set wX : (Fin n → X) → ℝ := r.xWeight μ xw yw with hwX
  set wY : (Fin n → Y) → ℝ := r.yWeight μ xw yw with hwY
  have hsX : setWeightX (insert r.i r.CX) μ (keepOn (insert r.i r.CX) xw)
      (keepOff (insert r.i r.CX) yw) = wX := setWeightX_canon _ μ xw yw
  have hsY : setWeightY (insert r.i r.CY) μ (keepOff (insert r.i r.CY) xw)
      (keepOn (insert r.i r.CY) yw) = wY := setWeightY_canon _ μ xw yw
  have hwX0 : ∀ w, 0 ≤ wX w := r.xWeight_nonneg μ hμ xw yw
  have hwY0 : ∀ v, 0 ≤ wY v := r.yWeight_nonneg μ hμ xw yw
  -- The refined payoff as a weighted double sum of core successes.
  have hRP : S.refinedPayoff μ V D r.i (xw r.i) (yw r.i)
      (aLabel D (insert r.i r.CX) xw yw zD.1) (bLabel D (insert r.i r.CY) xw yw zD.2)
      = (∑ w, wX w)⁻¹ * (∑ v, wY v)⁻¹ *
        ∑ w : Fin n → X, ∑ v : Fin n → Y, wX w * wY v *
          S.coreSucc V D r.i (xw r.i) (yw r.i) w v zD := by
    unfold refinedPayoff coreSucc
    have hre : ∀ (as : Fin n → A) (bs : Fin n → B),
        (S.M.τ (star S.σ * (S.refinedA D μ (aLabel D (insert r.i r.CX) xw yw zD.1) as * S.σ *
          S.refinedB D μ (bLabel D (insert r.i r.CY) xw yw zD.2) bs))).re
        = (∑ w, wX w)⁻¹ * (∑ v, wY v)⁻¹ *
          ∑ w : Fin n → X, ∑ v : Fin n → Y, wX w * wY v *
            (if agreesOn D as (extendCoreA D zD.1) ∧ agreesOn D bs (extendCoreB D zD.2) then
              S.correlation w v as bs else 0) := by
      intro as bs
      rw [S.re_pairing_refined μ D]
      simp only [aLabel, bLabel]
      rw [hsX, hsY]
      congr 1
    simp only [hre]
    simp only [Finset.mul_sum]
    rw [sum_comm4]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun v _ =>
      Finset.sum_congr rfl fun as _ => Finset.sum_congr rfl fun bs _ => ?_
    split_ifs <;> ring
  -- The fiber mass and the fiber weights.
  have hmass := r.priorWeight_mass_eq μ xw yw
  have hpw : ∀ w v, priorWeight r μ xw yw w v = r.pinnedWeight μ xw yw * (wX w * wY v) :=
    fun w v => r.priorWeight_eq_mul μ xw yw w v
  rw [hmass, hRP]
  simp only [hpw]
  by_cases hX : (∑ w, wX w) = 0
  · have hz := (Finset.sum_eq_zero_iff_of_nonneg fun w _ => hwX0 w).mp hX
    rw [hX]
    simp only [zero_mul, mul_zero, inv_zero]
    symm
    refine Finset.sum_eq_zero fun w _ => Finset.sum_eq_zero fun v _ => ?_
    rw [hz w (Finset.mem_univ w)]
    ring
  by_cases hY : (∑ v, wY v) = 0
  · have hz := (Finset.sum_eq_zero_iff_of_nonneg fun v _ => hwY0 v).mp hY
    rw [hY]
    simp only [zero_mul, mul_zero, inv_zero]
    symm
    refine Finset.sum_eq_zero fun w _ => Finset.sum_eq_zero fun v _ => ?_
    rw [hz v (Finset.mem_univ v)]
    ring
  rw [show r.pinnedWeight μ xw yw * ((∑ w, wX w) * ∑ v, wY v) *
      ((∑ w, wX w)⁻¹ * (∑ v, wY v)⁻¹ *
        ∑ w : Fin n → X, ∑ v : Fin n → Y, wX w * wY v *
          S.coreSucc V D r.i (xw r.i) (yw r.i) w v zD)
      = r.pinnedWeight μ xw yw *
        ∑ w : Fin n → X, ∑ v : Fin n → Y, wX w * wY v *
          S.coreSucc V D r.i (xw r.i) (yw r.i) w v zD from by
    field_simp]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  ring

/-! ### The ideal answer pairing of the package -/

variable (R : ResolverArena S.M (S.refinedA D μ) (S.refinedB D μ))

/-- The branch mass is the revealed-set pairing (`branch_norm` at the refined
family's totals). -/
theorem re_pairing_setEffect (s : ALabel n X Y A) (t : BLabel n X Y B) :
    (S.M.τ (star S.σ * (S.setEffectA D s.1 μ s.2.1 s.2.2.1 s.2.2.2 * S.σ *
        S.setEffectB D t.1 μ t.2.1 t.2.2.1 t.2.2.2))).re
      = ‖R.branch S.σ s t‖ ^ 2 := by
  have hnorm : S.M.τ (star S.σ * ((∑ as : Fin n → A, S.refinedA D μ s as) * S.σ *
      (∑ bs : Fin n → B, S.refinedB D μ t bs)))
      = ((‖R.branch S.σ s t‖ ^ 2 : ℝ) : ℂ) := by
    rw [← R.branch_norm S.σ s t, inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [S.sum_refinedA, S.sum_refinedB] at hnorm
  rw [hnorm, Complex.ofReal_re]

/-- Off the support of the branch, the payoff-weighted refined mass vanishes. -/
theorem refinedPayoff_eq_zero (hμ : ∀ x y, 0 ≤ μ x y) (hV0 : ∀ x y a b, 0 ≤ V x y a b)
    (hV1 : ∀ x y a b, V x y a b ≤ 1) (i : Fin n) (x : X) (y : Y)
    (s : ALabel n X Y A) (t : BLabel n X Y B) (hb : R.branch S.σ s t = 0) :
    S.refinedPayoff μ V D i x y s t = 0 := by
  have h1 := S.refinedPayoff_le μ V hμ hV1 D i x y s t
  rw [S.re_pairing_setEffect μ R, hb, norm_zero, zero_pow two_ne_zero] at h1
  exact le_antisymm h1 (S.refinedPayoff_nonneg μ V hμ hV0 D i x y s t)

/-- The payoff of the package's ideal answer law at a history and live
questions (the summand of `PreroundedStrategy.idealSuccess`). -/
noncomputable def idealPayoff (h : PostTuple n X Y A B D) (x : X) (y : Y) : ℝ :=
  ∑ a : A, ∑ b : B, V x y a b *
    tracialPairLaw R.N (S.uVec μ R) (S.Apov μ R) (S.Bpov μ R) (h, x) (h, y) a b

/-- The same, on flattened tuples. -/
noncomputable def idealPayoffFlat (u : PostTuple n X Y A B D × X × Y) : ℝ :=
  S.idealPayoff μ V R u.1 u.2.1 u.2.2

/-- **The ideal payoff on a nonzero branch** is the refined payoff-weighted
mass divided by the branch mass (eq ideal-answer-law, coarse-grained). -/
theorem idealPayoff_eq (h : PostTuple n X Y A B D) (x : X) (y : Y)
    (hb : R.branch S.σ (labelA D h x) (labelB D h y) ≠ 0) :
    S.idealPayoff μ V R h x y
      = S.refinedPayoff μ V D h.1.i x y (labelA D h x) (labelB D h y) /
          ‖R.branch S.σ (labelA D h x) (labelB D h y)‖ ^ 2 := by
  have hcp := fun a b => S.candidate_pairing μ R (labelA D h x) (labelB D h y) h.1.i a b hb
  unfold idealPayoff tracialPairLaw uVec Apov Bpov
  dsimp only
  rw [R.unitOr_branch S.σ _ _ hb]
  simp only [hcp]
  unfold refinedPayoff
  set Z : (Fin n → A) → (Fin n → B) → ℝ := fun as bs =>
    (S.M.τ (star S.σ * (S.refinedA D μ (labelA D h x) as * S.σ *
      S.refinedB D μ (labelB D h y) bs))).re with hZ
  have hkey : (∑ a : A, ∑ b : B, V x y a b * ∑ as : Fin n → A, ∑ bs : Fin n → B,
      if as h.1.i = a ∧ bs h.1.i = b then Z as bs else 0)
      = ∑ as : Fin n → A, ∑ bs : Fin n → B, V x y (as h.1.i) (bs h.1.i) * Z as bs := by
    simp only [Finset.mul_sum]
    rw [sum_comm4]
    refine Finset.sum_congr rfl fun as _ => Finset.sum_congr rfl fun bs _ => ?_
    have h1 : ∀ a : A,
        (∑ b : B, V x y a b * (if as h.1.i = a ∧ bs h.1.i = b then Z as bs else 0))
          = if as h.1.i = a then V x y a (bs h.1.i) * Z as bs else 0 := by
      intro a
      by_cases ha : as h.1.i = a
      · simp only [ha, true_and, if_true, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ]
      · simp only [ha, false_and, if_false, mul_zero, Finset.sum_const_zero]
    simp only [h1, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← hkey, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_div_assoc]

/-! ### The tower identity on posterior tuples -/

/-- The posterior-weighted refined payoff at a tuple's canonical labels. -/
noncomputable def tupleSucc
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (p : ℝ) (t : PostTuple n X Y A B D) : ℝ :=
  t.1.revealLaw * (∏ j : Fin n, μ (t.2.1 j) (t.2.2.1 j)) * w t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2 *
    S.refinedPayoff μ V D t.1.i (t.2.1 t.1.i) (t.2.2.1 t.1.i)
      (aLabel D (insert t.1.i t.1.CX) t.2.1 t.2.2.1 t.2.2.2.1)
      (bLabel D (insert t.1.i t.1.CY) t.2.1 t.2.2.1 t.2.2.2.2) / p

/-- The posterior-weighted word-level payoff-weighted core correlation. -/
noncomputable def tupleCore
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (p : ℝ) (t : PostTuple n X Y A B D) : ℝ :=
  t.1.revealLaw * (∏ j : Fin n, μ (t.2.1 j) (t.2.2.1 j)) * w t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2 *
    S.coreSucc V D t.1.i (t.2.1 t.1.i) (t.2.2.1 t.1.i) t.2.1 t.2.2.1 t.2.2.2 / p

/-- The posterior mass times the ideal payoff at the flattened tuple: the
branch mass cancels. -/
theorem posteriorQ_mul_idealPayoff (hμ : ∀ x y, 0 ≤ μ x y) (hV0 : ∀ x y a b, 0 ≤ V x y a b)
    (hV1 : ∀ x y a b, V x y a b ≤ 1)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (p : ℝ) (t : PostTuple n X Y A B D) :
    S.posteriorQ R D μ w p t * S.idealPayoffFlat μ V R (flattenPost t)
      = S.tupleSucc μ V w p t := by
  obtain ⟨r, xw, yw, zD⟩ := t
  have hlA := labelA_histCore (D := D) (r, xw, yw, zD)
  have hlB := labelB_histCore (D := D) (r, xw, yw, zD)
  unfold idealPayoffFlat flattenPost tupleSucc posteriorQ
  dsimp only at hlA hlB ⊢
  by_cases hb : R.branch S.σ (aLabel D (insert r.i r.CX) xw yw zD.1)
      (bLabel D (insert r.i r.CY) xw yw zD.2) = 0
  · rw [S.refinedPayoff_eq_zero μ V R hμ hV0 hV1 _ _ _ _ _ hb, hb, norm_zero]
    simp
  · rw [S.idealPayoff_eq μ V R _ _ _ (by rw [hlA, hlB]; exact hb), hlA, hlB]
    have hb2 : ‖R.branch S.σ (aLabel D (insert r.i r.CX) xw yw zD.1)
        (bLabel D (insert r.i r.CY) xw yw zD.2)‖ ^ 2 ≠ 0 :=
      pow_ne_zero 2 (norm_ne_zero_iff.mpr hb)
    have hi : (histCore (D := D) (r, xw, yw, zD)).1.i = r.i := rfl
    rw [hi, div_mul_div_comm]
    rw [show r.revealLaw * (∏ j : Fin n, μ (xw j) (yw j)) * w xw yw zD.1 zD.2 *
        ‖R.branch S.σ (aLabel D (insert r.i r.CX) xw yw zD.1)
          (bLabel D (insert r.i r.CY) xw yw zD.2)‖ ^ 2 *
        S.refinedPayoff μ V D r.i (xw r.i) (yw r.i) (aLabel D (insert r.i r.CX) xw yw zD.1)
          (bLabel D (insert r.i r.CY) xw yw zD.2)
      = r.revealLaw * (∏ j : Fin n, μ (xw j) (yw j)) * w xw yw zD.1 zD.2 *
        S.refinedPayoff μ V D r.i (xw r.i) (yw r.i) (aLabel D (insert r.i r.CX) xw yw zD.1)
          (bLabel D (insert r.i r.CY) xw yw zD.2) *
        ‖R.branch S.σ (aLabel D (insert r.i r.CX) xw yw zD.1)
          (bLabel D (insert r.i r.CY) xw yw zD.2)‖ ^ 2 by ring]
    rw [mul_div_mul_right _ _ hb2]

open Classical in
/-- **The tower property on a flattening fiber**: the fiber sums of the
refined-payoff and core-success tuple weights agree (`priorWeight_refinedPayoff`
with the labels constant on the fiber). -/
theorem tupleSucc_fiber (hμ : ∀ x y, 0 ≤ μ x y)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hwD : ∀ (xw xw' : Fin n → X) (yw yw' : Fin n → Y) zA zB,
      agreesOn D xw xw' → agreesOn D yw yw' →
      w xw yw zA zB = w xw' yw' zA zB)
    (p : ℝ) (t : PostTuple n X Y A B D) :
    (∑ t' : PostTuple n X Y A B D,
        if flattenPost t' = flattenPost t then S.tupleSucc μ V w p t' else 0)
      = ∑ t' : PostTuple n X Y A B D,
          if flattenPost t' = flattenPost t then S.tupleCore μ V w p t' else 0 := by
  rw [sum_fiber_flattenPost, sum_fiber_flattenPost]
  obtain ⟨r, xw, yw, zD⟩ := t
  dsimp only
  have hkey := S.priorWeight_refinedPayoff μ V hμ r xw yw zD
  set sA := aLabel D (insert r.i r.CX) xw yw zD.1 with hsA
  set tB := bLabel D (insert r.i r.CY) xw yw zD.2 with htB
  set c : ℝ := r.revealLaw * w xw yw zD.1 zD.2 / p with hc
  have hL : ∀ (xw' : Fin n → X) (yw' : Fin n → Y),
      (if agreesOn (insert r.i r.CX) xw' xw ∧ agreesOn (insert r.i r.CY) yw' yw then
        S.tupleSucc μ V w p (r, xw', yw', zD) else 0)
      = c * (priorWeight r μ xw yw xw' yw' *
          S.refinedPayoff μ V D r.i (xw r.i) (yw r.i) sA tB) := by
    intro xw' yw'
    unfold priorWeight tupleSucc
    dsimp only
    split_ifs with hag
    · obtain ⟨hX, hY⟩ := hag
      have hxi : xw' r.i = xw r.i := hX _ (Finset.mem_insert_self _ _)
      have hyi : yw' r.i = yw r.i := hY _ (Finset.mem_insert_self _ _)
      have hw : w xw' yw' zD.1 zD.2 = w xw yw zD.1 zD.2 :=
        hwD _ _ _ _ _ _ (agreesOn_mono r.core_subset_insert_CX hX)
          (agreesOn_mono r.core_subset_insert_CY hY)
      have hlA : aLabel D (insert r.i r.CX) xw' yw' zD.1 = sA := by
        refine aLabel_congr D _ zD.1 (fun j hj => hX j hj) (fun j hj => ?_)
        rw [Finset.mem_insert, not_or] at hj
        exact hY j (Finset.mem_insert_of_mem (r.mem_CY_of_ne hj.1 hj.2))
      have hlB : bLabel D (insert r.i r.CY) xw' yw' zD.2 = tB := by
        refine bLabel_congr D _ zD.2 (fun j hj => ?_) (fun j hj => hY j hj)
        rw [Finset.mem_insert, not_or] at hj
        exact hX j (Finset.mem_insert_of_mem (r.mem_CX_of_ne hj.1 hj.2))
      rw [hxi, hyi, hw, hlA, hlB, hc]
      ring
    · ring
  have hR : ∀ (xw' : Fin n → X) (yw' : Fin n → Y),
      (if agreesOn (insert r.i r.CX) xw' xw ∧ agreesOn (insert r.i r.CY) yw' yw then
        S.tupleCore μ V w p (r, xw', yw', zD) else 0)
      = c * (priorWeight r μ xw yw xw' yw' *
          S.coreSucc V D r.i (xw r.i) (yw r.i) xw' yw' zD) := by
    intro xw' yw'
    unfold priorWeight tupleCore
    dsimp only
    split_ifs with hag
    · obtain ⟨hX, hY⟩ := hag
      have hxi : xw' r.i = xw r.i := hX _ (Finset.mem_insert_self _ _)
      have hyi : yw' r.i = yw r.i := hY _ (Finset.mem_insert_self _ _)
      have hw : w xw' yw' zD.1 zD.2 = w xw yw zD.1 zD.2 :=
        hwD _ _ _ _ _ _ (agreesOn_mono r.core_subset_insert_CX hX)
          (agreesOn_mono r.core_subset_insert_CY hY)
      rw [hxi, hyi, hw, hc]
      ring
    · ring
  simp only [hL, hR]
  simp only [← Finset.mul_sum]
  congr 1
  rw [← hkey, Finset.sum_mul]
  exact Finset.sum_congr rfl fun xw' _ => (Finset.sum_mul _ _ _).symm

/-- **The ideal success of the package, on posterior tuples**: the
`Q`-average of the ideal payoff is the posterior-weighted word-level
payoff-weighted core correlation. -/
theorem sum_flatQ_idealPayoff (hμ : ∀ x y, 0 ≤ μ x y) (hV0 : ∀ x y a b, 0 ≤ V x y a b)
    (hV1 : ∀ x y a b, V x y a b ≤ 1)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hwD : ∀ (xw xw' : Fin n → X) (yw yw' : Fin n → Y) zA zB,
      agreesOn D xw xw' → agreesOn D yw yw' →
      w xw yw zA zB = w xw' yw' zA zB)
    (p : ℝ) :
    (∑ u : PostTuple n X Y A B D × X × Y, S.flatQ R D μ w p u * S.idealPayoffFlat μ V R u)
      = ∑ t : PostTuple n X Y A B D, S.tupleCore μ V w p t := by
  classical
  unfold flatQ
  rw [HistoryKL.sum_groupedMass_mul,
    Finset.sum_congr rfl fun t _ => S.posteriorQ_mul_idealPayoff μ V R hμ hV0 hV1 w p t,
    ← HistoryKL.sum_groupedMass (flattenPost (D := D)) (S.tupleSucc μ V w p),
    ← HistoryKL.sum_groupedMass (flattenPost (D := D)) (S.tupleCore μ V w p)]
  refine Finset.sum_congr rfl fun u _ => ?_
  exact groupedMass_ext_of_fibers _ _ _ (fun t => S.tupleSucc_fiber μ V hμ w hwD p t) u

/-! ### Regrouping by the live coordinate -/

/-- The payoff-weighted core success read at live coordinate `i`:
`∑_{x,y} Πμ ∑_z w_D(z) · coreSucc_i`. -/
noncomputable def liveSucc
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (i : Fin n) : ℝ :=
  ∑ xw : Fin n → X, ∑ yw : Fin n → Y, (∏ j : Fin n, μ (xw j) (yw j)) *
    ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
      w xw yw zD.1 zD.2 * S.coreSucc V D i (xw i) (yw i) xw yw zD

theorem sum_tupleCore
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (p : ℝ) :
    (∑ t : PostTuple n X Y A B D, S.tupleCore μ V w p t)
      = (1 / p) * ∑ r : RevealDatum n D, r.revealLaw * S.liveSucc μ V w r.i := by
  unfold tupleCore liveSucc
  simp only [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun xw _ =>
    Finset.sum_congr rfl fun yw _ => Finset.sum_congr rfl fun zA _ =>
    Finset.sum_congr rfl fun zB _ => ?_
  ring

end TracialStrategy

namespace RevealDatum

variable {D : Finset (Fin n)}

/-- A reveal-law average of a function of the live coordinate is the uniform
average over the non-core coordinates (`revealLaw_sum_fiber`). -/
theorem sum_revealLaw_mul (f : Fin n → ℝ) :
    (∑ r : RevealDatum n D, r.revealLaw * f r.i)
      = ∑ i ∈ Finset.univ \ D, (1 / ((n - D.card : ℕ) : ℝ)) * f i := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ \ D)
    (g := fun r : RevealDatum n D => r.i)
    (fun r _ => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, r.i_notMem⟩)
    (fun r : RevealDatum n D => r.revealLaw * f r.i)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ∉ D := (Finset.mem_sdiff.mp hi).2
  rw [← RevealDatum.revealLaw_sum_fiber i hi', Finset.sum_mul, Finset.sum_filter]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs with h
  · rw [h]
  · ring

end RevealDatum

end CommutingRepetition
