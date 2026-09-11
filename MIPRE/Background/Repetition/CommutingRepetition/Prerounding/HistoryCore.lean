/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Prerounding/HistoryCore.lean
-/
/-
# Pre-rounding: the core posterior law and the history fibers (node 1.2.10)

Proof-side layer for `history_relative_entropy`. The posterior branch law
`posteriorQ` (05_prerounding.tex, eq posterior-branch-law) collapses, along
the fibers of the flattening `flattenPost`, onto the *core posterior law*
`ℚ⁰(x, y, z) = Πμ(x,y) · w(x,y,z) · re τ(σ* E_x^{z_A} σ F_y^{z_B}) / p`
tensored with the reveal law: the branch mass at the full canonical labels is
the effective-effect pairing (`branch_probability`), and the effective
effects are the conditional averages of the core effects over the fiber
(eq prior-factorization). Everything downstream of that collapse is finite
probability over words (`HistoryKL`). Nothing here is a manuscript
statement.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Prerounding.Costs
import MIPRE.Background.Repetition.CommutingRepetition.Prerounding.HistoryKL

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped BigOperators InnerProductSpace

set_option linter.unusedSectionVars false

variable {n : ℕ} {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]

/-! ### Word agreement -/

section Agreement

variable {α : Type} [DecidableEq α]

theorem agreesOn_refl (S : Finset (Fin n)) (a : Fin n → α) : agreesOn S a a :=
  fun _ _ => rfl

theorem agreesOn_comm {S : Finset (Fin n)} {a b : Fin n → α} :
    agreesOn S a b ↔ agreesOn S b a :=
  ⟨fun h j hj => (h j hj).symm, fun h j hj => (h j hj).symm⟩

theorem agreesOn_univ_iff {a b : Fin n → α} : agreesOn Finset.univ a b ↔ a = b :=
  ⟨fun h => funext fun j => h j (Finset.mem_univ j), fun h j _ => by rw [h]⟩

theorem agreesOn_insert_iff {S : Finset (Fin n)} {i : Fin n} {a b : Fin n → α} :
    agreesOn (insert i S) a b ↔ a i = b i ∧ agreesOn S a b := by
  constructor
  · intro h
    exact ⟨h i (Finset.mem_insert_self i S), fun j hj => h j (Finset.mem_insert_of_mem hj)⟩
  · rintro ⟨hi, h⟩ j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hi
    · exact h j hj

theorem agreesOn_mono {S T : Finset (Fin n)} (hST : S ⊆ T) {a b : Fin n → α}
    (h : agreesOn T a b) : agreesOn S a b :=
  fun j hj => h j (hST hj)

theorem keepOn_eq_iff [Nonempty α] (S : Finset (Fin n)) (a b : Fin n → α) :
    keepOn S a = keepOn S b ↔ agreesOn S a b := by
  constructor
  · intro h j hj
    have := congrFun h j
    simpa [keepOn, hj] using this
  · intro h
    funext j
    unfold keepOn
    split_ifs with hj
    · exact h j hj
    · rfl

/-- **Fiber product identity**: summing a product over the words agreeing
with a reference on `S` pins the `S`-factors and sums the others. -/
theorem sum_agree_prod [Fintype α] (S : Finset (Fin n)) (xw : Fin n → α)
    (f : Fin n → α → ℝ) :
    (∑ xw' : Fin n → α, if agreesOn S xw' xw then ∏ j, f j (xw' j) else 0)
      = ∏ j, if j ∈ S then f j (xw j) else ∑ x, f j x := by
  have hterm : ∀ xw' : Fin n → α,
      (if agreesOn S xw' xw then ∏ j, f j (xw' j) else 0)
        = ∏ j, (if j ∈ S then (if xw' j = xw j then f j (xw' j) else 0)
            else f j (xw' j)) := by
    intro xw'
    by_cases h : agreesOn S xw' xw
    · rw [if_pos h]
      refine Finset.prod_congr rfl fun j _ => ?_
      by_cases hj : j ∈ S
      · rw [if_pos hj, if_pos (h j hj)]
      · rw [if_neg hj]
    · rw [if_neg h]
      have h' : ∃ j ∈ S, xw' j ≠ xw j := by
        by_contra hc
        exact h fun j hj => by
          by_contra hne
          exact hc ⟨j, hj, hne⟩
      obtain ⟨j, hj, hne⟩ := h'
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      rw [if_pos hj, if_neg hne]
  rw [Finset.sum_congr rfl fun xw' _ => hterm xw']
  have h := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset α))
    (fun j x => if j ∈ S then (if x = xw j then f j x else 0) else f j x)
  rw [Fintype.piFinset_univ] at h
  rw [← h]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hj : j ∈ S
  · simp [hj]
  · simp [hj]

end Agreement

namespace TracialStrategy

variable [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
variable (S : TracialStrategy.{0}
  (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B))
variable {D : Finset (Fin n)}
variable {Af Bf : Type} [Fintype Af] [Fintype Bf]

/-! ### The core posterior law -/

/-- The core tuple space: the two full question words and the core word
(the second factor of `PostTuple`). -/
abbrev CoreTuple (n : ℕ) (X Y A B : Type) (D : Finset (Fin n)) : Type :=
  (Fin n → X) × (Fin n → Y) × (({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B))

/-- The core pairing `re τ(σ* E_x^{z_A} σ F_y^{z_B})`. -/
noncomputable def corePair (D : Finset (Fin n)) (s : CoreTuple n X Y A B D) : ℝ :=
  (S.M.τ (star S.σ * (S.coreEffectA D s.1 (extendCoreA D s.2.2.1) * S.σ *
    S.coreEffectB D s.2.1 (extendCoreB D s.2.2.2)))).re

/-- The full product prior on a core tuple's words. -/
noncomputable def prodPrior (D : Finset (Fin n)) (μ : X → Y → ℝ)
    (s : CoreTuple n X Y A B D) : ℝ :=
  ∏ j : Fin n, μ (s.1 j) (s.2.1 j)

/-- **The core posterior law** `ℚ⁰(x, y, z) = Πμ · w · pairing / p`: the
posterior branch law with the reveal datum integrated out (eq
posterior-branch-law at the core, i.e. the weighted core correlation
normalized by `p`). -/
noncomputable def corePost (D : Finset (Fin n)) (μ : X → Y → ℝ)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (p : ℝ) (s : CoreTuple n X Y A B D) : ℝ :=
  prodPrior D μ s * w s.1 s.2.1 s.2.2.1 s.2.2.2 * S.corePair D s / p

theorem corePair_nonneg (D : Finset (Fin n)) (s : CoreTuple n X Y A B D) :
    0 ≤ S.corePair D s :=
  S.M.pairing_nonneg S.σ (S.coreEffectA_isPosElem D _ _) (S.coreEffectB_isPosElem D _ _)

/-- The core pairings over all core words sum to `τ(σ*σ) = 1`. -/
theorem sum_corePair (D : Finset (Fin n)) (xw : Fin n → X) (yw : Fin n → Y) :
    (∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
      S.corePair D (xw, yw, zD)) = 1 := by
  classical
  have hexp : star S.σ *
      ((∑ zA : {j : Fin n // j ∈ D} → A, S.coreEffectA D xw (extendCoreA D zA)) * S.σ *
        (∑ zB : {j : Fin n // j ∈ D} → B, S.coreEffectB D yw (extendCoreB D zB)))
      = ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
          star S.σ * (S.coreEffectA D xw (extendCoreA D zD.1) * S.σ *
            S.coreEffectB D yw (extendCoreB D zD.2)) := by
    rw [Finset.sum_mul, Finset.sum_mul, Finset.mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun zA _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
  have h1 := congrArg (fun z => (S.M.τ z).re) hexp
  simp only [map_sum, Complex.re_sum] at h1
  unfold corePair
  rw [← h1, S.sum_coreEffectA_ext D xw (extendCoreA D) (fun zD j hj => by
      simp [extendCoreA, hj]),
    S.sum_coreEffectB_ext D yw (extendCoreB D) (fun zD j hj => by
      simp [extendCoreB, hj]),
    one_mul, mul_one, S.σ_normalized, Complex.one_re]

theorem corePair_le_one (D : Finset (Fin n)) (s : CoreTuple n X Y A B D) :
    S.corePair D s ≤ 1 := by
  obtain ⟨xw, yw, zD⟩ := s
  rw [← S.sum_corePair D xw yw]
  exact Finset.single_le_sum (f := fun zD' => S.corePair D (xw, yw, zD'))
    (fun zD' _ => S.corePair_nonneg D _) (Finset.mem_univ zD)

theorem prodPrior_nonneg (D : Finset (Fin n)) (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (s : CoreTuple n X Y A B D) : 0 ≤ prodPrior D μ s :=
  Finset.prod_nonneg fun j _ => hμ _ _

theorem corePost_nonneg (D : Finset (Fin n)) (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB) {p : ℝ} (hppos : 0 < p)
    (s : CoreTuple n X Y A B D) : 0 ≤ S.corePost D μ w p s :=
  div_nonneg (mul_nonneg (mul_nonneg (prodPrior_nonneg D μ hμ s) (hw0 _ _ _ _))
    (S.corePair_nonneg D s)) hppos.le

/-- The core posterior law is a probability law (the weighted core mass
is `p`). -/
theorem sum_corePost (D : Finset (Fin n)) (μ : X → Y → ℝ)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    {p : ℝ} (hp : p = S.coreMass D μ w) (hppos : 0 < p) :
    (∑ s : CoreTuple n X Y A B D, S.corePost D μ w p s) = 1 := by
  have h : (∑ s : CoreTuple n X Y A B D, S.corePost D μ w p s) = S.coreMass D μ w / p := by
    unfold coreMass corePost corePair prodPrior
    rw [Fintype.sum_prod_type, Finset.sum_div]
    refine Finset.sum_congr rfl fun xw _ => ?_
    rw [Fintype.sum_prod_type, Finset.sum_div]
    refine Finset.sum_congr rfl fun yw _ => ?_
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun zD _ => ?_
    ring
  rw [h, ← hp, div_self hppos.ne']

/-- **Pointwise density bound**: `ℚ⁰ ≤ Πμ / p` (eq
question-answer-conditioning-budget, pointwise form). -/
theorem corePost_le (D : Finset (Fin n)) (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB)
    (hw1 : ∀ xw yw zA zB, w xw yw zA zB ≤ 1) {p : ℝ} (hppos : 0 < p)
    (s : CoreTuple n X Y A B D) :
    S.corePost D μ w p s ≤ p⁻¹ * prodPrior D μ s := by
  unfold corePost
  rw [div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hppos.le)
  calc prodPrior D μ s * w s.1 s.2.1 s.2.2.1 s.2.2.2 * S.corePair D s
      ≤ prodPrior D μ s * 1 * 1 := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left (hw1 _ _ _ _)
          (prodPrior_nonneg D μ hμ s)) (S.corePair_le_one D s) (S.corePair_nonneg D s) ?_
        exact mul_nonneg (prodPrior_nonneg D μ hμ s) zero_le_one
    _ = prodPrior D μ s := by ring

/-- The core-word sum of the core posterior is at most `Πμ / p`. -/
theorem sum_zD_corePost_le (D : Finset (Fin n)) (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB)
    (hw1 : ∀ xw yw zA zB, w xw yw zA zB ≤ 1) {p : ℝ} (hppos : 0 < p)
    (xw : Fin n → X) (yw : Fin n → Y) :
    (∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
      S.corePost D μ w p (xw, yw, zD)) ≤ p⁻¹ * ∏ j : Fin n, μ (xw j) (yw j) := by
  have hpp : 0 ≤ ∏ j : Fin n, μ (xw j) (yw j) := Finset.prod_nonneg fun j _ => hμ _ _
  calc (∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
        S.corePost D μ w p (xw, yw, zD))
      ≤ ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
          p⁻¹ * (∏ j : Fin n, μ (xw j) (yw j)) * S.corePair D (xw, yw, zD) := by
        refine Finset.sum_le_sum fun zD _ => ?_
        unfold corePost prodPrior
        rw [div_eq_inv_mul]
        simp only
        rw [show p⁻¹ * ((∏ j, μ (xw j) (yw j)) * w xw yw zD.1 zD.2 * S.corePair D (xw, yw, zD))
            = (p⁻¹ * ∏ j, μ (xw j) (yw j)) * (w xw yw zD.1 zD.2 * S.corePair D (xw, yw, zD))
            from by ring]
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (inv_nonneg.mpr hppos.le) hpp)
        exact mul_le_of_le_one_left (S.corePair_nonneg D _) (hw1 _ _ _ _)
    _ = p⁻¹ * ∏ j : Fin n, μ (xw j) (yw j) := by
        rw [← Finset.mul_sum, S.sum_corePair D xw yw, mul_one]

theorem corePost_eq_zero_of_mu (D : Finset (Fin n)) (μ : X → Y → ℝ)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (p : ℝ) (s : CoreTuple n X Y A B D) (i : Fin n) (h : μ (s.1 i) (s.2.1 i) = 0) :
    S.corePost D μ w p s = 0 := by
  unfold corePost prodPrior
  rw [Finset.prod_eq_zero (Finset.mem_univ i) h]
  simp

/-- Positivity of the core posterior forces positivity of every question
factor. -/
theorem mu_pos_of_corePost_pos (D : Finset (Fin n)) (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (p : ℝ) (s : CoreTuple n X Y A B D) (hs : 0 < S.corePost D μ w p s) (i : Fin n) :
    0 < μ (s.1 i) (s.2.1 i) := by
  rcases (hμ (s.1 i) (s.2.1 i)).lt_or_eq with h | h
  · exact h
  · exact absurd (S.corePost_eq_zero_of_mu D μ w p s i h.symm) hs.ne'

theorem prodPrior_pos_of_corePost_pos (D : Finset (Fin n)) (μ : X → Y → ℝ)
    (hμ : ∀ x y, 0 ≤ μ x y)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (p : ℝ) (s : CoreTuple n X Y A B D) (hs : 0 < S.corePost D μ w p s) :
    0 < prodPrior D μ s :=
  Finset.prod_pos fun i _ => S.mu_pos_of_corePost_pos D μ hμ w p s hs i

/-! ### Class masses over revealed sets -/

/-- The mass of a function of core tuples over the class of `s` fixing the
Alice word on `SX`, the Bob word on `SY`, and the core word. -/
noncomputable def classMass (SX SY : Finset (Fin n)) (f : CoreTuple n X Y A B D → ℝ)
    (s : CoreTuple n X Y A B D) : ℝ :=
  ∑ xw' : Fin n → X, ∑ yw' : Fin n → Y,
    if agreesOn SX xw' s.1 ∧ agreesOn SY yw' s.2.1 then f (xw', yw', s.2.2) else 0

/-- The class map behind `classMass`. -/
noncomputable def classMap (SX SY : Finset (Fin n)) (s : CoreTuple n X Y A B D) :
    CoreTuple n X Y A B D :=
  (keepOn SX s.1, keepOn SY s.2.1, s.2.2)

theorem classMap_eq_iff (SX SY : Finset (Fin n)) (s s' : CoreTuple n X Y A B D) :
    classMap SX SY s' = classMap SX SY s
      ↔ agreesOn SX s'.1 s.1 ∧ agreesOn SY s'.2.1 s.2.1 ∧ s'.2.2 = s.2.2 := by
  unfold classMap
  rw [Prod.mk.injEq, Prod.mk.injEq, keepOn_eq_iff, keepOn_eq_iff]

/-- `classMass` is the grouped mass under `classMap`, as an indicator sum
over the whole tuple space. -/
theorem classMass_eq_sum_ite (SX SY : Finset (Fin n)) (f : CoreTuple n X Y A B D → ℝ)
    (s : CoreTuple n X Y A B D) :
    classMass SX SY f s
      = ∑ s' : CoreTuple n X Y A B D,
          if classMap SX SY s' = classMap SX SY s then f s' else 0 := by
  classical
  unfold classMass
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun xw' _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun yw' _ => ?_
  simp only [classMap_eq_iff]
  by_cases h : agreesOn SX xw' s.1 ∧ agreesOn SY yw' s.2.1
  · rw [if_pos h]
    rw [Finset.sum_eq_single s.2.2]
    · simp [h]
    · intro zD' _ hne
      rw [if_neg]
      rintro ⟨-, -, h3⟩
      exact hne h3
    · intro habs
      exact absurd (Finset.mem_univ _) habs
  · rw [if_neg h]
    refine (Finset.sum_eq_zero fun zD' _ => ?_).symm
    rw [if_neg]
    rintro ⟨h1, h2, -⟩
    exact h ⟨h1, h2⟩

theorem classMass_nonneg (SX SY : Finset (Fin n)) (f : CoreTuple n X Y A B D → ℝ)
    (hf : ∀ s, 0 ≤ f s) (s : CoreTuple n X Y A B D) : 0 ≤ classMass SX SY f s :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by
    split_ifs
    · exact hf _
    · exact le_rfl

theorem le_classMass (SX SY : Finset (Fin n)) (f : CoreTuple n X Y A B D → ℝ)
    (hf : ∀ s, 0 ≤ f s) (s : CoreTuple n X Y A B D) : f s ≤ classMass SX SY f s := by
  classical
  rw [classMass_eq_sum_ite]
  have := Finset.single_le_sum
    (f := fun s' : CoreTuple n X Y A B D =>
      if classMap SX SY s' = classMap SX SY s then f s' else 0)
    (fun s' _ => by split_ifs <;> [exact hf s'; exact le_rfl]) (Finset.mem_univ s)
  simpa using this

theorem classMass_mono_right (SX SY SY' : Finset (Fin n)) (hSY : SY ⊆ SY')
    (f : CoreTuple n X Y A B D → ℝ) (hf : ∀ s, 0 ≤ f s) (s : CoreTuple n X Y A B D) :
    classMass SX SY' f s ≤ classMass SX SY f s := by
  unfold classMass
  refine Finset.sum_le_sum fun xw' _ => Finset.sum_le_sum fun yw' _ => ?_
  by_cases h : agreesOn SX xw' s.1 ∧ agreesOn SY' yw' s.2.1
  · rw [if_pos h, if_pos ⟨h.1, agreesOn_mono hSY h.2⟩]
  · rw [if_neg h]
    split_ifs
    · exact hf _
    · exact le_rfl

/-- **Product formula for the prior class mass**: the doubly revealed
coordinates are pinned, the singly revealed ones carry a marginal, the
unrevealed ones the total mass. -/
theorem classMass_prodPrior (SX SY : Finset (Fin n)) (μ : X → Y → ℝ)
    (s : CoreTuple n X Y A B D) :
    classMass SX SY (prodPrior D μ) s
      = ∏ j : Fin n, if j ∈ SX then (if j ∈ SY then μ (s.1 j) (s.2.1 j)
            else ∑ y : Y, μ (s.1 j) y)
          else (if j ∈ SY then ∑ x : X, μ x (s.2.1 j) else ∑ x : X, ∑ y : Y, μ x y) := by
  unfold classMass prodPrior
  have hinner : ∀ xw' : Fin n → X,
      (∑ yw' : Fin n → Y, if agreesOn SX xw' s.1 ∧ agreesOn SY yw' s.2.1 then
          ∏ j, μ (xw' j) (yw' j) else 0)
        = if agreesOn SX xw' s.1 then
            ∏ j, (if j ∈ SY then μ (xw' j) (s.2.1 j) else ∑ y : Y, μ (xw' j) y) else 0 := by
    intro xw'
    by_cases hx : agreesOn SX xw' s.1
    · rw [if_pos hx, ← sum_agree_prod SY s.2.1 (fun j y => μ (xw' j) y)]
      refine Finset.sum_congr rfl fun yw' _ => ?_
      by_cases hy : agreesOn SY yw' s.2.1
      · rw [if_pos ⟨hx, hy⟩, if_pos hy]
      · rw [if_neg (fun h => hy h.2), if_neg hy]
    · rw [if_neg hx]
      exact Finset.sum_eq_zero fun yw' _ => if_neg (fun h => hx h.1)
  rw [Finset.sum_congr rfl fun xw' _ => hinner xw',
    sum_agree_prod SX s.1 (fun j x => if j ∈ SY then μ x (s.2.1 j) else ∑ y : Y, μ x y)]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hj : j ∈ SX
  · simp only [if_pos hj]
  · simp only [if_neg hj]
    by_cases hj' : j ∈ SY
    · simp only [if_pos hj']
    · simp only [if_neg hj']

/-- The ratio of the prior class masses at a covering pair, the Bob set
enlarged to everything: the pinned-to-marginal ratios on `SX \ SY`. -/
theorem classMass_prodPrior_univ_eq (SX SY : Finset (Fin n)) (hcov : SX ∪ SY = Finset.univ)
    (μ : X → Y → ℝ) (s : CoreTuple n X Y A B D)
    (hμX : ∀ j ∈ SX \ SY, (∑ y : Y, μ (s.1 j) y) ≠ 0) :
    classMass SX Finset.univ (prodPrior D μ) s
      = classMass SX SY (prodPrior D μ) s *
          ∏ j ∈ SX \ SY, μ (s.1 j) (s.2.1 j) / ∑ y : Y, μ (s.1 j) y := by
  rw [classMass_prodPrior, classMass_prodPrior, ← Finset.univ_inter (SX \ SY),
    ← Finset.prod_ite_mem, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hcov' : j ∉ SX → j ∈ SY := fun h => by
    have : j ∈ SX ∪ SY := by rw [hcov]; exact Finset.mem_univ j
    exact (Finset.mem_union.mp this).resolve_left h
  by_cases hX : j ∈ SX
  · by_cases hY : j ∈ SY
    · have : j ∉ SX \ SY := fun h => (Finset.mem_sdiff.mp h).2 hY
      simp [hX, hY, this]
    · have hmem : j ∈ SX \ SY := Finset.mem_sdiff.mpr ⟨hX, hY⟩
      have h0 := hμX j hmem
      simp only [hX, hY, hmem, Finset.mem_univ, if_true, if_false]
      field_simp
  · have hY := hcov' hX
    have : j ∉ SX \ SY := fun h => hX (Finset.mem_sdiff.mp h).1
    simp [hX, hY, this]


/-! ### Canonical labels along a fiber -/

end TracialStrategy

section Labels

variable [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]

/-- The canonical Alice label reads `xw` only on `R₀` and `yw` only off `R₀`. -/
theorem aLabel_congr (D R₀ : Finset (Fin n)) {xw xw' : Fin n → X} {yw yw' : Fin n → Y}
    (zD : {j : Fin n // j ∈ D} → A)
    (hx : ∀ j ∈ R₀, xw j = xw' j) (hy : ∀ j ∉ R₀, yw j = yw' j) :
    aLabel D R₀ xw yw zD = aLabel D R₀ xw' yw' zD := by
  unfold aLabel
  have h1 : keepOn R₀ xw = keepOn R₀ xw' := by
    funext j
    unfold keepOn
    by_cases hj : j ∈ R₀
    · rw [if_pos hj, if_pos hj, hx j hj]
    · rw [if_neg hj, if_neg hj]
  have h2 : keepOff R₀ yw = keepOff R₀ yw' := by
    funext j
    unfold keepOff
    by_cases hj : j ∈ R₀
    · rw [if_pos hj, if_pos hj]
    · rw [if_neg hj, if_neg hj, hy j hj]
  rw [h1, h2]

/-- The canonical Bob label reads `xw` only off `R₀` and `yw` only on `R₀`. -/
theorem bLabel_congr (D R₀ : Finset (Fin n)) {xw xw' : Fin n → X} {yw yw' : Fin n → Y}
    (zD : {j : Fin n // j ∈ D} → B)
    (hx : ∀ j ∉ R₀, xw j = xw' j) (hy : ∀ j ∈ R₀, yw j = yw' j) :
    bLabel D R₀ xw yw zD = bLabel D R₀ xw' yw' zD := by
  unfold bLabel
  have h1 : keepOff R₀ xw = keepOff R₀ xw' := by
    funext j
    unfold keepOff
    by_cases hj : j ∈ R₀
    · rw [if_pos hj, if_pos hj]
    · rw [if_neg hj, if_neg hj, hx j hj]
  have h2 : keepOn R₀ yw = keepOn R₀ yw' := by
    funext j
    unfold keepOn
    by_cases hj : j ∈ R₀
    · rw [if_pos hj, if_pos hj, hy j hj]
    · rw [if_neg hj, if_neg hj]
  rw [h1, h2]

end Labels

namespace RevealDatum

variable {D : Finset (Fin n)} (r : RevealDatum n D)

theorem core_subset_insert_CX : D ⊆ insert r.i r.CX := fun j hj =>
  Finset.mem_insert_of_mem (Finset.mem_inter.mp (r.core_subset hj)).1

theorem core_subset_insert_CY : D ⊆ insert r.i r.CY := fun j hj =>
  Finset.mem_insert_of_mem (Finset.mem_inter.mp (r.core_subset hj)).2

/-- Every coordinate is revealed to one side (eq reveal-cover). -/
theorem covX {j : Fin n} (hj : j ∉ insert r.i r.CX) : j ∈ insert r.i r.CY := by
  have hji : j ≠ r.i := by
    rintro rfl
    exact hj (Finset.mem_insert_self _ _)
  have hmem : j ∈ r.CX ∪ r.CY := by
    rw [r.union_eq_compl_singleton]
    simpa using hji
  rcases Finset.mem_union.mp hmem with h | h
  · exact absurd (Finset.mem_insert_of_mem h) hj
  · exact Finset.mem_insert_of_mem h

theorem covY {j : Fin n} (hj : j ∉ insert r.i r.CY) : j ∈ insert r.i r.CX := by
  have hji : j ≠ r.i := by
    rintro rfl
    exact hj (Finset.mem_insert_self _ _)
  have hmem : j ∈ r.CX ∪ r.CY := by
    rw [r.union_eq_compl_singleton]
    simpa using hji
  rcases Finset.mem_union.mp hmem with h | h
  · exact Finset.mem_insert_of_mem h
  · exact absurd (Finset.mem_insert_of_mem h) hj

theorem card_lt (r : RevealDatum n D) : D.card < n := by
  have h : D ⊂ Finset.univ := Finset.ssubset_univ_iff.mpr fun h =>
    r.i_notMem (Finset.eq_univ_iff_forall.mp h r.i)
  have := Finset.card_lt_card h
  simpa using this

theorem revealLaw_pos : 0 < r.revealLaw := by
  have hm : (0 : ℝ) < ((n - D.card : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt r.card_lt
  unfold revealLaw
  positivity

end RevealDatum

/-- Grouped masses agree once every fiber sum agrees. -/
theorem groupedMass_ext_of_fibers {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (g : ι → κ) (f f' : ι → ℝ)
    (h : ∀ t, (∑ t', if g t' = g t then f t' else 0) = ∑ t', if g t' = g t then f' t' else 0)
    (u : κ) :
    ClassicalInformation.groupedMass g f u = ClassicalInformation.groupedMass g f' u := by
  rw [HistoryKL.groupedMass_eq_sum_ite, HistoryKL.groupedMass_eq_sum_ite]
  by_cases hu : ∃ t, g t = u
  · obtain ⟨t, rfl⟩ := hu
    exact h t
  · have hu' : ∀ t, g t ≠ u := fun t ht => hu ⟨t, ht⟩
    rw [Finset.sum_eq_zero fun t' _ => if_neg (hu' t'),
      Finset.sum_eq_zero fun t' _ => if_neg (hu' t')]

namespace TracialStrategy

variable [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
variable (S : TracialStrategy.{0}
  (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B))
variable {D : Finset (Fin n)}
variable {Af Bf : Type} [Fintype Af] [Fintype Bf]

/-! ### The fiber collapse of the posterior branch law -/

/-- The fibers of the flattening: same datum, same core word, and the
words agree on `{i} ∪ C_X` resp. `{i} ∪ C_Y`. -/
theorem flattenPost_eq_iff (t t' : PostTuple n X Y A B D) :
    flattenPost t' = flattenPost t
      ↔ t'.1 = t.1 ∧ agreesOn (insert t.1.i t.1.CX) t'.2.1 t.2.1 ∧
          agreesOn (insert t.1.i t.1.CY) t'.2.2.1 t.2.2.1 ∧ t'.2.2.2 = t.2.2.2 := by
  obtain ⟨r, xw, yw, zD⟩ := t
  obtain ⟨r', xw', yw', zD'⟩ := t'
  simp only [flattenPost, histCore, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨rfl, h1, h2, h3⟩, h4, h5⟩
    refine ⟨rfl, ?_, ?_, h3⟩
    · exact agreesOn_insert_iff.mpr ⟨h4, (keepOn_eq_iff _ _ _).mp h1⟩
    · exact agreesOn_insert_iff.mpr ⟨h5, (keepOn_eq_iff _ _ _).mp h2⟩
  · rintro ⟨rfl, h1, h2, h3⟩
    obtain ⟨h1i, h1⟩ := agreesOn_insert_iff.mp h1
    obtain ⟨h2i, h2⟩ := agreesOn_insert_iff.mp h2
    exact ⟨⟨rfl, (keepOn_eq_iff _ _ _).mpr h1, (keepOn_eq_iff _ _ _).mpr h2, h3⟩, h1i, h2i⟩

open Classical in
/-- A fiber sum of the flattening, as a double word sum. -/
theorem sum_fiber_flattenPost (F : PostTuple n X Y A B D → ℝ) (t : PostTuple n X Y A B D) :
    (∑ t' : PostTuple n X Y A B D, if flattenPost t' = flattenPost t then F t' else 0)
      = ∑ xw' : Fin n → X, ∑ yw' : Fin n → Y,
          if agreesOn (insert t.1.i t.1.CX) xw' t.2.1 ∧ agreesOn (insert t.1.i t.1.CY) yw' t.2.2.1
          then F (t.1, xw', yw', t.2.2.2) else 0 := by
  classical
  obtain ⟨r, xw, yw, zD⟩ := t
  simp only [flattenPost_eq_iff]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single r]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun xw' _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun yw' _ => ?_
    rw [Finset.sum_eq_single zD]
    · simp only [true_and, and_true]
    · intro zD' _ hne
      rw [if_neg]
      rintro ⟨-, -, -, h⟩
      exact hne h
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro r' _ hne
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [if_neg]
    rintro ⟨h, -⟩
    exact hne h
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Branch mass at the full canonical labels: the effective-effect pairing. -/
theorem branch_normSq_eq (μ : X → Y → ℝ)
    {Ffam : ALabel n X Y A → Af → S.M.A}
    {Gfam : BLabel n X Y B → Bf → S.M.A}
    (R : ResolverArena S.M Ffam Gfam)
    (htotF : ∀ s : ALabel n X Y A,
      (∑ a : Af, Ffam s a) = S.setEffectA D s.1 μ s.2.1 s.2.2.1 s.2.2.2)
    (htotG : ∀ t : BLabel n X Y B,
      (∑ b : Bf, Gfam t b) = S.setEffectB D t.1 μ t.2.1 t.2.2.1 t.2.2.2)
    (r : RevealDatum n D) (xw : Fin n → X) (yw : Fin n → Y)
    (zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B)) :
    ‖R.branch S.σ (aLabel D (insert r.i r.CX) xw yw zD.1)
        (bLabel D (insert r.i r.CY) xw yw zD.2)‖ ^ 2
      = (S.M.τ (star S.σ *
          (S.effectiveH r μ xw yw (extendCoreA D zD.1) * S.σ *
            S.effectiveK r μ xw yw (extendCoreB D zD.2)))).re := by
  have htF : (∑ a : Af, Ffam (aLabel D (insert r.i r.CX) xw yw zD.1) a)
      = S.setEffectA D (insert r.i r.CX) μ (keepOn (insert r.i r.CX) xw)
          (keepOff (insert r.i r.CX) yw) (extendCoreA D zD.1) :=
    htotF (aLabel D (insert r.i r.CX) xw yw zD.1)
  have htG : (∑ b : Bf, Gfam (bLabel D (insert r.i r.CY) xw yw zD.2) b)
      = S.setEffectB D (insert r.i r.CY) μ (keepOff (insert r.i r.CY) xw)
          (keepOn (insert r.i r.CY) yw) (extendCoreB D zD.2) :=
    htotG (bLabel D (insert r.i r.CY) xw yw zD.2)
  have hcanA : S.setEffectA D (insert r.i r.CX) μ (keepOn (insert r.i r.CX) xw)
      (keepOff (insert r.i r.CX) yw) (extendCoreA D zD.1)
      = S.setEffectA D (insert r.i r.CX) μ xw yw (extendCoreA D zD.1) :=
    S.setEffectA_congr D _ μ _ (fun j hj => by simp [keepOn, hj])
      (fun j hj => by simp [keepOff, hj])
  have hcanB : S.setEffectB D (insert r.i r.CY) μ (keepOff (insert r.i r.CY) xw)
      (keepOn (insert r.i r.CY) yw) (extendCoreB D zD.2)
      = S.setEffectB D (insert r.i r.CY) μ xw yw (extendCoreB D zD.2) :=
    S.setEffectB_congr D _ μ _ (fun j hj => by simp [keepOff, hj])
      (fun j hj => by simp [keepOn, hj])
  have hb := R.branch_norm S.σ (aLabel D (insert r.i r.CX) xw yw zD.1)
    (bLabel D (insert r.i r.CY) xw yw zD.2)
  rw [htF, htG, hcanA, hcanB,
    ← S.effectiveH_eq_setEffectA r μ xw yw (extendCoreA D zD.1),
    ← S.effectiveK_eq_setEffectB r μ xw yw (extendCoreB D zD.2),
    inner_self_eq_norm_sq_to_K] at hb
  rw [← hb]
  norm_cast

/-- **The fiber collapse** (eq posterior-branch-law through eqs
branch-probability and prior-factorization): over a flattening fiber the
posterior branch law sums to the reveal law times the core posterior class
mass. -/
theorem posteriorQ_fiber (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    {Ffam : ALabel n X Y A → Af → S.M.A}
    {Gfam : BLabel n X Y B → Bf → S.M.A}
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
    (p : ℝ) (r : RevealDatum n D) (xw : Fin n → X) (yw : Fin n → Y)
    (zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B)) :
    (∑ xw' : Fin n → X, ∑ yw' : Fin n → Y,
      if agreesOn (insert r.i r.CX) xw' xw ∧ agreesOn (insert r.i r.CY) yw' yw then
        S.posteriorQ R D μ w p (r, xw', yw', zD) else 0)
      = r.revealLaw *
          classMass (insert r.i r.CX) (insert r.i r.CY) (S.corePost D μ w p) (xw, yw, zD) := by
  classical
  have hDX : D ⊆ insert r.i r.CX := r.core_subset_insert_CX
  have hDY : D ⊆ insert r.i r.CY := r.core_subset_insert_CY
  set w₀ := w xw yw zD.1 zD.2 with hw₀
  set B₀ := ‖R.branch S.σ (aLabel D (insert r.i r.CX) xw yw zD.1)
    (bLabel D (insert r.i r.CY) xw yw zD.2)‖ ^ 2 with hB₀
  have hwconst : ∀ (xw' : Fin n → X) (yw' : Fin n → Y),
      agreesOn (insert r.i r.CX) xw' xw → agreesOn (insert r.i r.CY) yw' yw →
      w xw' yw' zD.1 zD.2 = w₀ := fun xw' yw' hx hy =>
    hwD xw' xw yw' yw zD.1 zD.2 (agreesOn_mono hDX hx) (agreesOn_mono hDY hy)
  -- Step 1: the posterior fiber sum in terms of the conditioned prior weight.
  have hL : (∑ xw' : Fin n → X, ∑ yw' : Fin n → Y,
      if agreesOn (insert r.i r.CX) xw' xw ∧ agreesOn (insert r.i r.CY) yw' yw then
        S.posteriorQ R D μ w p (r, xw', yw', zD) else 0)
      = r.revealLaw * (w₀ * B₀ / p) *
          ∑ xw' : Fin n → X, ∑ yw' : Fin n → Y, priorWeight r μ xw yw xw' yw' := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun xw' _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun yw' _ => ?_
    unfold priorWeight
    by_cases h : agreesOn (insert r.i r.CX) xw' xw ∧ agreesOn (insert r.i r.CY) yw' yw
    · rw [if_pos h, if_pos h]
      have hA : aLabel D (insert r.i r.CX) xw' yw' zD.1 = aLabel D (insert r.i r.CX) xw yw zD.1 :=
        aLabel_congr D _ zD.1 (fun j hj => h.1 j hj) (fun j hj => h.2 j (r.covX hj))
      have hB : bLabel D (insert r.i r.CY) xw' yw' zD.2 = bLabel D (insert r.i r.CY) xw yw zD.2 :=
        bLabel_congr D _ zD.2 (fun j hj => h.1 j (r.covY hj)) (fun j hj => h.2 j hj)
      unfold posteriorQ
      dsimp only
      rw [hwconst xw' yw' h.1 h.2, hA, hB]
      ring
    · rw [if_neg h, if_neg h, mul_zero]
  -- Step 2: the core class mass in terms of the conditioned prior weight.
  have hR : classMass (insert r.i r.CX) (insert r.i r.CY) (S.corePost D μ w p) (xw, yw, zD)
      = (w₀ / p) * ∑ xw' : Fin n → X, ∑ yw' : Fin n → Y,
          priorWeight r μ xw yw xw' yw' * S.corePair D (xw', yw', zD) := by
    unfold classMass
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun xw' _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun yw' _ => ?_
    unfold priorWeight
    dsimp only
    by_cases h : agreesOn (insert r.i r.CX) xw' xw ∧ agreesOn (insert r.i r.CY) yw' yw
    · rw [if_pos h, if_pos h]
      unfold corePost prodPrior
      dsimp only
      rw [hwconst xw' yw' h.1 h.2]
      ring
    · rw [if_neg h, if_neg h]
      ring
  -- Step 3: the branch mass times the fiber mass is the pairing mass.
  have hpw0 : ∀ (xw' : Fin n → X) (yw' : Fin n → Y), 0 ≤ priorWeight r μ xw yw xw' yw' := by
    intro xw' yw'
    unfold priorWeight
    split_ifs
    · exact Finset.prod_nonneg fun j _ => hμ _ _
    · exact le_rfl
  have hkey : B₀ * (∑ xw' : Fin n → X, ∑ yw' : Fin n → Y, priorWeight r μ xw yw xw' yw')
      = ∑ xw' : Fin n → X, ∑ yw' : Fin n → Y,
          priorWeight r μ xw yw xw' yw' * S.corePair D (xw', yw', zD) := by
    have hcorr : ∀ (xw' : Fin n → X) (yw' : Fin n → Y),
        (∑ as : Fin n → A, ∑ bs : Fin n → B,
          if agreesOn D as (extendCoreA D zD.1) ∧ agreesOn D bs (extendCoreB D zD.2) then
            S.correlation xw' yw' as bs else 0) = S.corePair D (xw', yw', zD) :=
      fun xw' yw' => S.coreEffect_correlation D xw' yw' _ _
    have hB₀' : B₀ = (S.M.τ (star S.σ *
        (S.effectiveH r μ xw yw (extendCoreA D zD.1) * S.σ *
          S.effectiveK r μ xw yw (extendCoreB D zD.2)))).re :=
      S.branch_normSq_eq μ R htotF htotG r xw yw zD
    rcases (Finset.sum_nonneg fun xw' _ => Finset.sum_nonneg fun yw' _ => hpw0 xw' yw').lt_or_eq
      with hM | hM
    · have hbp := S.branch_probability r μ xw yw (extendCoreA D zD.1) (extendCoreB D zD.2) hM
      rw [Finset.sum_congr rfl fun xw' _ => Finset.sum_congr rfl fun yw' _ => by
        rw [hcorr xw' yw']] at hbp
      rw [hB₀', ← hbp, div_mul_cancel₀ _ hM.ne']
    · have hz := (Finset.sum_eq_zero_iff_of_nonneg fun xw' _ =>
        Finset.sum_nonneg fun yw' _ => hpw0 xw' yw').mp hM.symm
      rw [← hM, mul_zero]
      symm
      refine Finset.sum_eq_zero fun xw' _ => ?_
      have hz' := (Finset.sum_eq_zero_iff_of_nonneg fun yw' _ => hpw0 xw' yw').mp
        (hz xw' (Finset.mem_univ _))
      exact Finset.sum_eq_zero fun yw' _ => by rw [hz' yw' (Finset.mem_univ _), zero_mul]
  rw [hL, hR, ← hkey]
  ring

open Classical in
/-- **The pushforward identity** (F0): the flattened posterior is the
pushforward of `revealLaw ⊗ ℚ⁰` under the flattening. -/
theorem flatQ_eq (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    {Ffam : ALabel n X Y A → Af → S.M.A}
    {Gfam : BLabel n X Y B → Bf → S.M.A}
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
    (p : ℝ) (u : PostTuple n X Y A B D × X × Y) :
    S.flatQ R D μ w p u
      = ClassicalInformation.groupedMass (flattenPost (D := D))
          (fun t : PostTuple n X Y A B D => t.1.revealLaw * S.corePost D μ w p t.2) u := by
  classical
  unfold flatQ
  refine groupedMass_ext_of_fibers _ _ _ (fun t => ?_) u
  rw [sum_fiber_flattenPost, sum_fiber_flattenPost]
  obtain ⟨r, xw, yw, zD⟩ := t
  rw [S.posteriorQ_fiber μ hμ R htotF htotG w hwD p r xw yw zD]
  unfold classMass
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun xw' _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun yw' _ => ?_
  dsimp only
  split_ifs <;> simp

/-- (F1) The flattened posterior at a flattened tuple. -/
theorem flatQ_flattenPost (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    {Ffam : ALabel n X Y A → Af → S.M.A}
    {Gfam : BLabel n X Y B → Bf → S.M.A}
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
    S.flatQ R D μ w p (flattenPost t)
      = t.1.revealLaw *
          classMass (insert t.1.i t.1.CX) (insert t.1.i t.1.CY) (S.corePost D μ w p) t.2 := by
  classical
  rw [S.flatQ_eq μ hμ R htotF htotG w hwD p, HistoryKL.groupedMass_eq_sum_ite,
    sum_fiber_flattenPost]
  obtain ⟨r, xw, yw, zD⟩ := t
  unfold classMass
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun xw' _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun yw' _ => ?_
  dsimp only
  split_ifs <;> simp

/-- (F2) The flattened posterior summed over the live Bob question. -/
theorem sum_flatQ_hist (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    {Ffam : ALabel n X Y A → Af → S.M.A}
    {Gfam : BLabel n X Y B → Bf → S.M.A}
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
    (∑ y : Y, S.flatQ R D μ w p (histCore t, t.2.1 t.1.i, y))
      = t.1.revealLaw * classMass (insert t.1.i t.1.CX) t.1.CY (S.corePost D μ w p) t.2 := by
  classical
  obtain ⟨r, xw, yw, zD⟩ := t
  have hflat : ∀ y : Y, (histCore (r, xw, yw, zD), xw r.i, y)
      = flattenPost (r, xw, Function.update yw r.i y, zD) := by
    intro y
    simp only [flattenPost, histCore, Function.update_self, Prod.mk.injEq, true_and, and_true]
    funext j
    unfold keepOn
    by_cases hj : j ∈ r.CY
    · rw [if_pos hj, if_pos hj, Function.update_of_ne]
      rintro rfl
      exact r.i_notMem_CY hj
    · rw [if_neg hj, if_neg hj]
  simp only [hflat, S.flatQ_flattenPost μ hμ R htotF htotG w hwD p]
  rw [← Finset.mul_sum]
  congr 1
  unfold classMass
  dsimp only
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun xw' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun yw' _ => ?_
  have hiff : ∀ y : Y, agreesOn (insert r.i r.CY) yw' (Function.update yw r.i y)
      ↔ yw' r.i = y ∧ agreesOn r.CY yw' yw := by
    intro y
    rw [agreesOn_insert_iff, Function.update_self]
    refine and_congr_right fun _ => ?_
    constructor
    · intro h j hj
      rw [h j hj, Function.update_of_ne]
      rintro rfl
      exact r.i_notMem_CY hj
    · intro h j hj
      rw [h j hj, Function.update_of_ne]
      rintro rfl
      exact r.i_notMem_CY hj
  simp only [hiff]
  rw [Finset.sum_eq_single (yw' r.i)]
  · simp
  · intro y _ hne
    rw [if_neg]
    rintro ⟨-, h, -⟩
    exact hne h.symm
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- (F3) The flattened posterior mass of a live coordinate and live Alice
question: the reveal law's fiber mass times the core marginal. -/
theorem sum_flatQ_live (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    {Ffam : ALabel n X Y A → Af → S.M.A}
    {Gfam : BLabel n X Y B → Bf → S.M.A}
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
    (p : ℝ) (i₀ : Fin n) (x : X) :
    (∑ h : PostTuple n X Y A B D,
      if h.1.i = i₀ then ∑ y : Y, S.flatQ R D μ w p (h, x, y) else 0)
      = (∑ r : RevealDatum n D, if r.i = i₀ then r.revealLaw else 0) *
          ∑ s : CoreTuple n X Y A B D, if s.1 i₀ = x then S.corePost D μ w p s else 0 := by
  classical
  have hL : (∑ h : PostTuple n X Y A B D,
      if h.1.i = i₀ then ∑ y : Y, S.flatQ R D μ w p (h, x, y) else 0)
      = ∑ u : PostTuple n X Y A B D × X × Y,
          S.flatQ R D μ w p u * (if u.1.1.i = i₀ ∧ u.2.1 = x then 1 else 0) := by
    rw [Fintype.sum_prod_type (f := fun u : PostTuple n X Y A B D × X × Y =>
      S.flatQ R D μ w p u * (if u.1.1.i = i₀ ∧ u.2.1 = x then (1 : ℝ) else 0))]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Fintype.sum_prod_type (f := fun q : X × Y =>
      S.flatQ R D μ w p (h, q) * (if h.1.i = i₀ ∧ q.1 = x then (1 : ℝ) else 0)),
      Finset.sum_eq_single x]
    · by_cases hi : h.1.i = i₀
      · simp [hi]
      · simp [hi]
    · intro x' _ hx'
      exact Finset.sum_eq_zero fun y _ => by simp [hx']
    · intro h
      exact absurd (Finset.mem_univ x) h
  rw [hL]
  simp only [S.flatQ_eq μ hμ R htotF htotG w hwD p]
  rw [HistoryKL.sum_groupedMass_mul (flattenPost (D := D))
    (fun t : PostTuple n X Y A B D => t.1.revealLaw * S.corePost D μ w p t.2)
    (fun u => if u.1.1.i = i₀ ∧ u.2.1 = x then (1 : ℝ) else 0)]
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

theorem posteriorQ_nonneg (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    {Ffam : ALabel n X Y A → Af → S.M.A}
    {Gfam : BLabel n X Y B → Bf → S.M.A}
    (R : ResolverArena S.M Ffam Gfam)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB) {p : ℝ} (hppos : 0 < p)
    (t : PostTuple n X Y A B D) : 0 ≤ S.posteriorQ R D μ w p t := by
  unfold posteriorQ
  have h1 := t.1.revealLaw_nonneg
  have h2 : 0 ≤ ∏ j : Fin n, μ (t.2.1 j) (t.2.2.1 j) := Finset.prod_nonneg fun j _ => hμ _ _
  have h3 := hw0 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2
  positivity

theorem flatQ_nonneg (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    {Ffam : ALabel n X Y A → Af → S.M.A}
    {Gfam : BLabel n X Y B → Bf → S.M.A}
    (R : ResolverArena S.M Ffam Gfam)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB) {p : ℝ} (hppos : 0 < p)
    (u : PostTuple n X Y A B D × X × Y) : 0 ≤ S.flatQ R D μ w p u := by
  unfold flatQ
  exact Finset.sum_nonneg fun t _ => S.posteriorQ_nonneg μ hμ R w hw0 hppos t

/-- The flattened posterior is a probability law (eq
posterior-branch-normalization pushed forward). -/
theorem sum_flatQ (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    {Ffam : ALabel n X Y A → Af → S.M.A}
    {Gfam : BLabel n X Y B → Bf → S.M.A}
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
    {p : ℝ} (hp : p = S.coreMass D μ w) (hppos : 0 < p) (hm : D.card < n) :
    (∑ u : PostTuple n X Y A B D × X × Y, S.flatQ R D μ w p u) = 1 := by
  classical
  unfold flatQ
  rw [HistoryKL.sum_groupedMass]
  exact S.posteriorQ_sum μ hμ R htotF htotG w hwD hp hppos hm

end TracialStrategy

/-! ### The reveal law's fiber mass at a live coordinate -/

namespace RevealDatum

variable {D : Finset (Fin n)}

/-- The reveal law restricted to a fixed live coordinate `i₀ ∉ D` has mass
`1/m` (the live coordinate is uniform on the `m` non-core coordinates; the
same count as `revealLaw_sum`, one fibre of the outer sum). -/
theorem revealLaw_sum_fiber (i₀ : Fin n) (hi₀ : i₀ ∉ D) :
    (∑ d : RevealDatum n D, if d.i = i₀ then d.revealLaw else 0)
      = 1 / ((n - D.card : ℕ) : ℝ) := by
  classical
  have key : (∑ d : RevealDatum n D, if d.i = i₀ then d.revealLaw else 0)
      = ∑ t : Σ i : {i : Fin n // i ∉ D},
          Σ L : {L : Finset (Fin n) // L ⊆ (insert i.1 D)ᶜ},
            ((Fin L.1.card ≃ {j : Fin n // j ∈ L.1}) ×
             (Fin ((insert i.1 D)ᶜ \ L.1).card ≃
               {j : Fin n // j ∈ (insert i.1 D)ᶜ \ L.1}) ×
             Fin (L.1.card + 1) ×
             Fin (((insert i.1 D)ᶜ \ L.1).card + 1)),
          if t.1.1 = i₀ then
            (1 / (n - D.card : ℕ) : ℝ) * (1 / 2 ^ (n - D.card - 1)) *
              (1 / (Nat.factorial t.2.1.1.card)) *
              (1 / (Nat.factorial ((insert t.1.1 D)ᶜ \ t.2.1.1).card)) *
              (1 / (t.2.1.1.card + 1)) *
              (1 / (((insert t.1.1 D)ᶜ \ t.2.1.1).card + 1))
          else 0 := by
    refine Finset.sum_nbij'
      (fun d => ⟨⟨d.i, d.i_notMem⟩, ⟨⟨d.LX, d.LX_subset⟩,
        (d.πX,
         (show d.LY = (insert d.i D)ᶜ \ d.LX by
            rw [← d.partition, Finset.union_sdiff_cancel_left d.disjoint])
           ▸ d.πY,
         d.kX,
         (show d.LY = (insert d.i D)ᶜ \ d.LX by
            rw [← d.partition, Finset.union_sdiff_cancel_left d.disjoint])
           ▸ d.kY)⟩⟩)
      (fun t => { i := t.1.1
                  i_notMem := t.1.2
                  LX := t.2.1.1
                  LY := (insert t.1.1 D)ᶜ \ t.2.1.1
                  disjoint := Finset.disjoint_sdiff
                  partition := Finset.union_sdiff_of_subset t.2.1.2
                  πX := t.2.2.1
                  πY := t.2.2.2.1
                  kX := t.2.2.2.2.1
                  kY := t.2.2.2.2.2 })
      (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _)
      ?_ ?_ ?_
    · rintro ⟨i, hi, LX, LY, hdisj, hpart, πX, πY, kX, kY⟩ _
      have e : LY = ((insert i D)ᶜ : Finset (Fin n)) \ LX := by
        rw [← hpart, Finset.union_sdiff_cancel_left hdisj]
      subst e
      rfl
    · rintro ⟨⟨i, hi⟩, ⟨L, hL⟩, e1, e2, k1, k2⟩ _
      rfl
    · rintro ⟨i, hi, LX, LY, hdisj, hpart, πX, πY, kX, kY⟩ _
      have e : LY = ((insert i D)ᶜ : Finset (Fin n)) \ LX := by
        rw [← hpart, Finset.union_sdiff_cancel_left hdisj]
      subst e
      rfl
  have hfiber : ∀ (i : {i : Fin n // i ∉ D})
      (L : {L : Finset (Fin n) // L ⊆ (insert i.1 D)ᶜ}),
      (∑ _q : ((Fin L.1.card ≃ {j : Fin n // j ∈ L.1}) ×
         (Fin ((insert i.1 D)ᶜ \ L.1).card ≃
           {j : Fin n // j ∈ (insert i.1 D)ᶜ \ L.1}) ×
         Fin (L.1.card + 1) ×
         Fin (((insert i.1 D)ᶜ \ L.1).card + 1)),
        (1 / (n - D.card : ℕ) : ℝ) * (1 / 2 ^ (n - D.card - 1)) *
          (1 / (Nat.factorial L.1.card)) *
          (1 / (Nat.factorial ((insert i.1 D)ᶜ \ L.1).card)) *
          (1 / (L.1.card + 1)) *
          (1 / (((insert i.1 D)ᶜ \ L.1).card + 1)))
      = (1 / (n - D.card : ℕ) : ℝ) * (1 / 2 ^ (n - D.card - 1)) := by
    intro i L
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_prod, Fintype.card_prod,
      Fintype.card_equiv L.1.equivFin.symm,
      Fintype.card_equiv ((insert i.1 D)ᶜ \ L.1).equivFin.symm,
      Fintype.card_fin, Fintype.card_fin, Fintype.card_fin,
      Fintype.card_fin, nsmul_eq_mul]
    have hk : ((Nat.factorial L.1.card : ℝ)) ≠ 0 := by
      exact_mod_cast (Nat.factorial_pos _).ne'
    have hl : ((Nat.factorial ((insert i.1 D)ᶜ \ L.1).card : ℝ)) ≠ 0 := by
      exact_mod_cast (Nat.factorial_pos _).ne'
    have hk1 : ((L.1.card : ℝ) + 1) ≠ 0 := by positivity
    have hl1 : ((((insert i.1 D)ᶜ \ L.1).card : ℝ) + 1) ≠ 0 := by
      positivity
    push_cast
    generalize (Nat.factorial L.1.card : ℝ) = K at hk ⊢
    generalize (Nat.factorial ((insert i.1 D)ᶜ \ L.1).card : ℝ) = Lf
      at hl ⊢
    generalize ((L.1.card : ℝ) + 1) = K1 at hk1 ⊢
    generalize ((((insert i.1 D)ᶜ \ L.1).card : ℝ) + 1) = L1 at hl1 ⊢
    generalize ((n - D.card : ℕ) : ℝ) = M
    generalize ((2 : ℝ) ^ (n - D.card - 1)) = E
    field_simp
  have hstep : ∀ i : {i : Fin n // i ∉ D},
      (∑ p : Σ L : {L : Finset (Fin n) // L ⊆ (insert i.1 D)ᶜ},
          ((Fin L.1.card ≃ {j : Fin n // j ∈ L.1}) ×
           (Fin ((insert i.1 D)ᶜ \ L.1).card ≃
             {j : Fin n // j ∈ (insert i.1 D)ᶜ \ L.1}) ×
           Fin (L.1.card + 1) ×
           Fin (((insert i.1 D)ᶜ \ L.1).card + 1)),
        (1 / (n - D.card : ℕ) : ℝ) * (1 / 2 ^ (n - D.card - 1)) *
          (1 / (Nat.factorial p.1.1.card)) *
          (1 / (Nat.factorial ((insert i.1 D)ᶜ \ p.1.1).card)) *
          (1 / (p.1.1.card + 1)) *
          (1 / (((insert i.1 D)ᶜ \ p.1.1).card + 1)))
      = (1 / (n - D.card : ℕ) : ℝ) := by
    intro i
    rw [← Finset.univ_sigma_univ]
    rw [Finset.sum_sigma]
    calc (∑ L : {L : Finset (Fin n) // L ⊆ (insert i.1 D)ᶜ},
          ∑ _q : ((Fin L.1.card ≃ {j : Fin n // j ∈ L.1}) ×
             (Fin ((insert i.1 D)ᶜ \ L.1).card ≃
               {j : Fin n // j ∈ (insert i.1 D)ᶜ \ L.1}) ×
             Fin (L.1.card + 1) ×
             Fin (((insert i.1 D)ᶜ \ L.1).card + 1)),
            (1 / (n - D.card : ℕ) : ℝ) * (1 / 2 ^ (n - D.card - 1)) *
              (1 / (Nat.factorial L.1.card)) *
              (1 / (Nat.factorial ((insert i.1 D)ᶜ \ L.1).card)) *
              (1 / (L.1.card + 1)) *
              (1 / (((insert i.1 D)ᶜ \ L.1).card + 1)))
        = ∑ _L : {L : Finset (Fin n) // L ⊆ (insert i.1 D)ᶜ},
            (1 / (n - D.card : ℕ) : ℝ) * (1 / 2 ^ (n - D.card - 1)) :=
          Finset.sum_congr rfl fun L _ => hfiber i L
      _ = (1 / (n - D.card : ℕ) : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ]
          have hcardL : Fintype.card
              {L : Finset (Fin n) // L ⊆ (insert i.1 D)ᶜ}
              = 2 ^ (n - D.card - 1) := by
            rw [Fintype.card_subtype]
            have hfilter : (Finset.univ.filter
                fun L : Finset (Fin n) => L ⊆ (insert i.1 D)ᶜ)
                = ((insert i.1 D)ᶜ : Finset (Fin n)).powerset := by
              ext L
              simp [Finset.mem_powerset]
            rw [hfilter, Finset.card_powerset, Finset.card_compl,
              Finset.card_insert_of_notMem i.2, Fintype.card_fin,
              Nat.sub_sub]
          rw [hcardL, nsmul_eq_mul]
          have h2 : ((2 : ℝ) ^ (n - D.card - 1)) ≠ 0 := by positivity
          push_cast
          generalize hE : ((2 : ℝ) ^ (n - D.card - 1)) = E at h2 ⊢
          generalize ((n - D.card : ℕ) : ℝ) = M
          field_simp
  rw [key, ← Finset.univ_sigma_univ, Finset.sum_sigma,
    Finset.sum_eq_single (⟨i₀, hi₀⟩ : {i : Fin n // i ∉ D})]
  · exact (Finset.sum_congr rfl fun p _ => if_pos rfl).trans (hstep ⟨i₀, hi₀⟩)
  · intro i _ hne
    refine Finset.sum_eq_zero fun p _ => if_neg ?_
    intro h
    exact hne (Subtype.ext h)
  · intro h
    exact absurd (Finset.mem_univ _) h

end RevealDatum

end CommutingRepetition
