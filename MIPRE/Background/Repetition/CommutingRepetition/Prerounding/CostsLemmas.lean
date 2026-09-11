/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Prerounding/CostsLemmas.lean
-/
/-
# Scenario reveal martingales and the consumed column budget (node 1.2.9,
proof layer 2)

Second proof-side layer for `TracialStrategy.prior_alignment_bound`
(`Prerounding/Costs.lean`), built on the base helpers of `CostsLemmas0`.

- `scenMartA` — the Alice-side scenario reveal martingale: the path space
  is the Alice values on a progressively revealed block `L`, the law is
  the pinned-Bob conditional product weight (normalized by the block
  mass), and the index path is the canonical Alice label at the growing
  revealed set `SA ∪ π[1..j]`, freezing the off-block values to a
  background `g`.
- `scenMartA_isMeanTower` — this datum is a mass-weighted mean tower for
  the arena's Alice totals (`setEffectA_reveal`, fiber-refined): the
  law-weighted average of the next revealed-set effect on each fiber of
  the current canonical label is the current effect. This is the
  hypothesis the signed column budget (batch #13) consumes.
- `scenMartA_colBudget` — feeding the mean tower to `ColEntropyBudget`
  bounds the total law-weighted squared L²-increment of the branch
  vectors along the scenario reveal by the scalar entropy `H₁` of the
  initial branch pairing. Node 1.2.9 telescopes this at the uniform cut.
- `scenMartB`, `scenMartB_isMeanTower`, `scenMartB_rowBudget` — the
  Bob-side mirror (revealing the Bob values, pinned Alice reference),
  feeding `RowEntropyBudget` for the `I_B` bound.

Everything here is proof-side: no statement of a frozen batch is
restated.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Prerounding.CostsLemmas0

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

set_option linter.unusedSectionVars false

namespace CommutingRepetition

open scoped BigOperators InnerProductSpace

variable {n : ℕ} {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
variable [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]

variable {D : Finset (Fin n)}

/-- The Alice-side scenario reveal martingale: the path space is the
Alice values on the progressively revealed block `L`, the law is the
product of the pinned-Bob conditional weights (normalized by the total
block mass), and the index path is the canonical Alice label at the
growing revealed set `SA ∪ π[1..j]`, with the off-block values frozen
to the background `g`. -/
noncomputable def scenMartA (SA L : Finset (Fin n))
    (hdisj : Disjoint SA L)
    (π : Fin L.card ≃ {j : Fin n // j ∈ L}) (μ : X → Y → ℝ)
    (yw : Fin n → Y) (g : {j : Fin n // ¬ j ∈ L} → X)
    (za : {j : Fin n // j ∈ D} → A)
    (hμ : ∀ x y, 0 ≤ μ x y)
    (hM : (∏ c : {j : Fin n // j ∈ L}, ∑ v : X, μ v (yw c)) ≠ 0) :
    EffectMartingale
      (Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → A))
      L.card where
  Ω := {j : Fin n // j ∈ L} → X
  law ω := (∏ c : {j : Fin n // j ∈ L}, μ (ω c) (yw c)) /
    ∏ c : {j : Fin n // j ∈ L}, ∑ v : X, μ v (yw c)
  law_nonneg ω := div_nonneg
    (Finset.prod_nonneg fun c _ => hμ _ _)
    (Finset.prod_nonneg fun c _ => Finset.sum_nonneg fun v _ => hμ _ _)
  law_sum := by
    rw [← Finset.sum_div, sum_prod_pi_subtype L fun c v => μ v (yw c),
      div_self hM]
  idx j ω := mkALabel D (SA ∪ ordPrefix π (j : ℕ))
    ((wordSplit L X).symm (ω, g)) yw za
  idx_zero ω ω' := by
    refine mkALabel_congr D _ za (fun j hj => ?_) (fun _ _ => rfl)
    rcases Finset.mem_union.mp hj with h | h
    · have hjL : ¬ j ∈ L := fun hL => Finset.disjoint_left.mp hdisj h hL
      rw [wordSplit_symm_notMem L X ω g hjL,
        wordSplit_symm_notMem L X ω' g hjL]
    · simp only [Fin.val_zero, ordPrefix_zero] at h
      exact absurd h (Finset.notMem_empty j)

theorem scenMartA_law (SA L : Finset (Fin n)) (hdisj : Disjoint SA L)
    (π : Fin L.card ≃ {j : Fin n // j ∈ L}) (μ : X → Y → ℝ)
    (yw : Fin n → Y) (g : {j : Fin n // ¬ j ∈ L} → X)
    (za : {j : Fin n // j ∈ D} → A) (hμ : ∀ x y, 0 ≤ μ x y)
    (hM : (∏ c : {j : Fin n // j ∈ L}, ∑ v : X, μ v (yw c)) ≠ 0)
    (ω : {j : Fin n // j ∈ L} → X) :
    (scenMartA SA L hdisj π μ yw g za hμ hM).law ω
      = (∏ c : {j : Fin n // j ∈ L}, μ (ω c) (yw c)) /
        ∏ c : {j : Fin n // j ∈ L}, ∑ v : X, μ v (yw c) := rfl

theorem scenMartA_idx (SA L : Finset (Fin n)) (hdisj : Disjoint SA L)
    (π : Fin L.card ≃ {j : Fin n // j ∈ L}) (μ : X → Y → ℝ)
    (yw : Fin n → Y) (g : {j : Fin n // ¬ j ∈ L} → X)
    (za : {j : Fin n // j ∈ D} → A) (hμ : ∀ x y, 0 ≤ μ x y)
    (hM : (∏ c : {j : Fin n // j ∈ L}, ∑ v : X, μ v (yw c)) ≠ 0)
    (j : Fin (L.card + 1)) (ω : {j : Fin n // j ∈ L} → X) :
    (scenMartA SA L hdisj π μ yw g za hμ hM).idx j ω
      = mkALabel D (SA ∪ ordPrefix π (j : ℕ))
          ((wordSplit L X).symm (ω, g)) yw za := rfl

/-- The martingale's path-space Fintype `instFintypeΩ` is definitionally the
canonical one on `↥L → X`, but only at `default` transparency, so this
provable (non-`rfl`-trivial) `univ` equality is not skipped by `simp` and
canonicalizes the summation index after `simp only [scenMartA]` leaves the
projected instance behind. -/
theorem scenMartA_univ_eq
    (SA L : Finset (Fin n)) (hdisj : Disjoint SA L)
    (π : Fin L.card ≃ {j : Fin n // j ∈ L}) (μ : X → Y → ℝ)
    (yw : Fin n → Y) (g : {j : Fin n // ¬ j ∈ L} → X)
    (za : {j : Fin n // j ∈ D} → A) (hμ : ∀ x y, 0 ≤ μ x y)
    (hM : (∏ c : {j : Fin n // j ∈ L}, ∑ v : X, μ v (yw c)) ≠ 0) :
    (@Finset.univ ({j : Fin n // j ∈ L} → X)
        (scenMartA SA L hdisj π μ yw g za hμ hM).instFintypeΩ)
      = Finset.univ :=
  Finset.ext fun a => iff_of_true (Finset.mem_univ a) (Finset.mem_univ a)

theorem mem_ordPrefix_iff {L : Finset (Fin n)}
    (π : Fin L.card ≃ {j : Fin n // j ∈ L}) {m : ℕ} {j : Fin n} :
    j ∈ ordPrefix π m ↔ ∃ t : Fin L.card, (t : ℕ) < m ∧ (π t : Fin n) = j := by
  simp only [ordPrefix, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem mem_ordPrefix_of_lt {L : Finset (Fin n)}
    (π : Fin L.card ≃ {j : Fin n // j ∈ L}) {t : Fin L.card} {m : ℕ}
    (ht : (t : ℕ) < m) : (π t : Fin n) ∈ ordPrefix π m :=
  (mem_ordPrefix_iff π).mpr ⟨t, ht, rfl⟩

/-- The Bob-side scenario reveal martingale: the path space is the Bob
values on the progressively revealed block `L`, the law is the
pinned-Alice conditional weight (normalized by the block mass), and the
index path is the canonical Bob label at the growing revealed set
`SA ∪ π[1..j]`, freezing the off-block values to a background `g`. -/
noncomputable def scenMartB (SA L : Finset (Fin n))
    (hdisj : Disjoint SA L)
    (π : Fin L.card ≃ {j : Fin n // j ∈ L}) (μ : X → Y → ℝ)
    (xw : Fin n → X) (g : {j : Fin n // ¬ j ∈ L} → Y)
    (zb : {j : Fin n // j ∈ D} → B)
    (hμ : ∀ x y, 0 ≤ μ x y)
    (hM : (∏ c : {j : Fin n // j ∈ L}, ∑ v : Y, μ (xw c) v) ≠ 0) :
    EffectMartingale
      (Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → B))
      L.card where
  Ω := {j : Fin n // j ∈ L} → Y
  law ω := (∏ c : {j : Fin n // j ∈ L}, μ (xw c) (ω c)) /
    ∏ c : {j : Fin n // j ∈ L}, ∑ v : Y, μ (xw c) v
  law_nonneg ω := div_nonneg
    (Finset.prod_nonneg fun c _ => hμ _ _)
    (Finset.prod_nonneg fun c _ => Finset.sum_nonneg fun v _ => hμ _ _)
  law_sum := by
    rw [← Finset.sum_div, sum_prod_pi_subtype L fun c v => μ (xw c) v,
      div_self hM]
  idx j ω := mkBLabel D (SA ∪ ordPrefix π (j : ℕ))
    xw ((wordSplit L Y).symm (ω, g)) zb
  idx_zero ω ω' := by
    refine mkBLabel_congr D _ zb (fun _ _ => rfl) (fun j hj => ?_)
    rcases Finset.mem_union.mp hj with h | h
    · have hjL : ¬ j ∈ L := fun hL => Finset.disjoint_left.mp hdisj h hL
      rw [wordSplit_symm_notMem L Y ω g hjL,
        wordSplit_symm_notMem L Y ω' g hjL]
    · simp only [Fin.val_zero, ordPrefix_zero] at h
      exact absurd h (Finset.notMem_empty j)

theorem scenMartB_law (SA L : Finset (Fin n)) (hdisj : Disjoint SA L)
    (π : Fin L.card ≃ {j : Fin n // j ∈ L}) (μ : X → Y → ℝ)
    (xw : Fin n → X) (g : {j : Fin n // ¬ j ∈ L} → Y)
    (zb : {j : Fin n // j ∈ D} → B) (hμ : ∀ x y, 0 ≤ μ x y)
    (hM : (∏ c : {j : Fin n // j ∈ L}, ∑ v : Y, μ (xw c) v) ≠ 0)
    (ω : {j : Fin n // j ∈ L} → Y) :
    (scenMartB SA L hdisj π μ xw g zb hμ hM).law ω
      = (∏ c : {j : Fin n // j ∈ L}, μ (xw c) (ω c)) /
        ∏ c : {j : Fin n // j ∈ L}, ∑ v : Y, μ (xw c) v := rfl

theorem scenMartB_idx (SA L : Finset (Fin n)) (hdisj : Disjoint SA L)
    (π : Fin L.card ≃ {j : Fin n // j ∈ L}) (μ : X → Y → ℝ)
    (xw : Fin n → X) (g : {j : Fin n // ¬ j ∈ L} → Y)
    (zb : {j : Fin n // j ∈ D} → B) (hμ : ∀ x y, 0 ≤ μ x y)
    (hM : (∏ c : {j : Fin n // j ∈ L}, ∑ v : Y, μ (xw c) v) ≠ 0)
    (j : Fin (L.card + 1)) (ω : {j : Fin n // j ∈ L} → Y) :
    (scenMartB SA L hdisj π μ xw g zb hμ hM).idx j ω
      = mkBLabel D (SA ∪ ordPrefix π (j : ℕ))
          xw ((wordSplit L Y).symm (ω, g)) zb := rfl

/-- Bob-side Fintype canonicalization (mirror of `scenMartA_univ_eq`). -/
theorem scenMartB_univ_eq
    (SA L : Finset (Fin n)) (hdisj : Disjoint SA L)
    (π : Fin L.card ≃ {j : Fin n // j ∈ L}) (μ : X → Y → ℝ)
    (xw : Fin n → X) (g : {j : Fin n // ¬ j ∈ L} → Y)
    (zb : {j : Fin n // j ∈ D} → B) (hμ : ∀ x y, 0 ≤ μ x y)
    (hM : (∏ c : {j : Fin n // j ∈ L}, ∑ v : Y, μ (xw c) v) ≠ 0) :
    (@Finset.univ ({j : Fin n // j ∈ L} → Y)
        (scenMartB SA L hdisj π μ xw g zb hμ hM).instFintypeΩ)
      = Finset.univ :=
  Finset.ext fun a => iff_of_true (Finset.mem_univ a) (Finset.mem_univ a)

/-- **Block-law renormalization, Alice** (node 1.2.9 assembly step (2)):
the scenario law times the total block mass `M₀` is the unnormalized
block product weight `∏_{c∈L} μ(ω c, yw c)`. This converts the
martingale's law-weighted block-value sum into the `alignCostA`
reference-word prior sum after the `wordSplit` at `L`. -/
theorem scenMartA_law_mul_M0 (SA L : Finset (Fin n)) (hdisj : Disjoint SA L)
    (π : Fin L.card ≃ {j : Fin n // j ∈ L}) (μ : X → Y → ℝ)
    (yw : Fin n → Y) (g : {j : Fin n // ¬ j ∈ L} → X)
    (za : {j : Fin n // j ∈ D} → A) (hμ : ∀ x y, 0 ≤ μ x y)
    (hM : (∏ c : {j : Fin n // j ∈ L}, ∑ v : X, μ v (yw c)) ≠ 0)
    (ω : {j : Fin n // j ∈ L} → X) :
    (scenMartA SA L hdisj π μ yw g za hμ hM).law ω *
        (∏ c : {j : Fin n // j ∈ L}, ∑ v : X, μ v (yw c))
      = ∏ c : {j : Fin n // j ∈ L}, μ (ω c) (yw c) := by
  rw [scenMartA_law, div_mul_eq_mul_div, mul_div_assoc, div_self hM, mul_one]

/-- **Block-law renormalization, Bob** (mirror of `scenMartA_law_mul_M0`). -/
theorem scenMartB_law_mul_M0 (SA L : Finset (Fin n)) (hdisj : Disjoint SA L)
    (π : Fin L.card ≃ {j : Fin n // j ∈ L}) (μ : X → Y → ℝ)
    (xw : Fin n → X) (g : {j : Fin n // ¬ j ∈ L} → Y)
    (zb : {j : Fin n // j ∈ D} → B) (hμ : ∀ x y, 0 ≤ μ x y)
    (hM : (∏ c : {j : Fin n // j ∈ L}, ∑ v : Y, μ (xw c) v) ≠ 0)
    (ω : {j : Fin n // j ∈ L} → Y) :
    (scenMartB SA L hdisj π μ xw g zb hμ hM).law ω *
        (∏ c : {j : Fin n // j ∈ L}, ∑ v : Y, μ (xw c) v)
      = ∏ c : {j : Fin n // j ∈ L}, μ (xw c) (ω c) := by
  rw [scenMartB_law, div_mul_eq_mul_div, mul_div_assoc, div_self hM, mul_one]

namespace TracialStrategy

variable (S : TracialStrategy.{0}
  (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B))
variable {D : Finset (Fin n)}
variable {Af Bf : Type} [Fintype Af] [Fintype Bf]

/-- **The scenario martingale is a mean tower** for the arena's Alice
totals: on each fiber of the current canonical label, the law-weighted
average of the next revealed-set effect is the current one
(`setEffectA_reveal`, fiber-refined). -/
theorem scenMartA_isMeanTower
    (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    {Ffam : (Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → A))
      → Af → S.M.A}
    (htotF : ∀ s, (∑ a : Af, Ffam s a)
      = S.setEffectA D s.1 μ s.2.1 s.2.2.1 s.2.2.2)
    (SA L : Finset (Fin n)) (hdisj : Disjoint SA L)
    (π : Fin L.card ≃ {j : Fin n // j ∈ L})
    (yw : Fin n → Y) (g : {j : Fin n // ¬ j ∈ L} → X)
    (za : {j : Fin n // j ∈ D} → A)
    (hM : (∏ c : {j : Fin n // j ∈ L}, ∑ v : X, μ v (yw c)) ≠ 0) :
    (scenMartA SA L hdisj π μ yw g za hμ hM).IsMeanTower
      (fun i => ∑ a : Af, Ffam i a) := by
  unfold EffectMartingale.IsMeanTower
  intro s i
  -- Coordinate facts at the revealed position.
  have hcL : ((π s : Fin n)) ∈ L := (π s).2
  have hcRs : ((π s : Fin n)) ∉ SA ∪ ordPrefix π (s : ℕ) := by
    simp only [Finset.mem_union, not_or]
    exact ⟨fun h => Finset.disjoint_left.mp hdisj h hcL,
      notMem_ordPrefix_self π s⟩
  have hne_ts : ∀ t : Fin L.card, (t : ℕ) < (s : ℕ) → π t ≠ π s := by
    intro t ht heq
    have h2 : t = s := π.injective heq
    rw [h2] at ht
    exact lt_irrefl _ ht
  -- Convert the fiber sums to if-sums while the predicate is still the
  -- `idx`-projection (so the filter's decidability instance matches), then
  -- canonicalize the summation type `Ω → (↥L → X)` (matching the helper
  -- lemmas' Fintype), and finally reduce `.idx`/`.law` via their rfl-lemmas
  -- (which leave the Fintype untouched, avoiding an ill-typed intermediate).
  rw [Finset.sum_filter, Finset.sum_filter]
  simp only [scenMartA, Fin.val_castSucc, Fin.val_succ]
  simp only [scenMartA_univ_eq]
  by_cases hfib : ∃ ω₀ : {j : Fin n // j ∈ L} → X,
      mkALabel D (SA ∪ ordPrefix π (s : ℕ))
        ((wordSplit L X).symm (ω₀, g)) yw za = i
  case neg =>
    have h1 : ∀ ω : {j : Fin n // j ∈ L} → X,
        ¬ (mkALabel D (SA ∪ ordPrefix π (s : ℕ))
            ((wordSplit L X).symm (ω, g)) yw za = i) :=
      fun ω h => hfib ⟨ω, h⟩
    simp only [h1, ite_false, Finset.sum_const_zero, Complex.ofReal_zero,
      zero_smul]
  case pos =>
  obtain ⟨ω₀, hω₀⟩ := hfib
  subst hω₀
  -- The fiber of the current label is prefix agreement with `ω₀`.
  have hread : ∀ ω : {j : Fin n // j ∈ L} → X,
      (mkALabel D (SA ∪ ordPrefix π (s : ℕ))
          ((wordSplit L X).symm (ω, g)) yw za
        = mkALabel D (SA ∪ ordPrefix π (s : ℕ))
            ((wordSplit L X).symm (ω₀, g)) yw za)
      ↔ ∀ t : Fin L.card, (t : ℕ) < (s : ℕ) → ω (π t) = ω₀ (π t) := by
    intro ω
    constructor
    · intro h t ht
      have h1 := congrArg (fun l => l.2.1 ((π t : Fin n))) h
      simp only [mkALabel] at h1
      have hmem : ((π t : Fin n)) ∈ SA ∪ ordPrefix π (s : ℕ) :=
        Finset.mem_union_right _ (mem_ordPrefix_of_lt π ht)
      rw [mkKeepOn_eq_on _ _ hmem, mkKeepOn_eq_on _ _ hmem,
        wordSplit_symm_mem L X ω g (π t).2,
        wordSplit_symm_mem L X ω₀ g (π t).2] at h1
      exact h1
    · intro hagree
      refine mkALabel_congr D _ za (fun j hj => ?_) (fun _ _ => rfl)
      rcases Finset.mem_union.mp hj with h | h
      · have hjL : ¬ j ∈ L := fun hL => Finset.disjoint_left.mp hdisj h hL
        rw [wordSplit_symm_notMem L X ω g hjL,
          wordSplit_symm_notMem L X ω₀ g hjL]
      · obtain ⟨t, ht, rfl⟩ := (mem_ordPrefix_iff π).mp h
        rw [wordSplit_symm_mem L X ω g (π t).2,
          wordSplit_symm_mem L X ω₀ g (π t).2]
        exact hagree t ht
  simp only [hread]
  simp only [htotF, mkALabel, S.setEffectA_canon]
  -- Local names.
  set M0 : ℝ := ∏ c : {j : Fin n // j ∈ L}, ∑ v : X, μ v (yw ↑c)
    with hM0def
  set ν : ℝ := ∑ v : X, μ v (yw ((π s : Fin n))) with hνdef
  -- Degenerate live marginal: everything vanishes.
  by_cases hν : ν = 0
  · have hz : ∀ v : X, μ v (yw ((π s : Fin n))) = 0 := fun v =>
      (Finset.sum_eq_zero_iff_of_nonneg fun v _ =>
        hμ v (yw ((π s : Fin n)))).mp hν v (Finset.mem_univ v)
    have hlaw0 : ∀ ω : {j : Fin n // j ∈ L} → X,
        (∏ c : {j : Fin n // j ∈ L}, μ (ω c) (yw ↑c)) = 0 := fun ω =>
      Finset.prod_eq_zero (Finset.mem_univ (π s)) (hz (ω (π s)))
    rw [Finset.sum_congr rfl fun ω _ => show
        (if ∀ t : Fin L.card, (t : ℕ) < (s : ℕ) → ω (π t) = ω₀ (π t) then
          (∏ c : {j : Fin n // j ∈ L}, μ (ω c) (yw ↑c)) / M0 else 0)
        = 0 from by rw [hlaw0 ω, zero_div, ite_self],
      Finset.sum_const_zero, Complex.ofReal_zero, zero_smul]
    refine (Finset.sum_eq_zero fun ω _ => ?_).symm
    rw [hlaw0 ω, zero_div, Complex.ofReal_zero, zero_smul, ite_self]
  -- Positive live marginal: the genuine tower step.
  · rw [S.setEffectA_reveal D (SA ∪ ordPrefix π (s : ℕ)) μ hμ
      ((wordSplit L X).symm (ω₀, g)) yw (mkExtA D za) ((π s : Fin n)) hcRs]
    simp only [weightedAvg]
    -- Split the path space at the live position.
    set e := Equiv.piSplitAt (π s) (fun _ : {j : Fin n // j ∈ L} => X)
      with he
    have hsymm_c : ∀ (v : X)
        (q : {t : {j : Fin n // j ∈ L} // t ≠ π s} → X),
        e.symm (v, q) (π s) = v := by
      intro v q
      simp [he, Equiv.piSplitAt_symm_apply]
    have hsymm_ne : ∀ (v : X)
        (q : {t : {j : Fin n // j ∈ L} // t ≠ π s} → X)
        (t : {j : Fin n // j ∈ L}) (ht : t ≠ π s),
        e.symm (v, q) t = q ⟨t, ht⟩ := by
      intro v q t ht
      simp [he, Equiv.piSplitAt_symm_apply, ht]
    have hsum : ∀ {V : Type} [AddCommMonoid V]
        (F : ({j : Fin n // j ∈ L} → X) → V),
        (∑ ω : {j : Fin n // j ∈ L} → X, F ω)
          = ∑ v : X, ∑ q : {t : {j : Fin n // j ∈ L} // t ≠ π s} → X,
              F (e.symm (v, q)) := by
      intro V _ F
      rw [Fintype.sum_equiv e F (fun p => F (e.symm p))
        (fun ω => by rw [Equiv.symm_apply_apply]), Fintype.sum_prod_type]
    set v₀ : X := Classical.arbitrary X with hv₀
    -- Prefix agreement is independent of the live value.
    have hPredv : ∀ (v : X)
        (q : {t : {j : Fin n // j ∈ L} // t ≠ π s} → X),
        (∀ t : Fin L.card, (t : ℕ) < (s : ℕ) →
            e.symm (v, q) (π t) = ω₀ (π t))
        ↔ (∀ t : Fin L.card, (t : ℕ) < (s : ℕ) →
            e.symm (v₀, q) (π t) = ω₀ (π t)) := by
      intro v q
      constructor
      · intro hp t ht
        have h1 := hp t ht
        rw [hsymm_ne v q (π t) (hne_ts t ht)] at h1
        rw [hsymm_ne v₀ q (π t) (hne_ts t ht)]
        exact h1
      · intro hp t ht
        have h1 := hp t ht
        rw [hsymm_ne v₀ q (π t) (hne_ts t ht)] at h1
        rw [hsymm_ne v q (π t) (hne_ts t ht)]
        exact h1
    -- Law splitting at the live position.
    have hlawsplit : ∀ (v : X)
        (q : {t : {j : Fin n // j ∈ L} // t ≠ π s} → X),
        (∏ c : {j : Fin n // j ∈ L}, μ (e.symm (v, q) c) (yw ↑c)) / M0
          = μ v (yw ((π s : Fin n))) *
            ((∏ t ∈ Finset.univ.erase (π s),
              μ (e.symm (v₀, q) t) (yw ↑t)) / M0) := by
      intro v q
      rw [← Finset.mul_prod_erase Finset.univ
        (fun c => μ (e.symm (v, q) c) (yw ↑c)) (Finset.mem_univ (π s)),
        hsymm_c v q, mul_div_assoc]
      congr 2
      refine Finset.prod_congr rfl fun t htmem => ?_
      have htne : t ≠ π s := Finset.ne_of_mem_erase htmem
      rw [hsymm_ne v q t htne, hsymm_ne v₀ q t htne]
    -- The total fiber mass factors through the live marginal.
    set Q : ℝ := ∑ q : {t : {j : Fin n // j ∈ L} // t ≠ π s} → X,
      if ∀ t : Fin L.card, (t : ℕ) < (s : ℕ) →
          e.symm (v₀, q) (π t) = ω₀ (π t) then
        (∏ t ∈ Finset.univ.erase (π s), μ (e.symm (v₀, q) t) (yw ↑t)) / M0
      else 0 with hQdef
    have hTot : (∑ ω : {j : Fin n // j ∈ L} → X,
        if ∀ t : Fin L.card, (t : ℕ) < (s : ℕ) → ω (π t) = ω₀ (π t) then
          (∏ c : {j : Fin n // j ∈ L}, μ (ω c) (yw ↑c)) / M0 else 0)
        = ν * Q := by
      rw [hsum]
      calc (∑ v : X, ∑ q : {t : {j : Fin n // j ∈ L} // t ≠ π s} → X,
          if ∀ t : Fin L.card, (t : ℕ) < (s : ℕ) →
              e.symm (v, q) (π t) = ω₀ (π t) then
            (∏ c : {j : Fin n // j ∈ L}, μ (e.symm (v, q) c) (yw ↑c)) / M0
          else 0)
          = ∑ v : X, μ v (yw ((π s : Fin n))) * Q := by
            refine Finset.sum_congr rfl fun v _ => ?_
            rw [hQdef, Finset.mul_sum]
            refine Finset.sum_congr rfl fun q _ => ?_
            rw [if_congr (hPredv v q) (hlawsplit v q) rfl, mul_ite, mul_zero]
        _ = ν * Q := by rw [← Finset.sum_mul]
    simp only [hTot]
    -- Collapse the normalization against the live marginal.
    have hscal : ((ν * Q : ℝ) : ℂ) * (((ν : ℝ) : ℂ))⁻¹ = ((Q : ℝ) : ℂ) := by
      rw [← Complex.ofReal_inv, ← Complex.ofReal_mul]
      congr 1
      rw [mul_comm ν Q, mul_assoc, mul_inv_cancel₀ hν, mul_one]
    rw [smul_smul, hscal, Finset.smul_sum]
    -- Reindex the right side and collapse per live value.
    rw [hsum]
    refine Finset.sum_congr rfl fun v _ => ?_
    -- Child effect at the revealed value.
    have hchild : ∀ (q : {t : {j : Fin n // j ∈ L} // t ≠ π s} → X),
        (∀ t : Fin L.card, (t : ℕ) < (s : ℕ) →
          e.symm (v₀, q) (π t) = ω₀ (π t)) →
        S.setEffectA D (SA ∪ ordPrefix π ((s : ℕ) + 1)) μ
            ((wordSplit L X).symm (e.symm (v, q), g)) yw (mkExtA D za)
          = S.setEffectA D
              (insert ((π s : Fin n)) (SA ∪ ordPrefix π (s : ℕ))) μ
              (Function.update ((wordSplit L X).symm (ω₀, g))
                ((π s : Fin n)) v) yw (mkExtA D za) := by
      intro q hq
      rw [ordPrefix_succ π s, Finset.union_insert]
      refine S.setEffectA_congr D _ μ _ (fun j hj => ?_) (fun _ _ => rfl)
      rcases Finset.mem_insert.mp hj with rfl | hjRs
      · rw [Function.update_self, wordSplit_symm_mem L X _ g (π s).2]
        exact hsymm_c v q
      · have hne : j ≠ (π s : Fin n) := by rintro rfl; exact hcRs hjRs
        rw [Function.update_of_ne hne]
        rcases Finset.mem_union.mp hjRs with hSA' | hpre
        · have hjL : ¬ j ∈ L := fun hL =>
            Finset.disjoint_left.mp hdisj hSA' hL
          rw [wordSplit_symm_notMem L X _ g hjL,
            wordSplit_symm_notMem L X ω₀ g hjL]
        · obtain ⟨t, ht, rfl⟩ := (mem_ordPrefix_iff π).mp hpre
          rw [wordSplit_symm_mem L X _ g (π t).2,
            wordSplit_symm_mem L X ω₀ g (π t).2,
            hsymm_ne v q (π t) (hne_ts t ht)]
          have h1 := hq t ht
          rw [hsymm_ne v₀ q (π t) (hne_ts t ht)] at h1
          exact h1
    calc (((Q : ℝ) : ℂ)) • (((μ v (yw ((π s : Fin n))) : ℝ) : ℂ)) •
          S.setEffectA D (insert ((π s : Fin n)) (SA ∪ ordPrefix π (s : ℕ)))
            μ (Function.update ((wordSplit L X).symm (ω₀, g))
              ((π s : Fin n)) v) yw (mkExtA D za)
        = (((μ v (yw ((π s : Fin n))) * Q : ℝ) : ℂ)) •
            S.setEffectA D
              (insert ((π s : Fin n)) (SA ∪ ordPrefix π (s : ℕ))) μ
              (Function.update ((wordSplit L X).symm (ω₀, g))
                ((π s : Fin n)) v) yw (mkExtA D za) := by
          rw [smul_smul, ← Complex.ofReal_mul, mul_comm]
      _ = ∑ q : {t : {j : Fin n // j ∈ L} // t ≠ π s} → X,
            if ∀ t : Fin L.card, (t : ℕ) < (s : ℕ) →
                e.symm (v, q) (π t) = ω₀ (π t) then
              (((∏ c : {j : Fin n // j ∈ L},
                  μ (e.symm (v, q) c) (yw ↑c)) / M0 : ℝ) : ℂ) •
                S.setEffectA D (SA ∪ ordPrefix π ((s : ℕ) + 1)) μ
                  ((wordSplit L X).symm (e.symm (v, q), g)) yw
                  (mkExtA D za)
            else 0 := by
          rw [show (((μ v (yw ((π s : Fin n))) * Q : ℝ) : ℂ))
              = ∑ q : {t : {j : Fin n // j ∈ L} // t ≠ π s} → X,
                if ∀ t : Fin L.card, (t : ℕ) < (s : ℕ) →
                    e.symm (v₀, q) (π t) = ω₀ (π t) then
                  (((∏ c : {j : Fin n // j ∈ L},
                      μ (e.symm (v, q) c) (yw ↑c)) / M0 : ℝ) : ℂ)
                else 0 from by
            rw [hQdef, Finset.mul_sum, Complex.ofReal_sum]
            refine Finset.sum_congr rfl fun q _ => ?_
            rw [mul_ite, mul_zero, ← hlawsplit v q, apply_ite
              (fun r : ℝ => ((r : ℝ) : ℂ)), Complex.ofReal_zero],
            Finset.sum_smul]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [ite_smul, zero_smul]
          rw [if_congr (hPredv v q).symm rfl rfl]
          by_cases hq : ∀ t : Fin L.card, (t : ℕ) < (s : ℕ) →
              e.symm (v, q) (π t) = ω₀ (π t)
          · rw [if_pos hq, if_pos hq, hchild q ((hPredv v q).mp hq)]
          · rw [if_neg hq, if_neg hq]

/-- **Alice-column budget, consumed on the scenario martingale** (node
1.2.6 → 1.2.9 bridge): the reveal-martingale mean tower feeds the signed
column budget, so the total law-weighted squared L²-increment of the
branch vectors along the Alice scenario reveal (block `L`, background
`SA`, pinned Bob index `j`) is at most the scalar entropy `H₁` of the
initial branch pairing. This is the per-scenario budget consumption that
node 1.2.9 telescopes at the uniform cut. -/
theorem scenMartA_colBudget
    (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    {Ffam : (Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → A))
      → Af → S.M.A}
    {Gfam : (Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → B))
      → Bf → S.M.A}
    (R : ResolverArena S.M Ffam Gfam) (hcol : R.ColEntropyBudget)
    (htotF : ∀ s, (∑ a : Af, Ffam s a)
      = S.setEffectA D s.1 μ s.2.1 s.2.2.1 s.2.2.2)
    (SA L : Finset (Fin n)) (hdisj : Disjoint SA L)
    (π : Fin L.card ≃ {j : Fin n // j ∈ L})
    (yw : Fin n → Y) (g : {j : Fin n // ¬ j ∈ L} → X)
    (za : {j : Fin n // j ∈ D} → A)
    (hM : (∏ c : {j : Fin n // j ∈ L}, ∑ v : X, μ v (yw c)) ≠ 0)
    (σ : S.M.A) (hσ : S.M.τ (star σ * σ) = 1)
    (j : Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → B))
    (ω₀ : {j : Fin n // j ∈ L} → X) :
    (∑ s : Fin L.card, ∑ ω : {j : Fin n // j ∈ L} → X,
        (scenMartA SA L hdisj π μ yw g za hμ hM).law ω *
          ‖R.branch σ
              ((scenMartA SA L hdisj π μ yw g za hμ hM).idx s.succ ω) j
            - R.branch σ
                ((scenMartA SA L hdisj π μ yw g za hμ hM).idx s.castSucc ω)
                j‖ ^ 2)
      ≤ Real.negMulLog
          (S.M.τ (star σ *
            ((∑ a : Af,
                Ffam ((scenMartA SA L hdisj π μ yw g za hμ hM).idx 0 ω₀) a) *
              σ * (∑ b : Bf, Gfam j b)))).re :=
  hcol L.card (scenMartA SA L hdisj π μ yw g za hμ hM)
    (S.scenMartA_isMeanTower μ hμ htotF SA L hdisj π yw g za hM) σ hσ j ω₀


/-- **The Bob scenario martingale is a mean tower** for the arena's Bob
totals (`setEffectB_reveal`, fiber-refined). -/
theorem scenMartB_isMeanTower
    (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    {Gfam : (Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → B))
      → Bf → S.M.A}
    (htotG : ∀ t, (∑ b : Bf, Gfam t b)
      = S.setEffectB D t.1 μ t.2.1 t.2.2.1 t.2.2.2)
    (SA L : Finset (Fin n)) (hdisj : Disjoint SA L)
    (π : Fin L.card ≃ {j : Fin n // j ∈ L})
    (xw : Fin n → X) (g : {j : Fin n // ¬ j ∈ L} → Y)
    (zb : {j : Fin n // j ∈ D} → B)
    (hM : (∏ c : {j : Fin n // j ∈ L}, ∑ v : Y, μ (xw c) v) ≠ 0) :
    (scenMartB SA L hdisj π μ xw g zb hμ hM).IsMeanTower
      (fun j => ∑ b : Bf, Gfam j b) := by
  unfold EffectMartingale.IsMeanTower
  intro s i
  have hcL : ((π s : Fin n)) ∈ L := (π s).2
  have hcRs : ((π s : Fin n)) ∉ SA ∪ ordPrefix π (s : ℕ) := by
    simp only [Finset.mem_union, not_or]
    exact ⟨fun h => Finset.disjoint_left.mp hdisj h hcL,
      notMem_ordPrefix_self π s⟩
  have hne_ts : ∀ t : Fin L.card, (t : ℕ) < (s : ℕ) → π t ≠ π s := by
    intro t ht heq
    have h2 : t = s := π.injective heq
    rw [h2] at ht
    exact lt_irrefl _ ht
  rw [Finset.sum_filter, Finset.sum_filter]
  simp only [scenMartB, Fin.val_castSucc, Fin.val_succ]
  simp only [scenMartB_univ_eq]
  by_cases hfib : ∃ ω₀ : {j : Fin n // j ∈ L} → Y,
      mkBLabel D (SA ∪ ordPrefix π (s : ℕ))
        xw ((wordSplit L Y).symm (ω₀, g)) zb = i
  case neg =>
    have h1 : ∀ ω : {j : Fin n // j ∈ L} → Y,
        ¬ (mkBLabel D (SA ∪ ordPrefix π (s : ℕ))
            xw ((wordSplit L Y).symm (ω, g)) zb = i) :=
      fun ω h => hfib ⟨ω, h⟩
    simp only [h1, ite_false, Finset.sum_const_zero, Complex.ofReal_zero,
      zero_smul]
  case pos =>
  obtain ⟨ω₀, hω₀⟩ := hfib
  subst hω₀
  have hread : ∀ ω : {j : Fin n // j ∈ L} → Y,
      (mkBLabel D (SA ∪ ordPrefix π (s : ℕ))
          xw ((wordSplit L Y).symm (ω, g)) zb
        = mkBLabel D (SA ∪ ordPrefix π (s : ℕ))
            xw ((wordSplit L Y).symm (ω₀, g)) zb)
      ↔ ∀ t : Fin L.card, (t : ℕ) < (s : ℕ) → ω (π t) = ω₀ (π t) := by
    intro ω
    constructor
    · intro h t ht
      have h1 := congrArg (fun l => l.2.2.1 ((π t : Fin n))) h
      simp only [mkBLabel] at h1
      have hmem : ((π t : Fin n)) ∈ SA ∪ ordPrefix π (s : ℕ) :=
        Finset.mem_union_right _ (mem_ordPrefix_of_lt π ht)
      rw [mkKeepOn_eq_on _ _ hmem, mkKeepOn_eq_on _ _ hmem,
        wordSplit_symm_mem L Y ω g (π t).2,
        wordSplit_symm_mem L Y ω₀ g (π t).2] at h1
      exact h1
    · intro hagree
      refine mkBLabel_congr D _ zb (fun _ _ => rfl) (fun j hj => ?_)
      rcases Finset.mem_union.mp hj with h | h
      · have hjL : ¬ j ∈ L := fun hL => Finset.disjoint_left.mp hdisj h hL
        rw [wordSplit_symm_notMem L Y ω g hjL,
          wordSplit_symm_notMem L Y ω₀ g hjL]
      · obtain ⟨t, ht, rfl⟩ := (mem_ordPrefix_iff π).mp h
        rw [wordSplit_symm_mem L Y ω g (π t).2,
          wordSplit_symm_mem L Y ω₀ g (π t).2]
        exact hagree t ht
  simp only [hread]
  simp only [htotG, mkBLabel, S.setEffectB_canon]
  set M0 : ℝ := ∏ c : {j : Fin n // j ∈ L}, ∑ v : Y, μ (xw ↑c) v
    with hM0def
  set ν : ℝ := ∑ v : Y, μ (xw ((π s : Fin n))) v with hνdef
  by_cases hν : ν = 0
  · have hz : ∀ v : Y, μ (xw ((π s : Fin n))) v = 0 := fun v =>
      (Finset.sum_eq_zero_iff_of_nonneg fun v _ =>
        hμ (xw ((π s : Fin n))) v).mp hν v (Finset.mem_univ v)
    have hlaw0 : ∀ ω : {j : Fin n // j ∈ L} → Y,
        (∏ c : {j : Fin n // j ∈ L}, μ (xw ↑c) (ω c)) = 0 := fun ω =>
      Finset.prod_eq_zero (Finset.mem_univ (π s)) (hz (ω (π s)))
    rw [Finset.sum_congr rfl fun ω _ => show
        (if ∀ t : Fin L.card, (t : ℕ) < (s : ℕ) → ω (π t) = ω₀ (π t) then
          (∏ c : {j : Fin n // j ∈ L}, μ (xw ↑c) (ω c)) / M0 else 0)
        = 0 from by rw [hlaw0 ω, zero_div, ite_self],
      Finset.sum_const_zero, Complex.ofReal_zero, zero_smul]
    refine (Finset.sum_eq_zero fun ω _ => ?_).symm
    rw [hlaw0 ω, zero_div, Complex.ofReal_zero, zero_smul, ite_self]
  · rw [S.setEffectB_reveal D (SA ∪ ordPrefix π (s : ℕ)) μ hμ
      xw ((wordSplit L Y).symm (ω₀, g)) (mkExtB D zb) ((π s : Fin n)) hcRs]
    simp only [weightedAvg]
    set e := Equiv.piSplitAt (π s) (fun _ : {j : Fin n // j ∈ L} => Y)
      with he
    have hsymm_c : ∀ (v : Y)
        (q : {t : {j : Fin n // j ∈ L} // t ≠ π s} → Y),
        e.symm (v, q) (π s) = v := by
      intro v q
      simp [he, Equiv.piSplitAt_symm_apply]
    have hsymm_ne : ∀ (v : Y)
        (q : {t : {j : Fin n // j ∈ L} // t ≠ π s} → Y)
        (t : {j : Fin n // j ∈ L}) (ht : t ≠ π s),
        e.symm (v, q) t = q ⟨t, ht⟩ := by
      intro v q t ht
      simp [he, Equiv.piSplitAt_symm_apply, ht]
    have hsum : ∀ {V : Type} [AddCommMonoid V]
        (F : ({j : Fin n // j ∈ L} → Y) → V),
        (∑ ω : {j : Fin n // j ∈ L} → Y, F ω)
          = ∑ v : Y, ∑ q : {t : {j : Fin n // j ∈ L} // t ≠ π s} → Y,
              F (e.symm (v, q)) := by
      intro V _ F
      rw [Fintype.sum_equiv e F (fun p => F (e.symm p))
        (fun ω => by rw [Equiv.symm_apply_apply]), Fintype.sum_prod_type]
    set v₀ : Y := Classical.arbitrary Y with hv₀
    have hPredv : ∀ (v : Y)
        (q : {t : {j : Fin n // j ∈ L} // t ≠ π s} → Y),
        (∀ t : Fin L.card, (t : ℕ) < (s : ℕ) →
            e.symm (v, q) (π t) = ω₀ (π t))
        ↔ (∀ t : Fin L.card, (t : ℕ) < (s : ℕ) →
            e.symm (v₀, q) (π t) = ω₀ (π t)) := by
      intro v q
      constructor
      · intro hp t ht
        have h1 := hp t ht
        rw [hsymm_ne v q (π t) (hne_ts t ht)] at h1
        rw [hsymm_ne v₀ q (π t) (hne_ts t ht)]
        exact h1
      · intro hp t ht
        have h1 := hp t ht
        rw [hsymm_ne v₀ q (π t) (hne_ts t ht)] at h1
        rw [hsymm_ne v q (π t) (hne_ts t ht)]
        exact h1
    have hlawsplit : ∀ (v : Y)
        (q : {t : {j : Fin n // j ∈ L} // t ≠ π s} → Y),
        (∏ c : {j : Fin n // j ∈ L}, μ (xw ↑c) (e.symm (v, q) c)) / M0
          = μ (xw ((π s : Fin n))) v *
            ((∏ t ∈ Finset.univ.erase (π s),
              μ (xw ↑t) (e.symm (v₀, q) t)) / M0) := by
      intro v q
      rw [← Finset.mul_prod_erase Finset.univ
        (fun c : {j : Fin n // j ∈ L} => μ (xw ↑c) (e.symm (v, q) c))
          (Finset.mem_univ (π s)),
        hsymm_c v q, mul_div_assoc]
      congr 2
      refine Finset.prod_congr rfl fun t htmem => ?_
      have htne : t ≠ π s := Finset.ne_of_mem_erase htmem
      rw [hsymm_ne v q t htne, hsymm_ne v₀ q t htne]
    set Q : ℝ := ∑ q : {t : {j : Fin n // j ∈ L} // t ≠ π s} → Y,
      if ∀ t : Fin L.card, (t : ℕ) < (s : ℕ) →
          e.symm (v₀, q) (π t) = ω₀ (π t) then
        (∏ t ∈ Finset.univ.erase (π s), μ (xw ↑t) (e.symm (v₀, q) t)) / M0
      else 0 with hQdef
    have hTot : (∑ ω : {j : Fin n // j ∈ L} → Y,
        if ∀ t : Fin L.card, (t : ℕ) < (s : ℕ) → ω (π t) = ω₀ (π t) then
          (∏ c : {j : Fin n // j ∈ L}, μ (xw ↑c) (ω c)) / M0 else 0)
        = ν * Q := by
      rw [hsum]
      calc (∑ v : Y, ∑ q : {t : {j : Fin n // j ∈ L} // t ≠ π s} → Y,
          if ∀ t : Fin L.card, (t : ℕ) < (s : ℕ) →
              e.symm (v, q) (π t) = ω₀ (π t) then
            (∏ c : {j : Fin n // j ∈ L}, μ (xw ↑c) (e.symm (v, q) c)) / M0
          else 0)
          = ∑ v : Y, μ (xw ((π s : Fin n))) v * Q := by
            refine Finset.sum_congr rfl fun v _ => ?_
            rw [hQdef, Finset.mul_sum]
            refine Finset.sum_congr rfl fun q _ => ?_
            rw [if_congr (hPredv v q) (hlawsplit v q) rfl, mul_ite, mul_zero]
        _ = ν * Q := by rw [← Finset.sum_mul]
    simp only [hTot]
    have hscal : ((ν * Q : ℝ) : ℂ) * (((ν : ℝ) : ℂ))⁻¹ = ((Q : ℝ) : ℂ) := by
      rw [← Complex.ofReal_inv, ← Complex.ofReal_mul]
      congr 1
      rw [mul_comm ν Q, mul_assoc, mul_inv_cancel₀ hν, mul_one]
    rw [smul_smul, hscal, Finset.smul_sum]
    rw [hsum]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hchild : ∀ (q : {t : {j : Fin n // j ∈ L} // t ≠ π s} → Y),
        (∀ t : Fin L.card, (t : ℕ) < (s : ℕ) →
          e.symm (v₀, q) (π t) = ω₀ (π t)) →
        S.setEffectB D (SA ∪ ordPrefix π ((s : ℕ) + 1)) μ
            xw ((wordSplit L Y).symm (e.symm (v, q), g)) (mkExtB D zb)
          = S.setEffectB D
              (insert ((π s : Fin n)) (SA ∪ ordPrefix π (s : ℕ))) μ
              xw (Function.update ((wordSplit L Y).symm (ω₀, g))
                ((π s : Fin n)) v) (mkExtB D zb) := by
      intro q hq
      rw [ordPrefix_succ π s, Finset.union_insert]
      refine S.setEffectB_congr D _ μ _ (fun _ _ => rfl) (fun j hj => ?_)
      rcases Finset.mem_insert.mp hj with rfl | hjRs
      · rw [Function.update_self, wordSplit_symm_mem L Y _ g (π s).2]
        exact hsymm_c v q
      · have hne : j ≠ (π s : Fin n) := by rintro rfl; exact hcRs hjRs
        rw [Function.update_of_ne hne]
        rcases Finset.mem_union.mp hjRs with hSA' | hpre
        · have hjL : ¬ j ∈ L := fun hL =>
            Finset.disjoint_left.mp hdisj hSA' hL
          rw [wordSplit_symm_notMem L Y _ g hjL,
            wordSplit_symm_notMem L Y ω₀ g hjL]
        · obtain ⟨t, ht, rfl⟩ := (mem_ordPrefix_iff π).mp hpre
          rw [wordSplit_symm_mem L Y _ g (π t).2,
            wordSplit_symm_mem L Y ω₀ g (π t).2,
            hsymm_ne v q (π t) (hne_ts t ht)]
          have h1 := hq t ht
          rw [hsymm_ne v₀ q (π t) (hne_ts t ht)] at h1
          exact h1
    calc (((Q : ℝ) : ℂ)) • (((μ (xw ((π s : Fin n))) v : ℝ) : ℂ)) •
          S.setEffectB D (insert ((π s : Fin n)) (SA ∪ ordPrefix π (s : ℕ)))
            μ xw (Function.update ((wordSplit L Y).symm (ω₀, g))
              ((π s : Fin n)) v) (mkExtB D zb)
        = (((μ (xw ((π s : Fin n))) v * Q : ℝ) : ℂ)) •
            S.setEffectB D
              (insert ((π s : Fin n)) (SA ∪ ordPrefix π (s : ℕ))) μ
              xw (Function.update ((wordSplit L Y).symm (ω₀, g))
                ((π s : Fin n)) v) (mkExtB D zb) := by
          rw [smul_smul, ← Complex.ofReal_mul, mul_comm]
      _ = ∑ q : {t : {j : Fin n // j ∈ L} // t ≠ π s} → Y,
            if ∀ t : Fin L.card, (t : ℕ) < (s : ℕ) →
                e.symm (v, q) (π t) = ω₀ (π t) then
              (((∏ c : {j : Fin n // j ∈ L},
                  μ (xw ↑c) (e.symm (v, q) c)) / M0 : ℝ) : ℂ) •
                S.setEffectB D (SA ∪ ordPrefix π ((s : ℕ) + 1)) μ
                  xw ((wordSplit L Y).symm (e.symm (v, q), g))
                  (mkExtB D zb)
            else 0 := by
          rw [show (((μ (xw ((π s : Fin n))) v * Q : ℝ) : ℂ))
              = ∑ q : {t : {j : Fin n // j ∈ L} // t ≠ π s} → Y,
                if ∀ t : Fin L.card, (t : ℕ) < (s : ℕ) →
                    e.symm (v₀, q) (π t) = ω₀ (π t) then
                  (((∏ c : {j : Fin n // j ∈ L},
                      μ (xw ↑c) (e.symm (v, q) c)) / M0 : ℝ) : ℂ)
                else 0 from by
            rw [hQdef, Finset.mul_sum, Complex.ofReal_sum]
            refine Finset.sum_congr rfl fun q _ => ?_
            rw [mul_ite, mul_zero, ← hlawsplit v q, apply_ite
              (fun r : ℝ => ((r : ℝ) : ℂ)), Complex.ofReal_zero],
            Finset.sum_smul]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [ite_smul, zero_smul]
          rw [if_congr (hPredv v q).symm rfl rfl]
          by_cases hq : ∀ t : Fin L.card, (t : ℕ) < (s : ℕ) →
              e.symm (v, q) (π t) = ω₀ (π t)
          · rw [if_pos hq, if_pos hq, hchild q ((hPredv v q).mp hq)]
          · rw [if_neg hq, if_neg hq]

/-- **Bob-row budget, consumed on the scenario martingale** (mirror of
`scenMartA_colBudget`): feeding the Bob mean tower to `RowEntropyBudget`
bounds the total law-weighted squared L²-increment of the branch vectors
(second slot) along the Bob scenario reveal by the scalar entropy `H₁` of
the initial branch pairing. -/
theorem scenMartB_rowBudget
    (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    {Ffam : (Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → A))
      → Af → S.M.A}
    {Gfam : (Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → B))
      → Bf → S.M.A}
    (R : ResolverArena S.M Ffam Gfam) (hrow : R.RowEntropyBudget)
    (htotG : ∀ t, (∑ b : Bf, Gfam t b)
      = S.setEffectB D t.1 μ t.2.1 t.2.2.1 t.2.2.2)
    (SA L : Finset (Fin n)) (hdisj : Disjoint SA L)
    (π : Fin L.card ≃ {j : Fin n // j ∈ L})
    (xw : Fin n → X) (g : {j : Fin n // ¬ j ∈ L} → Y)
    (zb : {j : Fin n // j ∈ D} → B)
    (hM : (∏ c : {j : Fin n // j ∈ L}, ∑ v : Y, μ (xw c) v) ≠ 0)
    (σ : S.M.A) (hσ : S.M.τ (star σ * σ) = 1)
    (i : Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → A))
    (ω₀ : {j : Fin n // j ∈ L} → Y) :
    (∑ s : Fin L.card, ∑ ω : {j : Fin n // j ∈ L} → Y,
        (scenMartB SA L hdisj π μ xw g zb hμ hM).law ω *
          ‖R.branch σ i
              ((scenMartB SA L hdisj π μ xw g zb hμ hM).idx s.succ ω)
            - R.branch σ i
                ((scenMartB SA L hdisj π μ xw g zb hμ hM).idx
                  s.castSucc ω)‖ ^ 2)
      ≤ Real.negMulLog
          (S.M.τ (star σ *
            ((∑ a : Af, Ffam i a) * σ *
              (∑ b : Bf,
                Gfam ((scenMartB SA L hdisj π μ xw g zb hμ hM).idx 0 ω₀)
                  b)))).re :=
  hrow L.card (scenMartB SA L hdisj π μ xw g zb hμ hM)
    (S.scenMartB_isMeanTower μ hμ htotG SA L hdisj π xw g zb hM) σ hσ i ω₀

/-- **Single cut-step column budget** (node 1.2.9 assembly step (1)):
dropping the other nonnegative reveal steps, the law-weighted squared
increment at any single step `k` is bounded by the same scalar entropy
`H₁`. This is the per-datum cut increment that node 1.2.9 identifies
with the `alignCostA` integrand. -/
theorem scenMartA_cut_le
    (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    {Ffam : (Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → A))
      → Af → S.M.A}
    {Gfam : (Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → B))
      → Bf → S.M.A}
    (R : ResolverArena S.M Ffam Gfam) (hcol : R.ColEntropyBudget)
    (htotF : ∀ s, (∑ a : Af, Ffam s a)
      = S.setEffectA D s.1 μ s.2.1 s.2.2.1 s.2.2.2)
    (SA L : Finset (Fin n)) (hdisj : Disjoint SA L)
    (π : Fin L.card ≃ {j : Fin n // j ∈ L})
    (yw : Fin n → Y) (g : {j : Fin n // ¬ j ∈ L} → X)
    (za : {j : Fin n // j ∈ D} → A)
    (hM : (∏ c : {j : Fin n // j ∈ L}, ∑ v : X, μ v (yw c)) ≠ 0)
    (σ : S.M.A) (hσ : S.M.τ (star σ * σ) = 1)
    (j : Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → B))
    (ω₀ : {j : Fin n // j ∈ L} → X) (k : Fin L.card) :
    (∑ ω : {j : Fin n // j ∈ L} → X,
        (scenMartA SA L hdisj π μ yw g za hμ hM).law ω *
          ‖R.branch σ
              ((scenMartA SA L hdisj π μ yw g za hμ hM).idx k.succ ω) j
            - R.branch σ
                ((scenMartA SA L hdisj π μ yw g za hμ hM).idx k.castSucc ω)
                j‖ ^ 2)
      ≤ Real.negMulLog
          (S.M.τ (star σ *
            ((∑ a : Af,
                Ffam ((scenMartA SA L hdisj π μ yw g za hμ hM).idx 0 ω₀) a) *
              σ * (∑ b : Bf, Gfam j b)))).re := by
  refine le_trans ?_
    (S.scenMartA_colBudget μ hμ R hcol htotF SA L hdisj π yw g za hM σ hσ j ω₀)
  exact Finset.single_le_sum
    (f := fun s : Fin L.card => ∑ ω : {j : Fin n // j ∈ L} → X,
        (scenMartA SA L hdisj π μ yw g za hμ hM).law ω *
          ‖R.branch σ
              ((scenMartA SA L hdisj π μ yw g za hμ hM).idx s.succ ω) j
            - R.branch σ
                ((scenMartA SA L hdisj π μ yw g za hμ hM).idx s.castSucc ω)
                j‖ ^ 2)
    (fun s _ => Finset.sum_nonneg fun ω _ =>
      mul_nonneg ((scenMartA SA L hdisj π μ yw g za hμ hM).law_nonneg ω)
        (sq_nonneg _))
    (Finset.mem_univ k)

/-- **Single cut-step row budget** (Bob-side mirror of
`scenMartA_cut_le`). -/
theorem scenMartB_cut_le
    (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    {Ffam : (Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → A))
      → Af → S.M.A}
    {Gfam : (Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → B))
      → Bf → S.M.A}
    (R : ResolverArena S.M Ffam Gfam) (hrow : R.RowEntropyBudget)
    (htotG : ∀ t, (∑ b : Bf, Gfam t b)
      = S.setEffectB D t.1 μ t.2.1 t.2.2.1 t.2.2.2)
    (SA L : Finset (Fin n)) (hdisj : Disjoint SA L)
    (π : Fin L.card ≃ {j : Fin n // j ∈ L})
    (xw : Fin n → X) (g : {j : Fin n // ¬ j ∈ L} → Y)
    (zb : {j : Fin n // j ∈ D} → B)
    (hM : (∏ c : {j : Fin n // j ∈ L}, ∑ v : Y, μ (xw c) v) ≠ 0)
    (σ : S.M.A) (hσ : S.M.τ (star σ * σ) = 1)
    (i : Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → A))
    (ω₀ : {j : Fin n // j ∈ L} → Y) (k : Fin L.card) :
    (∑ ω : {j : Fin n // j ∈ L} → Y,
        (scenMartB SA L hdisj π μ xw g zb hμ hM).law ω *
          ‖R.branch σ i
              ((scenMartB SA L hdisj π μ xw g zb hμ hM).idx k.succ ω)
            - R.branch σ i
                ((scenMartB SA L hdisj π μ xw g zb hμ hM).idx
                  k.castSucc ω)‖ ^ 2)
      ≤ Real.negMulLog
          (S.M.τ (star σ *
            ((∑ a : Af, Ffam i a) * σ *
              (∑ b : Bf,
                Gfam ((scenMartB SA L hdisj π μ xw g zb hμ hM).idx 0 ω₀)
                  b)))).re := by
  refine le_trans ?_
    (S.scenMartB_rowBudget μ hμ R hrow htotG SA L hdisj π xw g zb hM σ hσ i ω₀)
  exact Finset.single_le_sum
    (f := fun s : Fin L.card => ∑ ω : {j : Fin n // j ∈ L} → Y,
        (scenMartB SA L hdisj π μ xw g zb hμ hM).law ω *
          ‖R.branch σ i
              ((scenMartB SA L hdisj π μ xw g zb hμ hM).idx s.succ ω)
            - R.branch σ i
                ((scenMartB SA L hdisj π μ xw g zb hμ hM).idx
                  s.castSucc ω)‖ ^ 2)
    (fun s _ => Finset.sum_nonneg fun ω _ =>
      mul_nonneg ((scenMartB SA L hdisj π μ xw g zb hμ hM).law_nonneg ω)
        (sq_nonneg _))
    (Finset.mem_univ k)

/-- **Column budget in canonical-label form** (node 1.2.9 assembly bridge):
`scenMartA_colBudget` with the martingale's `.idx` steps expanded via
`scenMartA_idx`/`ordPrefix_succ` into the `mkALabel` canonical labels that the
`alignCostA` integrand (through the `aLabel = mkALabel` rfl bridge and the
reveal-datum wiring `revealMartA_cut(Succ)_eq_effectiveH(Bar)`) actually names.
The total, over all reveal steps `s`, of the law-weighted squared branch
increment `‖φ_{insert (π s) prefix} − φ_{prefix}‖²` against a fixed Bob index
`J` is bounded by `H₁` of the initial pairing (label at the background `SA`).
Node 1.2.9 identifies each `alignCostA` cut-datum (at cut `kY`) with the step
`s = kY` (`prefix = SA ∪ ordPrefix π kY = C_X`,
`insert (π kY) prefix = insert i C_X`); summing the cut-data over the uniform
interior cut `kY : Fin L.card` reconstructs this `∑ s` telescoping sum, because
the Bob index `bLabel (insert i C_Y) = bLabel (D ∪ L ∪ alicePrefixX)` is
`kY`-independent (`insert i C_Y` collapses off the live coordinate). -/
theorem scenMartA_colBudget_mkALabel
    (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    {Ffam : (Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → A))
      → Af → S.M.A}
    {Gfam : (Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → B))
      → Bf → S.M.A}
    (R : ResolverArena S.M Ffam Gfam) (hcol : R.ColEntropyBudget)
    (htotF : ∀ s, (∑ a : Af, Ffam s a)
      = S.setEffectA D s.1 μ s.2.1 s.2.2.1 s.2.2.2)
    (SA L : Finset (Fin n)) (hdisj : Disjoint SA L)
    (π : Fin L.card ≃ {j : Fin n // j ∈ L})
    (yw : Fin n → Y) (g : {j : Fin n // ¬ j ∈ L} → X)
    (za : {j : Fin n // j ∈ D} → A)
    (hM : (∏ c : {j : Fin n // j ∈ L}, ∑ v : X, μ v (yw c)) ≠ 0)
    (σ : S.M.A) (hσ : S.M.τ (star σ * σ) = 1)
    (J : Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → B))
    (ω₀ : {j : Fin n // j ∈ L} → X) :
    (∑ s : Fin L.card, ∑ ω : {j : Fin n // j ∈ L} → X,
        (scenMartA SA L hdisj π μ yw g za hμ hM).law ω *
          ‖R.branch σ
              (mkALabel D (insert (π s : Fin n) (SA ∪ ordPrefix π (s : ℕ)))
                ((wordSplit L X).symm (ω, g)) yw za) J
            - R.branch σ
                (mkALabel D (SA ∪ ordPrefix π (s : ℕ))
                  ((wordSplit L X).symm (ω, g)) yw za) J‖ ^ 2)
      ≤ Real.negMulLog
          (S.M.τ (star σ *
            ((∑ a : Af,
                Ffam (mkALabel D SA ((wordSplit L X).symm (ω₀, g)) yw za) a) *
              σ * (∑ b : Bf, Gfam J b)))).re := by
  have base := S.scenMartA_colBudget μ hμ R hcol htotF SA L hdisj π yw g za hM σ hσ J ω₀
  simp only [scenMartA_idx, Fin.val_succ, Fin.val_castSucc, Fin.val_zero,
    ordPrefix_succ, ordPrefix_zero, Finset.union_insert, Finset.union_empty] at base
  exact base

/-- **Row budget in canonical-label form** (Bob-side mirror of
`scenMartA_colBudget_mkALabel`), for the `alignCostB` cut assembly. -/
theorem scenMartB_rowBudget_mkBLabel
    (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    {Ffam : (Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → A))
      → Af → S.M.A}
    {Gfam : (Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → B))
      → Bf → S.M.A}
    (R : ResolverArena S.M Ffam Gfam) (hrow : R.RowEntropyBudget)
    (htotG : ∀ t, (∑ b : Bf, Gfam t b)
      = S.setEffectB D t.1 μ t.2.1 t.2.2.1 t.2.2.2)
    (SA L : Finset (Fin n)) (hdisj : Disjoint SA L)
    (π : Fin L.card ≃ {j : Fin n // j ∈ L})
    (xw : Fin n → X) (g : {j : Fin n // ¬ j ∈ L} → Y)
    (zb : {j : Fin n // j ∈ D} → B)
    (hM : (∏ c : {j : Fin n // j ∈ L}, ∑ v : Y, μ (xw c) v) ≠ 0)
    (σ : S.M.A) (hσ : S.M.τ (star σ * σ) = 1)
    (I : Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → A))
    (ω₀ : {j : Fin n // j ∈ L} → Y) :
    (∑ s : Fin L.card, ∑ ω : {j : Fin n // j ∈ L} → Y,
        (scenMartB SA L hdisj π μ xw g zb hμ hM).law ω *
          ‖R.branch σ I
              (mkBLabel D (insert (π s : Fin n) (SA ∪ ordPrefix π (s : ℕ)))
                xw ((wordSplit L Y).symm (ω, g)) zb)
            - R.branch σ I
                (mkBLabel D (SA ∪ ordPrefix π (s : ℕ))
                  xw ((wordSplit L Y).symm (ω, g)) zb)‖ ^ 2)
      ≤ Real.negMulLog
          (S.M.τ (star σ *
            ((∑ a : Af, Ffam I a) * σ *
              (∑ b : Bf,
                Gfam (mkBLabel D SA xw ((wordSplit L Y).symm (ω₀, g)) zb)
                  b)))).re := by
  have base := S.scenMartB_rowBudget μ hμ R hrow htotG SA L hdisj π xw g zb hM σ hσ I ω₀
  simp only [scenMartB_idx, Fin.val_succ, Fin.val_castSucc, Fin.val_zero,
    ordPrefix_succ, ordPrefix_zero, Finset.union_insert, Finset.union_empty] at base
  exact base

end TracialStrategy

end CommutingRepetition
