/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Sofic.Soundness
public import MIPRE.Tailored.Sofic.TraceSound
public import MIPRE.Tailored.Sofic.TraceComplete
public import MIPRE.Tailored.Sofic.Undecidable

@[expose] public section

/-!
# Main Theorem II, and the sofic value is not approximable from a halting reduction

Theorem I:2126 for the tailored games of `MIPRE/TailoredGameValue.lean`, assembled from its two
halves:

* completeness (`valSof_eq_one_of_hasPerfectZPC`): a perfect ZPC strategy lifts to an action of
  value `1` (`exists_value_one_of_hasPerfectZPC`), and no action has value above `1`;
* soundness (`gameValue_ge_of_valSof`): an action of value `1 − ε` is perturbed into one passing
  Checks 1–3 (`exists_checks_of_value`), whose quotient by `J` is a strategy for the game
  (`gameValue_ge_of_checks`), so the game's synchronous value is at least
  `1 − 600 (Λ+1)^4 2^{6(Λ+1)} ε`, `Λ` the answer length.

So `MainTheoremII` holds with the gap function `gapK Λ = 600 (Λ+1)^4 2^{6(Λ+1)}`, which is
primitive recursive, and `not_sofValueApproximable_of` gives `not_sofValueApproximable`: a halting
reduction to tailored games makes the sofic value not approximable.
-/

namespace MIPRE.Tailored.Sofic

open SubgroupTestValue TailoredGameValue HaltingGameValue

/-! ## Values lie in `[0, 1]` -/

theorem sum_mul_le_sum {l : List (ℕ × List Word × List (List (ℕ × Bool)))} (p : _ → ℝ)
    (hp : ∀ c, p c ≤ 1) :
    (l.map fun c => (c.1 : ℝ) * p c).sum ≤ ((l.map (·.1)).sum : ℝ) := by
  induction l with
  | nil => simp
  | cons c l ih =>
    simp only [List.map_cons, List.sum_cons]
    have : (c.1 : ℝ) * p c ≤ c.1 := mul_le_of_le_one_right (Nat.cast_nonneg _) (hp c)
    linarith

/-- **No action has value above `1`.** -/
theorem value_le_one (T : SubgroupTestData) (σ : FiniteAction T.nGen) : T.value σ ≤ 1 := by
  unfold SubgroupTestData.value
  rcases Nat.eq_zero_or_pos T.totalWeight with h | h
  · simp [h]
  · rw [div_le_one (by exact_mod_cast h)]
    have := sum_mul_le_sum (l := T.challenges) _ fun c => passProb_le_one σ c.2.1 c.2.2
    rw [SubgroupTestData.totalWeight, Nat.cast_list_sum, List.map_map]
    exact this

/-- The trivial action, on one point. -/
def trivialAction (n : ℕ) : FiniteAction n := ⟨1, Nat.one_pos, fun _ => 1⟩

instance (n : ℕ) : Nonempty (FiniteAction n) := ⟨trivialAction n⟩

theorem bddAbove_value (T : SubgroupTestData) : BddAbove (Set.range T.value) :=
  ⟨1, by rintro _ ⟨σ, rfl⟩; exact value_le_one T σ⟩

theorem valSof_le_one (T : SubgroupTestData) : T.valSof ≤ 1 :=
  ciSup_le fun σ => value_le_one T σ

/-! ## Main Theorem II -/

/-- **Completeness of Main Theorem II** (Theorem I:2126 (1)). -/
theorem valSof_eq_one_of_hasPerfectZPC (g : TailoredGameData) (h : g.HasPerfectZPC) :
    (assocTest g).valSof = 1 := by
  obtain ⟨σ, hσ⟩ := exists_value_one_of_hasPerfectZPC g h
  refine le_antisymm (valSof_le_one _) ?_
  have : (assocTest g).value σ ≤ (assocTest g).valSof :=
    le_ciSup (f := (assocTest g).value) (bddAbove_value _) σ
  rw [hσ] at this
  exact this

/-- The constant of Main Theorem II's soundness. -/
def CII : ℝ := 600

/-- **Soundness of Main Theorem II** (Theorem I:2126 (2)): a sofic value of at least `1 − ε` gives
a synchronous value of at least `1 − 600 (Λ+1)^4 2^{6(Λ+1)} ε`. -/
theorem gameValue_ge_of_valSof (g : TailoredGameData) (ε : ℝ)
    (h : 1 - ε ≤ (assocTest g).valSof) :
    1 - CII * ((g.ansLen : ℝ) + 1) ^ 4 * 2 ^ (6 * (g.ansLen + 1)) * ε ≤ gameValue g.toGame := by
  set A : ℝ := CII * ((g.ansLen : ℝ) + 1) ^ 4 * 2 ^ (6 * (g.ansLen + 1)) with hA
  have hA0 : 0 ≤ A := by rw [hA, CII]; positivity
  -- for every slack `δ > 0`
  have key : ∀ δ > 0, 1 - A * (ε + δ) ≤ gameValue g.toGame := by
    intro δ hδ
    obtain ⟨σ, hσ⟩ := exists_lt_of_lt_ciSup (f := (assocTest g).value)
      (show (assocTest g).valSof - δ < ⨆ σ, (assocTest g).value σ by
        change (assocTest g).valSof - δ < (assocTest g).valSof; linarith)
    obtain ⟨σ', hc, hv⟩ := exists_checks_of_value g σ (ε + δ) (by linarith)
    have hg := gameValue_ge_of_checks g σ' hc
    have e : Cq * 2 ^ (2 * (g.ansLen + 1)) * (Cp * ((g.ansLen : ℝ) + 1) ^ 4 *
        2 ^ (4 * (g.ansLen + 1))) = A := by
      rw [hA, Cq, Cp, CII, show 6 * (g.ansLen + 1) = 2 * (g.ansLen + 1) + 4 * (g.ansLen + 1) by
        ring, pow_add]
      ring
    have hK : 0 ≤ Cq * (2 : ℝ) ^ (2 * (g.ansLen + 1)) := by rw [Cq]; positivity
    have : 1 - (assocTest g).value σ' ≤ Cp * ((g.ansLen : ℝ) + 1) ^ 4 *
        2 ^ (4 * (g.ansLen + 1)) * (ε + δ) := by linarith
    calc 1 - A * (ε + δ) = 1 - Cq * 2 ^ (2 * (g.ansLen + 1)) * (Cp * ((g.ansLen : ℝ) + 1) ^ 4 *
          2 ^ (4 * (g.ansLen + 1)) * (ε + δ)) := by rw [← e]; ring
      _ ≤ 1 - Cq * 2 ^ (2 * (g.ansLen + 1)) * (1 - (assocTest g).value σ') := by
          have := mul_le_mul_of_nonneg_left this hK
          linarith
      _ ≤ gameValue g.toGame := hg
  -- let `δ → 0`
  by_contra hlt
  push Not at hlt
  set d := 1 - A * ε - gameValue g.toGame with hd
  have hdpos : 0 < d := by linarith
  have := key (d / (2 * (A + 1))) (by positivity)
  have h2 : A * (d / (2 * (A + 1))) < d := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  nlinarith

/-! ## The gap function -/

/-- The gap function of Main Theorem II: `600 (Λ+1)^4 2^{6(Λ+1)}`. -/
def gapK (Λ : ℕ) : ℕ := 600 * (Λ + 1) ^ 4 * 2 ^ (6 * (Λ + 1))

theorem primrec_gapK : Primrec gapK :=
  (Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const 600)
    (Cost.primrec_nat_pow.comp Primrec.succ (Primrec.const 4)))
    (Cost.primrec_nat_pow.comp (Primrec.const 2)
      (Primrec.nat_mul.comp (Primrec.const 6) Primrec.succ))).of_eq fun _ => rfl

/-- **Main Theorem II** (Theorem I:2126), in the form the corollary uses. -/
theorem mainTheoremII : MainTheoremII gapK where
  one_le Λ := by
    have : 0 < gapK Λ := by unfold gapK; positivity
    omega
  complete := valSof_eq_one_of_hasPerfectZPC
  sound g hg := by
    by_contra hlt
    push Not at hlt
    have hK : (gapK g.ansLen : ℝ) = CII * ((g.ansLen : ℝ) + 1) ^ 4 * 2 ^ (6 * (g.ansLen + 1)) := by
      unfold gapK CII; push_cast; ring
    have hKpos : (0 : ℝ) < gapK g.ansLen := by
      have : 0 < gapK g.ansLen := by unfold gapK; positivity
      exact_mod_cast this
    set ε := 1 - (assocTest g).valSof with hε
    have hε' : ε < 1 / (2 * (gapK g.ansLen : ℝ)) := by linarith
    have h1 := gameValue_ge_of_valSof g ε (by linarith)
    rw [← hK] at h1
    have h2 : (gapK g.ansLen : ℝ) * ε < 1 / 2 := by
      have := mul_lt_mul_of_pos_left hε' hKpos
      rwa [show (gapK g.ansLen : ℝ) * (1 / (2 * gapK g.ansLen)) = 1 / 2 by field_simp] at this
    linarith

/-- **The sofic value is not approximable, from a halting reduction to tailored games**
(Corollary I:2144, measure-free). -/
theorem not_sofValueApproximable (hred : TailoredHaltingReduction) : ¬ SofValueApproximable :=
  not_sofValueApproximable_of primrec_gapK mainTheoremII hred

end MIPRE.Tailored.Sofic

end
