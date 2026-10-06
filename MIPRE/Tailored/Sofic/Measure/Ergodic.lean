/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Sofic.Measure.Value

@[expose] public section

/-!
# The ergodic value, and the sofic value under the Aldous–Lyons conjecture

Paper I, I:497 and Corollary I:550. The ergodic value `valErg T` of a test is the supremum of its
value over the invariant random subgroups. The finitely described IRSs are invariant
(`finDescIRS_subset_IRS`), so the sofic value is at most the ergodic value
(`valSof_le_valErg`). Under the Aldous–Lyons conjecture they are equal (`valSof_eq_valErg`): the
finitely described IRSs are dense in the IRSs and the value is weak-* continuous.
-/

namespace SubgroupTestValue

open MeasureTheory MIPRE.Tailored.Sofic.Measure

/-! ## Conjugation -/

theorem continuous_conj {s : ℕ} (w : FreeGroup (Fin s)) :
    Continuous (conj w : SubgroupSpace s → SubgroupSpace s) := by
  unfold conj
  apply Continuous.subtype_mk
  exact continuous_pi fun v => (continuous_apply (w⁻¹ * v * w)).comp continuous_subtype_val

theorem measurable_conj {s : ℕ} (w : FreeGroup (Fin s)) :
    Measurable (conj w : SubgroupSpace s → SubgroupSpace s) :=
  (continuous_conj w).measurable

/-- Conjugating a stabilizer: `w Stab(σ, x) w⁻¹ = Stab(σ, σ(w) x)`. -/
theorem conj_stab {s : ℕ} (σ : FiniteAction s) (w : FreeGroup (Fin s)) (x : Fin σ.N) :
    conj w (stab σ x) = stab σ (FreeGroup.lift σ.σ w x) := by
  apply Subtype.ext
  funext v
  simp only [conj, stab, map_mul, map_inv, Equiv.Perm.mul_apply]
  congr 1
  apply propext
  rw [Equiv.Perm.inv_eq_iff_eq]

/-- **The finitely described IRSs are invariant.** -/
theorem finDescIRS_subset_IRS (s : ℕ) : finDescIRS s ⊆ IRS s := by
  rintro μ ⟨σ, hμ⟩ w
  ext E hE
  rw [Measure.map_apply (measurable_conj w) hE, hμ]
  simp only [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.dirac_apply' _ hE, Measure.dirac_apply' _ (measurable_conj w hE)]
  congr 1
  refine (Finset.sum_congr rfl fun x _ => ?_).trans
    (Equiv.sum_comp (FreeGroup.lift σ.σ w) (fun x => E.indicator 1 (stab σ x)))
  rw [← conj_stab]
  rfl

namespace FiniteAction

/-- The trivial action on one point. -/
def trivial (s : ℕ) : FiniteAction s := ⟨1, one_pos, fun _ => 1⟩

instance (s : ℕ) : Nonempty (FiniteAction s) := ⟨trivial s⟩

theorem finDesc_mem_IRS {s : ℕ} (σ : FiniteAction s) : σ.finDesc ∈ IRS s :=
  finDescIRS_subset_IRS s σ.finDesc_mem

end FiniteAction

namespace SubgroupTestData

variable (T : SubgroupTestData)

/-- **The ergodic value** (I:497): the supremum of the value over the invariant random
subgroups. -/
noncomputable def valErg : ℝ := ⨆ μ ∈ IRS T.nGen, T.valOn μ

theorem le_valErg {μ : MeasureTheory.ProbabilityMeasure (SubgroupSpace T.nGen)}
    (hμ : μ ∈ IRS T.nGen) : T.valOn μ ≤ T.valErg := by
  have hb : BddAbove (Set.range fun ν : ProbabilityMeasure (SubgroupSpace T.nGen) =>
      ⨆ _ : ν ∈ IRS T.nGen, T.valOn ν) :=
    ⟨1, by
      rintro _ ⟨ν, rfl⟩
      exact Real.iSup_le (fun _ => T.valOn_le_one ν) zero_le_one⟩
  refine le_trans ?_ (le_ciSup hb μ)
  rw [ciSup_pos hμ]

theorem valErg_le {a : ℝ} (h : ∀ μ ∈ IRS T.nGen, T.valOn μ ≤ a) (ha : 0 ≤ a) : T.valErg ≤ a :=
  Real.iSup_le (fun μ => Real.iSup_le (fun hμ => h μ hμ) ha) ha

theorem valErg_le_one : T.valErg ≤ 1 :=
  T.valErg_le (fun _ _ => T.valOn_le_one _) zero_le_one

theorem bddAbove_value : BddAbove (Set.range T.value) :=
  ⟨1, by rintro _ ⟨σ, rfl⟩; exact T.value_le_one σ⟩

theorem le_valSof (σ : FiniteAction T.nGen) : T.value σ ≤ T.valSof :=
  le_ciSup T.bddAbove_value σ

theorem valSof_nonneg : 0 ≤ T.valSof :=
  (T.value_nonneg (FiniteAction.trivial _)).trans (T.le_valSof _)

theorem valSof_le_one : T.valSof ≤ 1 :=
  ciSup_le T.value_le_one

theorem valErg_nonneg : 0 ≤ T.valErg :=
  (T.valOn_nonneg _).trans (T.le_valErg (FiniteAction.trivial T.nGen).finDesc_mem_IRS)

/-- **The sofic value is at most the ergodic value** (I:524). -/
theorem valSof_le_valErg : T.valSof ≤ T.valErg :=
  ciSup_le fun σ => T.valOn_finDesc σ ▸ T.le_valErg σ.finDesc_mem_IRS

/-- The value of every IRS in the closure of the finitely described ones is at most the sofic
value. -/
theorem valOn_le_valSof_of_mem_closure {μ : ProbabilityMeasure (SubgroupSpace T.nGen)}
    (hμ : μ ∈ closure (finDescIRS T.nGen)) : T.valOn μ ≤ T.valSof := by
  have hcl : IsClosed {ν : ProbabilityMeasure (SubgroupSpace T.nGen) | T.valOn ν ≤ T.valSof} :=
    isClosed_le T.continuous_valOn continuous_const
  refine (hcl.closure_subset_iff.2 ?_) hμ
  rintro ν ⟨σ, hν⟩
  show T.valOn ν ≤ T.valSof
  rw [T.valOn_of_eq σ ν hν]
  exact T.le_valSof σ

/-- **Corollary I:550**: under the Aldous–Lyons conjecture the sofic and ergodic values of every
test are equal. -/
theorem valSof_eq_valErg (hAL : AldousLyons) : T.valSof = T.valErg :=
  le_antisymm T.valSof_le_valErg
    (T.valErg_le (fun _ hμ => T.valOn_le_valSof_of_mem_closure (hAL _ hμ)) T.valSof_nonneg)

end SubgroupTestData

end SubgroupTestValue

end
