/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Prelim/Information.lean
-/
/-
# Classical information toolkit

Ported from `QuantumParallelRepetition.lean` (github.com/openai/ten-proofs,
Apache-2.0; see lean/NOTICE), lines 10615-11405, with the outer namespace renamed.
Classical/scalar material only; no quantum layer is imported.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Prelim.Entropy
import MIPRE.Background.Repetition.CommutingRepetition.Prelim.Seed

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

noncomputable section

open scoped BigOperators

namespace ClassicalInformation

open Pinsker
open ClassicalSampling

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def distributionFloorNumerator (denominator : ℕ) (p : ι → ℝ) : ι → ℕ :=
  fun i => Nat.floor (p i * (denominator : ℝ))

def distributionFloorResidual (denominator : ℕ) (p : ι → ℝ) : ℕ :=
  denominator - ∑ i, distributionFloorNumerator denominator p i

def distributionRoundedNumerator
    (base : ι) (denominator : ℕ) (p : ι → ℝ) : ι → ℕ :=
  fun i => distributionFloorNumerator denominator p i +
    if i = base then distributionFloorResidual denominator p else 0

def distributionFloorProbability
    (denominator : ℕ) (p : ι → ℝ) : ι → ℝ :=
  fun i => (distributionFloorNumerator denominator p i : ℝ) / denominator

def distributionRoundedProbability
    (base : ι) (denominator : ℕ) (p : ι → ℝ) : ι → ℝ :=
  fun i =>
    (distributionRoundedNumerator base denominator p i : ℝ) / denominator

omit [Fintype ι] [DecidableEq ι] in

theorem distributionFloorNumerator_cast_le
    (denominator : ℕ) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (i : ι) :
    (distributionFloorNumerator denominator p i : ℝ) ≤
      p i * denominator := by
  unfold distributionFloorNumerator
  exact Nat.floor_le (mul_nonneg (hp i) (Nat.cast_nonneg _))

omit [Fintype ι] [DecidableEq ι] in

theorem distributionFloorProbability_le
    (denominator : ℕ) (positive : 0 < denominator)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (i : ι) :
    distributionFloorProbability denominator p i ≤ p i := by
  have hden : 0 < (denominator : ℝ) := by exact_mod_cast positive
  unfold distributionFloorProbability
  apply (div_le_iff₀ hden).mpr
  exact distributionFloorNumerator_cast_le denominator p hp i

omit [Fintype ι] [DecidableEq ι] in

theorem distributionFloorProbability_error_lt
    (denominator : ℕ) (positive : 0 < denominator)
    (p : ι → ℝ) (i : ι) :
    p i - distributionFloorProbability denominator p i <
      (1 : ℝ) / denominator := by
  have hden : 0 < (denominator : ℝ) := by exact_mod_cast positive
  apply (lt_div_iff₀ hden).mpr
  have hupper := Nat.lt_floor_add_one (p i * (denominator : ℝ))
  unfold distributionFloorProbability distributionFloorNumerator
  calc
    (p i - (Nat.floor (p i * (denominator : ℝ)) : ℝ) /
        (denominator : ℝ)) * (denominator : ℝ) =
      p i * (denominator : ℝ) - Nat.floor (p i * (denominator : ℝ)) := by
        field_simp
    _ < 1 := by linarith

omit [DecidableEq ι] in

theorem distributionFloorNumerator_sum_le
    (denominator : ℕ) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (normalized : (∑ i, p i) = 1) :
    (∑ i, distributionFloorNumerator denominator p i) ≤ denominator := by
  have hreal :
      ((∑ i, distributionFloorNumerator denominator p i) : ℝ) ≤
        (denominator : ℝ) := by
    calc
      ((∑ i, distributionFloorNumerator denominator p i) : ℝ) =
          ∑ i, (distributionFloorNumerator denominator p i : ℝ) := by
        simp
      _ ≤ ∑ i, p i * (denominator : ℝ) :=
        Finset.sum_le_sum fun i _ =>
          distributionFloorNumerator_cast_le denominator p hp i
      _ = (denominator : ℝ) := by
        rw [← Finset.sum_mul, normalized]
        simp
  exact_mod_cast hreal

theorem distributionRoundedNumerator_sum
    (base : ι) (denominator : ℕ) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (normalized : (∑ i, p i) = 1) :
    (∑ i, distributionRoundedNumerator base denominator p i) =
      denominator := by
  have hfloor := distributionFloorNumerator_sum_le
    denominator p hp normalized
  unfold distributionRoundedNumerator
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  unfold distributionFloorResidual
  omega

omit [DecidableEq ι] in

theorem distributionFloorResidual_probability_eq_sum
    (denominator : ℕ) (positive : 0 < denominator)
    (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (normalized : (∑ i, p i) = 1) :
    (distributionFloorResidual denominator p : ℝ) / denominator =
      ∑ i, (p i - distributionFloorProbability denominator p i) := by
  have hfloor := distributionFloorNumerator_sum_le
    denominator p hp normalized
  have hden : (denominator : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt positive)
  unfold distributionFloorResidual distributionFloorProbability
  rw [Nat.cast_sub hfloor, Nat.cast_sum, Finset.sum_sub_distrib,
    normalized, ← Finset.sum_div]
  field_simp

theorem distributionRoundedProbability_eq_floor_add
    (base : ι) (denominator : ℕ) (p : ι → ℝ) (i : ι) :
    distributionRoundedProbability base denominator p i =
      distributionFloorProbability denominator p i +
        if i = base then
          (distributionFloorResidual denominator p : ℝ) / denominator
        else 0 := by
  by_cases hbase : i = base
  · simp [distributionRoundedProbability,
      distributionRoundedNumerator, distributionFloorProbability,
      hbase, Nat.cast_add]
    ring
  · simp [distributionRoundedProbability,
      distributionRoundedNumerator, distributionFloorProbability, hbase]

theorem distributionRoundedProbability_totalVariation_le
    (base : ι) (denominator : ℕ) (positive : 0 < denominator)
    (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (normalized : (∑ i, p i) = 1) :
    finiteTotalVariation p
        (distributionRoundedProbability base denominator p) ≤
      (Fintype.card ι : ℝ) / denominator := by
  have hden : 0 < (denominator : ℝ) := by exact_mod_cast positive
  have hres :
      0 ≤ (distributionFloorResidual denominator p : ℝ) / denominator :=
    div_nonneg (Nat.cast_nonneg _) hden.le
  have hpoint : ∀ i,
      |p i - distributionRoundedProbability base denominator p i| ≤
        (p i - distributionFloorProbability denominator p i) +
          if i = base then
            (distributionFloorResidual denominator p : ℝ) / denominator
          else 0 := by
    intro i
    have hdefect :
        0 ≤ p i - distributionFloorProbability denominator p i :=
      sub_nonneg.mpr
        (distributionFloorProbability_le denominator positive p hp i)
    have htriangle := abs_sub_le (p i)
      (distributionFloorProbability denominator p i)
      (distributionRoundedProbability base denominator p i)
    rw [abs_of_nonneg hdefect] at htriangle
    have hcorrection :
        |distributionFloorProbability denominator p i -
            distributionRoundedProbability base denominator p i| =
          if i = base then
            (distributionFloorResidual denominator p : ℝ) / denominator
          else 0 := by
      rw [distributionRoundedProbability_eq_floor_add]
      by_cases hbase : i = base
      · simp [hbase, abs_of_nonneg hres]
      · simp [hbase]
    rw [hcorrection] at htriangle
    exact htriangle
  have htv_defect :
      finiteTotalVariation p
          (distributionRoundedProbability base denominator p) ≤
        ∑ i, (p i - distributionFloorProbability denominator p i) := by
    calc
      finiteTotalVariation p
          (distributionRoundedProbability base denominator p) =
        (∑ i, |p i - distributionRoundedProbability
          base denominator p i|) / 2 := rfl
      _ ≤ (∑ i,
          ((p i - distributionFloorProbability denominator p i) +
            if i = base then
              (distributionFloorResidual denominator p : ℝ) / denominator
            else 0)) / 2 := by
        apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr
        exact Finset.sum_le_sum fun i _ => hpoint i
      _ = ∑ i, (p i - distributionFloorProbability denominator p i) := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        rw [distributionFloorResidual_probability_eq_sum
          denominator positive p hp normalized]
        ring
  calc
    finiteTotalVariation p
        (distributionRoundedProbability base denominator p) ≤
      ∑ i, (p i - distributionFloorProbability denominator p i) :=
        htv_defect
    _ ≤ ∑ _i : ι, (1 : ℝ) / denominator :=
      Finset.sum_le_sum fun i _ =>
        (distributionFloorProbability_error_lt denominator positive p i).le
    _ = (Fintype.card ι : ℝ) / denominator := by
      simp [div_eq_mul_inv]

omit [Fintype ι] [DecidableEq ι] in

theorem finite_log_sum_inequality
    (indices : Finset ι) (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hq : ∀ i, 0 ≤ q i)
    (absolute_continuity : ∀ i, q i = 0 → p i = 0)
    (positive_mass : 0 < ∑ i ∈ indices, q i) :
    (∑ i ∈ indices, q i) *
        InformationTheory.klFun
          ((∑ i ∈ indices, p i) / (∑ i ∈ indices, q i)) ≤
      ∑ i ∈ indices,
        q i * InformationTheory.klFun (p i / q i) := by
  let total : ℝ := ∑ i ∈ indices, q i
  have htotal : 0 < total := positive_mass
  have hnormalized :
      (∑ i ∈ indices, q i / total) = 1 := by
    rw [← Finset.sum_div]
    exact div_self htotal.ne'
  have hmean :
      (∑ i ∈ indices, (q i / total) * (p i / q i)) =
        (∑ i ∈ indices, p i) / total := by
    calc
      (∑ i ∈ indices, (q i / total) * (p i / q i)) =
          ∑ i ∈ indices, p i / total := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hqi : q i = 0
        · simp [hqi, absolute_continuity i hqi]
        · field_simp [hqi, htotal.ne']
      _ = (∑ i ∈ indices, p i) / total := by
        rw [Finset.sum_div]
  have hjensen :
      InformationTheory.klFun ((∑ i ∈ indices, p i) / total) ≤
        ∑ i ∈ indices,
          (q i / total) * InformationTheory.klFun (p i / q i) := by
    have h := InformationTheory.convexOn_klFun.map_sum_le
      (t := indices)
      (w := fun i => q i / total)
      (p := fun i => p i / q i)
      (fun i _ => div_nonneg (hq i) htotal.le)
      hnormalized
      (fun i _ => show p i / q i ∈ Set.Ici (0 : ℝ) from
        div_nonneg (hp i) (hq i))
    simpa only [smul_eq_mul, hmean] using h
  change
    total * InformationTheory.klFun
      ((∑ i ∈ indices, p i) / total) ≤
      ∑ i ∈ indices, q i * InformationTheory.klFun (p i / q i)
  calc
    total * InformationTheory.klFun
        ((∑ i ∈ indices, p i) / total) ≤
      total * (∑ i ∈ indices,
        (q i / total) * InformationTheory.klFun (p i / q i)) :=
      mul_le_mul_of_nonneg_left hjensen htotal.le
    _ = ∑ i ∈ indices,
        q i * InformationTheory.klFun (p i / q i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      field_simp [htotal.ne']

section CoarseGraining

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def groupedMass (map : ι → κ) (p : ι → ℝ) (j : κ) : ℝ :=
  ∑ i ∈ (Finset.univ.filter fun i => map i = j), p i

omit [DecidableEq ι] in

theorem finite_relative_entropy_data_processing
    (map : ι → κ) (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hq : ∀ i, 0 ≤ q i)
    (absolute_continuity : ∀ i, q i = 0 → p i = 0) :
    finiteRelativeEntropy (groupedMass map p) (groupedMass map q) ≤
      finiteRelativeEntropy p q := by
  change
    (∑ j : κ, groupedMass map q j *
      InformationTheory.klFun
        (groupedMass map p j / groupedMass map q j)) ≤
      ∑ i : ι, q i * InformationTheory.klFun (p i / q i)
  calc
    (∑ j : κ, groupedMass map q j *
        InformationTheory.klFun
          (groupedMass map p j / groupedMass map q j)) ≤
      ∑ j : κ,
        ∑ i ∈ (Finset.univ.filter fun i => map i = j),
          q i * InformationTheory.klFun (p i / q i) := by
        apply Finset.sum_le_sum
        intro j _
        let indices : Finset ι :=
          Finset.univ.filter fun i => map i = j
        change
          (∑ i ∈ indices, q i) *
              InformationTheory.klFun
                ((∑ i ∈ indices, p i) / (∑ i ∈ indices, q i)) ≤
            ∑ i ∈ indices,
              q i * InformationTheory.klFun (p i / q i)
        have hreference : 0 ≤ ∑ i ∈ indices, q i :=
          Finset.sum_nonneg (fun i _ => hq i)
        by_cases hzero : (∑ i ∈ indices, q i) = 0
        · rw [hzero, zero_mul]
          apply Finset.sum_nonneg
          intro i _
          exact mul_nonneg (hq i)
            (InformationTheory.klFun_nonneg
              (div_nonneg (hp i) (hq i)))
        · exact finite_log_sum_inequality indices p q hp hq
            absolute_continuity (lt_of_le_of_ne hreference (Ne.symm hzero))
    _ = ∑ i : ι,
        q i * InformationTheory.klFun (p i / q i) := by
      simpa only [] using
        (Finset.sum_fiberwise (Finset.univ : Finset ι) map
          (fun i => q i * InformationTheory.klFun (p i / q i)))

end CoarseGraining

section JointChainRule

variable {κ : Type*} [Fintype κ]

def jointFirstMarginal (joint : ι × κ → ℝ) : ι → ℝ :=
  fun i => ∑ j : κ, joint (i, j)

def jointConditional (joint : ι × κ → ℝ) (i : ι) : κ → ℝ :=
  fun j => joint (i, j) / jointFirstMarginal joint i

omit [Fintype ι] [DecidableEq ι] in

theorem jointFirstMarginal_nonneg
    (joint : ι × κ → ℝ)
    (nonnegative : ∀ point, 0 ≤ joint point) (i : ι) :
    0 ≤ jointFirstMarginal joint i := by
  exact Finset.sum_nonneg (fun j _ => nonnegative (i, j))

omit [DecidableEq ι] in

theorem jointFirstMarginal_sum (joint : ι × κ → ℝ) :
    (∑ i : ι, jointFirstMarginal joint i) =
      ∑ point : ι × κ, joint point := by
  exact (Fintype.sum_prod_type joint).symm

omit [Fintype ι] [DecidableEq ι] in

theorem jointFirstMarginal_absolute_continuity
    (p q : ι × κ → ℝ)
    (hq : ∀ point, 0 ≤ q point)
    (absolute_continuity : ∀ point, q point = 0 → p point = 0)
    (i : ι) :
    jointFirstMarginal q i = 0 → jointFirstMarginal p i = 0 := by
  intro hzero
  change (∑ j : κ, q (i, j)) = 0 at hzero
  have hcoordinates : ∀ j : κ, q (i, j) = 0 := by
    intro j
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => hq (i, j))).mp hzero j (Finset.mem_univ j)
  change (∑ j : κ, p (i, j)) = 0
  exact Finset.sum_eq_zero
    (fun j _ => absolute_continuity (i, j) (hcoordinates j))

omit [Fintype ι] [DecidableEq ι] in

theorem jointConditional_sum
    (joint : ι × κ → ℝ) (i : ι)
    (nonzero : jointFirstMarginal joint i ≠ 0) :
    (∑ j : κ, jointConditional joint i j) = 1 := by
  unfold jointConditional
  rw [← Finset.sum_div]
  exact div_self nonzero

omit [DecidableEq ι] in

theorem finite_relative_entropy_joint_chain_rule
    (p q : ι × κ → ℝ)
    (hp : ∀ point, 0 ≤ p point)
    (hq : ∀ point, 0 ≤ q point)
    (absolute_continuity : ∀ point, q point = 0 → p point = 0)
    (hp_normalized : (∑ point, p point) = 1)
    (hq_normalized : (∑ point, q point) = 1) :
    finiteRelativeEntropy p q =
      finiteRelativeEntropy (jointFirstMarginal p)
        (jointFirstMarginal q) +
      ∑ i : ι, jointFirstMarginal p i *
        finiteRelativeEntropy (jointConditional p i)
          (jointConditional q i) := by
  have hp_marginal : (∑ i : ι, jointFirstMarginal p i) = 1 :=
    (jointFirstMarginal_sum p).trans hp_normalized
  have hq_marginal : (∑ i : ι, jointFirstMarginal q i) = 1 :=
    (jointFirstMarginal_sum q).trans hq_normalized
  have h_marginal_absolute :
      ∀ i : ι, jointFirstMarginal q i = 0 →
        jointFirstMarginal p i = 0 :=
    jointFirstMarginal_absolute_continuity p q hq absolute_continuity
  have h_joint_log :
      finiteRelativeEntropy p q =
        ∑ point : ι × κ,
          p point * Real.log (p point / q point) :=
    finiteRelativeEntropy_eq_log_sum_of_absolute_continuity
      p q hq absolute_continuity hp_normalized hq_normalized
  have h_marginal_log :
      finiteRelativeEntropy (jointFirstMarginal p)
        (jointFirstMarginal q) =
        ∑ i : ι, jointFirstMarginal p i *
          Real.log (jointFirstMarginal p i /
            jointFirstMarginal q i) :=
    finiteRelativeEntropy_eq_log_sum_of_absolute_continuity
      (jointFirstMarginal p) (jointFirstMarginal q)
      (jointFirstMarginal_nonneg q hq)
      h_marginal_absolute hp_marginal hq_marginal
  calc
    finiteRelativeEntropy p q =
      ∑ point : ι × κ,
        p point * Real.log (p point / q point) := h_joint_log
    _ = ∑ i : ι, ∑ j : κ,
        p (i, j) * Real.log (p (i, j) / q (i, j)) :=
          Fintype.sum_prod_type _
    _ = ∑ i : ι,
        (jointFirstMarginal p i *
          Real.log (jointFirstMarginal p i /
            jointFirstMarginal q i) +
          jointFirstMarginal p i *
            finiteRelativeEntropy (jointConditional p i)
              (jointConditional q i)) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hpzero : jointFirstMarginal p i = 0
      · have hcoordinates : ∀ j : κ, p (i, j) = 0 := by
          intro j
          apply (Finset.sum_eq_zero_iff_of_nonneg
            (fun j _ => hp (i, j))).mp
              (show (∑ j : κ, p (i, j)) = 0 from hpzero)
              j (Finset.mem_univ j)
        simp [hpzero, hcoordinates]
      · have hqzero : jointFirstMarginal q i ≠ 0 := by
          intro hzero
          exact hpzero (h_marginal_absolute i hzero)
        have hconditional_absolute :
            ∀ j : κ, jointConditional q i j = 0 →
              jointConditional p i j = 0 := by
          intro j hzero
          change q (i, j) / jointFirstMarginal q i = 0 at hzero
          have hpoint : q (i, j) = 0 := by
            rcases (div_eq_zero_iff.mp hzero) with hpoint | hmarginal
            · exact hpoint
            · exact (hqzero hmarginal).elim
          simp [jointConditional, absolute_continuity (i, j) hpoint]
        have hconditional_log :
            finiteRelativeEntropy (jointConditional p i)
              (jointConditional q i) =
              ∑ j : κ,
                jointConditional p i j *
                  Real.log (jointConditional p i j /
                    jointConditional q i j) := by
          apply finiteRelativeEntropy_eq_log_sum_of_absolute_continuity
          · intro j
            exact div_nonneg (hq (i, j))
              (jointFirstMarginal_nonneg q hq i)
          · exact hconditional_absolute
          · exact jointConditional_sum p i hpzero
          · exact jointConditional_sum q i hqzero
        rw [hconditional_log]
        calc
          (∑ j : κ,
            p (i, j) * Real.log (p (i, j) / q (i, j))) =
            ∑ j : κ,
              (p (i, j) *
                Real.log (jointFirstMarginal p i /
                  jointFirstMarginal q i) +
                jointFirstMarginal p i *
                  (jointConditional p i j *
                    Real.log (jointConditional p i j /
                      jointConditional q i j))) := by
              apply Finset.sum_congr rfl
              intro j _
              by_cases hpj : p (i, j) = 0
              · simp [hpj, jointConditional]
              · have hqj : q (i, j) ≠ 0 := by
                  intro hzero
                  exact hpj (absolute_continuity (i, j) hzero)
                have hfactorization :
                    p (i, j) / q (i, j) =
                      (jointFirstMarginal p i /
                        jointFirstMarginal q i) *
                        (jointConditional p i j /
                          jointConditional q i j) := by
                  unfold jointConditional
                  field_simp [hpzero, hqzero, hqj]
                have hfirst :
                    jointFirstMarginal p i /
                      jointFirstMarginal q i ≠ 0 :=
                  div_ne_zero hpzero hqzero
                have hsecond :
                    jointConditional p i j /
                      jointConditional q i j ≠ 0 := by
                  unfold jointConditional
                  exact div_ne_zero
                    (div_ne_zero hpj hpzero)
                    (div_ne_zero hqj hqzero)
                rw [hfactorization, Real.log_mul hfirst hsecond]
                unfold jointConditional
                field_simp [hpzero]
          _ = jointFirstMarginal p i *
              Real.log (jointFirstMarginal p i /
                jointFirstMarginal q i) +
              jointFirstMarginal p i *
                (∑ j : κ,
                  jointConditional p i j *
                    Real.log (jointConditional p i j /
                      jointConditional q i j)) := by
                rw [Finset.sum_add_distrib, ← Finset.sum_mul,
                  ← Finset.mul_sum]
                rfl
    _ = (∑ i : ι,
          jointFirstMarginal p i *
            Real.log (jointFirstMarginal p i /
              jointFirstMarginal q i)) +
        ∑ i : ι, jointFirstMarginal p i *
          finiteRelativeEntropy (jointConditional p i)
            (jointConditional q i) := by
      rw [Finset.sum_add_distrib]
    _ = finiteRelativeEntropy (jointFirstMarginal p)
          (jointFirstMarginal q) +
        ∑ i : ι, jointFirstMarginal p i *
          finiteRelativeEntropy (jointConditional p i)
            (jointConditional q i) := by
      rw [h_marginal_log]

end JointChainRule

section SharedPermutationSampling

def rationalPermutationOutput
    (denominator : ℕ) (numerator : ι → ℕ)
    (nonempty : (rationalMarked denominator numerator).Nonempty)
    (permutation : Equiv.Perm (ι × Fin denominator)) : ι :=
  (markedFirst (Fintype.equivFin (ι × Fin denominator))
    (rationalMarked denominator numerator) nonempty permutation).1

theorem rationalPermutationOutput_probability
    (denominator : ℕ) (numerator : ι → ℕ)
    (normalized : (∑ i, numerator i) = denominator)
    (nonempty : (rationalMarked denominator numerator).Nonempty)
    (letter : ι) :
    uniformPermutationProbability
        (fun permutation : Equiv.Perm (ι × Fin denominator) =>
          rationalPermutationOutput denominator numerator
            nonempty permutation = letter) =
      (numerator letter : ℝ) / denominator := by
  exact rationalMarked_letter_probability denominator numerator normalized
    nonempty (Fintype.equivFin (ι × Fin denominator)) letter

theorem rationalMarked_inter
    (denominator : ℕ) (left right : ι → ℕ) :
    rationalMarked denominator left ∩ rationalMarked denominator right =
      rationalMarked denominator (fun i => min (left i) (right i)) := by
  ext point
  simp [rationalMarked]

theorem rationalMarked_inter_card
    (denominator : ℕ) (left right : ι → ℕ)
    (hleft : (∑ i, left i) = denominator)
    (_hright : (∑ i, right i) = denominator) :
    (rationalMarked denominator left ∩
      rationalMarked denominator right).card =
        ∑ i : ι, min (left i) (right i) := by
  rw [rationalMarked_inter]
  calc
    (rationalMarked denominator
        (fun i => min (left i) (right i))).card =
      ∑ i : ι,
        ((rationalMarked denominator
          (fun i => min (left i) (right i))).filter
            fun point => point.1 = i).card := by
      simpa using
        (Finset.card_eq_sum_card_fiberwise
          (f := fun point : ι × Fin denominator => point.1)
          (s := rationalMarked denominator
            (fun i => min (left i) (right i)))
          (t := (Finset.univ : Finset ι))
          (fun _ _ => Finset.mem_univ _))
    _ = ∑ i : ι, min (left i) (right i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [rationalMarked_fiber_card, min_eq_right]
      exact (min_le_left (left i) (right i)).trans
        (rationalNumerator_le_denominator
          denominator left hleft i)

theorem rationalMarked_markedTotalVariation_eq
    (denominator : ℕ) (positive : 0 < denominator)
    (left right : ι → ℕ)
    (hleft : (∑ i, left i) = denominator)
    (hright : (∑ i, right i) = denominator) :
    markedTotalVariation
        (rationalMarked denominator left)
        (rationalMarked denominator right) =
      finiteTotalVariation
        (fun i => (left i : ℝ) / denominator)
        (fun i => (right i : ℝ) / denominator) := by
  let L := rationalMarked denominator left
  let R := rationalMarked denominator right
  have hL : L.card = denominator :=
    rationalMarked_card denominator left hleft
  have hR : R.card = denominator :=
    rationalMarked_card denominator right hright
  have hI :
      ((L ∩ R).card : ℝ) =
        ∑ i : ι, (min (left i) (right i) : ℝ) := by
    change
      (((rationalMarked denominator left ∩
        rationalMarked denominator right).card : ℕ) : ℝ) =
        ∑ i : ι, (min (left i) (right i) : ℝ)
    rw [rationalMarked_inter_card denominator left right hleft hright,
      Nat.cast_sum]
    simp only [Nat.cast_min]
  have hdisjoint : Disjoint (L \ R) (R \ L) := by
    apply Finset.disjoint_left.mpr
    intro point hpoint_left hpoint_right
    exact (Finset.mem_sdiff.mp hpoint_left).2
      (Finset.mem_sdiff.mp hpoint_right).1
  have hunion :
      (((L \ R) ∪ (R \ L)).card : ℝ) =
        ((L \ R).card : ℝ) + ((R \ L).card : ℝ) := by
    exact_mod_cast (Finset.card_union_of_disjoint hdisjoint)
  have hleft_difference :
      ((L \ R).card : ℝ) + ((L ∩ R).card : ℝ) =
        (L.card : ℝ) := by
    exact_mod_cast (Finset.card_sdiff_add_card_inter L R)
  have hright_difference :
      ((R \ L).card : ℝ) + ((L ∩ R).card : ℝ) =
        (R.card : ℝ) := by
    have h := Finset.card_sdiff_add_card_inter R L
    rw [Finset.inter_comm R L] at h
    exact_mod_cast h
  have hsymmetric :
      (((L \ R) ∪ (R \ L)).card : ℝ) =
        (denominator : ℝ) + denominator -
          2 * ∑ i : ι, (min (left i) (right i) : ℝ) := by
    have hLreal : (L.card : ℝ) = denominator := by exact_mod_cast hL
    have hRreal : (R.card : ℝ) = denominator := by exact_mod_cast hR
    linarith
  have hpointwise : ∀ i : ι,
      |(left i : ℝ) / denominator -
        (right i : ℝ) / denominator| =
        ((left i : ℝ) + right i -
          2 * (min (left i) (right i) : ℝ)) / denominator := by
    intro i
    rw [← sub_div, abs_div]
    have hdenominator_abs : |(denominator : ℝ)| = denominator :=
      abs_of_nonneg (Nat.cast_nonneg denominator)
    rw [hdenominator_abs]
    by_cases horder : left i ≤ right i
    · have hreal : (left i : ℝ) ≤ right i := by
        exact_mod_cast horder
      rw [min_eq_left hreal, abs_of_nonpos (sub_nonpos.mpr hreal)]
      ring
    · have horder' : right i ≤ left i :=
        (Nat.le_of_lt (Nat.lt_of_not_ge horder))
      have hreal : (right i : ℝ) ≤ left i := by
        exact_mod_cast horder'
      rw [min_eq_right hreal, abs_of_nonneg (sub_nonneg.mpr hreal)]
      ring
  have hleft_real : (∑ i : ι, (left i : ℝ)) = denominator := by
    exact_mod_cast hleft
  have hright_real : (∑ i : ι, (right i : ℝ)) = denominator := by
    exact_mod_cast hright
  have hdenominator : (denominator : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt positive)
  change
    (((L \ R) ∪ (R \ L)).card : ℝ) /
        (2 * (L.card : ℝ)) =
      (∑ i : ι,
        |(left i : ℝ) / denominator -
          (right i : ℝ) / denominator|) / 2
  rw [hsymmetric, hL]
  simp_rw [hpointwise]
  rw [← Finset.sum_div, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum,
    hleft_real, hright_real]
  field_simp [hdenominator]

theorem uniformPermutationProbability_mono
    {α : Type*} [Fintype α] [DecidableEq α]
    (small large : Equiv.Perm α → Prop)
    (hinclusion : ∀ permutation, small permutation → large permutation) :
    uniformPermutationProbability small ≤
      uniformPermutationProbability large := by
  classical
  unfold uniformPermutationProbability
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Finset.card_le_card (show
      (Finset.univ.filter fun permutation : Equiv.Perm α =>
        small permutation) ⊆
      (Finset.univ.filter fun permutation : Equiv.Perm α =>
        large permutation) from by
        intro permutation hpermutation
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hinclusion permutation
            (Finset.mem_filter.mp hpermutation).2⟩)
  · exact_mod_cast (Nat.zero_le (Fintype.card (Equiv.Perm α)))

theorem rationalPermutationOutput_disagreement_le_two_mul_tv
    (denominator : ℕ) (left right : ι → ℕ)
    (hleft : (∑ i, left i) = denominator)
    (hright : (∑ i, right i) = denominator)
    (nonempty_left : (rationalMarked denominator left).Nonempty)
    (nonempty_right : (rationalMarked denominator right).Nonempty) :
    uniformPermutationProbability
        (fun permutation : Equiv.Perm (ι × Fin denominator) =>
          rationalPermutationOutput denominator left
            nonempty_left permutation ≠
          rationalPermutationOutput denominator right
            nonempty_right permutation) ≤
      2 * markedTotalVariation
        (rationalMarked denominator left)
        (rationalMarked denominator right) := by
  let rank := Fintype.equivFin (ι × Fin denominator)
  calc
    uniformPermutationProbability
        (fun permutation : Equiv.Perm (ι × Fin denominator) =>
          rationalPermutationOutput denominator left
            nonempty_left permutation ≠
          rationalPermutationOutput denominator right
            nonempty_right permutation) ≤
      uniformPermutationProbability
        (fun permutation : Equiv.Perm (ι × Fin denominator) =>
          markedFirst rank (rationalMarked denominator left)
            nonempty_left permutation ≠
          markedFirst rank (rationalMarked denominator right)
            nonempty_right permutation) := by
        apply uniformPermutationProbability_mono
        intro permutation hdifferent hequal
        apply hdifferent
        exact congrArg Prod.fst hequal
    _ ≤ 2 * markedTotalVariation
        (rationalMarked denominator left)
        (rationalMarked denominator right) := by
      apply sharedPermutation_disagreement_probability_le_two_mul_tv
      calc
        (rationalMarked denominator left).card = denominator :=
          rationalMarked_card denominator left hleft
        _ = (rationalMarked denominator right).card :=
          (rationalMarked_card denominator right hright).symm

theorem rationalPermutationOutput_disagreement_le_two_mul_finiteTotalVariation
    (denominator : ℕ) (positive : 0 < denominator)
    (left right : ι → ℕ)
    (hleft : (∑ i, left i) = denominator)
    (hright : (∑ i, right i) = denominator)
    (nonempty_left : (rationalMarked denominator left).Nonempty)
    (nonempty_right : (rationalMarked denominator right).Nonempty) :
    uniformPermutationProbability
        (fun permutation : Equiv.Perm (ι × Fin denominator) =>
          rationalPermutationOutput denominator left
            nonempty_left permutation ≠
          rationalPermutationOutput denominator right
            nonempty_right permutation) ≤
      2 * finiteTotalVariation
        (fun i => (left i : ℝ) / denominator)
        (fun i => (right i : ℝ) / denominator) := by
  calc
    uniformPermutationProbability
        (fun permutation : Equiv.Perm (ι × Fin denominator) =>
          rationalPermutationOutput denominator left
            nonempty_left permutation ≠
          rationalPermutationOutput denominator right
            nonempty_right permutation) ≤
      2 * markedTotalVariation
        (rationalMarked denominator left)
        (rationalMarked denominator right) :=
          rationalPermutationOutput_disagreement_le_two_mul_tv
            denominator left right hleft hright
            nonempty_left nonempty_right
    _ = 2 * finiteTotalVariation
        (fun i => (left i : ℝ) / denominator)
        (fun i => (right i : ℝ) / denominator) := by
      rw [rationalMarked_markedTotalVariation_eq
        denominator positive left right hleft hright]

end SharedPermutationSampling

section Hellinger

omit [DecidableEq ι] in
/-- Squared Hellinger distance between two finitely supported densities,
`H²(P, Q) = ∑ ω, (√(P ω) − √(Q ω))²` (manuscript, Preliminaries). -/
def finiteHellingerSq (p q : ι → ℝ) : ℝ :=
  ∑ i, (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2

omit [DecidableEq ι] in
theorem finiteHellingerSq_nonneg (p q : ι → ℝ) :
    0 ≤ finiteHellingerSq p q :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem sub_one_le_mul_log {u : ℝ} (hu : 0 ≤ u) :
    u - 1 ≤ u * Real.log u := by
  rcases eq_or_lt_of_le hu with hzero | hpos
  · rw [← hzero]
    norm_num
  · calc
      u - 1 = u * (1 - u⁻¹) := by
        rw [mul_sub, mul_one, mul_inv_cancel₀ hpos.ne']
      _ ≤ u * Real.log u :=
        mul_le_mul_of_nonneg_left
          (Real.one_sub_inv_le_log_of_pos hpos) hpos.le

theorem sqrt_sub_one_sq_le_klFun {t : ℝ} (ht : 0 ≤ t) :
    (Real.sqrt t - 1) ^ 2 ≤ InformationTheory.klFun t := by
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht
  have hkey : Real.sqrt t - 1 ≤ Real.sqrt t * Real.log (Real.sqrt t) :=
    sub_one_le_mul_log (Real.sqrt_nonneg t)
  have hlog : t * Real.log t =
      2 * (Real.sqrt t * (Real.sqrt t * Real.log (Real.sqrt t))) := by
    calc
      t * Real.log t = Real.sqrt t ^ 2 * Real.log (Real.sqrt t ^ 2) := by
        rw [hsq]
      _ = 2 * (Real.sqrt t * (Real.sqrt t * Real.log (Real.sqrt t))) := by
        rw [Real.log_pow]
        push_cast
        ring
  have hmul := mul_le_mul_of_nonneg_left hkey (Real.sqrt_nonneg t)
  unfold InformationTheory.klFun
  nlinarith [hmul, hsq, hlog]

theorem hellinger_density_le_weighted_kl
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    (Real.sqrt p - Real.sqrt q) ^ 2 ≤
      q * InformationTheory.klFun (p / q) := by
  have hscalar := sqrt_sub_one_sq_le_klFun (div_nonneg hp hq.le)
  have hweighted := mul_le_mul_of_nonneg_left hscalar hq.le
  have hsqrt_mul : Real.sqrt q * Real.sqrt (p / q) = Real.sqrt p := by
    have hcancel : q * (p / q) = p := by
      field_simp
    rw [← Real.sqrt_mul hq.le, hcancel]
  calc
    (Real.sqrt p - Real.sqrt q) ^ 2 =
        (Real.sqrt q * (Real.sqrt (p / q) - 1)) ^ 2 := by
      rw [mul_sub, hsqrt_mul, mul_one]
    _ = q * (Real.sqrt (p / q) - 1) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hq.le]
    _ ≤ q * InformationTheory.klFun (p / q) := hweighted

omit [DecidableEq ι] in
/-- Hellinger–relative-entropy bound `H²(P, Q) ≤ D(P ‖ Q)` (manuscript,
Preliminaries), with the relative entropy in mass-weighted `klFun` form. -/
theorem finiteHellingerSq_le_relative_entropy
    (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hq : ∀ i, 0 ≤ q i)
    (absolute_continuity : ∀ i, q i = 0 → p i = 0) :
    finiteHellingerSq p q ≤
      ∑ i, q i * InformationTheory.klFun (p i / q i) := by
  unfold finiteHellingerSq
  apply Finset.sum_le_sum
  intro i _
  by_cases hqi : q i = 0
  · rw [hqi, absolute_continuity i hqi]
    simp
  · exact hellinger_density_le_weighted_kl (hp i)
      (lt_of_le_of_ne (hq i) (Ne.symm hqi))

omit [DecidableEq ι] in
/-- Total-variation–Hellinger bound: the manuscript display is
`‖P − Q‖₁ ≤ 2 H(P, Q)`; since `finiteTotalVariation` is the halved ℓ¹
distance `(∑ i, |p i − q i|) / 2`, the exact-constant form is
`finiteTotalVariation p q ≤ √(finiteHellingerSq p q)`. -/
theorem finiteTotalVariation_le_hellinger
    (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hq : ∀ i, 0 ≤ q i)
    (hp_normalized : (∑ i, p i) = 1)
    (hq_normalized : (∑ i, q i) = 1) :
    finiteTotalVariation p q ≤ Real.sqrt (finiteHellingerSq p q) := by
  apply Real.le_sqrt_of_sq_le
  have hpoint : ∀ i,
      |p i - q i| =
        |Real.sqrt (p i) - Real.sqrt (q i)| *
          (Real.sqrt (p i) + Real.sqrt (q i)) := by
    intro i
    have hfactor : p i - q i =
        (Real.sqrt (p i) - Real.sqrt (q i)) *
          (Real.sqrt (p i) + Real.sqrt (q i)) := by
      calc
        p i - q i = Real.sqrt (p i) ^ 2 - Real.sqrt (q i) ^ 2 := by
          rw [Real.sq_sqrt (hp i), Real.sq_sqrt (hq i)]
        _ = (Real.sqrt (p i) - Real.sqrt (q i)) *
            (Real.sqrt (p i) + Real.sqrt (q i)) := by
          ring
    rw [hfactor, abs_mul, abs_of_nonneg
      (add_nonneg (Real.sqrt_nonneg (p i)) (Real.sqrt_nonneg (q i)))]
  have hsum_eq :
      (∑ i, |p i - q i|) =
        ∑ i, |Real.sqrt (p i) - Real.sqrt (q i)| *
          (Real.sqrt (p i) + Real.sqrt (q i)) :=
    Finset.sum_congr rfl fun i _ => hpoint i
  have hcauchy :
      (∑ i, |Real.sqrt (p i) - Real.sqrt (q i)| *
          (Real.sqrt (p i) + Real.sqrt (q i))) ^ 2 ≤
        (∑ i, |Real.sqrt (p i) - Real.sqrt (q i)| ^ 2) *
          ∑ i, (Real.sqrt (p i) + Real.sqrt (q i)) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  have habs_sum :
      (∑ i, |Real.sqrt (p i) - Real.sqrt (q i)| ^ 2) =
        finiteHellingerSq p q := by
    unfold finiteHellingerSq
    exact Finset.sum_congr rfl fun i _ => sq_abs _
  have hcross :
      (∑ i, (Real.sqrt (p i) + Real.sqrt (q i)) ^ 2) ≤ 4 := by
    calc
      (∑ i, (Real.sqrt (p i) + Real.sqrt (q i)) ^ 2) ≤
          ∑ i, (2 * p i + 2 * q i) := by
        apply Finset.sum_le_sum
        intro i _
        have hpi : Real.sqrt (p i) ^ 2 = p i := Real.sq_sqrt (hp i)
        have hqi : Real.sqrt (q i) ^ 2 = q i := Real.sq_sqrt (hq i)
        nlinarith [sq_nonneg (Real.sqrt (p i) - Real.sqrt (q i))]
      _ = 4 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          hp_normalized, hq_normalized]
        norm_num
  calc
    finiteTotalVariation p q ^ 2 =
        (∑ i, |Real.sqrt (p i) - Real.sqrt (q i)| *
          (Real.sqrt (p i) + Real.sqrt (q i))) ^ 2 / 4 := by
      unfold finiteTotalVariation
      rw [hsum_eq, div_pow]
      norm_num
    _ ≤ (finiteHellingerSq p q *
          ∑ i, (Real.sqrt (p i) + Real.sqrt (q i)) ^ 2) / 4 := by
      apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 4)).mpr
      rw [← habs_sum]
      exact hcauchy
    _ ≤ (finiteHellingerSq p q * 4) / 4 := by
      apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 4)).mpr
      exact mul_le_mul_of_nonneg_left hcross
        (finiteHellingerSq_nonneg p q)
    _ = finiteHellingerSq p q := by
      ring

end Hellinger

end ClassicalInformation

end

end CommutingRepetition
