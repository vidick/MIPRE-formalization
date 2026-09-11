/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Prerounding/Sampler.lean
-/
/-
# Pre-rounding assembly: the rounded shared-permutation samplers (node 1.2.11)

The samplers `r_A(ω, x)`, `r_B(ω, y)` of the pre-rounded package draw the
history from the conditional laws `ℚ(· ∣ i, X_i = x)` resp. `ℚ(· ∣ i, Y_i = y)`
with a shared seed. To make the seed finite the conditional laws are rounded
to a common denominator `dens`: numerators `⌈dens (1−ρ) q(h)⌉` with the
leftover placed on a base history of the same live coordinate. The rounded
law dominates `(1−ρ) q` pointwise, so the relative entropy against it exceeds
the ideal one by at most `log(1/(1−ρ))`; the shared uniform permutation of
`H × Fin dens` (`rationalPermutationOutput`) realizes the rounded law exactly
and its disagreement probability is at most twice the total variation of the
two rounded laws. Nothing here is a manuscript statement.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Prelim.Information
import MIPRE.Background.Repetition.CommutingRepetition.Prelim.Entropy
import MIPRE.Background.Repetition.CommutingRepetition.Prerounding.HistoryKL

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped BigOperators
open Pinsker ClassicalSampling ClassicalInformation

set_option linter.unusedSectionVars false

namespace RoundedSampler

variable {H ι X Y : Type} [Fintype H] [DecidableEq H] [Fintype ι] [DecidableEq ι]
variable [Fintype X] [Fintype Y]

/-! ### Rounding a law to a common denominator -/

/-- Ceiling numerators `⌈dens (1−ρ) q(h)⌉`. -/
noncomputable def ceilNum (dens : ℕ) (ρ : ℝ) (q : H → ℝ) (h : H) : ℕ := ⌈(dens : ℝ) * (1 - ρ) * q h⌉₊

/-- The rounded numerators: the ceilings, with the leftover on a base point. -/
noncomputable def roundedNum (dens : ℕ) (ρ : ℝ) (q : H → ℝ) (h₀ : H) (h : H) : ℕ :=
  ceilNum dens ρ q h + if h = h₀ then dens - ∑ h', ceilNum dens ρ q h' else 0

theorem sum_ceilNum_le (dens : ℕ) {ρ : ℝ} (hρ1 : ρ ≤ 1) (q : H → ℝ) (hq0 : ∀ h, 0 ≤ q h)
    (hq1 : (∑ h, q h) ≤ 1) (hcard : (Fintype.card H : ℝ) ≤ dens * ρ) :
    (∑ h, ceilNum dens ρ q h) ≤ dens := by
  have hρ0 : 0 ≤ 1 - ρ := by linarith
  have hreal : ((∑ h, ceilNum dens ρ q h : ℕ) : ℝ) ≤ dens := by
    push_cast
    calc (∑ h, ((⌈(dens : ℝ) * (1 - ρ) * q h⌉₊ : ℕ) : ℝ))
        ≤ ∑ h, ((dens : ℝ) * (1 - ρ) * q h + 1) := Finset.sum_le_sum fun h _ =>
          (Nat.ceil_lt_add_one (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hρ0) (hq0 h))).le
      _ = (dens : ℝ) * (1 - ρ) * ∑ h, q h + Fintype.card H := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul, mul_one]
      _ ≤ (dens : ℝ) * (1 - ρ) * 1 + dens * ρ :=
          add_le_add (mul_le_mul_of_nonneg_left hq1 (mul_nonneg (Nat.cast_nonneg _) hρ0)) hcard
      _ = dens := by ring
  exact_mod_cast hreal

theorem sum_roundedNum (dens : ℕ) {ρ : ℝ} (hρ1 : ρ ≤ 1) (q : H → ℝ) (hq0 : ∀ h, 0 ≤ q h)
    (hq1 : (∑ h, q h) ≤ 1) (hcard : (Fintype.card H : ℝ) ≤ dens * ρ) (h₀ : H) :
    (∑ h, roundedNum dens ρ q h₀ h) = dens := by
  unfold roundedNum
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ h₀, if_pos (Finset.mem_univ _)]
  exact Nat.add_sub_cancel' (sum_ceilNum_le dens hρ1 q hq0 hq1 hcard)

theorem le_roundedNum (dens : ℕ) (ρ : ℝ) (q : H → ℝ) (h₀ h : H) :
    (dens : ℝ) * (1 - ρ) * q h ≤ roundedNum dens ρ q h₀ h := by
  unfold roundedNum
  rw [Nat.cast_add]
  have h1 : (dens : ℝ) * (1 - ρ) * q h ≤ (ceilNum dens ρ q h : ℝ) := Nat.le_ceil _
  have h2 : (0 : ℝ) ≤ ((if h = h₀ then dens - ∑ h', ceilNum dens ρ q h' else 0 : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  linarith

theorem roundedNum_eq_zero (dens : ℕ) (ρ : ℝ) (q : H → ℝ) (h₀ h : H) (hq : q h = 0)
    (hne : h ≠ h₀) : roundedNum dens ρ q h₀ h = 0 := by
  unfold roundedNum ceilNum
  rw [hq, mul_zero, Nat.ceil_zero, if_neg hne]

/-! ### The shared seed and the output -/

theorem rationalMarked_nonempty (dens : ℕ) (hdens : 0 < dens) (num : H → ℕ)
    (hsum : (∑ h, num h) = dens) : (rationalMarked dens num).Nonempty := by
  have hne : (∑ h, num h) ≠ 0 := by rw [hsum]; exact hdens.ne'
  obtain ⟨h, -, hh⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  refine ⟨(h, ⟨0, hdens⟩), ?_⟩
  simp [rationalMarked, Nat.pos_of_ne_zero hh]

/-- The shared seed: a live coordinate and a permutation of `H × Fin dens`. -/
abbrev Seed (H ι : Type) (dens : ℕ) : Type := ι × Equiv.Perm (H × Fin dens)

/-- The uniform seed law. -/
noncomputable def ν (dens : ℕ) (_ω : Seed H ι dens) : ℝ :=
  ((Fintype.card ι : ℝ) * (Fintype.card (Equiv.Perm (H × Fin dens)) : ℝ))⁻¹

theorem ν_nonneg (dens : ℕ) (ω : Seed H ι dens) : 0 ≤ ν dens ω :=
  inv_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

theorem ν_sum [Nonempty ι] (dens : ℕ) : (∑ ω : Seed H ι dens, ν dens ω) = 1 := by
  unfold ν
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul]
  have h1 : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h2 : (0 : ℝ) < Fintype.card (Equiv.Perm (H × Fin dens)) := by
    exact_mod_cast Fintype.card_pos
  push_cast
  exact mul_inv_cancel₀ (mul_pos h1 h2).ne'

/-- The output of the shared-permutation sampler at seed `ω` for the
numerators of live coordinate `ω.1`. -/
noncomputable def output (dens : ℕ) (hdens : 0 < dens) (num : ι → H → ℕ)
    (hsum : ∀ i, (∑ h, num i h) = dens) (ω : Seed H ι dens) : H :=
  rationalPermutationOutput dens (num ω.1)
    (rationalMarked_nonempty dens hdens (num ω.1) (hsum ω.1)) ω.2

/-- The uniform permutation probability as an indicator sum. -/
theorem sum_ite_eq_uniform (dens : ℕ) (P : Equiv.Perm (H × Fin dens) → Prop) [DecidablePred P] :
    (∑ π : Equiv.Perm (H × Fin dens), if P π then (1 : ℝ) else 0)
      = uniformPermutationProbability P * Fintype.card (Equiv.Perm (H × Fin dens)) := by
  unfold uniformPermutationProbability
  have hc : (0 : ℝ) < Fintype.card (Equiv.Perm (H × Fin dens)) := by
    exact_mod_cast Fintype.card_pos
  rw [div_mul_cancel₀ _ hc.ne', Finset.sum_boole]
  congr

/-- The disagreement probability as an indicator sum. -/
theorem sum_ite_ne_eq_uniform (dens : ℕ) (f g : Equiv.Perm (H × Fin dens) → H) :
    (∑ π : Equiv.Perm (H × Fin dens), if f π = g π then (0 : ℝ) else 1)
      = uniformPermutationProbability (fun π => f π ≠ g π) *
          Fintype.card (Equiv.Perm (H × Fin dens)) := by
  rw [← sum_ite_eq_uniform]
  refine Finset.sum_congr rfl fun π _ => ?_
  by_cases h : f π = g π <;> simp [h]

/-- **The output law**: `Pr[output = h] = (1/|ι|) ∑_i num(i, h)/dens`. -/
theorem sum_ν_output (dens : ℕ) (hdens : 0 < dens) (num : ι → H → ℕ)
    (hsum : ∀ i, (∑ h, num i h) = dens) (h : H) :
    (∑ ω : Seed H ι dens, ν dens ω * (if output dens hdens num hsum ω = h then (1 : ℝ) else 0))
      = (Fintype.card ι : ℝ)⁻¹ * ∑ i : ι, (num i h : ℝ) / dens := by
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ν]
  rw [← Finset.mul_sum]
  have hprob := rationalPermutationOutput_probability dens (num i) (hsum i)
    (rationalMarked_nonempty dens hdens (num i) (hsum i)) h
  have hcount : (∑ π : Equiv.Perm (H × Fin dens),
      if output dens hdens num hsum (i, π) = h then (1 : ℝ) else 0)
      = uniformPermutationProbability (fun π : Equiv.Perm (H × Fin dens) =>
          rationalPermutationOutput dens (num i)
            (rationalMarked_nonempty dens hdens (num i) (hsum i)) π = h) *
        Fintype.card (Equiv.Perm (H × Fin dens)) :=
    sum_ite_eq_uniform dens _
  rw [hcount, hprob]
  have hc : (0 : ℝ) < Fintype.card (Equiv.Perm (H × Fin dens)) := by
    exact_mod_cast Fintype.card_pos
  have hι : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨i⟩
  field_simp

/-- Numerators supported on the live coordinate collapse the coordinate sum. -/
theorem sum_num_eq (dens : ℕ) (num : ι → H → ℕ) (lc : H → ι)
    (hsupp : ∀ i h, lc h ≠ i → num i h = 0) (h : H) :
    (∑ i : ι, (num i h : ℝ) / dens) = (num (lc h) h : ℝ) / dens := by
  rw [Finset.sum_eq_single (lc h)]
  · intro i _ hne
    rw [hsupp i h (Ne.symm hne)]
    simp
  · intro h'
    exact absurd (Finset.mem_univ _) h'

/-! ### Relative entropy against a dominating law -/

/-- If `J' ≥ (1−ρ) J₀` pointwise, the relative entropy against `J'` is at
most the log-sum against `J₀` plus `log(1/(1−ρ))`. -/
theorem finiteRelativeEntropy_le_of_dominates {κ : Type} [Fintype κ] (Q J₀ J' : κ → ℝ)
    (hQ0 : ∀ u, 0 ≤ Q u) (hQ1 : (∑ u, Q u) = 1) (hJ₀ : ∀ u, 0 ≤ J₀ u)
    (habs : ∀ u, J₀ u = 0 → Q u = 0) (hJ'0 : ∀ u, 0 ≤ J' u) (hJ'1 : (∑ u, J' u) ≤ 1)
    {ρ : ℝ} (hρ : ρ < 1) (hdom : ∀ u, (1 - ρ) * J₀ u ≤ J' u) :
    finiteRelativeEntropy Q J'
      ≤ (∑ u, Q u * Real.log (Q u / J₀ u)) + Real.log (1 / (1 - ρ)) := by
  have hρ0 : 0 < 1 - ρ := by linarith
  have habs' : ∀ u, J' u = 0 → Q u = 0 := by
    intro u hu
    apply habs
    have h1 : (1 - ρ) * J₀ u ≤ (1 - ρ) * 0 := by rw [mul_zero, ← hu]; exact hdom u
    exact le_antisymm (le_of_mul_le_mul_left h1 hρ0) (hJ₀ u)
  have hkl := HistoryKL.finiteRelativeEntropy_le_log_sum Q J' hQ0 hJ'0 habs' hQ1 hJ'1
  refine hkl.trans ?_
  have hpt : ∀ u, Q u * Real.log (Q u / J' u)
      ≤ Q u * Real.log (Q u / J₀ u) + Q u * Real.log (1 / (1 - ρ)) := by
    intro u
    rcases (hQ0 u).lt_or_eq with hQ | hQ
    · have hJ₀pos : 0 < J₀ u :=
        lt_of_le_of_ne (hJ₀ u) fun h => hQ.ne' (habs u h.symm)
      have hJ'pos : 0 < J' u := lt_of_lt_of_le (mul_pos hρ0 hJ₀pos) (hdom u)
      rw [← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ hQ.le
      rw [← Real.log_mul (div_pos hQ hJ₀pos).ne' (one_div_pos.mpr hρ0).ne']
      refine Real.log_le_log (div_pos hQ hJ'pos) ?_
      rw [div_mul_div_comm, mul_one, div_le_div_iff₀ hJ'pos (mul_pos hJ₀pos hρ0)]
      refine mul_le_mul_of_nonneg_left ?_ hQ.le
      rw [mul_comm]
      exact hdom u
    · rw [← hQ]
      simp
  calc (∑ u, Q u * Real.log (Q u / J' u))
      ≤ ∑ u, (Q u * Real.log (Q u / J₀ u) + Q u * Real.log (1 / (1 - ρ))) :=
        Finset.sum_le_sum fun u _ => hpt u
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul, hQ1, one_mul]

/-! ### Total variation -/

theorem finiteTotalVariation_triangle {κ : Type} [Fintype κ] (p q r : κ → ℝ) :
    finiteTotalVariation q r ≤ finiteTotalVariation p q + finiteTotalVariation p r := by
  unfold finiteTotalVariation
  rw [← add_div, ← Finset.sum_add_distrib]
  gcongr with u
  calc |q u - r u| = |(p u - r u) - (p u - q u)| := by congr 1; ring
    _ ≤ |p u - r u| + |p u - q u| := abs_sub _ _
    _ = |p u - q u| + |p u - r u| := add_comm _ _

/-- Moving the first of three finite sums to the back. -/
theorem sum_comm3' {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] (F : α → β → γ → ℝ) :
    (∑ a, ∑ b, ∑ c, F a b c) = ∑ b, ∑ c, ∑ a, F a b c := by
  calc (∑ a, ∑ b, ∑ c, F a b c) = ∑ b, ∑ a, ∑ c, F a b c := Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ a, F a b c := Finset.sum_congr rfl fun b _ => Finset.sum_comm

/-- **The mismatch bound**: the shared seed makes the two outputs disagree
with probability at most twice the total variation of the two output tuple
laws. -/
theorem sum_ν_disagree_le (dens : ℕ) (hdens : 0 < dens)
    (numA : ι → X → H → ℕ) (numB : ι → Y → H → ℕ)
    (hA : ∀ i x, (∑ h, numA i x h) = dens) (hB : ∀ i y, (∑ h, numB i y h) = dens)
    (lc : H → ι) (hsA : ∀ i x h, lc h ≠ i → numA i x h = 0)
    (hsB : ∀ i y h, lc h ≠ i → numB i y h = 0)
    (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y) :
    (∑ ω : Seed H ι dens, ∑ x : X, ∑ y : Y, ν dens ω * μ x y *
        (if output dens hdens (fun i => numA i x) (fun i => hA i x) ω
            = output dens hdens (fun i => numB i y) (fun i => hB i y) ω then (0 : ℝ) else 1))
      ≤ 2 * finiteTotalVariation
          (fun u : H × X × Y => (Fintype.card ι : ℝ)⁻¹ * μ u.2.1 u.2.2 *
            ((numA (lc u.1) u.2.1 u.1 : ℝ) / dens))
          (fun u : H × X × Y => (Fintype.card ι : ℝ)⁻¹ * μ u.2.1 u.2.2 *
            ((numB (lc u.1) u.2.2 u.1 : ℝ) / dens)) := by
  have hc : (0 : ℝ) < Fintype.card (Equiv.Perm (H × Fin dens)) := by
    exact_mod_cast Fintype.card_pos
  set c : ℝ := (Fintype.card ι : ℝ)⁻¹ with hc_def
  -- Step A: the per-(i, x, y) disagreement bound.
  have hstep : ∀ (i : ι) (x : X) (y : Y),
      (∑ π : Equiv.Perm (H × Fin dens), ν dens (i, π) * μ x y *
        (if output dens hdens (fun i => numA i x) (fun i => hA i x) (i, π)
            = output dens hdens (fun i => numB i y) (fun i => hB i y) (i, π) then (0 : ℝ) else 1))
      ≤ c * μ x y * ∑ h : H, |(numA i x h : ℝ) / dens - (numB i y h : ℝ) / dens| := by
    intro i x y
    simp only [ν]
    rw [← Finset.mul_sum]
    have hcount := sum_ite_ne_eq_uniform dens
      (fun π : Equiv.Perm (H × Fin dens) =>
        rationalPermutationOutput dens (numA i x)
          (rationalMarked_nonempty dens hdens (numA i x) (hA i x)) π)
      (fun π : Equiv.Perm (H × Fin dens) =>
        rationalPermutationOutput dens (numB i y)
          (rationalMarked_nonempty dens hdens (numB i y) (hB i y)) π)
    have hdis := rationalPermutationOutput_disagreement_le_two_mul_finiteTotalVariation dens hdens
      (numA i x) (numB i y) (hA i x) (hB i y)
      (rationalMarked_nonempty dens hdens (numA i x) (hA i x))
      (rationalMarked_nonempty dens hdens (numB i y) (hB i y))
    have hsum_eq : (∑ π : Equiv.Perm (H × Fin dens),
        if output dens hdens (fun i => numA i x) (fun i => hA i x) (i, π)
            = output dens hdens (fun i => numB i y) (fun i => hB i y) (i, π) then (0 : ℝ) else 1)
        = uniformPermutationProbability (fun π : Equiv.Perm (H × Fin dens) =>
            rationalPermutationOutput dens (numA i x)
              (rationalMarked_nonempty dens hdens (numA i x) (hA i x)) π ≠
            rationalPermutationOutput dens (numB i y)
              (rationalMarked_nonempty dens hdens (numB i y) (hB i y)) π) *
          Fintype.card (Equiv.Perm (H × Fin dens)) := hcount
    rw [hsum_eq]
    have htv : 2 * finiteTotalVariation (fun h => (numA i x h : ℝ) / dens)
        (fun h => (numB i y h : ℝ) / dens)
        = ∑ h : H, |(numA i x h : ℝ) / dens - (numB i y h : ℝ) / dens| := by
      unfold finiteTotalVariation
      ring
    rw [htv] at hdis
    have hμxy := hμ x y
    calc ((Fintype.card ι : ℝ) * (Fintype.card (Equiv.Perm (H × Fin dens)) : ℝ))⁻¹ * μ x y *
          (uniformPermutationProbability _ * Fintype.card (Equiv.Perm (H × Fin dens)))
        ≤ ((Fintype.card ι : ℝ) * (Fintype.card (Equiv.Perm (H × Fin dens)) : ℝ))⁻¹ * μ x y *
          ((∑ h : H, |(numA i x h : ℝ) / dens - (numB i y h : ℝ) / dens|) *
            Fintype.card (Equiv.Perm (H × Fin dens))) := by
          gcongr
      _ = c * μ x y * ∑ h : H, |(numA i x h : ℝ) / dens - (numB i y h : ℝ) / dens| := by
          rw [hc_def]
          field_simp
  -- Step B: assemble.
  have hL : (∑ ω : Seed H ι dens, ∑ x : X, ∑ y : Y, ν dens ω * μ x y *
        (if output dens hdens (fun i => numA i x) (fun i => hA i x) ω
            = output dens hdens (fun i => numB i y) (fun i => hB i y) ω then (0 : ℝ) else 1))
      ≤ ∑ i : ι, ∑ x : X, ∑ y : Y,
          c * μ x y * ∑ h : H, |(numA i x h : ℝ) / dens - (numB i y h : ℝ) / dens| := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [sum_comm3']
    exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hstep i x y
  refine hL.trans (le_of_eq ?_)
  -- Both sides in the normal form `∑ x ∑ y ∑ h`.
  have hcollapse : ∀ (x : X) (y : Y) (h : H),
      (∑ i : ι, c * μ x y * |(numA i x h : ℝ) / dens - (numB i y h : ℝ) / dens|)
        = c * μ x y * |(numA (lc h) x h : ℝ) / dens - (numB (lc h) y h : ℝ) / dens| := by
    intro x y h
    rw [Finset.sum_eq_single (lc h)]
    · intro i _ hne
      rw [hsA i x h (Ne.symm hne), hsB i y h (Ne.symm hne)]
      simp
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  have hR : 2 * finiteTotalVariation
        (fun u : H × X × Y => c * μ u.2.1 u.2.2 * ((numA (lc u.1) u.2.1 u.1 : ℝ) / dens))
        (fun u : H × X × Y => c * μ u.2.1 u.2.2 * ((numB (lc u.1) u.2.2 u.1 : ℝ) / dens))
      = ∑ x : X, ∑ y : Y, ∑ h : H,
          c * μ x y * |(numA (lc h) x h : ℝ) / dens - (numB (lc h) y h : ℝ) / dens| := by
    unfold finiteTotalVariation
    rw [mul_div_cancel₀ _ two_ne_zero, Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type]
    rw [sum_comm3']
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_congr rfl fun h _ => ?_
    rw [← mul_sub, abs_mul, abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (hμ x y))]
  rw [hR]
  simp only [Finset.mul_sum]
  rw [sum_comm3']
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun h _ => hcollapse x y h

/-! ### Sum reorderings and the normalization of the output tuple laws -/

theorem sum_triple {H X Y : Type} [Fintype H] [Fintype X] [Fintype Y] (F : H × X × Y → ℝ) :
    (∑ u : H × X × Y, F u) = ∑ h : H, ∑ x : X, ∑ y : Y, F (h, x, y) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Fintype.sum_prod_type]

theorem sum_comm_hxyω {H X Y S : Type} [Fintype H] [Fintype X] [Fintype Y] [Fintype S]
    (F : H → X → Y → S → ℝ) :
    (∑ h, ∑ x, ∑ y, ∑ ω, F h x y ω) = ∑ ω, ∑ x, ∑ y, ∑ h, F h x y ω := by
  calc (∑ h, ∑ x, ∑ y, ∑ ω, F h x y ω)
      = ∑ h, ∑ x, ∑ ω, ∑ y, F h x y ω :=
        Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ h, ∑ ω, ∑ x, ∑ y, F h x y ω := Finset.sum_congr rfl fun h _ => Finset.sum_comm
    _ = ∑ ω, ∑ h, ∑ x, ∑ y, F h x y ω := Finset.sum_comm
    _ = ∑ ω, ∑ x, ∑ h, ∑ y, F h x y ω := Finset.sum_congr rfl fun ω _ => Finset.sum_comm
    _ = ∑ ω, ∑ x, ∑ y, ∑ h, F h x y ω :=
        Finset.sum_congr rfl fun ω _ => Finset.sum_congr rfl fun x _ => Finset.sum_comm

/-- The Alice-side output tuple law `(∑_ω ν(ω) [r_A(ω,x) = h]) μ(x,y)` is a
probability law. -/
theorem sum_law_A [Nonempty ι] (dens : ℕ) (hdens : 0 < dens) (num : X → ι → H → ℕ)
    (hsum : ∀ x i, (∑ h, num x i h) = dens) (μ : X → Y → ℝ)
    (hμsum : (∑ x : X, ∑ y : Y, μ x y) = 1) :
    (∑ u : H × X × Y, (∑ ω : Seed H ι dens, ν dens ω *
        (if output dens hdens (num u.2.1) (hsum u.2.1) ω = u.1 then (1 : ℝ) else 0)) *
      μ u.2.1 u.2.2) = 1 := by
  have hexp : ∀ (h : H) (x : X) (y : Y),
      (∑ ω : Seed H ι dens, ν dens ω *
        (if output dens hdens (num x) (hsum x) ω = h then (1 : ℝ) else 0)) * μ x y
      = ∑ ω : Seed H ι dens,
          if output dens hdens (num x) (hsum x) ω = h then ν dens ω * μ x y else 0 := by
    intro h x y
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun ω _ => ?_
    split_ifs <;> ring
  rw [sum_triple]
  simp only [hexp]
  rw [sum_comm_hxyω]
  calc (∑ ω : Seed H ι dens, ∑ x : X, ∑ y : Y, ∑ h : H,
        if output dens hdens (num x) (hsum x) ω = h then ν dens ω * μ x y else 0)
      = ∑ ω : Seed H ι dens, ∑ x : X, ∑ y : Y, ν dens ω * μ x y := by
        refine Finset.sum_congr rfl fun ω _ => Finset.sum_congr rfl fun x _ =>
          Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_ite_eq]
        simp
    _ = ∑ ω : Seed H ι dens, ν dens ω := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [show (∑ x : X, ∑ y : Y, ν dens ω * μ x y) = ν dens ω * ∑ x : X, ∑ y : Y, μ x y from by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun x _ => (Finset.mul_sum _ _ _).symm]
        rw [hμsum, mul_one]
    _ = 1 := ν_sum dens

/-- The Bob-side output tuple law is a probability law. -/
theorem sum_law_B [Nonempty ι] (dens : ℕ) (hdens : 0 < dens) (num : Y → ι → H → ℕ)
    (hsum : ∀ y i, (∑ h, num y i h) = dens) (μ : X → Y → ℝ)
    (hμsum : (∑ x : X, ∑ y : Y, μ x y) = 1) :
    (∑ u : H × X × Y, (∑ ω : Seed H ι dens, ν dens ω *
        (if output dens hdens (num u.2.2) (hsum u.2.2) ω = u.1 then (1 : ℝ) else 0)) *
      μ u.2.1 u.2.2) = 1 := by
  have hexp : ∀ (h : H) (x : X) (y : Y),
      (∑ ω : Seed H ι dens, ν dens ω *
        (if output dens hdens (num y) (hsum y) ω = h then (1 : ℝ) else 0)) * μ x y
      = ∑ ω : Seed H ι dens,
          if output dens hdens (num y) (hsum y) ω = h then ν dens ω * μ x y else 0 := by
    intro h x y
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun ω _ => ?_
    split_ifs <;> ring
  rw [sum_triple]
  simp only [hexp]
  rw [sum_comm_hxyω]
  calc (∑ ω : Seed H ι dens, ∑ x : X, ∑ y : Y, ∑ h : H,
        if output dens hdens (num y) (hsum y) ω = h then ν dens ω * μ x y else 0)
      = ∑ ω : Seed H ι dens, ∑ x : X, ∑ y : Y, ν dens ω * μ x y := by
        refine Finset.sum_congr rfl fun ω _ => Finset.sum_congr rfl fun x _ =>
          Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_ite_eq]
        simp
    _ = ∑ ω : Seed H ι dens, ν dens ω := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [show (∑ x : X, ∑ y : Y, ν dens ω * μ x y) = ν dens ω * ∑ x : X, ∑ y : Y, μ x y from by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun x _ => (Finset.mul_sum _ _ _).symm]
        rw [hμsum, mul_one]
    _ = 1 := ν_sum dens

end RoundedSampler

end CommutingRepetition
