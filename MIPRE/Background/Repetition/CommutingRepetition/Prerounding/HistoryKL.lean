/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Prerounding/HistoryKL.lean
-/
/-
# Pre-rounding: finite relative-entropy inequalities for the history bound

Proof-side lemmas for `history_relative_entropy` (node 1.2.10) that involve
only finite sums of reals: the log-sum upper bound on the finite relative
entropy against a subnormalized reference, the pointwise-density bound, the
Gibbs lower bound, the pushforward (grouping) identity, the class-function
forms of the two bounds, and the tensorization inequality for the coordinate
marginals of a law dominated by a product (05_prerounding.tex, eqs
conditioning-divergence, first-history-chain-term, bob-block-chain-rule).
Nothing here is a manuscript statement.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Prelim.Entropy
import MIPRE.Background.Repetition.CommutingRepetition.Prelim.Information

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace HistoryKL

open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **Log-sum upper bound.** Against a nonnegative, subnormalized,
absolutely continuous reference, the finite relative entropy is at most the
log-sum `∑ p log(p/q)` (equality when the reference is normalized). -/
theorem finiteRelativeEntropy_le_log_sum (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (habs : ∀ i, q i = 0 → p i = 0)
    (hp1 : (∑ i, p i) = 1) (hq1 : (∑ i, q i) ≤ 1) :
    Pinsker.finiteRelativeEntropy p q ≤ ∑ i, p i * Real.log (p i / q i) := by
  have hterm : ∀ i, q i * InformationTheory.klFun (p i / q i)
      = p i * Real.log (p i / q i) + q i - p i := by
    intro i
    rcases (hq i).lt_or_eq with hqi | hqi
    · unfold InformationTheory.klFun
      field_simp
    · rw [← hqi, habs i hqi.symm]
      simp
  unfold Pinsker.finiteRelativeEntropy
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, hp1]
  linarith

/-- **Pointwise-density bound**: if `q ≤ K·P` pointwise then
`∑ q log(q/P) ≤ log K`. -/
theorem sum_mul_log_le_log_of_le (q P : ι → ℝ) {K : ℝ} (hK : 0 < K)
    (hq : ∀ i, 0 ≤ q i) (hqK : ∀ i, q i ≤ K * P i) (hq1 : (∑ i, q i) = 1) :
    (∑ i, q i * Real.log (q i / P i)) ≤ Real.log K := by
  calc (∑ i, q i * Real.log (q i / P i)) ≤ ∑ i, q i * Real.log K := by
        refine Finset.sum_le_sum fun i _ => ?_
        rcases (hq i).lt_or_eq with hqi | hqi
        · refine mul_le_mul_of_nonneg_left ?_ (hq i)
          have hP : 0 < P i := by
            by_contra h
            have h' : P i ≤ 0 := not_lt.mp h
            have := hqK i
            nlinarith [mul_nonpos_of_nonneg_of_nonpos hK.le h']
          refine Real.log_le_log (div_pos hqi hP) ?_
          rw [div_le_iff₀ hP]
          exact hqK i
        · rw [← hqi]; simp
    _ = Real.log K := by rw [← Finset.sum_mul, hq1, one_mul]

/-- **Gibbs lower bound** against an unnormalized nonnegative reference of
total mass `T`: `∑ q log(q/P) ≥ −log T`. -/
theorem neg_log_sum_le_sum_mul_log (q P : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hP : ∀ i, 0 ≤ P i)
    (habs : ∀ i, P i = 0 → q i = 0) (hq1 : (∑ i, q i) = 1)
    (hT : 0 < ∑ i, P i) :
    - Real.log (∑ i, P i) ≤ ∑ i, q i * Real.log (q i / P i) := by
  set T := ∑ i, P i with hTdef
  have hterm : ∀ i, q i - P i / T - q i * Real.log T ≤ q i * Real.log (q i / P i) := by
    intro i
    rcases (hq i).lt_or_eq with hqi | hqi
    · have hPi : 0 < P i := by
        rcases (hP i).lt_or_eq with h | h
        · exact h
        · exact absurd (habs i h.symm) hqi.ne'
      have h1 : 1 - P i / (q i * T) ≤ Real.log (q i * T / P i) := by
        have := Real.one_sub_inv_le_log_of_pos (div_pos (mul_pos hqi hT) hPi)
        rwa [inv_div] at this
      have h2 : Real.log (q i / P i) = Real.log (q i * T / P i) - Real.log T := by
        rw [Real.log_div (mul_pos hqi hT).ne' hPi.ne', Real.log_mul hqi.ne' hT.ne',
          Real.log_div hqi.ne' hPi.ne']
        ring
      have h3 : q i * (1 - P i / (q i * T)) = q i - P i / T := by
        field_simp
      rw [h2]
      nlinarith [mul_le_mul_of_nonneg_left h1 (hq i)]
    · rw [← hqi]
      simp only [zero_sub, zero_mul, sub_zero, zero_div, neg_nonpos]
      exact div_nonneg (hP i) hT.le
  calc - Real.log T = ∑ i, (q i - P i / T - q i * Real.log T) := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hq1,
          ← Finset.sum_div, ← hTdef, div_self hT.ne']
        ring
    _ ≤ _ := Finset.sum_le_sum fun i _ => hterm i

section Grouping

variable [DecidableEq κ]

omit [Fintype κ] in
/-- The grouped mass as an indicator sum. -/
theorem groupedMass_eq_sum_ite [DecidableEq ι] (f : ι → κ) (p : ι → ℝ) (j : κ) :
    ClassicalInformation.groupedMass f p j = ∑ i, if f i = j then p i else 0 := by
  unfold ClassicalInformation.groupedMass
  rw [Finset.sum_filter]

/-- **Pushforward identity**: an expectation of a function of the grouped
variable is the expectation of its composite. -/
theorem sum_groupedMass_mul [DecidableEq ι] (f : ι → κ) (p : ι → ℝ) (φ : κ → ℝ) :
    (∑ j, ClassicalInformation.groupedMass f p j * φ j) = ∑ i, p i * φ (f i) := by
  unfold ClassicalInformation.groupedMass
  rw [← Finset.sum_fiberwise Finset.univ f (fun i => p i * φ (f i))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [(Finset.mem_filter.mp hi).2]

theorem sum_groupedMass [DecidableEq ι] (f : ι → κ) (p : ι → ℝ) :
    (∑ j, ClassicalInformation.groupedMass f p j) = ∑ i, p i := by
  have := sum_groupedMass_mul f p (fun _ => (1 : ℝ))
  simpa using this

omit [Fintype κ] in
theorem groupedMass_nonneg [DecidableEq ι] (f : ι → κ) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (j : κ) : 0 ≤ ClassicalInformation.groupedMass f p j :=
  Finset.sum_nonneg fun i _ => hp i

theorem groupedMass_le_mul [DecidableEq ι] (f : ι → κ) (p P : ι → ℝ) (K : ℝ)
    (h : ∀ i, p i ≤ K * P i) (j : κ) :
    ClassicalInformation.groupedMass f p j ≤ K * ClassicalInformation.groupedMass f P j := by
  unfold ClassicalInformation.groupedMass
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => h i

/-- The summand of a class-function expectation depends on the class only. -/
theorem sum_mul_class_eq [DecidableEq ι] (c : ι → κ) (q : ι → ℝ) (ψ : κ → ℝ) :
    (∑ i, q i * ψ (c i))
      = ∑ u, ClassicalInformation.groupedMass c q u * ψ u :=
  (sum_groupedMass_mul c q ψ).symm

/-- **Pointwise-density bound, class form**: the expected log-ratio of the
class masses of `q` and `P` is at most `log K` when `q ≤ K·P`. -/
theorem sum_mul_log_class_le [DecidableEq ι] (c : ι → κ) (q P : ι → ℝ) {K : ℝ}
    (hK : 0 < K) (hq : ∀ i, 0 ≤ q i) (hqK : ∀ i, q i ≤ K * P i)
    (hq1 : (∑ i, q i) = 1) :
    (∑ i, q i * Real.log ((∑ i', if c i' = c i then q i' else 0) /
        (∑ i', if c i' = c i then P i' else 0)))
      ≤ Real.log K := by
  have hre : (∑ i, q i * Real.log ((∑ i', if c i' = c i then q i' else 0) /
      (∑ i', if c i' = c i then P i' else 0)))
      = ∑ u, ClassicalInformation.groupedMass c q u *
          Real.log (ClassicalInformation.groupedMass c q u /
            ClassicalInformation.groupedMass c P u) := by
    simp only [← groupedMass_eq_sum_ite]
    exact sum_mul_class_eq c q (fun u => Real.log (ClassicalInformation.groupedMass c q u /
      ClassicalInformation.groupedMass c P u))
  rw [hre]
  refine sum_mul_log_le_log_of_le _ _ hK (groupedMass_nonneg c q hq)
    (groupedMass_le_mul c q P K hqK) ?_
  rw [sum_groupedMass, hq1]

/-- **Gibbs lower bound, class form**. -/
theorem neg_log_le_sum_mul_log_class [DecidableEq ι] (c : ι → κ) (q P : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hP : ∀ i, 0 ≤ P i)
    (habs : ∀ i, P i = 0 → q i = 0) (hq1 : (∑ i, q i) = 1)
    (hT : 0 < ∑ i, P i) :
    - Real.log (∑ i, P i)
      ≤ ∑ i, q i * Real.log ((∑ i', if c i' = c i then q i' else 0) /
          (∑ i', if c i' = c i then P i' else 0)) := by
  have hre : (∑ i, q i * Real.log ((∑ i', if c i' = c i then q i' else 0) /
      (∑ i', if c i' = c i then P i' else 0)))
      = ∑ u, ClassicalInformation.groupedMass c q u *
          Real.log (ClassicalInformation.groupedMass c q u /
            ClassicalInformation.groupedMass c P u) := by
    simp only [← groupedMass_eq_sum_ite]
    exact sum_mul_class_eq c q (fun u => Real.log (ClassicalInformation.groupedMass c q u /
      ClassicalInformation.groupedMass c P u))
  rw [hre, ← sum_groupedMass c P]
  refine neg_log_sum_le_sum_mul_log _ _ (groupedMass_nonneg c q hq)
    (groupedMass_nonneg c P hP) ?_ (by rw [sum_groupedMass, hq1]) (by rwa [sum_groupedMass])
  intro u hu
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hP i).mp hu
  exact Finset.sum_eq_zero fun i hi => habs i (hz i hi)

end Grouping

section Tensorization

variable {α : Type*} [Fintype α] [DecidableEq α] [DecidableEq ι]

/-- The `j`-th coordinate marginal of a law on words. -/
noncomputable def coordMarginal (q : (ι → α) → ℝ) (j : ι) (x : α) : ℝ :=
  ∑ w, if w j = x then q w else 0

theorem coordMarginal_nonneg (q : (ι → α) → ℝ) (hq : ∀ w, 0 ≤ q w) (j : ι) (x : α) :
    0 ≤ coordMarginal q j x :=
  Finset.sum_nonneg fun w _ => by split_ifs <;> [exact hq w; exact le_rfl]

theorem le_coordMarginal (q : (ι → α) → ℝ) (hq : ∀ w, 0 ≤ q w) (j : ι) (w : ι → α) :
    q w ≤ coordMarginal q j (w j) := by
  unfold coordMarginal
  have := Finset.single_le_sum (f := fun w' => if w' j = w j then q w' else 0)
    (fun w' _ => by split_ifs <;> [exact hq w'; exact le_rfl]) (Finset.mem_univ w)
  simpa using this

theorem sum_coordMarginal (q : (ι → α) → ℝ) (j : ι) :
    (∑ x, coordMarginal q j x) = ∑ w, q w := by
  unfold coordMarginal
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun w _ => by simp

/-- The product of the coordinate marginals is a probability law. -/
theorem sum_prod_coordMarginal (q : (ι → α) → ℝ) (hq1 : (∑ w, q w) = 1) :
    (∑ w : ι → α, ∏ j, coordMarginal q j (w j)) = 1 := by
  have h := Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset α))
    (fun j x => coordMarginal q j x)
  rw [Fintype.piFinset_univ] at h
  rw [← h]
  exact Finset.prod_eq_one fun j _ => by rw [sum_coordMarginal, hq1]

/-- **Tensorization**: for a law on words dominated by `K` times a product
reference, the coordinate marginals' log-sums against the factor total at
most `log K` — `∑_j D(q_j ‖ ν) ≤ D(q ‖ ν^{⊗}) ≤ log K`
(eq first-history-chain-term). -/
theorem sum_coordMarginal_log_le (q : (ι → α) → ℝ) (ν : α → ℝ) {K : ℝ} (hK : 0 < K)
    (hq : ∀ w, 0 ≤ q w) (hq1 : (∑ w, q w) = 1) (hν : ∀ x, 0 ≤ ν x)
    (hqK : ∀ w, q w ≤ K * ∏ j, ν (w j)) :
    (∑ j : ι, ∑ x : α, coordMarginal q j x * Real.log (coordMarginal q j x / ν x))
      ≤ Real.log K := by
  -- Expectation form of each marginal log-sum.
  have hgroup : ∀ j : ι,
      (∑ x : α, coordMarginal q j x * Real.log (coordMarginal q j x / ν x))
        = ∑ w, q w * Real.log (coordMarginal q j (w j) / ν (w j)) := by
    intro j
    have := sum_groupedMass_mul (fun w : ι → α => w j) q
      (fun x => Real.log (coordMarginal q j x / ν x))
    rw [← this]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [groupedMass_eq_sum_ite]
    rfl
  -- Pointwise split for words of positive mass.
  have hsplit : ∀ w, q w * ∑ j, Real.log (coordMarginal q j (w j) / ν (w j))
      = q w * Real.log (q w / ∏ j, ν (w j))
        - q w * Real.log (q w / ∏ j, coordMarginal q j (w j)) := by
    intro w
    rcases (hq w).lt_or_eq with hqw | hqw
    · have hprodν : 0 < ∏ j, ν (w j) := by
        have h1 : 0 < K * ∏ j, ν (w j) := lt_of_lt_of_le hqw (hqK w)
        exact pos_of_mul_pos_right h1 hK.le
      have hνj : ∀ j, ν (w j) ≠ 0 := fun j =>
        (Finset.prod_ne_zero_iff.mp hprodν.ne') j (Finset.mem_univ j)
      have hmj : ∀ j, coordMarginal q j (w j) ≠ 0 := fun j =>
        (lt_of_lt_of_le hqw (le_coordMarginal q hq j w)).ne'
      have hprodm : (∏ j, coordMarginal q j (w j)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun j _ => hmj j
      rw [← mul_sub]
      congr 1
      rw [Real.log_div hqw.ne' hprodν.ne', Real.log_div hqw.ne' hprodm,
        Real.log_prod (fun j _ => hνj j), Real.log_prod (fun j _ => hmj j),
        Finset.sum_congr rfl fun j _ => Real.log_div (hmj j) (hνj j),
        Finset.sum_sub_distrib]
      ring
    · rw [← hqw]; simp
  calc (∑ j : ι, ∑ x : α, coordMarginal q j x * Real.log (coordMarginal q j x / ν x))
      = ∑ j : ι, ∑ w, q w * Real.log (coordMarginal q j (w j) / ν (w j)) :=
        Finset.sum_congr rfl fun j _ => hgroup j
    _ = ∑ w, q w * ∑ j, Real.log (coordMarginal q j (w j) / ν (w j)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun w _ => (Finset.mul_sum _ _ _).symm
    _ = (∑ w, q w * Real.log (q w / ∏ j, ν (w j)))
          - ∑ w, q w * Real.log (q w / ∏ j, coordMarginal q j (w j)) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun w _ => hsplit w
    _ ≤ Real.log K - 0 := by
        refine sub_le_sub (sum_mul_log_le_log_of_le q _ hK hq hqK hq1) ?_
        have hG := neg_log_sum_le_sum_mul_log q (fun w => ∏ j, coordMarginal q j (w j)) hq
          (fun w => Finset.prod_nonneg fun j _ => coordMarginal_nonneg q hq j (w j))
          (fun w hw => by
            obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.mp hw
            exact le_antisymm (hj ▸ le_coordMarginal q hq j w) (hq w))
          hq1 (by rw [sum_prod_coordMarginal q hq1]; exact one_pos)
        rw [sum_prod_coordMarginal q hq1, Real.log_one, neg_zero] at hG
        exact hG
    _ = Real.log K := sub_zero _

end Tensorization

end HistoryKL

end CommutingRepetition
