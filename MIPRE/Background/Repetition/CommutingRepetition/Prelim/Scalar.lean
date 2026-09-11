/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Prelim/Scalar.lean
-/
/-
# Scalar and finite-sum helper lemmas (WP-A1)

Auxiliary facts with no single manuscript anchor, consumed across the
development: absolute values of nested sums, and the telescoping product
perturbation used by the payoff-approximation arguments
(07_main_theorem.tex, eq payoff-rational-approximation).
-/
import Mathlib

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped BigOperators

/-- Triangle inequality for a four-fold nested finite sum. -/
theorem abs_sum4_le {X Y A B : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (f : X → Y → A → B → ℝ) :
    |∑ x : X, ∑ y : Y, ∑ a : A, ∑ b : B, f x y a b|
      ≤ ∑ x : X, ∑ y : Y, ∑ a : A, ∑ b : B, |f x y a b| :=
  (Finset.abs_sum_le_sum_abs _ _).trans <| Finset.sum_le_sum fun _ _ =>
    (Finset.abs_sum_le_sum_abs _ _).trans <| Finset.sum_le_sum fun _ _ =>
      (Finset.abs_sum_le_sum_abs _ _).trans <| Finset.sum_le_sum fun _ _ =>
        Finset.abs_sum_le_sum_abs _ _

section SumHelpers

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

theorem sum2_sub (f g : A → B → ℝ) :
    (∑ a : A, ∑ b : B, (f a b - g a b))
      = (∑ a : A, ∑ b : B, f a b) - ∑ a : A, ∑ b : B, g a b := by
  simp [Finset.sum_sub_distrib]

theorem sum2_add (f g : A → B → ℝ) :
    (∑ a : A, ∑ b : B, (f a b + g a b))
      = (∑ a : A, ∑ b : B, f a b) + ∑ a : A, ∑ b : B, g a b := by
  simp [Finset.sum_add_distrib]

theorem sum2_mul_left (c : ℝ) (f : A → B → ℝ) :
    (∑ a : A, ∑ b : B, c * f a b) = c * ∑ a : A, ∑ b : B, f a b := by
  simp [Finset.mul_sum]

theorem sum3_sub (f g : A → B → C → ℝ) :
    (∑ a : A, ∑ b : B, ∑ c : C, (f a b c - g a b c))
      = (∑ a : A, ∑ b : B, ∑ c : C, f a b c) -
        ∑ a : A, ∑ b : B, ∑ c : C, g a b c := by
  simp [Finset.sum_sub_distrib]

theorem sum3_div (f : A → B → C → ℝ) (d : ℝ) :
    (∑ a : A, ∑ b : B, ∑ c : C, f a b c) / d
      = ∑ a : A, ∑ b : B, ∑ c : C, f a b c / d := by
  simp [Finset.sum_div]

/-- Move the outermost index of a three-fold nested sum inside. -/
theorem sum3_swap (f : A → B → C → ℝ) :
    (∑ a : A, ∑ b : B, ∑ c : C, f a b c)
      = ∑ c : C, ∑ a : A, ∑ b : B, f a b c := by
  calc (∑ a : A, ∑ b : B, ∑ c : C, f a b c)
      = ∑ a : A, ∑ c : C, ∑ b : B, f a b c :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c : C, ∑ a : A, ∑ b : B, f a b c := Finset.sum_comm

/-- Move the outer pair of a four-fold nested sum inside. -/
theorem sum4_swap {D : Type*} [Fintype D] (f : A → B → C → D → ℝ) :
    (∑ a : A, ∑ b : B, ∑ c : C, ∑ d : D, f a b c d)
      = ∑ c : C, ∑ d : D, ∑ a : A, ∑ b : B, f a b c d := by
  calc (∑ a : A, ∑ b : B, ∑ c : C, ∑ d : D, f a b c d)
      = ∑ a : A, ∑ c : C, ∑ b : B, ∑ d : D, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c : C, ∑ a : A, ∑ b : B, ∑ d : D, f a b c d := Finset.sum_comm
    _ = ∑ c : C, ∑ a : A, ∑ d : D, ∑ b : B, f a b c d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ =>
          Finset.sum_comm
    _ = ∑ c : C, ∑ d : D, ∑ a : A, ∑ b : B, f a b c d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm

end SumHelpers

/-- Telescoping perturbation of a product of `[0,1]`-valued factors:
`|∏ f − ∏ g| ≤ ∑ |f − g|`. [07_main_theorem.tex, "the second inequality
follows by telescoping the product"] -/
theorem abs_prod_sub_prod_le {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f g : ι → ℝ)
    (hf0 : ∀ i ∈ s, 0 ≤ f i) (hf1 : ∀ i ∈ s, f i ≤ 1)
    (hg0 : ∀ i ∈ s, 0 ≤ g i) (hg1 : ∀ i ∈ s, g i ≤ 1) :
    |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤ ∑ i ∈ s, |f i - g i| := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
    have hfmem : ∀ i ∈ s, 0 ≤ f i :=
      fun i hi => hf0 i (Finset.mem_insert_of_mem hi)
    have hfmem1 : ∀ i ∈ s, f i ≤ 1 :=
      fun i hi => hf1 i (Finset.mem_insert_of_mem hi)
    have hgmem : ∀ i ∈ s, 0 ≤ g i :=
      fun i hi => hg0 i (Finset.mem_insert_of_mem hi)
    have hgmem1 : ∀ i ∈ s, g i ≤ 1 :=
      fun i hi => hg1 i (Finset.mem_insert_of_mem hi)
    have ihs := ih hfmem hfmem1 hgmem hgmem1
    have hjf := hf0 j (Finset.mem_insert_self j s)
    have hjf1 := hf1 j (Finset.mem_insert_self j s)
    have hjg := hg0 j (Finset.mem_insert_self j s)
    have hjg1 := hg1 j (Finset.mem_insert_self j s)
    have hPf : |∏ i ∈ s, f i| ≤ 1 := by
      rw [abs_of_nonneg (Finset.prod_nonneg hfmem)]
      exact Finset.prod_le_one hfmem hfmem1
    have key : f j * (∏ i ∈ s, f i) - g j * (∏ i ∈ s, g i)
        = (f j - g j) * (∏ i ∈ s, f i) +
          g j * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) := by ring
    calc |f j * (∏ i ∈ s, f i) - g j * (∏ i ∈ s, g i)|
        = |(f j - g j) * (∏ i ∈ s, f i) +
            g j * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)| := by rw [key]
      _ ≤ |(f j - g j) * (∏ i ∈ s, f i)| +
            |g j * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)| := abs_add_le _ _
      _ = |f j - g j| * |∏ i ∈ s, f i| +
            |g j| * |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| := by
          rw [abs_mul, abs_mul]
      _ ≤ |f j - g j| * 1 + 1 * (∑ i ∈ s, |f i - g i|) := by
          have h1 : |f j - g j| * |∏ i ∈ s, f i| ≤ |f j - g j| * 1 :=
            mul_le_mul_of_nonneg_left hPf (abs_nonneg _)
          have hgj : |g j| ≤ 1 := by rw [abs_of_nonneg hjg]; exact hjg1
          have h2 : |g j| * |(∏ i ∈ s, f i) - ∏ i ∈ s, g i|
              ≤ 1 * (∑ i ∈ s, |f i - g i|) :=
            mul_le_mul hgj ihs (abs_nonneg _) zero_le_one
          linarith
      _ = |f j - g j| + ∑ i ∈ s, |f i - g i| := by ring

end CommutingRepetition
