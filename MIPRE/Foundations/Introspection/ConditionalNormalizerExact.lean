/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.ConditionalNormalizer

/-! # Exact conditional products from rejected-outcome orthogonality -/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical

set_option linter.unusedSectionVars false

variable {H I O Y Z : Type*} [Fintype H] [DecidableEq H]
  [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
  [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]

/-- A complete family restricted to its only possible coarse outcome acts as
the identity on a compatible projector. -/
theorem fibSum_mul_of_reject (P : I → Matrix H H ℂ) (R : Matrix H H ℂ)
    (hP : ∑ i, P i = 1) (f : I → Z) (z₀ : Z)
    (hzero : ∀ i, f i ≠ z₀ → P i * R = 0) (z : Z) :
    fibSum P f z * R = if z = z₀ then R else 0 := by
  rw [fibSum, Finset.sum_mul, Finset.sum_filter]
  by_cases hz : z = z₀
  · subst z
    rw [if_pos rfl]
    calc
      _ = ∑ i, P i * R := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : f i = z₀
        · simp [hi]
        · simp [hi, hzero i hi]
      _ = R := by rw [← Finset.sum_mul, hP, one_mul]
  · rw [if_neg hz]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : f i = z
    · simp [hi, hzero i (by simpa only [hi] using hz)]
    · simp [hi]

/-- If a later PVM's prefix is selected by `Q`, and all rejected keyed
comparisons are orthogonal, the conditional ideal product is exactly its
coarse later measurement. -/
theorem conditionalIdeal_eq_coarse_of_reject
    (P : I → Matrix H H ℂ) (N : O → Matrix H H ℂ) (Q : Y → Matrix H H ℂ)
    (f : Y → I → Z) (g : O → Y × Z)
    (hP : IsPVM P) (hN : IsPVM N)
    (hc : ∀ y i, Commute (Q y) (P i))
    (hprefix : ∀ y o, Q y * N o = if (g o).1 = y then N o else 0)
    (hreject : ∀ i o, f (g o).1 i ≠ (g o).2 → P i * N o = 0)
    (p : Y × Z) : conditionalIdeal P Q f p = fibSum N g p := by
  calc
    _ = conditionalIdeal P Q f p * (∑ o, N o) := by rw [hN.sum_eq_one, mul_one]
    _ = ∑ o, if g o = p then N o else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro o _
      rw [conditionalIdeal, (commute_fibSum_right P Q hc (f p.1) p.1 p.2).eq,
        mul_assoc, hprefix]
      by_cases hy : (g o).1 = p.1
      · rw [if_pos hy]
        have hf := fibSum_mul_of_reject P (N o) hP.sum_eq_one (f (g o).1) (g o).2
          (fun i hi => hreject i o hi) p.2
        rw [hy] at hf
        rw [hf]
        by_cases hz : p.2 = (g o).2
        · have hg : g o = p := Prod.ext hy hz.symm
          simp [hz, hg]
        · have hg : g o ≠ p := by intro he; exact hz (congrArg Prod.snd he).symm
          simp [hz, hg]
      · have hg : g o ≠ p := by intro he; exact hy (congrArg Prod.fst he)
        simp [hy, hg]
    _ = _ := by rw [fibSum, Finset.sum_filter]

end MIPRE.Introspection
