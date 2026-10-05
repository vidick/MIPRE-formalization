/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/Bernoulli/
FromHToG/Core/BernoulliTail.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored
file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.Statements
public import MIPRE.Background.LIDT.Co.Pasting.Bernoulli.Weights
public import MIPRE.Background.LIDT.Co.Pasting.Bernoulli.Scalar
public import MIPRE.Background.LIDT.Co.Pasting.Bernoulli.TruncatedSums
public import MIPStarRE.LDT.Pasting.Bernoulli.FromHToG.Core.BernoulliTail

@[expose] public section

/-!
# Section 12 pasting: Bernoulli tail polynomial combinatorics

Finset re-indexing and cardinality-grouping lemmas for the Bernoulli-tail operator endpoint of
the `fromHToG` recurrence: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/Core/BernoulliTail.lean` in the
port of `planning/c6b-plan.md` (milestone M11, section "Port conventions").

No declaration of the vendored file reads a state. The type monomials and truncated type sums
of `Co/Pasting/Defs/Tuples.lean` are generic over a ring, so the four lemmas about them hold for
any `[Ring R]`, and the two that reach the Bernoulli tail operator, whose binomial coefficients
are complex scalars, for any `[Ring R] [Algebra ℂ R]`: they serve the local algebra `𝔓` (the
vendored `Op ι`) and `K →L[ℂ] K` alike. The vendored `simp [Algebra.smul_def]` turning the
natural-number multiples of `Finset.sum_powerset_apply_card` into complex ones is
`Nat.cast_smul_eq_nsmul` here.

The support-finset equivalence and its weight identity are classical: this file imports the
vendored file and names them through an explicit `open MIPStarRE.LDT.Pasting (…)` list.

## Not ported

- `gHatTypeFinsetEquiv`: classical, imported.
- `fromHToG_gHatTypeWeight_of_finset`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT.Pasting (GHatType gHatTypeWeight gHatTypeFinsetEquiv
  fromHToG_gHatTypeWeight_of_finset)

section Ring

variable {R : Type*} [Ring R]

/-- The type monomial of the support pattern of a finset `s` is `G^{|s|} (1 - G)^{k - |s|}`. -/
theorem fromHToG_gHatTypeOperator_of_finset (G : R) {k : ℕ} (s : Finset (Fin k)) :
    gHatTypeOperator G (fun i : Fin k => i ∈ s) =
      G ^ s.card * (1 - G) ^ (k - s.card) := by
  simp [gHatTypeOperator, fromHToG_gHatTypeWeight_of_finset]

/-- Rewrite the terminal truncated type sum as a sum over support finsets. -/
theorem fromHToG_truncatedTypeSums_full_as_finset_sum (G : R) (d k : ℕ) :
    truncatedTypeSums G d k (default : GHatType 0) =
      ∑ s : Finset (Fin k),
        if d + 1 ≤ s.card then G ^ s.card * (1 - G) ^ (k - s.card) else 0 := by
  unfold truncatedTypeSums
  refine Fintype.sum_equiv (gHatTypeFinsetEquiv k) _ _ fun τ => ?_
  have hτ : τ = fun i : Fin k => i ∈ gHatTypeFinsetEquiv k τ := by
    ext i
    simp [gHatTypeFinsetEquiv]
  have hw : gHatTypeWeight (default : GHatType 0) = 0 := by simp [gHatTypeWeight]
  conv_lhs => rw [hτ]
  rw [hw, add_zero, fromHToG_gHatTypeWeight_of_finset, fromHToG_gHatTypeOperator_of_finset]

variable [Algebra ℂ R]

/-- Group the terminal support-finset sum by cardinality, producing the binomial coefficients
in the Bernoulli-tail polynomial. The key combinatorial step is Mathlib's
`Finset.sum_powerset_apply_card`, applied to `Finset.univ : Finset (Fin k)`. -/
theorem fromHToG_sum_finsets_by_card_indicator (G : R) (d k : ℕ) :
    (∑ s : Finset (Fin k),
        if d + 1 ≤ s.card then G ^ s.card * (1 - G) ^ (k - s.card) else 0) =
      ∑ r ∈ Finset.Icc (d + 1) k,
        (Nat.choose k r : ℂ) • (G ^ r * (1 - G) ^ (k - r)) := by
  let F : ℕ → R := fun r => if d + 1 ≤ r then G ^ r * (1 - G) ^ (k - r) else 0
  calc
    (∑ s : Finset (Fin k),
        if d + 1 ≤ s.card then G ^ s.card * (1 - G) ^ (k - s.card) else 0)
      = ∑ s ∈ (Finset.univ : Finset (Fin k)).powerset, F s.card := by
        rw [Finset.powerset_univ]
    _ = ∑ r ∈ Finset.range (k + 1), Nat.choose k r • F r := by
        rw [Finset.sum_powerset_apply_card, Finset.card_univ, Fintype.card_fin]
    _ = ∑ r ∈ Finset.Icc (d + 1) k, Nat.choose k r • F r := by
        refine (Finset.sum_subset (fun r hr => ?_) fun r hrange hrnot => ?_).symm
        · simp only [Finset.mem_Icc, Finset.mem_range] at hr ⊢
          omega
        · simp only [Finset.mem_range, Finset.mem_Icc] at hrange hrnot
          have hnot : ¬ d + 1 ≤ r := fun hdr => hrnot ⟨hdr, by omega⟩
          simp only [F, hnot, ↓reduceIte, smul_zero]
    _ = ∑ r ∈ Finset.Icc (d + 1) k,
        (Nat.choose k r : ℂ) • (G ^ r * (1 - G) ^ (k - r)) := by
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [Finset.mem_Icc] at hr
        simp only [F, hr.1, ↓reduceIte, Nat.cast_smul_eq_nsmul]

/-- Terminal endpoint of the recurrence weight: after all `k` bits have been converted, the
truncated type sum is exactly the Bernoulli-tail polynomial `F(G)`. -/
theorem fromHToG_truncatedTypeSums_full_eq_bernoulliTailOperator (G : R) (d k : ℕ) :
    truncatedTypeSums G d k (default : GHatType 0) = bernoulliTailOperator k d G := by
  rw [fromHToG_truncatedTypeSums_full_as_finset_sum, fromHToG_sum_finsets_by_card_indicator]
  rfl

omit [Algebra ℂ R] in
/-- At prefix length zero, the recurrence weight is exactly the eligibility indicator for the
remaining type: the empty prefix contributes the identity when `|τtail| ≥ d + 1`, and zero
otherwise. -/
theorem fromHToG_truncatedTypeSums_zero_eq_indicator (G : R) (d : ℕ) {tailLen : ℕ}
    (τtail : GHatType tailLen) :
    truncatedTypeSums G d 0 τtail =
      if d + 1 ≤ gHatTypeWeight τtail then 1 else 0 := by
  simp [truncatedTypeSums, gHatTypeOperator, gHatTypeWeight]

end Ring

end MIPRE.LIDT.Co.Pasting

end
