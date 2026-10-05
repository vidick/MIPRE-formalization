/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/Bernoulli/
TruncatedSums.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.Defs.Tuples
public import MIPStarRE.LDT.Pasting.Bernoulli.TruncatedSums

@[expose] public section

/-!
# Section 12 pasting: Bernoulli truncated sums

Truncated type sums and their one-step recurrence: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Bernoulli/TruncatedSums.lean` in the port of
`planning/c6b-plan.md` (milestone M11, section "Port conventions").

No declaration of the vendored file reads a state. The algebraic identities (the one-bit
recurrences of the type monomials, their commutation with `G` and `1 - G`, the binomial
expansion `∑_τ G^{|τ|} (1 - G)^{k - |τ|} = 1`) hold in any ring, and the positivity facts in any
C*-algebra with its order, through `CStarAlgebra.pow_nonneg` and `Commute.mul_nonneg` in place
of the vendored `Matrix.PosSemidef` arguments, as in `Co/Pasting/Sandwich/GHatSandwich.lean`; so
they serve the local algebra `𝔓` and `K →L[ℂ] K` alike. The Hermitian clause of
`truncatedTypeSumRecurrence` is `star T = T` (the vendored `Tᴴ = T`), read off positivity.

The three type-weight identities of the vendored file are classical: this file imports the
vendored file and names them through an explicit `open MIPStarRE.LDT.Pasting (…)` list.

## Not ported

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT.Pasting (GHatType gHatTypeWeight prependTypeBit)

/-- Upstream keeps this helper `private` since its Lean-module port (`LionSR/MIPStarRE` at `5fc363b`); the port carries its own copy, with upstream's proof. -/
lemma gHatTypeWeight_prepend_true {k : ℕ} (τ : GHatType k) :
    gHatTypeWeight (prependTypeBit true τ) = gHatTypeWeight τ + 1 := by
  unfold gHatTypeWeight
  rw [Fin.card_filter_univ_succ]
  simp [prependTypeBit, Fin.cons_zero, Fin.cons_succ, add_comm]

/-- Upstream keeps this helper `private` since its Lean-module port (`LionSR/MIPStarRE` at `5fc363b`); the port carries its own copy, with upstream's proof. -/
lemma gHatTypeWeight_prepend_false {k : ℕ} (τ : GHatType k) :
    gHatTypeWeight (prependTypeBit false τ) = gHatTypeWeight τ := by
  unfold gHatTypeWeight
  rw [Fin.card_filter_univ_succ]
  simp [prependTypeBit, Fin.cons_zero, Fin.cons_succ]

/-- Upstream keeps this helper `private` since its Lean-module port (`LionSR/MIPStarRE` at
`5fc363b`); the port carries its own copy, with upstream's proof. -/
theorem gHatTypeWeight_le {k : ℕ} (τ : GHatType k) : gHatTypeWeight τ ≤ k := by
  unfold gHatTypeWeight
  simpa using (Finset.card_filter_le (s := (Finset.univ : Finset (Fin k))) (p := fun i : Fin k => τ i))

/-! ### Bernoulli recurrence weights -/

section Ring

variable {R : Type*} [Ring R]

/-- Prepending a `true` bit multiplies the type monomial by `G`. -/
theorem gHatTypeOperator_prepend_true (G : R) {k : ℕ} (τ : GHatType k) :
    gHatTypeOperator G (prependTypeBit true τ) = gHatTypeOperator G τ * G := by
  have hcomm : Commute G (1 - G) := (Commute.one_right G).sub_right (Commute.refl G)
  have hsub : k + 1 - (gHatTypeWeight τ + 1) = k - gHatTypeWeight τ := by
    have := gHatTypeWeight_le τ
    omega
  unfold gHatTypeOperator
  rw [gHatTypeWeight_prepend_true, hsub, pow_succ, mul_assoc, (hcomm.pow_right _).eq,
    ← mul_assoc]

/-- Prepending a `false` bit multiplies the type monomial by `1 - G`. -/
theorem gHatTypeOperator_prepend_false (G : R) {k : ℕ} (τ : GHatType k) :
    gHatTypeOperator G (prependTypeBit false τ) = gHatTypeOperator G τ * (1 - G) := by
  have hsub : k + 1 - gHatTypeWeight τ = k - gHatTypeWeight τ + 1 := by
    have := gHatTypeWeight_le τ
    omega
  unfold gHatTypeOperator
  rw [gHatTypeWeight_prepend_false, hsub, pow_succ, mul_assoc]

/-- Each Boolean-type monomial commutes with the base operator `G`. -/
theorem gHatTypeOperator_commute_base (G : R) {k : ℕ} (τ : GHatType k) :
    Commute (gHatTypeOperator G τ) G :=
  ((Commute.refl G).pow_left _).mul_left
    (((Commute.one_right G).sub_right (Commute.refl G)).symm.pow_left _)

/-- Each Boolean-type monomial commutes with the complementary base operator `1 - G`. -/
theorem gHatTypeOperator_commute_one_sub_base (G : R) {k : ℕ} (τ : GHatType k) :
    Commute (gHatTypeOperator G τ) (1 - G) :=
  (((Commute.one_right G).sub_right (Commute.refl G)).pow_left _).mul_left
    ((Commute.refl (1 - G)).pow_left _)

/-- The truncated type sum commutes with the base operator `G`. -/
theorem truncatedTypeSums_commute_base (G : R) (d prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    Commute (truncatedTypeSums G d prefixLen τtail) G :=
  Commute.sum_left _ _ _ fun τprefix _ => by
    split_ifs
    · exact gHatTypeOperator_commute_base G τprefix
    · exact Commute.zero_left G

/-- The truncated type sum commutes with the complementary base operator `1 - G`. -/
theorem truncatedTypeSums_commute_one_sub_base (G : R) (d prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    Commute (truncatedTypeSums G d prefixLen τtail) (1 - G) :=
  Commute.sum_left _ _ _ fun τprefix _ => by
    split_ifs
    · exact gHatTypeOperator_commute_one_sub_base G τprefix
    · exact Commute.zero_left _

/-- The full sum of type operators equals the identity.

This is the commuting binomial expansion
`∑ τ : GHatType k, G ^ |τ| * (1 - G) ^ (k - |τ|) = (G + (1 - G))^k = 1`. -/
theorem full_gHatType_sum_eq_one (G : R) :
    ∀ prefixLen : ℕ, ∑ τprefix : GHatType prefixLen, gHatTypeOperator G τprefix = 1
  | 0 => by simp [gHatTypeOperator, gHatTypeWeight]
  | prefixLen + 1 => by
      rw [← (Fin.consEquiv fun _ : Fin (prefixLen + 1) => Bool).sum_comp,
        Fintype.sum_prod_type, Fintype.sum_bool]
      change (∑ τ, gHatTypeOperator G (prependTypeBit true τ)) +
          ∑ τ, gHatTypeOperator G (prependTypeBit false τ) = 1
      simp only [gHatTypeOperator_prepend_true, gHatTypeOperator_prepend_false,
        ← Finset.sum_mul, full_gHatType_sum_eq_one G prefixLen, one_mul, add_sub_cancel]

/-- The one-step recurrence of the truncated type sums: the new prefix bit is moved onto the
tail, and the monomial picks up the Bernoulli factor `G` or `1 - G`. -/
private theorem truncatedTypeSums_succ (G : R) (d prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    truncatedTypeSums G d (prefixLen + 1) τtail =
      truncatedTypeSums G d prefixLen (prependTypeBit true τtail) * G +
        truncatedTypeSums G d prefixLen (prependTypeBit false τtail) * (1 - G) := by
  unfold truncatedTypeSums
  rw [← (Fin.consEquiv fun _ : Fin (prefixLen + 1) => Bool).sum_comp,
    Fintype.sum_prod_type, Fintype.sum_bool, Finset.sum_mul, Finset.sum_mul]
  change (∑ τ, if d + 1 ≤ gHatTypeWeight (prependTypeBit true τ) + gHatTypeWeight τtail then
        gHatTypeOperator G (prependTypeBit true τ) else 0) +
      (∑ τ, if d + 1 ≤ gHatTypeWeight (prependTypeBit false τ) + gHatTypeWeight τtail then
        gHatTypeOperator G (prependTypeBit false τ) else 0) = _
  congr 1 <;> refine Finset.sum_congr rfl fun τ _ => ?_
  · rw [gHatTypeWeight_prepend_true, gHatTypeWeight_prepend_true,
      gHatTypeOperator_prepend_true, ite_mul, zero_mul, add_right_comm, add_assoc]
  · rw [gHatTypeWeight_prepend_false, gHatTypeWeight_prepend_false,
      gHatTypeOperator_prepend_false, ite_mul, zero_mul]

end Ring

section CStar

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Each type monomial of a positive contraction is positive. -/
theorem gHatTypeOperator_nonneg (G : A) (hGpsd : 0 ≤ G) (hGleOne : G ≤ 1)
    {k : ℕ} (τ : GHatType k) :
    0 ≤ gHatTypeOperator G τ :=
  Commute.mul_nonneg (CStarAlgebra.pow_nonneg G _ hGpsd)
    (CStarAlgebra.pow_nonneg (1 - G) _ (sub_nonneg.mpr hGleOne))
    ((((Commute.one_right G).sub_right (Commute.refl G)).pow_left _).pow_right _)

/-- `lem:truncated-type-sum-recurrence`.

This records the Hermitian, positivity, boundedness, and one-step recurrence
properties of the truncated type sums used in the `fromHToG` reduction. -/
theorem truncatedTypeSumRecurrence (G : A) (hGpsd : 0 ≤ G) (hGleOne : G ≤ 1)
    (d prefixLen : ℕ) {tailLen : ℕ} (τtail : GHatType tailLen) :
    star (truncatedTypeSums G d prefixLen τtail) = truncatedTypeSums G d prefixLen τtail ∧
      0 ≤ truncatedTypeSums G d prefixLen τtail ∧
      truncatedTypeSums G d prefixLen τtail ≤ 1 ∧
      truncatedTypeSums G d (prefixLen + 1) τtail =
        truncatedTypeSums G d prefixLen (prependTypeBit true τtail) * G +
          truncatedTypeSums G d prefixLen (prependTypeBit false τtail) * (1 - G) := by
  /-
  Paper reference: `references/ldt-paper/ld-pasting.tex`,
  `lem:truncated-type-sum-recurrence`.
  The proof is the commuting-polynomial argument in `G` and `I - G`.
  -/
  have hnonneg : 0 ≤ truncatedTypeSums G d prefixLen τtail :=
    Finset.sum_nonneg fun τprefix _ => by
      split_ifs
      · exact gHatTypeOperator_nonneg G hGpsd hGleOne τprefix
      · exact le_rfl
  refine ⟨(IsSelfAdjoint.of_nonneg hnonneg).star_eq, hnonneg, ?_,
    truncatedTypeSums_succ G d prefixLen τtail⟩
  calc truncatedTypeSums G d prefixLen τtail
      ≤ ∑ τprefix : GHatType prefixLen, gHatTypeOperator G τprefix :=
        Finset.sum_le_sum fun τprefix _ => by
          split_ifs
          · exact le_rfl
          · exact gHatTypeOperator_nonneg G hGpsd hGleOne τprefix
    _ = 1 := full_gHatType_sum_eq_one G prefixLen

end CStar

end MIPRE.LIDT.Co.Pasting

end
