/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/Bernoulli/
Weights.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.Statements
public import MIPRE.Background.LIDT.Co.Pasting.Bernoulli.TruncatedSums

@[expose] public section

/-!
# Section 12 pasting: Bernoulli recurrence weights

Recurrence-weight identities for the `fromHToG` reduction: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Bernoulli/Weights.lean` in the port of
`planning/c6b-plan.md` (milestone M11, section "Port conventions").

The slice family is an `IdxPolyFamily params 𝔓`, so the recurrence weight
`fromHToGRecurrenceWeight params family prefixLen τtail` and the averaged complete operator
`G = family.averagedSubMeas.total` are local operators in `𝔓` (the vendored `Op ι`). Every fact
here is `truncatedTypeSumRecurrence` or a commutation lemma of
`Co/Pasting/Bernoulli/TruncatedSums.lean` at that `G`; the Hermitian statement is
`star W = W` (the vendored `Wᴴ = W`).

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel)
open MIPStarRE.LDT.Pasting (GHatType prependTypeBit)
open MIPRE.LIDT.Co (IdxPolyFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]

/-- Bundle the four proved facts about the averaged total operator `G` used by
`fromHToGRecurrenceWeight` into a single `truncatedTypeSumRecurrence` call. -/
theorem fromHToGRecurrenceWeight_recurrence (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    star (truncatedTypeSums family.averagedSubMeas.total params.d prefixLen τtail) =
        truncatedTypeSums family.averagedSubMeas.total params.d prefixLen τtail ∧
      0 ≤ truncatedTypeSums family.averagedSubMeas.total params.d prefixLen τtail ∧
      truncatedTypeSums family.averagedSubMeas.total params.d prefixLen τtail ≤ 1 ∧
      truncatedTypeSums family.averagedSubMeas.total params.d (prefixLen + 1) τtail =
        truncatedTypeSums family.averagedSubMeas.total params.d prefixLen
            (prependTypeBit true τtail) * family.averagedSubMeas.total +
          truncatedTypeSums family.averagedSubMeas.total params.d prefixLen
            (prependTypeBit false τtail) * (1 - family.averagedSubMeas.total) :=
  truncatedTypeSumRecurrence family.averagedSubMeas.total
    family.averagedSubMeas.total_nonneg family.averagedSubMeas.total_le_one
    params.d prefixLen τtail

/-- `fromHToGRecurrenceWeight` is self-adjoint (source-style API). -/
theorem fromHToGRecurrenceWeight_isHermitian (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    star (fromHToGRecurrenceWeight params family prefixLen τtail) =
      fromHToGRecurrenceWeight params family prefixLen τtail :=
  (fromHToGRecurrenceWeight_recurrence params family prefixLen τtail).1

/-- `fromHToGRecurrenceWeight` is positive (source-style API). -/
theorem fromHToGRecurrenceWeight_nonneg (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    0 ≤ fromHToGRecurrenceWeight params family prefixLen τtail :=
  (fromHToGRecurrenceWeight_recurrence params family prefixLen τtail).2.1

/-- `fromHToGRecurrenceWeight` is bounded above by the identity. -/
theorem fromHToGRecurrenceWeight_le_one (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    fromHToGRecurrenceWeight params family prefixLen τtail ≤ 1 :=
  (fromHToGRecurrenceWeight_recurrence params family prefixLen τtail).2.2.1

/-- `fromHToGRecurrenceWeight` commutes with the averaged complete operator `G`. -/
theorem fromHToGRecurrenceWeight_commute_base (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    Commute (fromHToGRecurrenceWeight params family prefixLen τtail)
      family.averagedSubMeas.total :=
  truncatedTypeSums_commute_base family.averagedSubMeas.total params.d prefixLen τtail

/-- `fromHToGRecurrenceWeight` commutes with `I - G`. -/
theorem fromHToGRecurrenceWeight_commute_one_sub_base (params : Parameters)
    [FieldModel params.q] (family : IdxPolyFamily params 𝔓) (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    Commute (fromHToGRecurrenceWeight params family prefixLen τtail)
      (1 - family.averagedSubMeas.total) :=
  truncatedTypeSums_commute_one_sub_base family.averagedSubMeas.total params.d prefixLen τtail

/-- One-step recurrence for `fromHToGRecurrenceWeight`: adding a new prefix bit
splits the weight into the `τ_ℓ = 1` and `τ_ℓ = 0` branches, each multiplied by
the appropriate Bernoulli factor `G` or `I - G`. -/
theorem fromHToGRecurrenceWeight_succ (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    fromHToGRecurrenceWeight params family (prefixLen + 1) τtail =
      fromHToGRecurrenceWeight params family prefixLen (prependTypeBit true τtail) *
          family.averagedSubMeas.total +
        fromHToGRecurrenceWeight params family prefixLen (prependTypeBit false τtail) *
          (1 - family.averagedSubMeas.total) :=
  (fromHToGRecurrenceWeight_recurrence params family prefixLen τtail).2.2.2

end MIPRE.LIDT.Co.Pasting

end
