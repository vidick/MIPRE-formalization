/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/Bernoulli/
FromHToG/Core/FactBundles.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored
file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.Bernoulli.FromHToG.Core.AveragesAndOps
public import MIPRE.Background.LIDT.Co.Pasting.Bernoulli.FromHToG.Core.StageMass
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.CommuteGHalfSandwich.Setup.StepLemmas.Split
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.CommuteGHalfSandwich.Setup.StepLemmas.Move
public import MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.Bernoulli.FromHToG.Core.FactBundles

@[expose] public section

/-!
# Section 12 pasting: exact identities and error-bound lemma

Exact recurrence identities and the paper-total error absorption lemma that assemble the final
`fromHToG` telescope conclusion: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/Core/FactBundles.lean` in the
port of `planning/c6b-plan.md` (milestone M11, section "Port conventions").

The fact bundle reads the vendored second bipartite state `ψbi : QuantumState (ι × ι)` only
through the tail stage masses and their expectations, so it is the symmetric model
`S : SymModel 𝔓 K`, in the vendored argument position, with the slice family an
`IdxPolyFamily params 𝔓`; `leftTensor (ι₂ := ι)`/`rightTensor (ι₁ := ι)` are `S.L`/`S.R`.

The scalar absorption lemma mentions no state, operator or measurement: this file imports the
vendored file and callers name it through an explicit `open MIPStarRE.LDT.Pasting (…)` list.

## Not ported

- `fromHToGPaperTotalError_le`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Fq uniformDistribution)
open MIPStarRE.LDT.Pasting (GHatType prependTypeBit)
open MIPRE.LIDT.Co (SymModel IdxPolyFamily averageOperatorOverDistribution)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Exact bookkeeping at the end of the adjacent-stage comparison.

This isolates the paper's `S`-recurrence step
`references/ldt-paper/ld-pasting.tex:1417--1425` and its use in the final
collapse at lines `1657--1661`: once the analytic move-right / commute /
move-right approximations have reached the branch-split expression, the
recurrence weight is exactly the next-stage weight. -/
structure FromHToGAdjacentStageExactFacts (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓) : Prop where
  /-- The complete branch of `\widehat G` averages to `G`. -/
  completeBranchAverage :
    averageOperatorOverDistribution (uniformDistribution (Fq params))
      (fun x => (completePartSubMeas params family x).total) =
        family.averagedSubMeas.total
  /-- The incomplete branch of `\widehat G` averages to `I - G`. -/
  incompleteBranchAverage :
    averageOperatorOverDistribution (uniformDistribution (Fq params))
      (fun x => (incompletePartSubMeas params family x).total) =
        1 - family.averagedSubMeas.total
  /-- The tail stage mass at prefix length `prefixLen + 1` expands by the one-step
  recurrence of the weight. -/
  tailWeightRecurrence :
    ∀ (prefixLen : ℕ) {tailLen : ℕ} (τtail : GHatType tailLen),
      fromHToGTailStageMass params S family (prefixLen + 1) τtail =
        S.ev (S.L (averagedSandwichByTypeSubMeas params family tailLen τtail).total *
          S.R (fromHToGRecurrenceWeight params family prefixLen
                (prependTypeBit true τtail) * family.averagedSubMeas.total +
              fromHToGRecurrenceWeight params family prefixLen
                (prependTypeBit false τtail) * (1 - family.averagedSubMeas.total)))

/-- Collect the exact `S`-recurrence identities proved in
`Core/AveragesAndOps` and `Core/StageMass`. -/
theorem fromHToGAdjacentStageExactFacts_of_weights (params : Parameters)
    [FieldModel params.q] (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓) :
    FromHToGAdjacentStageExactFacts params S family where
  completeBranchAverage := fromHToG_completePart_average_total_eq params family
  incompleteBranchAverage := fromHToG_incompletePart_average_total_eq params family
  tailWeightRecurrence := fromHToGTailStageMass_succ_weight_recurrence params S family

end MIPRE.LIDT.Co.Pasting

end
