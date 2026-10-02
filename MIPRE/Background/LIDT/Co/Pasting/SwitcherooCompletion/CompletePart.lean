/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
SwitcherooCompletion/CompletePart.lean, to the symmetric model of `planning/c6b-plan.md`; not a
vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.CommutativityPoints.SharedHelpers.Core
public import MIPRE.Background.LIDT.Co.Pasting.SwitcherooCompletion.SecondTerm
public import MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.SwitcherooCompletion.CompletePart

@[expose] public section

/-!
# Section 12 pasting: complete-part reductions

Complete-part aggregate commutation and scalar error bounds: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/SwitcherooCompletion/CompletePart.lean` in the port
of `planning/c6b-plan.md` (milestone M11, section "Port conventions").

The vendored second bipartite state `ψbi : QuantumState (ι × ι)` is the symmetric model
`S : SymModel 𝔓 K`, in the vendored argument position; the slice family is an
`IdxPolyFamily params 𝔓`. `completePartAggregateCommutation_as_total` applies
`CommutativityPoints.sddOpRel_congr_outcome` to `S.toVecState`, the outcomes agreeing after
`completePartSubMeas_outcome_unit` on both sides.

The two scalar bounds of the vendored file mention no state, operator or measurement, so they
are classical: this file imports the vendored file for them, and dependants name them through an
explicit `open MIPStarRE.LDT.Pasting (…)` list.

## Not ported

- `firstSwitcherooError_le_eighth_stage`: classical, imported.
- `firstSwitcherooError_le_commutingWithGCompleteError`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel uniformDistribution)
open MIPStarRE.LDT.Pasting (SlicePairQuestion)
open MIPRE.LIDT.Co (SymModel IdxPolyFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- When the left/right aggregate families are re-expressed using the
completed one-outcome form, the aggregate commutation bound translates to the
complete-part total-product commutation bound. -/
theorem completePartAggregateCommutation_as_total
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (gamma : ℝ)
    (hcomm : S.SDDOpRel
      (uniformDistribution (SlicePairQuestion params))
      (switcherooAggregateLeft S params family (completePartProjFamily params family))
      (switcherooAggregateRight S params family (completePartProjFamily params family))
      gamma) :
    S.SDDOpRel
      (uniformDistribution (SlicePairQuestion params))
      (completePartTotalProductLeft S params family)
      (completePartTotalProductRight S params family)
      gamma :=
  CommutativityPoints.sddOpRel_congr_outcome S.toVecState
    (uniformDistribution (SlicePairQuestion params))
    (switcherooAggregateLeft S params family (completePartProjFamily params family))
    (switcherooAggregateRight S params family (completePartProjFamily params family))
    (completePartTotalProductLeft S params family)
    (completePartTotalProductRight S params family)
    gamma
    (fun q a => by
      change S.L ((completePartSubMeas params family q.1).total *
          (completePartSubMeas params family q.2).outcome a) =
        S.L ((completePartSubMeas params family q.1).outcome a *
          (completePartSubMeas params family q.2).total)
      cases a
      rw [completePartSubMeas_outcome_unit, completePartSubMeas_outcome_unit])
    (fun q a => by
      change S.L ((completePartSubMeas params family q.2).outcome a *
          (completePartSubMeas params family q.1).total) =
        S.L ((completePartSubMeas params family q.2).total *
          (completePartSubMeas params family q.1).outcome a)
      cases a
      rw [completePartSubMeas_outcome_unit, completePartSubMeas_outcome_unit])
    hcomm

end MIPRE.LIDT.Co.Pasting

end
