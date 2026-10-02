/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/Defs/
Families.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.Defs.Interpolation
public import MIPRE.Background.LIDT.Co.Test.StrategyPolynomialFamilies
public import MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.Defs.Families

@[expose] public section

/-!
# Section 12 — Definitions: consistency and families

Global-consistency predicates and the completed-slice family constructions: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Defs/Families.lean` in the port of
`planning/c6b-plan.md` (milestone M11, section "Port conventions").

A slice family is an `IdxPolyFamily params 𝔓` (`Co/Test/StrategyPolynomialFamilies.lean`), with
its projective submeasurements in the local C*-algebra `𝔓` (the vendored `Op ι`). Its complete
part `G^x`, incomplete part `G^x_⊥ = 1 - G^x` and completion `\widehat G^x` are local
submeasurements in `𝔓`. The four placed families take the symmetric model `S : SymModel 𝔓 K`
as their first explicit argument, in place of the vendored named carriers `(ιA := ι)`,
`(ιB := ι)`, and place by `S.leftPlacedSubMeas` and `S.rightPlacedSubMeas`
(`Co/Basic/SubMeasurementFamilies.lean`), so their outcomes are `S.L (…)` and `S.R (…)` by
`rfl`.

The classical half of the vendored file (the global-consistency predicate `Global_τ(x)`, its
classical decidability, the global and nonglobal outcome sets, the choice of a global witness
and the interpolation map `interpolateCompletedSlices`) is not ported: this file imports the
vendored file, and the ported files of `Pasting` name those declarations through explicit
`open MIPStarRE.LDT.Pasting (…)` lists. The vendored instance
`isGloballyConsistent_decidablePred` comes with the import.

## Not ported

- `IsGloballyConsistent`: classical, imported.
- `isGloballyConsistent_decidablePred`: classical, imported.
- `globallyConsistentOutcomesByType`: classical, imported.
- `nonglobalOutcomesByType`: classical, imported.
- `globallyConsistentWitness`: classical, imported.
- `interpolateCompletedSlices`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Fq)
open MIPStarRE.LDT.Pasting (GHatOutcome SliceQuestion)
open MIPRE.LIDT.Co (SymModel SubMeas IdxSubMeas IdxMeas ProjSubMeas IdxPolyFamily postprocess
  completeSubMeas)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Aggregate the polynomial outcomes of `G^x` into its complete part `G^x`. -/
noncomputable def completePartSubMeas (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (x : Fq params) : SubMeas Unit 𝔓 :=
  postprocess ((family.meas x).toSubMeas) (fun _ => ())

/-- The total operator of the complete part is the original slice total. -/
@[simp] theorem completePartSubMeas_total (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (x : Fq params) :
    (completePartSubMeas params family x).total = (family.meas x).total :=
  rfl

/-- The unique outcome of the complete part equals its total operator. -/
@[simp] theorem completePartSubMeas_outcome_unit (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (x : Fq params) :
    (completePartSubMeas params family x).outcome () =
      (completePartSubMeas params family x).total := by
  rw [← (completePartSubMeas params family x).sum_eq_total, Fintype.sum_unique]

/-- Placeholder for the incomplete part `G^x_⊥ = I - G^x`. -/
noncomputable def incompletePartSubMeas (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (x : Fq params) : SubMeas Unit 𝔓 :=
  let X := 1 - (completePartSubMeas params family x).total
  SubMeas.singleOutcome X
    (sub_nonneg.mpr (completePartSubMeas params family x).total_le_one)
    (sub_le_self _ (completePartSubMeas params family x).total_nonneg)

/-- Complete each projective slice submeasurement by adjoining the failure outcome. -/
noncomputable def gHatIdxMeas (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) :
    IdxMeas (Fq params) (GHatOutcome params) 𝔓 :=
  fun x => completeSubMeas ((family.meas x).toSubMeas)

/-- Each completed `\widehat G` outcome is projective. -/
theorem gHatIdxMeas_proj
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (x : Fq params) (g : GHatOutcome params) :
    (gHatIdxMeas params family x).outcome g * (gHatIdxMeas params family x).outcome g =
      (gHatIdxMeas params family x).outcome g := by
  cases g with
  | none =>
      change (1 - (family.meas x).total) * (1 - (family.meas x).total) =
        1 - (family.meas x).total
      rw [sub_mul, one_mul, mul_sub, mul_one, ProjSubMeas.total_proj, sub_self, sub_zero]
  | some p => exact (family.meas x).proj p

/-- Left tensor-placement for the complete part `G^x` on the bipartite space. -/
noncomputable def completePartLeftFamily (S : SymModel 𝔓 K) (params : Parameters)
    [FieldModel params.q] (family : IdxPolyFamily params 𝔓) :
    IdxSubMeas (SliceQuestion params) Unit (K →L[ℂ] K) :=
  fun x => S.leftPlacedSubMeas (completePartSubMeas params family x)

/-- Right tensor-placement for the complete part `G^x` on the bipartite space. -/
noncomputable def completePartRightFamily (S : SymModel 𝔓 K) (params : Parameters)
    [FieldModel params.q] (family : IdxPolyFamily params 𝔓) :
    IdxSubMeas (SliceQuestion params) Unit (K →L[ℂ] K) :=
  fun x => S.rightPlacedSubMeas (completePartSubMeas params family x)

/-- Left tensor-placement for the incomplete part `G^x_⊥` on the bipartite space. -/
noncomputable def incompletePartLeftFamily (S : SymModel 𝔓 K) (params : Parameters)
    [FieldModel params.q] (family : IdxPolyFamily params 𝔓) :
    IdxSubMeas (SliceQuestion params) Unit (K →L[ℂ] K) :=
  fun x => S.leftPlacedSubMeas (incompletePartSubMeas params family x)

/-- Right tensor-placement for the incomplete part `G^x_⊥` on the bipartite space. -/
noncomputable def incompletePartRightFamily (S : SymModel 𝔓 K) (params : Parameters)
    [FieldModel params.q] (family : IdxPolyFamily params 𝔓) :
    IdxSubMeas (SliceQuestion params) Unit (K →L[ℂ] K) :=
  fun x => S.rightPlacedSubMeas (incompletePartSubMeas params family x)

end MIPRE.LIDT.Co.Pasting

end
