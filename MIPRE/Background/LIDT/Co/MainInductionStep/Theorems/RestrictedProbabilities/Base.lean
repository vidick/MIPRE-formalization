/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
MainInductionStep/Theorems/RestrictedProbabilities/Base.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.MainInductionStep.Statements
public import MIPRE.Background.LIDT.Co.Test.StrategyFailures
public import MIPRE.Background.LIDT.Co.CommutativityPoints.Approximation
public import MIPRE.Background.LIDT.MIPStarRE.LDT.MainInductionStep.Theorems.RestrictedProbabilities.Base

@[expose] public section

/-!
# Section 6 — Restricted probability common lemmas

The averaging and scalar normalization lemmas shared by the axis-parallel, diagonal and
answer-valued restricted-probability bounds: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/MainInductionStep/Theorems/RestrictedProbabilities/Base.lean`
in the port of `planning/c6b-plan.md` (milestone M12, section "Port conventions").

A strategy is a `SymStrat params.next 𝔓 K` (`Co/Test/StrategyCore.lean`), whose state is the
symmetric model `strategy.state : SymModel 𝔓 K`; the self-consistency surrogate is the bipartite
SSC error of that model (`Co/Test/StrategyFailures.lean`), and restricting a strategy to a slice
keeps its state (`xRestrictedStrategy_state`, by `rfl`).

All of the vendored file but `selfConsistencyRestrictedAverage_eq` is classical: the reindexing
equivalence and averages of a restriction height appended to a point or a restricted diagonal
sample, and the scalar lemmas on the transverse-direction weight and the conditioning loss. This
file imports the vendored file for them; they are reached in the Co namespace through an explicit
`open MIPStarRE.LDT.MainInductionStep (…)` list.

## Not ported

- `pointAppendProdEquiv`: classical, imported.
- `avgOver_uniform_pointAppend_prod`: classical, imported.
- `avgOver_uniform_restrictedDiagonalSample_append`: classical, imported.
- `weighted_embedded_average_le_full_average`: classical, imported.
- `weighted_bound_to_average`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/inductive_step.tex`
- `blueprint/src/chapter/ch10_induction.tex`
-/

namespace MIPRE.LIDT.Co.MainInductionStep

open MIPStarRE.LDT (Parameters FieldModel Point Fq avgOver uniformDistribution)
open MIPStarRE.LDT.CommutativityPoints (avgOver_uniform_pointNext_decompose)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Averaging the self-consistency defect over all horizontal restrictions
recovers the ambient self-consistency defect. -/
theorem selfConsistencyRestrictedAverage_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) :
    avgOver (uniformDistribution (Fq params))
        (fun x => (xRestrictedStrategy params strategy x).selfConsistencyFailureProbability) =
      strategy.selfConsistencyFailureProbability :=
  (avgOver_uniform_pointNext_decompose params
    (fun u => strategy.state.qBipartiteSSCDefect (strategy.pointMeasurement u).toSubMeas)).symm

end MIPRE.LIDT.Co.MainInductionStep

end
