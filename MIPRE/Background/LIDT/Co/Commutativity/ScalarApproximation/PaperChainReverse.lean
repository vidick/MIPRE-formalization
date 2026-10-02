/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/ScalarApproximation/PaperChainReverse.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.ScalarApproximation.PaperChainPhaseSix
public import MIPRE.Background.LIDT.Co.Commutativity.ScalarApproximation.PaperChainPhaseSeven

@[expose] public section

/-!
# Section 11 commutativity: the reverse insertions of the evaluated-slice paper chain

The two reverse `eq:add-an-a` bounds after the paper line-87 phase-five removal, packaged into
the combined phase-67 bridge consumed by `ProcessedG`: the counterpart of
`Commutativity/ScalarApproximation/PaperChainReverse.lean` under
`MIPRE/Background/LIDT/MIPStarRE/LDT/` in the port of `planning/c6b-plan.md` (milestone M7,
section "Port conventions").

`evaluatedSlice_phaseSixSeven_reverse_bound` drops the vendored hypothesis
`hnorm : strategy.state.IsNormalized`, a theorem of the model, so its arguments are
`params strategy zeta family hcombined_fst hcombined_snd`; the two hypotheses are stated with
`evaluatedPointFamilyLeft strategy.state` and `Preliminaries.totalSandwichFamily strategy.state`,
which take the model explicitly in the port.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Commutativity

open MIPStarRE.LDT (Parameters FieldModel avgOver uniformDistribution)
open MIPStarRE.LDT.Commutativity (EvaluatedSliceQuestion)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Paper lines 99--104: the combined phase-67 reverse-insertion bridge.

The scalar-chain assembly only needs the endpoint comparison from the paper
line-87/`eq:gcom10` term to `eq:gonna-cite-this-in-just-a-bit`.  This lemma
packages the two proved `eq:add-an-a` reverse insertions (`2√ζ` each) through
one triangle inequality, so downstream code no longer has to carry the
intermediate phase-six endpoint. -/
lemma evaluatedSlice_phaseSixSeven_reverse_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (zeta : ℝ)
    (family : IdxPolyFamily params 𝔓)
    (hcombined_fst : strategy.state.SDDRel
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => evaluatedPointFamilyLeft strategy.state params family q.1)
      (fun q =>
        (Preliminaries.totalSandwichFamily strategy.state
          (evaluatedPointFamily params family)
          (evaluatedSlicePointMeas params strategy) q.1))
      (4 * zeta))
    (hcombined_snd : strategy.state.SDDRel
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => evaluatedPointFamilyLeft strategy.state params family q.2)
      (fun q =>
        (Preliminaries.totalSandwichFamily strategy.state
          (evaluatedPointFamily params family)
          (evaluatedSlicePointMeas params strategy) q.2))
      (4 * zeta)) :
    let 𝒟 := uniformDistribution (EvaluatedSliceQuestion params)
    let phase5PaperRemoved : EvaluatedSliceQuestion params → ℝ :=
      evaluatedSlicePhaseFivePaperRemoved params strategy family
    let phase7GonnaCite : EvaluatedSliceQuestion params → ℝ :=
      evaluatedSlicePhaseSevenGonnaCite params strategy family
    |avgOver 𝒟 phase5PaperRemoved - avgOver 𝒟 phase7GonnaCite| ≤
      4 * Real.sqrt zeta :=
  (abs_sub_le _ (avgOver (uniformDistribution (EvaluatedSliceQuestion params))
      (evaluatedSlicePhaseSixFirstRemoved params strategy family)) _).trans <|
    (add_le_add
      (evaluatedSlice_phaseSix_first_reverse_bound params strategy zeta family hcombined_fst)
      (evaluatedSlice_phaseSeven_second_reverse_bound params strategy zeta family
        hcombined_snd)).trans_eq (by ring)

end MIPRE.LIDT.Co.Commutativity

end
