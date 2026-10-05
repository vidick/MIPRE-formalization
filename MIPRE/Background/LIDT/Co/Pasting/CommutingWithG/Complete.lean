/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
CommutingWithG/Complete.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored
file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.Main.Results
public import MIPRE.Background.LIDT.Co.Pasting.SwitcherooCompletion
public import MIPRE.Background.LIDT.Co.Preliminaries.CompletionTransfer
public import MIPStarRE.LDT.Pasting.CommutingWithG.Complete

@[expose] public section

/-!
# Section 12 pasting: commuting-with-G complete part

Complete-part commuting-with-`G` bounds, `cor:commuting-with-G-complete`: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/CommutingWithG/Complete.lean` in the port of
`planning/c6b-plan.md` (milestone M11, section "Port conventions").

A strategy is a `SymStrat params.next 𝔓 K` and the slice family an `IdxPolyFamily params 𝔓`; the
placed families take `strategy.state` as their first explicit argument. The vendored proofs read
`strategy.isNormalized`, `strategy.densityFixed` and `strategy.permInvState` only to pass them to
`commutativitySwitcheroo_ofCompleteSelfConsistency`, `Commutativity.comMain` and
`gCompleteSelfConsistency`, whose ported forms take no such hypothesis (section "Swap symmetry is
a theorem"), so the statements here are the vendored ones, translated, and the proofs no longer
read those fields.

The two switcheroo applications are as in the vendored proof: the first, on `M = G`, gives the
point-with-complete-part bound after swapping the two questions and the two families
(`sddOpRel_swap_questions`, `Preliminaries.sddOpRel_symm`); the second, on the complete-part
family, gives the total-product bound. The comparisons with `thm:com-main` and between the
placed families hold by definition, where the vendored proof unfolds them under `simpa`.

The scalar bound `secondSwitcherooError_le_commutingWithGCompleteError` mentions no state,
operator or measurement, so it is classical: this file imports the vendored file for it, and
dependants name it through an explicit `open MIPStarRE.LDT.Pasting (…)` list.

## Not ported

- `secondSwitcherooError_le_commutingWithGCompleteError`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel uniformDistribution)
open MIPStarRE.LDT.Pasting (SlicePairQuestion commutativitySwitcherooError
  commutingWithGCompleteError pairwiseCompletePartCommutationError
  firstSwitcherooError_le_commutingWithGCompleteError
  secondSwitcherooError_le_commutingWithGCompleteError)
open MIPRE.LIDT.Co (SymStrat IdxPolyFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Internal form of `cor:commuting-with-G-complete` after applying
`thm:com-main` and `lem:g-complete-self-consistency`.

**Source:** The proof in `references/ldt-paper/ld-pasting.tex:721-774`
uses `thm:com-main`, `lem:commutativity-switcheroo`, and
`lem:g-complete-self-consistency` internally.  The paper-facing theorem
`commutingWithGComplete` below derives the first and third inputs from the
source hypotheses rather than exposing them as public hypotheses. -/
theorem commutingWithGComplete_ofComMainAndSelfConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ)
    (hgamma_nonneg : 0 ≤ gamma) (hgamma : gamma ≤ 1)
    (hzeta_nonneg : 0 ≤ zeta) (hzeta : zeta ≤ 1)
    (hd_le_q : params.d ≤ params.q)
    (hcom : Commutativity.ComMainConclusion params strategy family gamma zeta)
    (hself : GCompleteSelfConsistencyStatement params strategy.state family zeta) :
    CommutingWithGCompleteStatement params strategy.state family gamma zeta := by
  have hswitch₁ :
      CommutativitySwitcherooStatement params strategy.state family family.meas
        zeta zeta (pairwiseCompletePartCommutationError params gamma zeta) :=
    commutativitySwitcheroo_ofCompleteSelfConsistency params strategy.state family family.meas
      zeta zeta (pairwiseCompletePartCommutationError params gamma zeta)
      hself hself.completePartSelfConsistency hcom
  have hpoint_raw :
      strategy.state.SDDOpRel
        (uniformDistribution (SlicePairQuestion params))
        (completePartPointProductLeft strategy.state params family)
        (completePartPointProductRight strategy.state params family)
        (commutativitySwitcherooError zeta zeta
          (pairwiseCompletePartCommutationError params gamma zeta)) :=
    Preliminaries.sddOpRel_symm strategy.state.toVecState
      (uniformDistribution (SlicePairQuestion params))
      (fun q => switcherooAggregateLeft strategy.state params family family.meas (q.2, q.1))
      (fun q => switcherooAggregateRight strategy.state params family family.meas (q.2, q.1))
      _
      (sddOpRel_swap_questions params strategy.state.toVecState
        (switcherooAggregateLeft strategy.state params family family.meas)
        (switcherooAggregateRight strategy.state params family family.meas)
        _ hswitch₁.aggregateCommutation)
  have hswitch₂ :
      CommutativitySwitcherooStatement params strategy.state family
        (completePartProjFamily params family) zeta zeta
        (commutativitySwitcherooError zeta zeta
          (pairwiseCompletePartCommutationError params gamma zeta)) :=
    commutativitySwitcheroo_ofCompleteSelfConsistency params strategy.state family
      (completePartProjFamily params family) zeta zeta _ hself
      (completePartProjFamily_selfConsistency params strategy family zeta hself)
      (pointWithCompletePart_as_switcheroo_input params strategy.state family _ hpoint_raw)
  refine ⟨hcom, ?_, ?_⟩
  · exact Preliminaries.sddOpRel_mono strategy.state.toVecState _ _ _ _ _ hpoint_raw
      (firstSwitcherooError_le_commutingWithGCompleteError params gamma zeta
        hgamma_nonneg hgamma hzeta_nonneg hzeta hd_le_q)
  · exact Preliminaries.sddOpRel_mono strategy.state.toVecState _ _ _ _ _
      (completePartAggregateCommutation_as_total params strategy.state family _
        hswitch₂.aggregateCommutation)
      (secondSwitcherooError_le_commutingWithGCompleteError params gamma zeta
        hgamma_nonneg hzeta_nonneg hzeta hd_le_q)

/-- `cor:commuting-with-G-complete`, source-facing form. -/
theorem commutingWithGComplete
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (eps delta gamma zeta : ℝ)
    (hgamma_nonneg : 0 ≤ gamma) (hgamma : gamma ≤ 1)
    (hzeta_nonneg : 0 ≤ zeta) (hzeta : zeta ≤ 1)
    (hd_le_q : params.d ≤ params.q)
    (hgood : strategy.IsGood eps delta gamma)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    CommutingWithGCompleteStatement params strategy.state family gamma zeta :=
  commutingWithGComplete_ofComMainAndSelfConsistency params strategy family gamma zeta
    hgamma_nonneg hgamma hzeta_nonneg hzeta hd_le_q
    (Commutativity.comMain params strategy eps delta gamma zeta hgood family hcons hself hbound)
    (gCompleteSelfConsistency params strategy.state family zeta hself)

end MIPRE.LIDT.Co.Pasting

end
