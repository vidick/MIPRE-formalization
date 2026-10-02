/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
GHatFacts.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.CommutingWithG.Incomplete

@[expose] public section

/-!
# Section 12 pasting: G-hat facts

Quadrant decompositions and `\widehat G` bookkeeping facts, `cor:G-hat-facts`: the counterpart
of `MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/GHatFacts.lean` in the port of
`planning/c6b-plan.md` (milestone M11, section "Port conventions").

The vendored second bipartite state `ψbi : QuantumState (ι × ι)` is the symmetric model
`S : SymModel 𝔓 K`, in the vendored argument position, and a strategy is a
`SymStrat params.next 𝔓 K`; the slice family is an `IdxPolyFamily params 𝔓`. The placed
families take `S` as their first explicit argument.

The vendored `gHatFacts` and `gHatFacts_ofComMainAndSelfConsistency` read
`strategy.permInvState` only to pass it to `gCompleteSelfConsistency` and `gBotSelfConsistency`,
whose ported forms take no such hypothesis (section "Swap symmetry is a theorem"), so the
statements here are the vendored ones, translated, and the proofs no longer read that field.

Every outcome of the `\widehat G` pair product is, by definition, the outcome of one of the four
quadrant families, so the quadrant decomposition is a regrouping of the sum over
`Option _ × Option _` with each summand matched by `rfl`, where the vendored proof rebuilds the
outcome functions by `simp`. The swapped incomplete quadrant is the incomplete point quadrant with
the questions and the two families exchanged, so its bound is
`sddOpRel_swap_questions` followed by `Preliminaries.sddOpRel_symm`.

## Not ported

Nothing: every declaration of the vendored file is ported here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel avgOver_add avgOver_congr uniformDistribution)
open MIPStarRE.LDT.Pasting (SliceQuestion SlicePairQuestion commutingWithGCompleteError
  commutingWithGIncompleteError pairwiseCompletePartCommutationError gHatSelfConsistencyError
  gHatCommutationError)
open MIPStarRE.LDT.Commutativity (comMainError)
open MIPRE.LIDT.Co (SymModel VecState SymStrat IdxSubMeas IdxProjSubMeas OpFamily IdxOpFamily
  IdxPolyFamily)
open MIPRE.LIDT.Co.CommutativityPoints (orderedProductOpFamily reversedProductOpFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The pointwise `\widehat G` pair product splits into the complete-complete,
complete-incomplete, incomplete-complete, and incomplete-incomplete quadrants. -/
theorem gHatPairProduct_qSDDOp_decompose
    (params : Parameters)
    [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (q : SlicePairQuestion params) :
    S.qSDDOp
        (gHatPairProductLeft S params family q)
        (gHatPairProductRight S params family q) =
      S.qSDDOp
          (OpFamily.leftPlacedOpFamily S <|
            orderedProductOpFamily
              ((family.meas q.1).toSubMeas)
              ((family.meas q.2).toSubMeas))
          (OpFamily.leftPlacedOpFamily S <|
            reversedProductOpFamily
              ((family.meas q.1).toSubMeas)
              ((family.meas q.2).toSubMeas)) +
        S.qSDDOp
          (incompletePartPointProductLeft S params family q)
          (incompletePartPointProductRight S params family q) +
          S.qSDDOp
            (OpFamily.leftPlacedOpFamily S <|
              multiplyByTotalOnLeft
                (incompletePartSubMeas params family q.1)
                ((family.meas q.2).toSubMeas))
            (OpFamily.leftPlacedOpFamily S <|
              multiplyByTotalOnRight
                ((family.meas q.2).toSubMeas)
                (incompletePartSubMeas params family q.1)) +
        S.qSDDOp
          (incompletePartTotalProductLeft S params family q)
          (incompletePartTotalProductRight S params family q) := by
  -- Each quadrant is the restriction of the summand `F` of the left side to one of the four
  -- parts of `Option _ × Option _`, by definition of `completeSubMeas`.
  set F : MIPStarRE.LDT.Pasting.GHatOutcome params × MIPStarRE.LDT.Pasting.GHatOutcome params →
      ℝ := fun ab =>
    S.ev (star ((gHatPairProductLeft S params family q).outcome ab -
        (gHatPairProductRight S params family q).outcome ab) *
      ((gHatPairProductLeft S params family q).outcome ab -
        (gHatPairProductRight S params family q).outcome ab)) with hF
  have hcomplete : S.qSDDOp
      (OpFamily.leftPlacedOpFamily S <|
        orderedProductOpFamily ((family.meas q.1).toSubMeas) ((family.meas q.2).toSubMeas))
      (OpFamily.leftPlacedOpFamily S <|
        reversedProductOpFamily ((family.meas q.1).toSubMeas) ((family.meas q.2).toSubMeas)) =
      ∑ g, ∑ h, F (some g, some h) :=
    Fintype.sum_prod_type _
  have hincomplete : S.qSDDOp
      (incompletePartPointProductLeft S params family q)
      (incompletePartPointProductRight S params family q) = ∑ g, F (some g, none) := rfl
  have hswapped : S.qSDDOp
      (OpFamily.leftPlacedOpFamily S <|
        multiplyByTotalOnLeft (incompletePartSubMeas params family q.1)
          ((family.meas q.2).toSubMeas))
      (OpFamily.leftPlacedOpFamily S <|
        multiplyByTotalOnRight ((family.meas q.2).toSubMeas)
          (incompletePartSubMeas params family q.1)) = ∑ h, F (none, some h) := rfl
  have htotal : S.qSDDOp
      (incompletePartTotalProductLeft S params family q)
      (incompletePartTotalProductRight S params family q) = F (none, none) :=
    Fintype.sum_unique fun _ : Unit => F (none, none)
  rw [hcomplete, hincomplete, hswapped, htotal]
  change ∑ ab, F ab = _
  rw [Fintype.sum_prod_type, Fintype.sum_option, Fintype.sum_option]
  simp only [Fintype.sum_option, Finset.sum_add_distrib]
  ring

/-- Internal form of `cor:G-hat-facts` after applying
`lem:g-complete-self-consistency`, `cor:g-bot-self-consistency`,
`cor:commuting-with-G-complete`, and `cor:commuting-with-G-incomplete`.

**Source:** The proof in `references/ldt-paper/ld-pasting.tex:817-862`
uses these four preceding Section 12 results internally.  The paper-facing
theorem `gHatFacts` below derives them from the source hypotheses rather than
exposing them as public hypotheses. -/
theorem gHatFacts_ofSelfConsistencyAndCommutation
    (params : Parameters)
    [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ)
    (hgamma_nonneg : 0 ≤ gamma) (hgamma : gamma ≤ 1)
    (hzeta_nonneg : 0 ≤ zeta) (hzeta : zeta ≤ 1)
    (hd_le_q : params.d ≤ params.q)
    (hselfComplete : GCompleteSelfConsistencyStatement params S family zeta)
    (hselfIncomplete : GBotSelfConsistencyStatement params S family zeta)
    (hcommComplete : CommutingWithGCompleteStatement params S family gamma zeta)
    (hcommIncomplete : CommutingWithGIncompleteStatement params S family gamma zeta) :
    GHatFactsStatement params S family gamma zeta := by
  refine ⟨⟨?_⟩, ⟨?_⟩⟩
  · -- Paper reference: `cor:G-hat-facts` in `ld-pasting.tex`. The `\widehat G` defect is the
    -- slice-family defect (the outcomes `some g`) plus the incomplete-part defect (`none`).
    have hsplit :
        S.sddError (uniformDistribution (SliceQuestion params))
            (gHatSelfConsistencyLeftFamily S params family)
            (gHatSelfConsistencyRightFamily S params family) =
          S.sddError (uniformDistribution (SliceQuestion params))
              (IdxSubMeas.liftLeft S (IdxProjSubMeas.toIdxSubMeas family.meas))
              (IdxSubMeas.liftRight S (IdxProjSubMeas.toIdxSubMeas family.meas)) +
            S.sddError (uniformDistribution (SliceQuestion params))
              (incompletePartLeftFamily S params family)
              (incompletePartRightFamily S params family) := by
      unfold VecState.sddError
      rw [← avgOver_add]
      refine avgOver_congr _ _ _ fun x => ?_
      unfold VecState.qSDD VecState.qSDDCore
      rw [Fintype.sum_option, add_comm]
      simp only [Fintype.sum_unique]
      rfl
    rw [hsplit, gHatSelfConsistencyError, two_mul]
    exact add_le_add hselfComplete.completePartSelfConsistency.squaredDistanceBound
      hselfIncomplete.incompletePartSelfConsistency.squaredDistanceBound
  · -- Paper reference: `cor:G-hat-facts` in `ld-pasting.tex`: split the pair product over
    -- `GHatOutcome × GHatOutcome` into the complete, incomplete, swapped and total quadrants.
    let swappedIncompletePointLeft :
        IdxOpFamily (SlicePairQuestion params) (MIPStarRE.LDT.Polynomial params) (K →L[ℂ] K) :=
      fun q =>
        OpFamily.leftPlacedOpFamily S <|
          multiplyByTotalOnLeft
            (incompletePartSubMeas params family q.1)
            ((family.meas q.2).toSubMeas)
    let swappedIncompletePointRight :
        IdxOpFamily (SlicePairQuestion params) (MIPStarRE.LDT.Polynomial params) (K →L[ℂ] K) :=
      fun q =>
        OpFamily.leftPlacedOpFamily S <|
          multiplyByTotalOnRight
            ((family.meas q.2).toSubMeas)
            (incompletePartSubMeas params family q.1)
    -- The swapped quadrant at `(x, y)` is the incomplete point quadrant at `(y, x)`, with the
    -- two families exchanged.
    have hswapIncompleteBound :
        S.SDDOpRel
          (uniformDistribution (SlicePairQuestion params))
          swappedIncompletePointLeft
          swappedIncompletePointRight
          (commutingWithGIncompleteError params gamma zeta) :=
      Preliminaries.sddOpRel_symm S.toVecState
        (uniformDistribution (SlicePairQuestion params))
        (fun q => incompletePartPointProductLeft S params family (q.2, q.1))
        (fun q => incompletePartPointProductRight S params family (q.2, q.1))
        _
        (sddOpRel_swap_questions params S.toVecState
          (incompletePartPointProductLeft S params family)
          (incompletePartPointProductRight S params family)
          _ hcommIncomplete.pointWithIncompletePartCommutation)
    have hdecomp :
        S.sddErrorOp
            (uniformDistribution (SlicePairQuestion params))
            (gHatPairProductLeft S params family)
            (gHatPairProductRight S params family) =
          S.sddErrorOp
              (uniformDistribution (SlicePairQuestion params))
              (fun q =>
                OpFamily.leftPlacedOpFamily S <|
                  orderedProductOpFamily
                    ((family.meas q.1).toSubMeas)
                    ((family.meas q.2).toSubMeas))
              (fun q =>
                OpFamily.leftPlacedOpFamily S <|
                  reversedProductOpFamily
                    ((family.meas q.1).toSubMeas)
                    ((family.meas q.2).toSubMeas)) +
            S.sddErrorOp
              (uniformDistribution (SlicePairQuestion params))
              (incompletePartPointProductLeft S params family)
              (incompletePartPointProductRight S params family) +
            S.sddErrorOp
              (uniformDistribution (SlicePairQuestion params))
              swappedIncompletePointLeft
              swappedIncompletePointRight +
            S.sddErrorOp
              (uniformDistribution (SlicePairQuestion params))
              (incompletePartTotalProductLeft S params family)
              (incompletePartTotalProductRight S params family) := by
      unfold VecState.sddErrorOp
      rw [← avgOver_add, ← avgOver_add, ← avgOver_add]
      exact avgOver_congr _ _ _ fun q => gHatPairProduct_qSDDOp_decompose params S family q
    have hratio_nonneg : 0 ≤ ((params.d : ℝ) / (params.q : ℝ)) := by
      positivity
    have hratio_le_one : ((params.d : ℝ) / (params.q : ℝ)) ≤ 1 := by
      have hq_pos : (0 : ℝ) < params.q := by
        exact_mod_cast params.hq
      exact (div_le_one hq_pos).2 (by exact_mod_cast hd_le_q)
    have hpow : (1 / (16 : ℝ)) ≤ (1 / (4 : ℝ)) := by norm_num
    have hquarter_gamma :
        Real.rpow gamma (1 / (4 : ℝ)) ≤ Real.rpow gamma (1 / (16 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge' hgamma_nonneg hgamma (by norm_num) hpow
    have hquarter_zeta :
        Real.rpow zeta (1 / (4 : ℝ)) ≤ Real.rpow zeta (1 / (16 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge' hzeta_nonneg hzeta (by norm_num) hpow
    have hquarter_ratio :
        Real.rpow (((params.d : ℝ) / (params.q : ℝ))) (1 / (4 : ℝ)) ≤
          Real.rpow (((params.d : ℝ) / (params.q : ℝ))) (1 / (16 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge' hratio_nonneg hratio_le_one (by norm_num) hpow
    have hm_nonneg : 0 ≤ (params.m : ℝ) := by positivity
    rw [hdecomp]
    calc
      _ ≤ pairwiseCompletePartCommutationError params gamma zeta +
            commutingWithGIncompleteError params gamma zeta +
            commutingWithGIncompleteError params gamma zeta +
            commutingWithGIncompleteError params gamma zeta :=
        add_le_add (add_le_add (add_le_add
          hcommComplete.pairwiseCompletePartCommutation.squaredDistanceBound
          hcommIncomplete.pointWithIncompletePartCommutation.squaredDistanceBound)
          hswapIncompleteBound.squaredDistanceBound)
          hcommIncomplete.incompletePartCommutation.squaredDistanceBound
      _ ≤ gHatCommutationError params gamma zeta := by
        simp only [pairwiseCompletePartCommutationError, commutingWithGIncompleteError,
          commutingWithGCompleteError, comMainError, gHatCommutationError]
        linarith [mul_le_mul_of_nonneg_left
          (add_le_add (add_le_add hquarter_gamma hquarter_zeta) hquarter_ratio) hm_nonneg]

/-- `cor:G-hat-facts`, source-facing form. -/
theorem gHatFacts
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
    GHatFactsStatement params strategy.state family gamma zeta :=
  gHatFacts_ofSelfConsistencyAndCommutation params strategy.state family gamma zeta
    hgamma_nonneg hgamma hzeta_nonneg hzeta hd_le_q
    (gCompleteSelfConsistency params strategy.state family zeta hself)
    (gBotSelfConsistency params strategy.state family zeta hself)
    (commutingWithGComplete params strategy family eps delta gamma zeta
      hgamma_nonneg hgamma hzeta_nonneg hzeta hd_le_q hgood hcons hself hbound)
    (commutingWithGIncomplete params strategy family eps delta gamma zeta
      hgamma_nonneg hgamma hzeta_nonneg hzeta hd_le_q hgood hcons hself hbound)

/-- Internal form of `cor:G-hat-facts` after applying `thm:com-main`.

The construction of the `\widehat G` estimates needs the commutativity
conclusion of Section 11 and the strong self-consistency of the slice family.
The full good-strategy hypothesis is therefore not part of this passage; it is
used only upstream when proving `thm:com-main`. -/
theorem gHatFacts_ofComMainAndSelfConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ)
    (hgamma_nonneg : 0 ≤ gamma) (hgamma : gamma ≤ 1)
    (hzeta_nonneg : 0 ≤ zeta) (hzeta : zeta ≤ 1)
    (hd_le_q : params.d ≤ params.q)
    (hcom : Commutativity.ComMainConclusion params strategy family gamma zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    GHatFactsStatement params strategy.state family gamma zeta := by
  have hselfComplete : GCompleteSelfConsistencyStatement params strategy.state family zeta :=
    gCompleteSelfConsistency params strategy.state family zeta hself
  have hcommComplete : CommutingWithGCompleteStatement params strategy.state family gamma zeta :=
    commutingWithGComplete_ofComMainAndSelfConsistency params strategy family gamma zeta
      hgamma_nonneg hgamma hzeta_nonneg hzeta hd_le_q hcom hselfComplete
  exact gHatFacts_ofSelfConsistencyAndCommutation params strategy.state family gamma zeta
    hgamma_nonneg hgamma hzeta_nonneg hzeta hd_le_q
    hselfComplete (gBotSelfConsistency params strategy.state family zeta hself) hcommComplete
    (commutingWithGIncomplete_ofComplete params strategy.state family gamma zeta hcommComplete)

end MIPRE.LIDT.Co.Pasting

end
