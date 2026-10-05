/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
ComparisonLemmas/CommuteGHalfSandwich/MoveChain/Lifting.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.CommuteGHalfSandwich.MoveChain.Base
public import MIPStarRE.LDT.Pasting.ComparisonLemmas.CommuteGHalfSandwich.MoveChain.Lifting

@[expose] public section

/-!
# Section 12 pasting: half-sandwich lifting constructions

The lifted operator families that transport an `r`-step half-sandwich move comparison to the
corresponding `(r + 1)`-step comparison: the counterpart of the vendored file of the same path
under `MIPRE/Background/LIDT/MIPStarRE/LDT/` in the port of `planning/c6b-plan.md` (milestone
M11, section "Port conventions").

The question and outcome equivalences are classical and imported from the vendored file. The
placed families take the symmetric model `S : SymModel 𝔓 K` as their first explicit argument, as
those of `Setup/Definitions` do: `commuteGHalfSandwich_prefixSecondSliceLeftFamily S params family
r F`, `commuteGHalfSandwich_secondSliceLiftFamily S params family r F` and
`commuteGHalfSandwich_moveChainLiftFamily S params family r F`. The reindexed family
`commuteGHalfSandwich_splitSuccLiftFamily params r F` places nothing and is generic over the
operator type. The lemmas take `S` second, after `params`, where the vendored `ψbi` was; the
three outcome identities, whose vendored versions have no state
(`commuteGHalfSandwich_prefixSecondSliceLeft_splitSuccLift_eq_secondSliceLift`,
`commuteGHalfSandwich_moveFamily_eq_moveStepTarget` and
`commuteGHalfSandwich_moveChainLift_moveFamily_eq_moveStepMid`), gain it there. No vendored lemma
here has a swap, density or normalization hypothesis.

The two lifts by a left completed-slice factor are the vendored route: the sandwich
`Preliminaries.cabApproxDelta_raw` by the placed slice, whose contraction bound is
`CommutativityPoints.liftLeft_sum_adjoint_mul_le_one`, then `sddOpRel_reindex` along the vendored
outcome equivalence and `sddOpRel_congr_outcome`, the outcomes agreeing by definitional equality
where the vendored proofs unfold by `simp`. Of the outcome identities, the first holds by `rfl`,
the second by `S.rightTensor_mul_rightTensor` and one association, the third by two
associations, through `Fin.cons` and `pointTupleTail` up to definitional equality.

## Not ported

- `swappedFrontQuestionEquiv`: classical, imported.
- `swappedFrontOutcomeEquiv`: classical, imported.
- `moveTailSwappedFrontQuestionEquiv`: classical, imported.
- `moveTailSwappedFrontOutcomeEquiv`: classical, imported.
- `commuteGHalfSandwich_moveChainLiftQuestionEquiv`: classical, imported.
- `commuteGHalfSandwich_moveChainLiftOutcomeEquiv`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel PointTuple uniformDistribution)
open MIPStarRE.LDT.Pasting (GHatOutcome GHatTupleOutcome SliceQuestion MoveQ MoveO
  pointTupleTail gHatTupleOutcomeTail gHatSelfConsistencyError splitQuestionEquiv
  prefixTripleOutcomeEquiv splitSuccQuestionEquiv splitSuccOutcomeEquiv moveTailQuestionEquiv
  moveTailOutcomeEquiv commuteGHalfSandwich_moveChainLiftQuestionEquiv
  commuteGHalfSandwich_moveChainLiftOutcomeEquiv)
open MIPRE.LIDT.Co (SymModel IdxOpFamily IdxPolyFamily)
open MIPRE.LIDT.Co.CommutativityPoints (sddOpRel_reindex sddOpRel_congr_outcome
  liftLeft_sum_adjoint_mul_le_one)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ## Lifting families for the half-sandwich chain -/

/-- Reindex an `r`-move operator family along the split-successor equivalences. -/
def commuteGHalfSandwich_splitSuccLiftFamily {R : Type*}
    (params : Parameters) [FieldModel params.q]
    (r : ℕ)
    (F : IdxOpFamily (MoveQ params r) (MoveO params r) R) :
    IdxOpFamily
      (SliceQuestion params × PointTuple params (r + 1))
      (GHatOutcome params × GHatTupleOutcome params (r + 1))
      R :=
  fun q =>
    { outcome := fun ogs =>
        (F ((splitSuccQuestionEquiv params r) q)).outcome ((splitSuccOutcomeEquiv params r) ogs)
      total := (F ((splitSuccQuestionEquiv params r) q)).total }

/-- Add a completed-slice factor on the left of an operator family, with the new
slice coordinate placed in the second distinguished position. -/
noncomputable def commuteGHalfSandwich_prefixSecondSliceLeftFamily (S : SymModel 𝔓 K)
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (r : ℕ)
    (F : IdxOpFamily
      (SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatTupleOutcome params r)
      (K →L[ℂ] K)) :
    IdxOpFamily (MoveQ params r) (MoveO params r) (K →L[ℂ] K) :=
  fun q =>
    { outcome := fun ogs =>
        S.L ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          (F (q.1, q.2.2)).outcome (ogs.1, ogs.2.2)
      total :=
        S.L (gHatIdxMeas params family q.2.1).total * (F (q.1, q.2.2)).total }

/-- A comparison of head-tail families persists after left multiplication by the completed slice
at a new second distinguished coordinate. -/
theorem commuteGHalfSandwich_prefixSecondSliceLeftLift
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (r : ℕ)
    (A B : IdxOpFamily
      (SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatTupleOutcome params r)
      (K →L[ℂ] K))
    (δ : ℝ)
    (hAB : S.SDDOpRel
      (uniformDistribution (SliceQuestion params × PointTuple params r))
      A B δ) :
    S.SDDOpRel
      (uniformDistribution (MoveQ params r))
      (commuteGHalfSandwich_prefixSecondSliceLeftFamily S params family r A)
      (commuteGHalfSandwich_prefixSecondSliceLeftFamily S params family r B)
      δ := by
  have hABtriple := (sddOpRel_uniform_equiv (splitQuestionEquiv params r) S.toVecState
    (fun q => A q.1) (fun q => B q.1) δ).1
    (sddOpRel_uniform_fst (β := SliceQuestion params) S.toVecState A B δ hAB)
  let C : MoveQ params r → (GHatOutcome params × GHatTupleOutcome params r) →
      GHatOutcome params → K →L[ℂ] K :=
    fun q _ gy => S.L ((gHatIdxMeas params family q.2.1).outcome gy)
  have hC : ∀ q a, ∑ gy : GHatOutcome params, star (C q a gy) * C q a gy ≤ 1 :=
    fun q _ => liftLeft_sum_adjoint_mul_le_one S (gHatIdxMeas params family q.2.1).toSubMeas
  have hcab := Preliminaries.cabApproxDelta_raw S.toVecState
    (uniformDistribution (MoveQ params r)) _ _ C δ hABtriple hC
  refine sddOpRel_congr_outcome S.toVecState _ _ _
    (commuteGHalfSandwich_prefixSecondSliceLeftFamily S params family r A)
    (commuteGHalfSandwich_prefixSecondSliceLeftFamily S params family r B) _ ?_ ?_
    (sddOpRel_reindex (prefixTripleOutcomeEquiv params r) S.toVecState _ _ _ _ hcab) <;>
  exact fun _ _ => rfl

/-- A comparison of `r`-move families persists after reindexing both along the split-successor
equivalences. -/
theorem commuteGHalfSandwich_splitSuccLift
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (r : ℕ)
    (A B : IdxOpFamily (MoveQ params r) (MoveO params r) (K →L[ℂ] K))
    (δ : ℝ)
    (hAB : S.SDDOpRel (uniformDistribution (MoveQ params r)) A B δ) :
    S.SDDOpRel
      (uniformDistribution (SliceQuestion params × PointTuple params (r + 1)))
      (commuteGHalfSandwich_splitSuccLiftFamily params r A)
      (commuteGHalfSandwich_splitSuccLiftFamily params r B)
      δ :=
  (sddOpRel_uniform_equiv (splitSuccQuestionEquiv params r) S.toVecState
    (commuteGHalfSandwich_splitSuccLiftFamily params r A)
    (commuteGHalfSandwich_splitSuccLiftFamily params r B) δ).2
    (sddOpRel_reindex (splitSuccOutcomeEquiv params r).symm S.toVecState _ A B δ hAB)

/-- Lift an `r`-move operator family to the `(r+1)`-move questions by inserting
the new second distinguished slice factor. -/
noncomputable def commuteGHalfSandwich_secondSliceLiftFamily (S : SymModel 𝔓 K)
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (r : ℕ)
    (F : IdxOpFamily (MoveQ params r) (MoveO params r) (K →L[ℂ] K)) :
    IdxOpFamily (MoveQ params (r + 1)) (MoveO params (r + 1)) (K →L[ℂ] K) :=
  fun q =>
    { outcome := fun ogs =>
        S.L ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          (F (q.1, q.2.2 0, pointTupleTail q.2.2)).outcome
            (ogs.1, ogs.2.2 0, gHatTupleOutcomeTail ogs.2.2)
      total :=
        S.L (gHatIdxMeas params family q.2.1).total *
          (F (q.1, q.2.2 0, pointTupleTail q.2.2)).total }

/-- Prefixing the second slice to the split-successor reindexing is the second-slice lift. -/
theorem commuteGHalfSandwich_prefixSecondSliceLeft_splitSuccLift_eq_secondSliceLift
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (r : ℕ)
    (F : IdxOpFamily (MoveQ params r) (MoveO params r) (K →L[ℂ] K))
    (q : MoveQ params (r + 1))
    (ogs : MoveO params (r + 1)) :
    (commuteGHalfSandwich_prefixSecondSliceLeftFamily S params family (r + 1)
      (commuteGHalfSandwich_splitSuccLiftFamily params r F) q).outcome ogs =
      (commuteGHalfSandwich_secondSliceLiftFamily S params family r F q).outcome ogs :=
  rfl

/-- The `(r + 1)`-move family is the move-step target family, after exposing the first tail
coordinate. -/
theorem commuteGHalfSandwich_moveFamily_eq_moveStepTarget
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (r : ℕ)
    (q : MoveQ params (r + 1))
    (ogs : MoveO params (r + 1)) :
    (commuteGHalfSandwich_moveFamily S params family (r + 1) q).outcome ogs =
      (commuteGHalfSandwich_moveStepTargetFamily S params family r
        ((moveTailQuestionEquiv params r) q)).outcome
        ((moveTailOutcomeEquiv params r) ogs) :=
  (congrArg (_ * ·) (S.rightTensor_mul_rightTensor _ _).symm).trans (mul_assoc _ _ _).symm

/-- Lift an `r`-move chain family by adjoining a new leading completed-slice
factor on the left tensor register. -/
noncomputable def commuteGHalfSandwich_moveChainLiftFamily (S : SymModel 𝔓 K)
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (r : ℕ)
    (F : IdxOpFamily (MoveQ params r) (MoveO params r) (K →L[ℂ] K)) :
    IdxOpFamily (MoveQ params (r + 1)) (MoveO params (r + 1)) (K →L[ℂ] K) :=
  fun q =>
    { outcome := fun ogs =>
        S.L ((gHatIdxMeas params family q.1).outcome ogs.1) *
          (F (q.2.1, q.2.2 0, pointTupleTail q.2.2)).outcome
            (ogs.2.1, ogs.2.2 0, gHatTupleOutcomeTail ogs.2.2)
      total :=
        S.L (gHatIdxMeas params family q.1).total *
          (F (q.2.1, q.2.2 0, pointTupleTail q.2.2)).total }

/-- A comparison of `r`-move families persists after the move-chain lift by a new leading
completed-slice factor. -/
theorem commuteGHalfSandwich_moveChainLift
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (r : ℕ)
    (A B : IdxOpFamily (MoveQ params r) (MoveO params r) (K →L[ℂ] K))
    (δ : ℝ)
    (hAB : S.SDDOpRel (uniformDistribution (MoveQ params r)) A B δ) :
    S.SDDOpRel
      (uniformDistribution (MoveQ params (r + 1)))
      (commuteGHalfSandwich_moveChainLiftFamily S params family r A)
      (commuteGHalfSandwich_moveChainLiftFamily S params family r B)
      δ := by
  have hABlift := (sddOpRel_uniform_equiv (commuteGHalfSandwich_moveChainLiftQuestionEquiv
    params r) S.toVecState (fun q => A q.1) (fun q => B q.1) δ).1
    (sddOpRel_uniform_fst (β := SliceQuestion params) S.toVecState A B δ hAB)
  let C : MoveQ params (r + 1) → MoveO params r → GHatOutcome params → K →L[ℂ] K :=
    fun q _ g₁ => S.L ((gHatIdxMeas params family q.1).outcome g₁)
  have hC : ∀ q a, ∑ g₁ : GHatOutcome params, star (C q a g₁) * C q a g₁ ≤ 1 :=
    fun q _ => liftLeft_sum_adjoint_mul_le_one S (gHatIdxMeas params family q.1).toSubMeas
  have hcab := Preliminaries.cabApproxDelta_raw S.toVecState
    (uniformDistribution (MoveQ params (r + 1))) _ _ C δ hABlift hC
  refine sddOpRel_congr_outcome S.toVecState _ _ _
    (commuteGHalfSandwich_moveChainLiftFamily S params family r A)
    (commuteGHalfSandwich_moveChainLiftFamily S params family r B) _ ?_ ?_
    (sddOpRel_reindex (commuteGHalfSandwich_moveChainLiftOutcomeEquiv params r) S.toVecState
      _ _ _ _ hcab) <;>
  exact fun _ _ => rfl

/-- The move-chain lift of the `r`-move family is the move-step middle family, after exposing
the first tail coordinate. -/
theorem commuteGHalfSandwich_moveChainLift_moveFamily_eq_moveStepMid
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (r : ℕ)
    (q : MoveQ params (r + 1))
    (ogs : MoveO params (r + 1)) :
    (commuteGHalfSandwich_moveChainLiftFamily S params family r
      (commuteGHalfSandwich_moveFamily S params family r) q).outcome ogs =
      (commuteGHalfSandwich_moveStepMidFamily S params family r
        ((moveTailQuestionEquiv params r) q)).outcome
        ((moveTailOutcomeEquiv params r) ogs) :=
  (mul_assoc _ _ _).symm.trans (congrArg (· * _) (mul_assoc _ _ _).symm)

/-- The last edge of the move chain: the move-chain lift of the `r`-move family is close to the
`(r + 1)`-move family, at the self-consistency error. -/
theorem commuteGHalfSandwich_moveChainLift_moveFamily_last
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (zeta : ℝ) (r : ℕ)
    (hsc : S.SDDRel
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily S params family)
      (gHatSelfConsistencyRightFamily S params family)
      (gHatSelfConsistencyError zeta)) :
    S.SDDOpRel
      (uniformDistribution (MoveQ params (r + 1)))
      (commuteGHalfSandwich_moveChainLiftFamily S params family r
        (commuteGHalfSandwich_moveFamily S params family r))
      (commuteGHalfSandwich_moveFamily S params family (r + 1))
      (gHatSelfConsistencyError zeta) := by
  have hmid := (sddOpRel_uniform_equiv (moveTailQuestionEquiv params r) S.toVecState
    (fun q => commuteGHalfSandwich_moveStepMidFamily S params family r
      ((moveTailQuestionEquiv params r) q))
    (fun q => commuteGHalfSandwich_moveStepTargetFamily S params family r
      ((moveTailQuestionEquiv params r) q))
    (gHatSelfConsistencyError zeta)).2
    (commuteGHalfSandwich_moveStepMid_toTarget params S family zeta r hsc)
  exact sddOpRel_congr_outcome S.toVecState _ _ _
    (commuteGHalfSandwich_moveChainLiftFamily S params family r
      (commuteGHalfSandwich_moveFamily S params family r))
    (commuteGHalfSandwich_moveFamily S params family (r + 1)) _
    (fun q ogs => (commuteGHalfSandwich_moveChainLift_moveFamily_eq_moveStepMid
      params S family r q ogs).symm)
    (fun q ogs => (commuteGHalfSandwich_moveFamily_eq_moveStepTarget params S family r q ogs).symm)
    (sddOpRel_reindex (moveTailOutcomeEquiv params r).symm S.toVecState _ _ _ _ hmid)

end MIPRE.LIDT.Co.Pasting

end
