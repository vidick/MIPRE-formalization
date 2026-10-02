/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
ComparisonLemmas/CommuteGHalfSandwich/Setup/StepLemmas/Split.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.CommuteGHalfSandwich.Setup.Definitions
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.CommuteGHalfSandwich.Setup.SumBounds

@[expose] public section

/-!
# Section 12 pasting: commute G half-sandwich split lemmas

The split reindexing lemmas and the two-term base case for the half-sandwich commutation chain:
the counterpart of the vendored file of the same path under `MIPRE/Background/LIDT/MIPStarRE/LDT/`
in the port of `planning/c6b-plan.md` (milestone M11, section "Port conventions").

The placed families are those of `Setup/Definitions`, which take the symmetric model
`S : SymModel 𝔓 K` as their first explicit argument. The lemmas take `S` in the vendored state's
argument position, second, after `params`, as the split lemmas of `Setup/Definitions` do: the
outcome lemmas `gHatHalfSandwich{Left,Right}_split_outcome_cons` and
`headTail{Ordered,Rotated}Family_split_one_outcome`, whose vendored versions have no state, gain
it there, and `commuteGHalfSandwich_split_iff`, `commuteGHalfSandwich_split_one_iff` and
`commuteGHalfSandwich_core_two` take it where the vendored `ψbi` was. No vendored lemma here has
a swap, density or normalization hypothesis.

The one-tuple outcome lemmas hold by `S.leftTensor_mul_leftTensor` and `mul_one` up to
definitional equality, where the vendored proofs unfold by `simp`. In
`commuteGHalfSandwich_core_two`, the bound `ν₃ ≤ 426 · 2² · m · (…)` uses that each sixteenth
root is nonnegative (`rpow_oneSixteenth_nonneg`), rather than the nonnegativity of the averaged
hypothesis.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel PointTuple uniformDistribution)
open MIPStarRE.LDT.Pasting (GHatOutcome GHatTupleOutcome SliceQuestion SlicePairQuestion
  gHatTupleOutcomeConsEquiv' gHatCommutationError commuteGHalfSandwichError pointTupleConsEquiv
  splitQuestionEquivOne splitOutcomeEquivOne rpow_oneSixteenth_nonneg)
open MIPRE.LIDT.Co (SymModel IdxPolyFamily)
open MIPRE.LIDT.Co.CommutativityPoints (sddOpRel_reindex sddOpRel_congr_outcome)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The outcomes of the `(k + 1)`-fold half-sandwich at the consed question and outcome are
those of the ordered head-tail family. -/
theorem gHatHalfSandwichLeft_split_outcome_cons
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (k : ℕ)
    (q : SliceQuestion params × PointTuple params k)
    (ogs : GHatOutcome params × GHatTupleOutcome params k) :
    (gHatHalfSandwichLeft S params family (k + 1) ((pointTupleConsEquiv params k).symm q)).outcome
        ((gHatTupleOutcomeConsEquiv' params k).symm ogs) =
      (headTailOrderedFamily S params family k q).outcome ogs := by
  have h := gHatHalfSandwichLeft_split_outcome params S family k
    ((pointTupleConsEquiv params k).symm q) ((gHatTupleOutcomeConsEquiv' params k).symm ogs)
  rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h

/-- The outcomes of the rotated `(k + 1)`-fold half-sandwich at the consed question and outcome
are those of the rotated head-tail family. -/
theorem gHatHalfSandwichRight_split_outcome_cons
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (k : ℕ)
    (q : SliceQuestion params × PointTuple params k)
    (ogs : GHatOutcome params × GHatTupleOutcome params k) :
    (gHatHalfSandwichRight S params family (k + 1) ((pointTupleConsEquiv params k).symm q)).outcome
        ((gHatTupleOutcomeConsEquiv' params k).symm ogs) =
      (headTailRotatedFamily S params family k q).outcome ogs := by
  have h := gHatHalfSandwichRight_split_outcome params S family k
    ((pointTupleConsEquiv params k).symm q) ((gHatTupleOutcomeConsEquiv' params k).symm ogs)
  rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h

/-- At tail length one, the ordered head-tail family is the ordered pair product. -/
theorem headTailOrderedFamily_split_one_outcome
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (q : SlicePairQuestion params)
    (og : GHatOutcome params × GHatOutcome params) :
    (headTailOrderedFamily S params family 1 ((splitQuestionEquivOne params).symm q)).outcome
        ((splitOutcomeEquivOne params).symm og) =
      (gHatPairProductLeft S params family q).outcome og := by
  rcases og with ⟨g₁, g₂⟩
  exact (S.leftTensor_mul_leftTensor _ _).trans (congrArg S.L (congrArg (_ * ·) (mul_one _)))

/-- At tail length one, the rotated head-tail family is the reversed pair product. -/
theorem headTailRotatedFamily_split_one_outcome
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (q : SlicePairQuestion params)
    (og : GHatOutcome params × GHatOutcome params) :
    (headTailRotatedFamily S params family 1 ((splitQuestionEquivOne params).symm q)).outcome
        ((splitOutcomeEquivOne params).symm og) =
      (gHatPairProductRight S params family q).outcome og := by
  rcases og with ⟨g₁, g₂⟩
  exact (S.leftTensor_mul_leftTensor _ _).trans (congrArg S.L (congrArg (· * _) (mul_one _)))

/-- The half-sandwich commutation relation on `(k + 1)`-tuples is equivalent to the head-tail
relation obtained by splitting off the first coordinate. -/
theorem commuteGHalfSandwich_split_iff
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (k : ℕ) (δ : ℝ) :
    S.SDDOpRel
      (uniformDistribution (PointTuple params (k + 1)))
      (gHatHalfSandwichLeft S params family (k + 1))
      (gHatHalfSandwichRight S params family (k + 1))
      δ ↔
    S.SDDOpRel
      (uniformDistribution (SliceQuestion params × PointTuple params k))
      (headTailOrderedFamily S params family k)
      (headTailRotatedFamily S params family k)
      δ := by
  let e := pointTupleConsEquiv params k
  let e' := gHatTupleOutcomeConsEquiv' params k
  rw [sddOpRel_uniform_equiv e S.toVecState]
  constructor
  · intro h
    exact sddOpRel_congr_outcome S.toVecState _ _ _ _ _ δ
      (gHatHalfSandwichLeft_split_outcome_cons params S family k)
      (gHatHalfSandwichRight_split_outcome_cons params S family k)
      (sddOpRel_reindex e' S.toVecState _ _ _ δ h)
  · intro h
    exact sddOpRel_congr_outcome S.toVecState _ _ _ _ _ δ
      (fun q gs => (gHatHalfSandwichLeft_split_outcome_cons params S family k q (e' gs)).symm.trans
        (congrArg _ (e'.symm_apply_apply gs)))
      (fun q gs => (gHatHalfSandwichRight_split_outcome_cons params S family k q (e' gs)).symm.trans
        (congrArg _ (e'.symm_apply_apply gs)))
      (sddOpRel_reindex e'.symm S.toVecState _ _ _ δ h)

/-- At tail length one, the head-tail commutation relation is equivalent to the commutation of
completed-slice pairs. -/
theorem commuteGHalfSandwich_split_one_iff
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (δ : ℝ) :
    S.SDDOpRel
      (uniformDistribution (SliceQuestion params × PointTuple params 1))
      (headTailOrderedFamily S params family 1)
      (headTailRotatedFamily S params family 1)
      δ ↔
    S.SDDOpRel
      (uniformDistribution (SlicePairQuestion params))
      (gHatPairProductLeft S params family)
      (gHatPairProductRight S params family)
      δ := by
  let e := splitQuestionEquivOne params
  let e' := splitOutcomeEquivOne params
  rw [sddOpRel_uniform_equiv e S.toVecState]
  constructor
  · intro h
    exact sddOpRel_congr_outcome S.toVecState _ _ _ _ _ δ
      (headTailOrderedFamily_split_one_outcome params S family)
      (headTailRotatedFamily_split_one_outcome params S family)
      (sddOpRel_reindex e' S.toVecState _ _ _ δ h)
  · intro h
    exact sddOpRel_congr_outcome S.toVecState _ _ _ _ _ δ
      (fun q og => (headTailOrderedFamily_split_one_outcome params S family q (e' og)).symm.trans
        (congrArg _ (e'.symm_apply_apply og)))
      (fun q og => (headTailRotatedFamily_split_one_outcome params S family q (e' og)).symm.trans
        (congrArg _ (e'.symm_apply_apply og)))
      (sddOpRel_reindex e'.symm S.toVecState _ _ _ δ h)

/-- Base case `k = 2` of the half-sandwich commutation: the commutation of completed-slice pairs
gives the commutation of the two-fold half-sandwich at the displayed error. -/
theorem commuteGHalfSandwich_core_two
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ)
    (hcom : S.SDDOpRel
      (uniformDistribution (SlicePairQuestion params))
      (gHatPairProductLeft S params family)
      (gHatPairProductRight S params family)
      (gHatCommutationError params gamma zeta)) :
    S.SDDOpRel
      (uniformDistribution (PointTuple params 2))
      (gHatHalfSandwichLeft S params family 2)
      (gHatHalfSandwichRight S params family 2)
      (commuteGHalfSandwichError params gamma zeta 2) := by
  have hpoint := (commuteGHalfSandwich_split_iff params S family 1 _).2
    ((commuteGHalfSandwich_split_one_iff params S family _).2 hcom)
  have hX : 0 ≤ (params.m : ℝ) *
      (Real.rpow gamma (1 / (16 : ℝ)) + Real.rpow zeta (1 / (16 : ℝ)) +
        Real.rpow ((params.d : ℝ) / (params.q : ℝ)) (1 / (16 : ℝ))) :=
    mul_nonneg (Nat.cast_nonneg _) (add_nonneg (add_nonneg (rpow_oneSixteenth_nonneg _)
      (rpow_oneSixteenth_nonneg _)) (rpow_oneSixteenth_nonneg _))
  refine ⟨hpoint.squaredDistanceBound.trans ?_⟩
  simp only [gHatCommutationError, commuteGHalfSandwichError]
  push_cast
  linarith

end MIPRE.LIDT.Co.Pasting

end
