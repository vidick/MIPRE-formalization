/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
ComparisonLemmas/CommuteGHalfSandwich/Setup/StepLemmas/Move.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.CommuteGHalfSandwich.Setup.Definitions
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.CommuteGHalfSandwich.Setup.SumBounds

@[expose] public section

/-!
# Section 12 pasting: commute G half-sandwich move lemmas

The move-chain lemmas for the half-sandwich commutation chain: the counterpart of the vendored
file of the same path under `MIPRE/Background/LIDT/MIPStarRE/LDT/` in the port of
`planning/c6b-plan.md` (milestone M11, section "Port conventions"). The split reindexing lemmas
and the two-term base case are in `StepLemmas/Split`.

The placed families are those of `Setup/Definitions`, which take the symmetric model
`S : SymModel 𝔓 K` as their first explicit argument. Every lemma here takes `S` where the vendored
`ψbi` was, second, after `params`: `gHatSelfConsistency_sddOpRel_quadThird params S family zeta r
hsc`, `commuteGHalfSandwich_step_commute params S family gamma zeta r hcom`,
`commuteGHalfSandwich_prefixFirstSliceLeft_move params S family r δ hAB` and
`commuteGHalfSandwich_moveStepMid_toTarget params S family zeta r hsc`. No vendored lemma here has
a swap, density or normalization hypothesis.

Each move is the vendored one: a sandwich by an auxiliary family `C` of contraction norm at most
one (`Preliminaries.cabApproxDelta_raw`), a reindexing of the outcomes
(`CommutativityPoints.sddOpRel_reindex`) and an identification of the outcomes
(`CommutativityPoints.sddOpRel_congr_outcome`). The identifications, which the vendored proofs
carry out by `simp` and calc chains through the Kronecker identities, are here one rewrite each by
`S.leftTensor_mul_leftTensor`, `S.rightTensor_mul_leftTensor_eq_opTensor` or `S.L_comm_R`, the
reindexed families unfolding by definitional equality. The contraction bounds on a single
placement are the private `sum_star_leftTensor_mul_le_one` and `sum_star_rightTensor_mul_le_one`.

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
  gHatSelfConsistencyError gHatCommutationError thirdSliceFrontEquiv pairTailOutcomeEquiv
  firstSliceBackQuestionEquiv firstSliceBackOutcomeEquiv thirdSliceFrontOutcomeEquiv)
open MIPRE.LIDT.Co (SymModel IdxSubMeas IdxOpFamily IdxPolyFamily)
open MIPRE.LIDT.Co.CommutativityPoints (sddOpRel_reindex sddOpRel_congr_outcome
  subMeas_sum_adjoint_mul_le_one)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A family with `∑ p^* p ≤ 1` keeps the bound under left placement. -/
private theorem sum_star_leftTensor_mul_le_one (S : SymModel 𝔓 K) {α : Type*} [Fintype α]
    (p : α → 𝔓) (h : ∑ a : α, star (p a) * p a ≤ 1) :
    ∑ a : α, star (S.L (p a)) * S.L (p a) ≤ 1 := by
  calc
    _ = ∑ a : α, S.L (star (p a) * p a) := Finset.sum_congr rfl fun a _ => by
        rw [S.leftTensor_conjTranspose, S.leftTensor_mul_leftTensor]
    _ = S.L (∑ a : α, star (p a) * p a) := S.leftTensor_finset_sum _ _
    _ ≤ 1 := S.leftTensor_le_one h

/-- A family with `∑ p^* p ≤ 1` keeps the bound under right placement. -/
private theorem sum_star_rightTensor_mul_le_one (S : SymModel 𝔓 K) {α : Type*} [Fintype α]
    (p : α → 𝔓) (h : ∑ a : α, star (p a) * p a ≤ 1) :
    ∑ a : α, star (S.R (p a)) * S.R (p a) ≤ 1 := by
  calc
    _ = ∑ a : α, S.R (star (p a) * p a) := Finset.sum_congr rfl fun a _ => by
        rw [S.rightTensor_conjTranspose, S.rightTensor_mul_rightTensor]
    _ = S.R (∑ a : α, star (p a) * p a) := S.rightTensor_finset_sum _ _
    _ ≤ 1 := S.rightTensor_le_one h

/-- The self-consistency of the completed slices, restated on the quadruple questions
`(x₁, x₂, x₃, xs)` with the slice read at the third coordinate. -/
theorem gHatSelfConsistency_sddOpRel_quadThird
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
      (uniformDistribution (SliceQuestion params × SliceQuestion params ×
        SliceQuestion params × PointTuple params r))
      (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyLeftFamily S params family)) q.2.2.1)
      (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyRightFamily S params family)) q.2.2.1)
      (gHatSelfConsistencyError zeta) :=
  (sddOpRel_uniform_equiv (thirdSliceFrontEquiv params r).symm S.toVecState
    (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyLeftFamily S params family)) q.1)
    (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyRightFamily S params family)) q.1)
    (gHatSelfConsistencyError zeta)).1
    (sddOpRel_uniform_fst
      (β := SliceQuestion params × SliceQuestion params × PointTuple params r) S.toVecState
      (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyLeftFamily S params family))
      (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyRightFamily S params family))
      (gHatSelfConsistencyError zeta)
      (gHatSelfConsistency_sddOpRel params S family zeta hsc))

/-- The commutation of completed-slice pairs, sandwiched by the reverse half-product on the
right register: the move family and the commuted family are at the commutation error. -/
theorem commuteGHalfSandwich_step_commute
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ) (r : ℕ)
    (hcom : S.SDDOpRel
      (uniformDistribution (SlicePairQuestion params))
      (gHatPairProductLeft S params family)
      (gHatPairProductRight S params family)
      (gHatCommutationError params gamma zeta)) :
    S.SDDOpRel
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      (commuteGHalfSandwich_moveFamily S params family r)
      (commuteGHalfSandwich_commuteFamily S params family r)
      (gHatCommutationError params gamma zeta) := by
  let C : (SliceQuestion params × SliceQuestion params × PointTuple params r) →
      (GHatOutcome params × GHatOutcome params) → GHatTupleOutcome params r → K →L[ℂ] K :=
    fun q _ gt => S.R (gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt)
  have hC : ∀ q a, ∑ gt : GHatTupleOutcome params r, star (C q a gt) * C q a gt ≤ 1 :=
    fun q _ => sum_star_rightTensor_mul_le_one S _
      (gHatReverseHalfProduct_sum_adjoint_mul_le_one params family r q.2.2)
  have hcab := Preliminaries.cabApproxDelta_raw S.toVecState
    (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
    (fun q => gHatPairProductLeft S params family (q.1, q.2.1))
    (fun q => gHatPairProductRight S params family (q.1, q.2.1))
    C (gHatCommutationError params gamma zeta)
    (gHatPairProduct_sddOpRel_triple params S family gamma zeta r hcom) hC
  refine sddOpRel_congr_outcome S.toVecState _ _ _
    (commuteGHalfSandwich_moveFamily S params family r)
    (commuteGHalfSandwich_commuteFamily S params family r) _ ?_ ?_
    (sddOpRel_reindex (pairTailOutcomeEquiv params r) S.toVecState _ _ _ _ hcab)
  · intro q ogs
    exact (S.rightTensor_mul_leftTensor_eq_opTensor _ _).trans
      (congrArg (· * _) (S.leftTensor_mul_leftTensor _ _).symm)
  · intro q ogs
    exact (S.rightTensor_mul_leftTensor_eq_opTensor _ _).trans
      (congrArg (· * _) (S.leftTensor_mul_leftTensor _ _).symm)

/-- A move-source comparison lifts, after left multiplication by the completed slice at a new
first question coordinate, to the move-step source and middle families. -/
theorem commuteGHalfSandwich_prefixFirstSliceLeft_move
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (r : ℕ)
    (δ : ℝ)
    (hAB : S.SDDOpRel
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      (commuteGHalfSandwich_moveSourceFamily S params family r)
      (commuteGHalfSandwich_moveFamily S params family r)
      δ) :
    S.SDDOpRel
      (uniformDistribution (SliceQuestion params × SliceQuestion params ×
        SliceQuestion params × PointTuple params r))
      (commuteGHalfSandwich_moveStepSourceFamily S params family r)
      (commuteGHalfSandwich_moveStepMidFamily S params family r)
      δ := by
  have hABquad := (sddOpRel_uniform_equiv (firstSliceBackQuestionEquiv params r) S.toVecState
    (fun q => commuteGHalfSandwich_moveSourceFamily S params family r q.1)
    (fun q => commuteGHalfSandwich_moveFamily S params family r q.1) δ).1
    (sddOpRel_uniform_fst (β := SliceQuestion params) S.toVecState
      (commuteGHalfSandwich_moveSourceFamily S params family r)
      (commuteGHalfSandwich_moveFamily S params family r) δ hAB)
  let C : (SliceQuestion params × SliceQuestion params × SliceQuestion params ×
      PointTuple params r) →
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) →
      GHatOutcome params → K →L[ℂ] K :=
    fun q _ g₁ => S.L ((gHatIdxMeas params family q.1).outcome g₁)
  have hC : ∀ q a, ∑ g₁ : GHatOutcome params, star (C q a g₁) * C q a g₁ ≤ 1 :=
    fun q _ => sum_star_leftTensor_mul_le_one S _
      (subMeas_sum_adjoint_mul_le_one (gHatIdxMeas params family q.1).toSubMeas)
  have hcab := Preliminaries.cabApproxDelta_raw S.toVecState
    (uniformDistribution
      (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r))
    _ _ C δ hABquad hC
  refine sddOpRel_congr_outcome S.toVecState _ _ _
    (commuteGHalfSandwich_moveStepSourceFamily S params family r)
    (commuteGHalfSandwich_moveStepMidFamily S params family r) _ ?_ ?_
    (sddOpRel_reindex (firstSliceBackOutcomeEquiv params r) S.toVecState _ _ _ _ hcab)
  · intro q ogs
    exact (mul_assoc _ _ _).symm.trans (congrArg (· * _) (mul_assoc _ _ _).symm)
  · intro q ogs
    exact (mul_assoc _ _ _).symm.trans (congrArg (· * _) (mul_assoc _ _ _).symm)

/-- The self-consistency of the completed slices moves the third distinguished factor of the
move-step middle family from the left register to the right one, at the self-consistency
error. -/
theorem commuteGHalfSandwich_moveStepMid_toTarget
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
      (uniformDistribution
        (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r))
      (commuteGHalfSandwich_moveStepMidFamily S params family r)
      (commuteGHalfSandwich_moveStepTargetFamily S params family r)
      (gHatSelfConsistencyError zeta) := by
  let Q := SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r
  let C : Q → GHatOutcome params →
      ((GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r) → K →L[ℂ] K :=
    fun q _ ag =>
      S.L ((gHatIdxMeas params family q.1).outcome ag.1.1 *
          (gHatIdxMeas params family q.2.1).outcome ag.1.2) *
        S.R (gHatReverseHalfProductOutcomeOperator params family r q.2.2.2 ag.2)
  have hC : ∀ q a, ∑ ag : (GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r,
      star (C q a ag) * C q a ag ≤ 1 :=
    fun q _ => leftTensor_rightTensor_sum_adjoint_mul_le_one S
      (prefixOp := fun og : GHatOutcome params × GHatOutcome params =>
        (gHatIdxMeas params family q.1).outcome og.1 *
          (gHatIdxMeas params family q.2.1).outcome og.2)
      (tailOp := gHatReverseHalfProductOutcomeOperator params family r q.2.2.2)
      (gHatPairPrefix_sum_adjoint_mul_le_one params family (q.1, q.2.1))
      (gHatReverseHalfProduct_sum_adjoint_mul_le_one params family r q.2.2.2)
  have hcab := Preliminaries.cabApproxDelta_raw S.toVecState (uniformDistribution Q) _ _ C
    (gHatSelfConsistencyError zeta)
    (gHatSelfConsistency_sddOpRel_quadThird params S family zeta r hsc) hC
  refine sddOpRel_congr_outcome S.toVecState _ _ _
    (commuteGHalfSandwich_moveStepMidFamily S params family r)
    (commuteGHalfSandwich_moveStepTargetFamily S params family r) _ ?_ ?_
    (sddOpRel_reindex (thirdSliceFrontOutcomeEquiv params r) S.toVecState _ _ _ _ hcab)
  · intro q ogs
    change S.L (_ * _) * S.R _ * S.L _ = S.L _ * S.L _ * S.L _ * S.R _
    rw [mul_assoc, ← (S.L_comm_R _ _).eq, ← mul_assoc, ← S.leftTensor_mul_leftTensor]
    rfl
  · intro q ogs
    exact congrArg (· * _ * _) (S.leftTensor_mul_leftTensor _ _).symm

end MIPRE.LIDT.Co.Pasting

end
