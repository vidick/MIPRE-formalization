/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
CommutativityPoints/Approximation.lean, to the symmetric model of `planning/c6b-plan.md`; not a
vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.CommutativityPoints.Defs
public import MIPRE.Background.LIDT.Co.Preliminaries.ComparisonCore
public import MIPRE.Background.LIDT.Co.Test.StrategyFailures
public import MIPStarRE.LDT.CommutativityPoints.Approximation

@[expose] public section

/-!
# Section 10 — commutativity points approximation layer

Restricted-diagonal approximation infrastructure for commutativity at points: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/CommutativityPoints/Approximation.lean` in the port of
`planning/c6b-plan.md` (milestone M1, section "Port conventions"). The diagonal branch of the
low individual degree test is evaluated at its last restriction index and transported to the
shared point-with-diagonal-line distribution, for a symmetric strategy
`strategy : SymStrat params 𝔓 K` and for an answer-valued one
`strategy : AnswerSymStrat params 𝔓 K`; the point answers are placed by `strategy.state.L`, the
line answers by `strategy.state.R`.

The classical half of the vendored file (the last restriction index, the decompositions of a
next-level point, and the equivalences between restricted diagonal samples, diagonal lines and
rebased questions) is not ported: this file imports the vendored file and names those
declarations through an explicit `open MIPStarRE.LDT.CommutativityPoints (…)` list.
`opFamilyOfOutcome` is ported, generic over an additive monoid `R` of operators (the vendored
`Op ι`); downstream it is applied to joint operators `K →L[ℂ] K`.

## Not ported

- `pointNextEquiv`: classical, imported.
- `avgOver_uniform_pointNext_decompose`: classical, imported.
- `avgOver_uniform_pointNext_height`: classical, imported.
- `pointPairOutcomeSwapEquiv`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-points.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`

In this repository: `lem:co-commutativity-points` in `blueprint/src/content/08_downstream.tex`.
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.CommutativityPoints

open MIPStarRE.LDT (Parameters FieldModel Fq Point DiagonalLine DiagonalLineAnswer zeroCoord addCoord
  subCoord mulCoord addPoint smulPoint addCoord_subCoord_left addCoord_subCoord_right avgOver
  avgOver_congr avgOver_uniform_fst uniformDistribution RestrictedDiagonalSample
  extendRestrictedDirection)
open MIPStarRE.LDT.CommutativityPoints (PointDiagonalLineQuestion
  sampledPointFromDiagonalQuestion pointWithDiagonalLineDistribution
  restrictedDiagonalLinesConsistencyError pointDiagonalLineApproxError)

/-- The final restriction index, corresponding to the paper's `m`-restricted diagonal-lines test.
Upstream keeps it `private` since its Lean-module port (`LionSR/MIPStarRE` at `5fc363b`); the
port carries its own copy. -/
def lastRestrictionIndex (params : Parameters) : Fin params.m :=
  ⟨params.m - 1, Nat.sub_lt params.hm Nat.zero_lt_one⟩

/-- Upstream keeps this helper `private` since its Lean-module port (`LionSR/MIPStarRE` at `5fc363b`); the port carries its own copy, with upstream's proof. -/
lemma lastRestrictionIndex_val_succ
    (params : Parameters) :
    (lastRestrictionIndex params).val + 1 = params.m := by
  have hm := params.hm
  dsimp [lastRestrictionIndex]
  omega

/-- Upstream keeps this helper `private` since its Lean-module port (`LionSR/MIPStarRE` at `5fc363b`); the port carries its own copy, with upstream's proof.

At the final restriction index, a restricted diagonal direction records all
`m` coordinates, so it is equivalent to an unrestricted point of `Point params`. -/
noncomputable def lastRestrictedDirectionEquiv
    (params : Parameters)
    [FieldModel params.q] :
    (Fin ((lastRestrictionIndex params).val + 1) → Fq params) ≃ Point params where
  toFun := extendRestrictedDirection (lastRestrictionIndex params)
  invFun := fun direction i =>
    direction ⟨i.val, by
      have h := lastRestrictionIndex_val_succ params
      omega⟩
  left_inv := fun free => by
    funext i
    have hlt : i.val < params.m := by
      have h := lastRestrictionIndex_val_succ params
      omega
    have hle : (⟨i.val, hlt⟩ : Fin params.m).val ≤ (lastRestrictionIndex params).val := by
      dsimp [lastRestrictionIndex]
      omega
    have hidx :
        (⟨i.val, Nat.lt_succ_of_le hle⟩ : Fin ((lastRestrictionIndex params).val + 1)) = i := by
      ext
      rfl
    rw [← hidx]
    simp [extendRestrictedDirection, hle]
  right_inv := fun direction => by
    funext k
    have hk : k.val ≤ (lastRestrictionIndex params).val := by
      dsimp [lastRestrictionIndex]
      omega
    have hidx :
        (⟨k.val, by
            have h := lastRestrictionIndex_val_succ params
            omega⟩ : Fin params.m) = k := by
      ext
      rfl
    rw [← hidx]
    simp [extendRestrictedDirection, hk]

/-- Upstream keeps this helper `private` since its Lean-module port (`LionSR/MIPStarRE` at `5fc363b`); the port carries its own copy, with upstream's proof.

At the final restriction index, a restricted diagonal sample is exactly a
full diagonal line: the sample point becomes the base point and the restricted
direction determines all line coefficients. -/
noncomputable def lastRestrictedSampleEquivDiagonalLine
    (params : Parameters)
    [FieldModel params.q] :
    RestrictedDiagonalSample params (lastRestrictionIndex params) ≃ DiagonalLine params where
  toFun := fun s =>
    { base := s.1
      direction := lastRestrictedDirectionEquiv params s.2 }
  invFun := fun ℓ =>
    (ℓ.base, (lastRestrictedDirectionEquiv params).symm ℓ.direction)
  left_inv := fun ⟨base, free⟩ => by
    refine Prod.ext rfl ?_
    funext i
    have hlt : i.val < params.m := by
      have h := lastRestrictionIndex_val_succ params
      omega
    have hle : (⟨i.val, hlt⟩ : Fin params.m).val ≤ (lastRestrictionIndex params).val := by
      dsimp [lastRestrictionIndex]
      omega
    have hidx :
        (⟨i.val, Nat.lt_succ_of_le hle⟩ : Fin ((lastRestrictionIndex params).val + 1)) = i := by
      ext
      rfl
    rw [← hidx]
    simp [lastRestrictedDirectionEquiv, extendRestrictedDirection, hle]
  right_inv := fun ⟨base, direction⟩ => by
    change
      ({ base := base,
         direction := extendRestrictedDirection (lastRestrictionIndex params)
           (fun i => direction ⟨i.val, by
             have h := lastRestrictionIndex_val_succ params
             omega⟩) } : DiagonalLine params) =
      ({ base := base, direction := direction } : DiagonalLine params)
    congr
    funext k
    have hk : k.val ≤ (lastRestrictionIndex params).val := by
      dsimp [lastRestrictionIndex]
      omega
    have hidx :
        (⟨k.val, by
            have h := lastRestrictionIndex_val_succ params
            omega⟩ : Fin params.m) = k := by
      ext
      rfl
    rw [← hidx]
    simp [extendRestrictedDirection, hk]

/-- Upstream keeps this helper `private` since its Lean-module port (`LionSR/MIPStarRE` at `5fc363b`); the port carries its own copy, with upstream's proof.

Rebase the last restricted diagonal sample so that its distinguished base
point appears at the queried parameter. This identifies the corrected diagonal
test sample space with the shared point-with-diagonal-line questions used in
the commutativity-at-points argument. -/
noncomputable def rebasedLastRestrictedQuestionEquiv
    (params : Parameters)
    [FieldModel params.q] :
    (RestrictedDiagonalSample params (lastRestrictionIndex params) × Fq params) ≃
      PointDiagonalLineQuestion params where
  toFun := fun st =>
    let ℓ := lastRestrictedSampleEquivDiagonalLine params st.1
    (DiagonalLine.rebaseAt ℓ (subCoord zeroCoord st.2), st.2)
  invFun := fun q =>
    let ℓ := DiagonalLine.rebaseAt q.1 q.2
    ((lastRestrictedSampleEquivDiagonalLine params).symm ℓ, q.2)
  left_inv := fun ⟨s, t⟩ => by
    simp [DiagonalLine.rebaseAt_rebase, addCoord_subCoord_left]
  right_inv := fun ⟨ℓ, t⟩ => by
    simp [DiagonalLine.rebaseAt_rebase, addCoord_subCoord_right]


/-- Build an operator family from its outcomes, taking the total to be their sum. -/
noncomputable def opFamilyOfOutcome {R : Type*} [AddCommMonoid R]
    {Outcome : Type*} [Fintype Outcome]
    (outcome : Outcome → R) :
    OpFamily Outcome R where
  outcome := outcome
  total := ∑ a : Outcome, outcome a

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Evaluate each restricted diagonal measurement at the distinguished base
parameter `zeroCoord`, matching the corrected paper definition of the diagonal
branch. -/
noncomputable def rawDiagonalLineAnswerFamily
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) 𝔓 :=
  fun s =>
    let v := extendRestrictedDirection j s.2
    postprocess
      ((strategy.diagonalMeasurement { base := s.1, direction := v }).toSubMeas)
      (· zeroCoord)

/-- Consistency transfer for the corrected diagonal branch at the final
restriction index.

The corrected test samples a restricted diagonal line and compares the point
measurement at its distinguished base point with the diagonal measurement
postprocessed by evaluation at `zeroCoord`. The global diagonal-line test bound
therefore controls this last restricted slice in particular. -/
theorem sampledDiagonalLineConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma) :
    strategy.state.ConsRel
      (uniformDistribution (RestrictedDiagonalSample params (lastRestrictionIndex params)))
      (diagonalPointAnswerFamily strategy (lastRestrictionIndex params))
      (rawDiagonalLineAnswerFamily params strategy (lastRestrictionIndex params))
      (restrictedDiagonalLinesConsistencyError
        params gamma) := by
  let j := lastRestrictionIndex params
  let err : Fin params.m → ℝ := fun j =>
    strategy.state.bipartiteConsError
      (uniformDistribution (RestrictedDiagonalSample params j))
      (diagonalPointAnswerFamily strategy j)
      (rawDiagonalLineAnswerFamily params strategy j)
  have herr_nonneg : ∀ j : Fin params.m, 0 ≤ err j := by
    intro j'
    exact strategy.state.bipartiteConsError_nonneg
      (uniformDistribution (RestrictedDiagonalSample params j'))
      (diagonalPointAnswerFamily strategy j')
      (rawDiagonalLineAnswerFamily params strategy j')
  have hsum_bound : ∑ j' : Fin params.m, err j' ≤ gamma * (params.m : ℝ) := by
    have hm_nonneg : 0 ≤ (params.m : ℝ) := by
      positivity
    have hm_ne : (params.m : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt params.hm
    have hdiag := hgood.diagonalLineTest
    dsimp [SymStrat.diagonalFailureProbability, err] at hdiag
    calc
      ∑ j' : Fin params.m, err j'
        = (params.m : ℝ) * ((1 / (params.m : ℝ)) * ∑ j' : Fin params.m, err j') := by
            field_simp [hm_ne]
      _ ≤ (params.m : ℝ) * gamma := by
            exact mul_le_mul_of_nonneg_left hdiag hm_nonneg
      _ = gamma * (params.m : ℝ) := by ring
  have hj_le : err j ≤ gamma * (params.m : ℝ) := by
    calc
      err j ≤ ∑ j' : Fin params.m, err j' := by
        exact Finset.single_le_sum (fun j' _ => herr_nonneg j') (Finset.mem_univ j)
      _ ≤ gamma * (params.m : ℝ) := hsum_bound
  refine ⟨?_⟩
  simpa [j, err, restrictedDiagonalLinesConsistencyError] using hj_le

/-- Convert the corrected restricted diagonal consistency estimate into the
corresponding SDD approximation bound.

This is the final-slice version of the diagonal branch that feeds the
commutativity-at-points argument. It packages the consistency estimate through
`Preliminaries.simeqToApprox`. -/
theorem sampledDiagonalLineApproximation
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma) :
    strategy.state.SDDRel
      (uniformDistribution (RestrictedDiagonalSample params (lastRestrictionIndex params)))
      (IdxSubMeas.liftLeft strategy.state
        (diagonalPointAnswerFamily strategy (lastRestrictionIndex params)))
      (IdxSubMeas.liftRight strategy.state
        (rawDiagonalLineAnswerFamily params strategy (lastRestrictionIndex params)))
      (pointDiagonalLineApproxError params gamma) := by
  let j := lastRestrictionIndex params
  let pointFamily : IdxMeas (RestrictedDiagonalSample params j) (Fq params) 𝔓 :=
    fun s => (strategy.pointMeasurement s.1).toMeasurement
  let lineFamily : IdxMeas (RestrictedDiagonalSample params j) (Fq params) 𝔓 :=
    fun s =>
      { toSubMeas := rawDiagonalLineAnswerFamily params strategy j s
        total_eq_one :=
          calc
            (rawDiagonalLineAnswerFamily params strategy j s).total =
                ((strategy.diagonalMeasurement
                  { base := s.1
                    direction := extendRestrictedDirection j s.2 }).toSubMeas).total := by
              dsimp [rawDiagonalLineAnswerFamily]
              rw [postprocess_total]
            _ = 1 :=
              (strategy.diagonalMeasurement
                { base := s.1
                  direction := extendRestrictedDirection j s.2 }).total_eq_one }
  have hcons := sampledDiagonalLineConsistency params strategy eps delta gamma hgood
  have hcons' :
      strategy.state.ConsRel
        (uniformDistribution (RestrictedDiagonalSample params j))
        (IdxMeas.toIdxSubMeas pointFamily)
        (IdxMeas.toIdxSubMeas lineFamily)
        (restrictedDiagonalLinesConsistencyError params gamma) := by
    change strategy.state.ConsRel
      (uniformDistribution (RestrictedDiagonalSample params (lastRestrictionIndex params)))
      (diagonalPointAnswerFamilyOf strategy.pointMeasurement (lastRestrictionIndex params))
      (rawDiagonalLineAnswerFamily params strategy (lastRestrictionIndex params))
      (restrictedDiagonalLinesConsistencyError params gamma)
    exact hcons
  have happrox :
      Preliminaries.BipartiteSDDRel strategy.state
        (uniformDistribution (RestrictedDiagonalSample params j))
        (IdxMeas.toIdxSubMeas pointFamily)
        (IdxMeas.toIdxSubMeas lineFamily)
        (2 * restrictedDiagonalLinesConsistencyError params gamma) :=
    Preliminaries.simeqToApprox strategy.state
      (uniformDistribution (RestrictedDiagonalSample params j))
      pointFamily lineFamily
      (restrictedDiagonalLinesConsistencyError params gamma) hcons'
  refine ⟨?_⟩
  simpa [j, pointFamily, lineFamily, diagonalPointAnswerFamily,
    pointDiagonalLineApproxError, restrictedDiagonalLinesConsistencyError,
    Preliminaries.BipartiteSDDRel, VecState.sddError, IdxMeas.toIdxSubMeas,
    IdxSubMeas.liftLeft, IdxSubMeas.liftRight] using
    happrox.leftRightSquaredDistanceBound

/-- Transport the corrected restricted-diagonal approximation bound to the
shared point-with-diagonal-line distribution used downstream.

The reindexing runs through `rebasedLastRestrictedQuestionEquiv`, which turns a
restricted sample together with an evaluation parameter into the corresponding
rebased diagonal-line question. -/
theorem sampledDiagonalLineApproximation_pointWithDiagonalLine
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma) :
    strategy.state.SDDRel
      (pointWithDiagonalLineDistribution params)
      (IdxSubMeas.liftLeft strategy.state
        (sampledPointMeasurement params strategy))
      (IdxSubMeas.liftRight strategy.state
        (sampledDiagonalLineEvaluation params strategy))
      (pointDiagonalLineApproxError params gamma) := by
  let j := lastRestrictionIndex params
  let e := rebasedLastRestrictedQuestionEquiv params
  rcases sampledDiagonalLineApproximation params strategy eps delta gamma hgood with ⟨hbase⟩
  let f : PointDiagonalLineQuestion params → ℝ := fun q =>
    strategy.state.qSDD
      ((IdxSubMeas.liftLeft strategy.state (sampledPointMeasurement params strategy)) q)
      ((IdxSubMeas.liftRight strategy.state (sampledDiagonalLineEvaluation params strategy)) q)
  have hreindex :
      avgOver (pointWithDiagonalLineDistribution params) f =
        avgOver
          (uniformDistribution (RestrictedDiagonalSample params j × Fq params))
          (fun st => f (e st)) := by
    symm
    simpa [pointWithDiagonalLineDistribution, f] using
      (MIPStarRE.LDT.avgOver_uniform_equiv e (fun st => f (e st)))
  let g : RestrictedDiagonalSample params j → ℝ := fun s =>
    strategy.state.qSDD
      ((IdxSubMeas.liftLeft strategy.state (diagonalPointAnswerFamily strategy j)) s)
      ((IdxSubMeas.liftRight strategy.state (rawDiagonalLineAnswerFamily params strategy j)) s)
  have hignore :
      avgOver
          (uniformDistribution (RestrictedDiagonalSample params j × Fq params))
          (fun st => g st.1) =
        avgOver (uniformDistribution (RestrictedDiagonalSample params j)) g := by
    exact avgOver_uniform_fst g
  refine ⟨?_⟩
  calc
    strategy.state.sddError
        (pointWithDiagonalLineDistribution params)
        (IdxSubMeas.liftLeft strategy.state (sampledPointMeasurement params strategy))
        (IdxSubMeas.liftRight strategy.state (sampledDiagonalLineEvaluation params strategy))
      = avgOver (pointWithDiagonalLineDistribution params) f := rfl
    _ = avgOver
          (uniformDistribution (RestrictedDiagonalSample params j × Fq params))
          (fun st => f (e st)) := hreindex
    _ = avgOver
          (uniformDistribution (RestrictedDiagonalSample params j × Fq params))
          (fun st =>
            strategy.state.qSDD
              ((IdxSubMeas.liftLeft strategy.state (diagonalPointAnswerFamily strategy j)) st.1)
              ((IdxSubMeas.liftRight strategy.state
                (rawDiagonalLineAnswerFamily params strategy j)) st.1)) := by
            apply avgOver_congr
            rintro ⟨s, t⟩
            let ℓ₀ : DiagonalLine params := lastRestrictedSampleEquivDiagonalLine params s
            have hpoint : sampledPointFromDiagonalQuestion params (e (s, t)) = s.1 := by
              change (MIPStarRE.LDT.DiagonalLine.rebaseAt ℓ₀ (subCoord zeroCoord t)).pointAt t
                = s.1
              calc
                (MIPStarRE.LDT.DiagonalLine.rebaseAt ℓ₀ (subCoord zeroCoord t)).pointAt t
                  = ℓ₀.pointAt (addCoord (subCoord zeroCoord t) t) := by
                      simpa using MIPStarRE.LDT.DiagonalLine.rebaseAt_pointAt ℓ₀
                        (subCoord zeroCoord t) t
                _ = ℓ₀.pointAt zeroCoord := by simp
                _ = s.1 := by
                      rcases s with ⟨u, free⟩
                      funext i
                      simp [ℓ₀, lastRestrictedSampleEquivDiagonalLine,
                        MIPStarRE.LDT.DiagonalLine.pointAt, addPoint, smulPoint, zeroCoord,
                        addCoord, mulCoord]
            have hA : ∀ a,
                (((IdxSubMeas.liftLeft strategy.state
                    (sampledPointMeasurement params strategy)) (e (s, t))).outcome a) =
                  (((IdxSubMeas.liftLeft strategy.state
                    (diagonalPointAnswerFamily strategy j)) s).outcome a) := by
              intro a
              simp [IdxSubMeas.liftLeft, sampledPointMeasurement, diagonalPointAnswerFamily,
                diagonalPointAnswerFamilyOf, hpoint]
            have hB : ∀ a,
                (((IdxSubMeas.liftRight strategy.state
                    (sampledDiagonalLineEvaluation params strategy)) (e (s, t))).outcome a) =
                  (((IdxSubMeas.liftRight strategy.state
                      (rawDiagonalLineAnswerFamily params strategy j)) s).outcome a) := by
              intro a
              have hreparam :=
                (DiagonalCovariantMeasurement.reparamInvariant
                  strategy.diagonalMeasurement)
                  (MIPStarRE.LDT.DiagonalLine.rebaseAt ℓ₀ (subCoord zeroCoord t)) t a
              have hline :
                  ((sampledDiagonalLineEvaluation params strategy) (e (s, t))).outcome a =
                    (rawDiagonalLineAnswerFamily params strategy j s).outcome a := by
                calc
                  ((sampledDiagonalLineEvaluation params strategy) (e (s, t))).outcome a
                    = (postprocess
                        ((strategy.diagonalMeasurement
                          (MIPStarRE.LDT.DiagonalLine.rebaseAt ℓ₀
                            (subCoord zeroCoord t))).toSubMeas)
                        (fun f => f t)).outcome a := by
                            simp [sampledDiagonalLineEvaluation, e,
                              rebasedLastRestrictedQuestionEquiv, ℓ₀]
                  _ = (postprocess
                        ((strategy.diagonalMeasurement
                          (MIPStarRE.LDT.DiagonalLine.rebaseAt
                            (MIPStarRE.LDT.DiagonalLine.rebaseAt ℓ₀ (subCoord zeroCoord t))
                            t)).toSubMeas)
                        (fun f => f zeroCoord)).outcome a := by
                            symm
                            exact hreparam
                  _ = (postprocess
                        ((strategy.diagonalMeasurement ℓ₀).toSubMeas)
                        (fun f => f zeroCoord)).outcome a := by
                            simp [MIPStarRE.LDT.DiagonalLine.rebaseAt_rebase,
                              addCoord_subCoord_left]
                  _ = (rawDiagonalLineAnswerFamily params strategy j s).outcome a := by
                            rcases s with ⟨u, free⟩
                            change
                              (postprocess
                                ((strategy.diagonalMeasurement
                                  { base := u,
                                    direction :=
                                      lastRestrictedDirectionEquiv params free
                                  }).toSubMeas)
                                (fun f => f zeroCoord)).outcome a =
                              (postprocess
                                ((strategy.diagonalMeasurement
                                  { base := u,
                                    direction :=
                                      extendRestrictedDirection
                                        (lastRestrictionIndex params) free
                                  }).toSubMeas)
                                (fun f => f zeroCoord)).outcome a
                            simp [lastRestrictedDirectionEquiv]
              simpa [IdxSubMeas.liftRight] using
                congrArg (fun X => strategy.state.R X) hline
            unfold f VecState.qSDD VecState.qSDDCore
            apply Finset.sum_congr rfl
            intro a _
            rw [hA a, hB a]
    _ = avgOver (uniformDistribution (RestrictedDiagonalSample params j))
          g := hignore
    _ = strategy.state.sddError
          (uniformDistribution (RestrictedDiagonalSample params j))
          (IdxSubMeas.liftLeft strategy.state (diagonalPointAnswerFamily strategy j))
          (IdxSubMeas.liftRight strategy.state
            (rawDiagonalLineAnswerFamily params strategy j)) := rfl
    _ ≤ pointDiagonalLineApproxError params gamma := hbase

/-- Evaluate each answer-valued restricted diagonal measurement at the
distinguished base parameter `zeroCoord`. -/
noncomputable def rawAnswerDiagonalLineAnswerFamily
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params 𝔓 K)
    (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) 𝔓 :=
  fun s =>
    let v := extendRestrictedDirection j s.2
    postprocess
      ((strategy.diagonalMeasurement { base := s.1, direction := v }).toSubMeas)
      (· zeroCoord)

/-- The answer-valued diagonal-line test controls the final restricted
diagonal slice. -/
theorem answer_sampledDiagonalLineConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma) :
    strategy.state.ConsRel
      (uniformDistribution (RestrictedDiagonalSample params (lastRestrictionIndex params)))
      (AnswerSymStrat.diagonalPointAnswerFamily strategy (lastRestrictionIndex params))
      (rawAnswerDiagonalLineAnswerFamily params strategy (lastRestrictionIndex params))
      (restrictedDiagonalLinesConsistencyError params gamma) := by
  let j := lastRestrictionIndex params
  let err : Fin params.m → ℝ := fun j =>
    strategy.state.bipartiteConsError
      (uniformDistribution (RestrictedDiagonalSample params j))
      (AnswerSymStrat.diagonalPointAnswerFamily strategy j)
      (rawAnswerDiagonalLineAnswerFamily params strategy j)
  have herr_nonneg : ∀ j : Fin params.m, 0 ≤ err j := by
    intro j'
    exact strategy.state.bipartiteConsError_nonneg
      (uniformDistribution (RestrictedDiagonalSample params j'))
      (AnswerSymStrat.diagonalPointAnswerFamily strategy j')
      (rawAnswerDiagonalLineAnswerFamily params strategy j')
  have hsum_bound : ∑ j' : Fin params.m, err j' ≤ gamma * (params.m : ℝ) := by
    have hm_nonneg : 0 ≤ (params.m : ℝ) := by
      positivity
    have hm_ne : (params.m : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt params.hm
    have hdiag := hgood.diagonalLineTest
    dsimp [AnswerSymStrat.diagonalFailureProbability, err,
      AnswerSymStrat.diagonalLineAnswerFamily, rawAnswerDiagonalLineAnswerFamily] at hdiag
    calc
      ∑ j' : Fin params.m, err j'
        = (params.m : ℝ) * ((1 / (params.m : ℝ)) * ∑ j' : Fin params.m, err j') := by
            field_simp [hm_ne]
      _ ≤ (params.m : ℝ) * gamma := by
            exact mul_le_mul_of_nonneg_left hdiag hm_nonneg
      _ = gamma * (params.m : ℝ) := by ring
  have hj_le : err j ≤ gamma * (params.m : ℝ) := by
    calc
      err j ≤ ∑ j' : Fin params.m, err j' := by
        exact Finset.single_le_sum (fun j' _ => herr_nonneg j') (Finset.mem_univ j)
      _ ≤ gamma * (params.m : ℝ) := hsum_bound
  refine ⟨?_⟩
  simpa [j, err, restrictedDiagonalLinesConsistencyError] using hj_le

/-- The answer-valued restricted diagonal test gives the same SDD
approximation at the final restriction index as the ordinary diagonal test. -/
theorem answer_sampledDiagonalLineApproximation
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma) :
    strategy.state.SDDRel
      (uniformDistribution (RestrictedDiagonalSample params (lastRestrictionIndex params)))
      (IdxSubMeas.liftLeft strategy.state
        (AnswerSymStrat.diagonalPointAnswerFamily strategy (lastRestrictionIndex params)))
      (IdxSubMeas.liftRight strategy.state
        (rawAnswerDiagonalLineAnswerFamily params strategy (lastRestrictionIndex params)))
      (pointDiagonalLineApproxError params gamma) := by
  let j := lastRestrictionIndex params
  let pointFamily : IdxMeas (RestrictedDiagonalSample params j) (Fq params) 𝔓 :=
    fun s => (strategy.pointMeasurement s.1).toMeasurement
  let lineFamily : IdxMeas (RestrictedDiagonalSample params j) (Fq params) 𝔓 :=
    fun s =>
      { toSubMeas := rawAnswerDiagonalLineAnswerFamily params strategy j s
        total_eq_one :=
          calc
            (rawAnswerDiagonalLineAnswerFamily params strategy j s).total =
                ((strategy.diagonalMeasurement
                  { base := s.1
                    direction := extendRestrictedDirection j s.2 }).toSubMeas).total := by
              dsimp [rawAnswerDiagonalLineAnswerFamily]
              rw [postprocess_total]
            _ = 1 :=
              (strategy.diagonalMeasurement
                { base := s.1
                  direction := extendRestrictedDirection j s.2 }).total_eq_one }
  have hcons := answer_sampledDiagonalLineConsistency params strategy eps delta gamma hgood
  have hcons' :
      strategy.state.ConsRel
        (uniformDistribution (RestrictedDiagonalSample params j))
        (IdxMeas.toIdxSubMeas pointFamily)
        (IdxMeas.toIdxSubMeas lineFamily)
        (restrictedDiagonalLinesConsistencyError params gamma) := by
    change strategy.state.ConsRel
      (uniformDistribution (RestrictedDiagonalSample params (lastRestrictionIndex params)))
      (diagonalPointAnswerFamilyOf strategy.pointMeasurement (lastRestrictionIndex params))
      (rawAnswerDiagonalLineAnswerFamily params strategy (lastRestrictionIndex params))
      (restrictedDiagonalLinesConsistencyError params gamma)
    exact hcons
  have happrox :
      Preliminaries.BipartiteSDDRel strategy.state
        (uniformDistribution (RestrictedDiagonalSample params j))
        (IdxMeas.toIdxSubMeas pointFamily)
        (IdxMeas.toIdxSubMeas lineFamily)
        (2 * restrictedDiagonalLinesConsistencyError params gamma) :=
    Preliminaries.simeqToApprox strategy.state
      (uniformDistribution (RestrictedDiagonalSample params j))
      pointFamily lineFamily
      (restrictedDiagonalLinesConsistencyError params gamma) hcons'
  refine ⟨?_⟩
  simpa [j, pointFamily, lineFamily, AnswerSymStrat.diagonalPointAnswerFamily,
    pointDiagonalLineApproxError, restrictedDiagonalLinesConsistencyError,
    Preliminaries.BipartiteSDDRel, VecState.sddError, IdxMeas.toIdxSubMeas,
    IdxSubMeas.liftLeft, IdxSubMeas.liftRight] using
    happrox.leftRightSquaredDistanceBound

/-- Answer-valued version of
`sampledDiagonalLineApproximation_pointWithDiagonalLine`.

This is the Section 10 diagonal approximation needed by the answer-valued
commutativity route: it uses the answer-valued diagonal verifier relation
directly and does not pass through an ordinary dummy diagonal measurement. -/
theorem answer_sampledDiagonalLineApproximation_pointWithDiagonalLine
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma) :
    strategy.state.SDDRel
      (pointWithDiagonalLineDistribution params)
      (IdxSubMeas.liftLeft strategy.state
        (fun q =>
          (strategy.pointMeasurement (sampledPointFromDiagonalQuestion params q)).toSubMeas))
      (IdxSubMeas.liftRight strategy.state
        (fun q =>
          postprocess ((strategy.diagonalMeasurement q.1).toSubMeas) (fun f => f q.2)))
      (pointDiagonalLineApproxError params gamma) := by
  let j := lastRestrictionIndex params
  let e := rebasedLastRestrictedQuestionEquiv params
  rcases answer_sampledDiagonalLineApproximation params strategy eps delta gamma hgood with
    ⟨hbase⟩
  let f : PointDiagonalLineQuestion params → ℝ := fun q =>
    strategy.state.qSDD
      ((IdxSubMeas.liftLeft strategy.state
        (fun q =>
          (strategy.pointMeasurement (sampledPointFromDiagonalQuestion params q)).toSubMeas)) q)
      ((IdxSubMeas.liftRight strategy.state
        (fun q => postprocess ((strategy.diagonalMeasurement q.1).toSubMeas)
          (fun f => f q.2))) q)
  have hreindex :
      avgOver (pointWithDiagonalLineDistribution params) f =
        avgOver
          (uniformDistribution (RestrictedDiagonalSample params j × Fq params))
          (fun st => f (e st)) := by
    symm
    simpa [pointWithDiagonalLineDistribution, f] using
      (MIPStarRE.LDT.avgOver_uniform_equiv e (fun st => f (e st)))
  let g : RestrictedDiagonalSample params j → ℝ := fun s =>
    strategy.state.qSDD
      ((IdxSubMeas.liftLeft strategy.state
        (AnswerSymStrat.diagonalPointAnswerFamily strategy j)) s)
      ((IdxSubMeas.liftRight strategy.state
        (rawAnswerDiagonalLineAnswerFamily params strategy j)) s)
  have hignore :
      avgOver
          (uniformDistribution (RestrictedDiagonalSample params j × Fq params))
          (fun st => g st.1) =
        avgOver (uniformDistribution (RestrictedDiagonalSample params j)) g := by
    exact avgOver_uniform_fst g
  refine ⟨?_⟩
  calc
    strategy.state.sddError
        (pointWithDiagonalLineDistribution params)
        (IdxSubMeas.liftLeft strategy.state
          (fun q =>
            (strategy.pointMeasurement (sampledPointFromDiagonalQuestion params q)).toSubMeas))
        (IdxSubMeas.liftRight strategy.state
          (fun q => postprocess ((strategy.diagonalMeasurement q.1).toSubMeas)
            (fun f => f q.2)))
      = avgOver (pointWithDiagonalLineDistribution params) f := rfl
    _ = avgOver
          (uniformDistribution (RestrictedDiagonalSample params j × Fq params))
          (fun st => f (e st)) := hreindex
    _ = avgOver
          (uniformDistribution (RestrictedDiagonalSample params j × Fq params))
          (fun st =>
            strategy.state.qSDD
              ((IdxSubMeas.liftLeft strategy.state
                (AnswerSymStrat.diagonalPointAnswerFamily strategy j)) st.1)
              ((IdxSubMeas.liftRight strategy.state
                  (rawAnswerDiagonalLineAnswerFamily params strategy j)) st.1)) := by
            apply avgOver_congr
            rintro ⟨s, t⟩
            let ℓ₀ : DiagonalLine params := lastRestrictedSampleEquivDiagonalLine params s
            have hpoint : sampledPointFromDiagonalQuestion params (e (s, t)) = s.1 := by
              change (MIPStarRE.LDT.DiagonalLine.rebaseAt ℓ₀ (subCoord zeroCoord t)).pointAt t
                = s.1
              calc
                (MIPStarRE.LDT.DiagonalLine.rebaseAt ℓ₀ (subCoord zeroCoord t)).pointAt t
                  = ℓ₀.pointAt (addCoord (subCoord zeroCoord t) t) := by
                      simpa using
                        MIPStarRE.LDT.DiagonalLine.rebaseAt_pointAt ℓ₀ (subCoord zeroCoord t) t
                _ = ℓ₀.pointAt zeroCoord := by simp
                _ = s.1 := by
                      rcases s with ⟨u, free⟩
                      funext i
                      simp [ℓ₀, lastRestrictedSampleEquivDiagonalLine,
                        MIPStarRE.LDT.DiagonalLine.pointAt, addPoint, smulPoint, zeroCoord,
                        addCoord, mulCoord]
            have hA : ∀ a,
                (((IdxSubMeas.liftLeft strategy.state
                    (fun q => (strategy.pointMeasurement
                      (sampledPointFromDiagonalQuestion params q)).toSubMeas))
                      (e (s, t))).outcome a) =
                  (((IdxSubMeas.liftLeft strategy.state
                    (AnswerSymStrat.diagonalPointAnswerFamily strategy j)) s).outcome a) := by
              intro a
              simp [IdxSubMeas.liftLeft, AnswerSymStrat.diagonalPointAnswerFamily,
                diagonalPointAnswerFamilyOf, hpoint]
            have hB : ∀ a,
                (((IdxSubMeas.liftRight strategy.state
                    (fun q => postprocess ((strategy.diagonalMeasurement q.1).toSubMeas)
                      (fun f => f q.2))) (e (s, t))).outcome a) =
                  (((IdxSubMeas.liftRight strategy.state
                      (rawAnswerDiagonalLineAnswerFamily params strategy j)) s).outcome a) := by
              intro a
              have hline :
                  (postprocess
                    ((strategy.diagonalMeasurement (e (s, t)).1).toSubMeas)
                    (fun f => f (e (s, t)).2)).outcome a =
                    (rawAnswerDiagonalLineAnswerFamily params strategy j s).outcome a := by
                calc
                  (postprocess
                    ((strategy.diagonalMeasurement (e (s, t)).1).toSubMeas)
                    (fun f => f (e (s, t)).2)).outcome a
                    = (postprocess
                        ((strategy.diagonalMeasurement
                          (MIPStarRE.LDT.DiagonalLine.rebaseAt ℓ₀
                            (subCoord zeroCoord t))).toSubMeas)
                        (fun f : DiagonalLineAnswer params => f t)).outcome a := by
                          simp [e, rebasedLastRestrictedQuestionEquiv, ℓ₀]
                  _ = (postprocess
                        ((ProjMeas.transport
                          (DiagonalLineAnswer.reparamAtEquiv (params := params)
                            (subCoord zeroCoord t))
                          (strategy.diagonalMeasurement ℓ₀)).toSubMeas)
                        (fun f : DiagonalLineAnswer params => f t)).outcome a := by
                          rw [strategy.diagonalMeasurement.transportInvariant ℓ₀
                            (subCoord zeroCoord t)]
                  _ = (postprocess
                        ((strategy.diagonalMeasurement ℓ₀).toSubMeas)
                        (fun f : DiagonalLineAnswer params =>
                          f (addCoord (subCoord zeroCoord t) t))).outcome a := by
                          have h :=
                            SubMeas.postprocess_transport
                              (e := DiagonalLineAnswer.reparamAtEquiv (params := params)
                                (subCoord zeroCoord t))
                              (A := (strategy.diagonalMeasurement ℓ₀).toSubMeas)
                              (f := fun f : DiagonalLineAnswer params => f t)
                          simpa [ProjMeas.transport, Measurement.transport,
                            DiagonalLineAnswer.reparamAtEquiv,
                            DiagonalLineAnswer.reparamAt] using
                            congrArg (fun M : SubMeas (Fq params) 𝔓 => M.outcome a) h
                  _ = (postprocess
                        ((strategy.diagonalMeasurement ℓ₀).toSubMeas)
                        (fun f : DiagonalLineAnswer params => f zeroCoord)).outcome a := by
                          simp
                  _ = (rawAnswerDiagonalLineAnswerFamily params strategy j s).outcome a := by
                          rcases s with ⟨u, free⟩
                          change
                            (postprocess
                              ((strategy.diagonalMeasurement
                                { base := u,
                                  direction :=
                                    lastRestrictedDirectionEquiv params free
                                }).toSubMeas)
                              (fun f : DiagonalLineAnswer params => f zeroCoord)).outcome a =
                            (postprocess
                              ((strategy.diagonalMeasurement
                                { base := u,
                                  direction :=
                                    extendRestrictedDirection
                                      (lastRestrictionIndex params) free
                                }).toSubMeas)
                              (fun f : DiagonalLineAnswer params => f zeroCoord)).outcome a
                          simp [lastRestrictedDirectionEquiv]
              simpa [IdxSubMeas.liftRight] using
                congrArg (fun X => strategy.state.R X) hline
            unfold f VecState.qSDD VecState.qSDDCore
            apply Finset.sum_congr rfl
            intro a _
            rw [hA a, hB a]
    _ = avgOver (uniformDistribution (RestrictedDiagonalSample params j))
          g := hignore
    _ = strategy.state.sddError
          (uniformDistribution (RestrictedDiagonalSample params j))
          (IdxSubMeas.liftLeft strategy.state
            (AnswerSymStrat.diagonalPointAnswerFamily strategy j))
          (IdxSubMeas.liftRight strategy.state
            (rawAnswerDiagonalLineAnswerFamily params strategy j)) := rfl
    _ ≤ pointDiagonalLineApproxError params gamma := hbase

end MIPRE.LIDT.Co.CommutativityPoints

end
