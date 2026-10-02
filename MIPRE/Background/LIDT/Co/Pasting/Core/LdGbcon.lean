/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/Core/
LdGbcon.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.Statements
public import MIPRE.Background.LIDT.Co.Preliminaries.SelfConsistency.Extensions
public import MIPRE.Background.LIDT.Co.Preliminaries.Triangles.SimEq

@[expose] public section

/-!
# Section 12 pasting: vertical-line consistency transfer

The `ldGbcon` transfer compares the slice family `G^x` with the vertical-line answers `B^u`. It
combines the conditioned axis-parallel consistency estimate with the point-to-vertical-line
state-dependent-distance bound: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Core/LdGbcon.lean` in the port of
`planning/c6b-plan.md` (milestone M11, section "Port conventions").

A strategy is a `SymStrat params.next 𝔓 K` and the slice family an `IdxPolyFamily params 𝔓`, so
the two vertical-line measurements are local families in `𝔓`, and the distance bounds are
`SDDRel`s of their right placements on `strategy.state`. The vendored swap
`consRel_symm_of_density_fixed strategy.state strategy.densityFixed` is the model's theorem
`SymModel.consRel_symm_of_density_fixed`, and the normalization `strategy.isNormalized` that the
vendored `triangleSub_right` takes is not a hypothesis of the ported one, so no swap or
normalization hypothesis appears.

Two proofs are shorter than the vendored ones. `pointVerticalLineSdd_of_axis_self` drops the
vendored point self-consistency `ConsRel`, which it computed and did not use. `ldGbcon_of_axis_self`
is `Preliminaries.triangleSub_right` applied to the point consistency of the family and to
`pointVerticalLineSdd_of_axis_self` directly, in place of a second copy of that bound's proof
followed by a rewrite along `ldGbconAxisLineMeasurement_eq_verticalLineMeasurement`.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Fq Point AxisParallelLine AxisParallelTestSample
  appendPoint truncatePoint pointHeight zeroCoord lastCoord avgOver avgOver_mono avgOver_const_mul
  avgOver_uniform_prod uniformDistribution uniformDistribution_weight_sum_le_one)
open MIPStarRE.LDT.Pasting (verticalLine_pointAt_appendPoint)
open MIPRE.LIDT.Co (SymStrat SubMeas Measurement IdxMeas IdxProjMeas IdxProjSubMeas IdxSubMeas
  IdxPolyFamily AxisParallelCovariantMeasurement postprocess evaluateFiberFamilyAtNextPoint
  axisParallelPointAnswerFamily axisParallelLineAnswerFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The axis-parallel line measurement in the last direction through `u`, read at its base
point: the line answer `B^u` of the axis-parallel test conditioned on the last direction. -/
noncomputable def ldGbconAxisLineMeasurement
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) :
    IdxMeas (Point params.next) (Fq params) 𝔓 := fun u =>
  let ℓ : AxisParallelLine params.next :=
    { base := u, direction := lastCoord params }
  { toSubMeas := postprocess ((strategy.axisParallelMeasurement ℓ).toSubMeas) (· zeroCoord)
    total_eq_one := (strategy.axisParallelMeasurement ℓ).total_eq_one }

/-- The vertical line through `u`, based at height zero, read at the height of `u`: the
vertical-line answer `B^u` as a measurement. -/
noncomputable def ldGbconVerticalLineMeasurement
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) :
    IdxMeas (Point params.next) (Fq params) 𝔓 := fun u =>
  { toSubMeas :=
      postprocess
        (verticalLineMeasurementFamily params strategy (truncatePoint params u))
        (fun f => f (pointHeight params u))
    total_eq_one :=
      let ℓ : AxisParallelLine params.next :=
        { base := appendPoint params (truncatePoint params u) zeroCoord
          direction := lastCoord params }
      (strategy.axisParallelMeasurement ℓ).total_eq_one }

/-- The two readings of `B^u` agree, by the rebasing covariance of the axis-parallel
measurement: rebasing the vertical line at the height of `u` gives the last-direction line
through `u`. -/
lemma ldGbconAxisLineMeasurement_eq_verticalLineMeasurement
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) :
    IdxMeas.toIdxSubMeas (ldGbconAxisLineMeasurement params strategy) =
      IdxMeas.toIdxSubMeas (ldGbconVerticalLineMeasurement params strategy) := by
  funext u
  refine SubMeas.ext (fun a => ?_) ((ldGbconAxisLineMeasurement params strategy u).total_eq_one.trans
    (ldGbconVerticalLineMeasurement params strategy u).total_eq_one.symm)
  let ℓ : AxisParallelLine params.next :=
    { base := appendPoint params (truncatePoint params u) zeroCoord
      direction := lastCoord params }
  have hrebased :
      AxisParallelLine.rebaseAt ℓ (pointHeight params u) =
        { base := u, direction := lastCoord params } := by
    change ({ base := ℓ.pointAt (pointHeight params u), direction := lastCoord params } :
      AxisParallelLine params.next) = _
    rw [verticalLine_pointAt_appendPoint]
    exact congrArg (fun b => ({ base := b, direction := lastCoord params } :
      AxisParallelLine params.next))
      ((MIPStarRE.LDT.CommutativityPoints.pointNextEquiv params).left_inv u)
  have h := AxisParallelCovariantMeasurement.reparamInvariant
    strategy.axisParallelMeasurement ℓ (pointHeight params u) a
  rw [hrebased] at h
  exact h

/-- The point measurements are `m'·ε`-consistent with the last-direction line answers, where
`m' = m + 1` is the number of directions and `ε` bounds the axis-parallel test averaged over all
directions. -/
lemma ldGbcon_axis_last_direction_consistency
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps : ℝ)
    (haxis : strategy.state.ConsRel
      (uniformDistribution (AxisParallelTestSample params.next))
      (axisParallelPointAnswerFamily strategy)
      (axisParallelLineAnswerFamily strategy)
      eps) :
    strategy.state.ConsRel
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (IdxMeas.toIdxSubMeas (ldGbconAxisLineMeasurement params strategy))
      ((params.next.m : ℝ) * eps) := by
  let err : AxisParallelTestSample params.next → ℝ := fun s =>
    strategy.state.qBipartiteConsDefect
      (axisParallelPointAnswerFamily strategy s)
      (axisParallelLineAnswerFamily strategy s)
  have hm : ((params.next.m : ℕ) : ℝ) ≠ 0 := by
    simp [Parameters.next]
    exact_mod_cast Nat.succ_ne_zero params.m
  have hpointwise : ∀ u,
      err (u, lastCoord params) ≤
        (params.next.m : ℝ) *
          avgOver (uniformDistribution (Fin params.next.m)) (fun i => err (u, i)) := by
    intro u
    have havg :
        (params.next.m : ℝ) *
            avgOver (uniformDistribution (Fin params.next.m)) (fun i => err (u, i)) =
          ∑ i : Fin params.next.m, err (u, i) := by
      simp only [avgOver, uniformDistribution, MIPStarRE.LDT.Distribution.uniformOnFinset,
        Finset.card_univ, Fintype.card_fin, Finset.mem_univ, ite_true, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp [hm]
    rw [havg]
    exact Finset.single_le_sum (f := fun i => err (u, i))
      (fun i _ => strategy.state.qBipartiteConsDefect_nonneg _ _) (Finset.mem_univ _)
  refine ⟨?_⟩
  change avgOver (uniformDistribution (Point params.next)) (fun u => err (u, lastCoord params)) ≤
    (params.next.m : ℝ) * eps
  calc
    avgOver (uniformDistribution (Point params.next)) (fun u => err (u, lastCoord params))
      ≤ avgOver (uniformDistribution (Point params.next)) (fun u =>
          (params.next.m : ℝ) *
            avgOver (uniformDistribution (Fin params.next.m)) (fun i => err (u, i))) :=
        avgOver_mono _ _ _ hpointwise
    _ = (params.next.m : ℝ) *
          avgOver (uniformDistribution (AxisParallelTestSample params.next)) err := by
        rw [avgOver_const_mul, ← avgOver_uniform_prod (f := fun u i => err (u, i))]
    _ ≤ (params.next.m : ℝ) * eps :=
        mul_le_mul_of_nonneg_left haxis.offDiagonalBound (by positivity)

/-- Axis/self-consistency form of `lem:point-vertical-line-sdd`.

The proof of the point-to-vertical-line transfer uses only the axis-parallel
test and point self-consistency.  The diagonal-line test is not part of this
calculation. -/
theorem pointVerticalLineSdd_of_axis_self
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta : ℝ)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself : strategy.selfConsistencyFailureProbability ≤ delta) :
    strategy.state.SDDRel
      (uniformDistribution (Point params.next))
      (IdxSubMeas.liftRight strategy.state (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      (IdxSubMeas.liftRight strategy.state
        (IdxMeas.toIdxSubMeas (ldGbconVerticalLineMeasurement params strategy)))
      (8 * (params.m : ℝ) * eps + 4 * delta) := by
  set S := strategy.state
  set 𝒟 := uniformDistribution (Point params.next)
  -- At outcome type `Fq params`, that of the line answers (`Fq params.next` is `Fq params`).
  let pointMeas : IdxMeas (Point params.next) (Fq params) 𝔓 :=
    IdxProjMeas.toIdxMeas strategy.pointMeasurement
  have heps : 0 ≤ eps := (S.bipartiteConsError_nonneg _ _ _).trans haxis
  have hnext : (params.next.m : ℝ) ≤ 2 * (params.m : ℝ) := by
    have := params.hm
    simp only [Parameters.next]
    push_cast
    linarith [(show (1 : ℝ) ≤ params.m by exact_mod_cast this)]
  -- `L A^u` is `2 m' ε`-close to `R B^u` (the last-direction line answer).
  have haxis_sdd : S.SDDRel 𝒟
      (IdxSubMeas.liftLeft S (IdxMeas.toIdxSubMeas pointMeas))
      (IdxSubMeas.liftRight S (IdxMeas.toIdxSubMeas (ldGbconAxisLineMeasurement params strategy)))
      (2 * ((params.next.m : ℝ) * eps)) :=
    ⟨(Preliminaries.simeqToApprox S 𝒟 pointMeas (ldGbconAxisLineMeasurement params strategy) _
      (ldGbcon_axis_last_direction_consistency params strategy eps ⟨haxis⟩)
      ).leftRightSquaredDistanceBound⟩
  -- `R A^u` is `2 δ`-close to `L A^u`, by self-consistency and the symmetry of the distance.
  have hself_sdd : S.SDDRel 𝒟
      (IdxSubMeas.liftRight S (IdxMeas.toIdxSubMeas pointMeas))
      (IdxSubMeas.liftLeft S (IdxMeas.toIdxSubMeas pointMeas))
      (2 * delta) :=
    Preliminaries.sddRel_symm S.toVecState 𝒟 _ _ _
      ⟨(Preliminaries.simeqToApprox S 𝒟 pointMeas pointMeas delta
        ((Preliminaries.bipartiteSSCRel_iff_consRel_self_measurement S 𝒟 pointMeas delta).mp
          ⟨hself⟩)).leftRightSquaredDistanceBound⟩
  have h : S.SDDRel 𝒟
      (IdxSubMeas.liftRight S (IdxMeas.toIdxSubMeas pointMeas))
      (IdxSubMeas.liftRight S (IdxMeas.toIdxSubMeas (ldGbconAxisLineMeasurement params strategy)))
      (2 * (2 * delta + 2 * ((params.next.m : ℝ) * eps))) :=
    Preliminaries.stateDependentDistanceRel_triangle S.toVecState 𝒟 _ _ _ _ _
      hself_sdd haxis_sdd
  rw [ldGbconAxisLineMeasurement_eq_verticalLineMeasurement params strategy] at h
  refine Preliminaries.stateDependentDistanceRel_mono S.toVecState 𝒟 _ _ _ _ ?_ h
  nlinarith

/-- Named submeasurement-family form of `pointVerticalLineSdd_of_axis_self`.

The proof above constructs the vertical-line measurement as a complete
measurement-valued family.  The degree-zero estimates use only its underlying
submeasurement family, namely `liftedVerticalLineAnswerFamily`. -/
theorem pointVerticalLineSdd_liftedVerticalLine_of_axis_self
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta : ℝ)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself : strategy.selfConsistencyFailureProbability ≤ delta) :
    strategy.state.SDDRel
      (uniformDistribution (Point params.next))
      (IdxSubMeas.liftRight strategy.state (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      (IdxSubMeas.liftRight strategy.state (liftedVerticalLineAnswerFamily params strategy))
      (8 * (params.m : ℝ) * eps + 4 * delta) :=
  pointVerticalLineSdd_of_axis_self params strategy eps delta haxis hself

/-- `lem:point-vertical-line-sdd`.
A good strategy induces a state-dependent distance bound between the point
measurements and the vertical-line (axis-parallel rebased) measurements. -/
theorem pointVerticalLineSdd
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma) :
    strategy.state.SDDRel
      (uniformDistribution (Point params.next))
      (IdxSubMeas.liftRight strategy.state (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      (IdxSubMeas.liftRight strategy.state
        (IdxMeas.toIdxSubMeas (ldGbconVerticalLineMeasurement params strategy)))
      (8 * (params.m : ℝ) * eps + 4 * delta) :=
  pointVerticalLineSdd_of_axis_self params strategy eps delta
    hgood.axisParallelTest hgood.selfConsistencyTest

/-- `lem:ld-gbcon`.

This is the direct consistency transfer from the slice family `G^x` to the
vertical line answers `B^u`, obtained by composing the hypothesis
`item:ld-pasting-consistency` with the conditioned axis-parallel test relation. -/
theorem ldGbcon_of_axis_self
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta zeta : ℝ)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself : strategy.selfConsistencyFailureProbability ≤ delta)
    (family : IdxPolyFamily params 𝔓)
    (hcons : family.ConsistentWithPoints strategy zeta) :
    strategy.state.ConsRel
      (uniformDistribution (Point params.next))
      (evaluateFiberFamilyAtNextPoint params
        (IdxProjSubMeas.toIdxSubMeas family.meas))
      (fun u =>
        postprocess
          (verticalLineMeasurementFamily params strategy (truncatePoint params u))
          (fun f => f (pointHeight params u)))
      (zeta + Real.sqrt (8 * (params.m : ℝ) * eps + 4 * delta)) :=
  Preliminaries.triangleSub_right strategy.state (uniformDistribution (Point params.next))
    (uniformDistribution_weight_sum_le_one (Point params.next))
    (evaluateFiberFamilyAtNextPoint params (IdxProjSubMeas.toIdxSubMeas family.meas))
    (IdxProjMeas.toIdxMeas strategy.pointMeasurement)
    (ldGbconVerticalLineMeasurement params strategy) zeta _
    (strategy.state.consRel_symm_of_density_fixed _ _ _ zeta hcons.pointConsistency)
    (pointVerticalLineSdd_of_axis_self params strategy eps delta haxis hself)

/-- `lem:ld-gbcon`.

This is the direct consistency transfer from the slice family `G^x` to the
vertical line answers `B^u`, obtained by composing the hypothesis
`item:ld-pasting-consistency` with the conditioned axis-parallel test relation. -/
theorem ldGbcon
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma zeta : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params 𝔓)
    (hcons : family.ConsistentWithPoints strategy zeta) :
    strategy.state.ConsRel
      (uniformDistribution (Point params.next))
      (evaluateFiberFamilyAtNextPoint params
        (IdxProjSubMeas.toIdxSubMeas family.meas))
      (fun u =>
        postprocess
          (verticalLineMeasurementFamily params strategy (truncatePoint params u))
          (fun f => f (pointHeight params u)))
      (zeta + Real.sqrt (8 * (params.m : ℝ) * eps + 4 * delta)) :=
  ldGbcon_of_axis_self params strategy eps delta zeta
    hgood.axisParallelTest hgood.selfConsistencyTest family hcons

/-- Named-family form of `lem:ld-gbcon`.

This is the same consistency transfer as `ldGbcon`, restated with the two
families used in the degree-zero branch of `thm:ld-pasting`: the evaluated slice
family `family.evaluatedAtNextPoint` and the lifted vertical-line family
`liftedVerticalLineAnswerFamily`.  In the degree-zero branch, these are the two
families whose pointwise invariance properties must be combined to control
height dependence. -/
theorem ldGbcon_liftedVerticalLine_of_axis_self
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta zeta : ℝ)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself : strategy.selfConsistencyFailureProbability ≤ delta)
    (family : IdxPolyFamily params 𝔓)
    (hcons : family.ConsistentWithPoints strategy zeta) :
    strategy.state.ConsRel
      (uniformDistribution (Point params.next))
      family.evaluatedAtNextPoint
      (liftedVerticalLineAnswerFamily params strategy)
      (zeta + Real.sqrt (8 * (params.m : ℝ) * eps + 4 * delta)) :=
  ldGbcon_of_axis_self params strategy eps delta zeta haxis hself family hcons

/-- Named-family form of `lem:ld-gbcon`. -/
theorem ldGbcon_liftedVerticalLine
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma zeta : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params 𝔓)
    (hcons : family.ConsistentWithPoints strategy zeta) :
    strategy.state.ConsRel
      (uniformDistribution (Point params.next))
      family.evaluatedAtNextPoint
      (liftedVerticalLineAnswerFamily params strategy)
      (zeta + Real.sqrt (8 * (params.m : ℝ) * eps + 4 * delta)) :=
  ldGbcon_liftedVerticalLine_of_axis_self params strategy eps delta zeta
    hgood.axisParallelTest hgood.selfConsistencyTest family hcons

end MIPRE.LIDT.Co.Pasting

end
