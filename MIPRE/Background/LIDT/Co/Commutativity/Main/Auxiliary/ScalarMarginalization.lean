/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/Main/Auxiliary/ScalarMarginalization.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Basic.DistributionAvg
public import MIPRE.Background.LIDT.Co.Commutativity.Transport.FullSlice.Bridges.Closeness
public import MIPRE.Background.LIDT.Co.Commutativity.Transport.FullSlice.Bridges.ClosenessXEval
public import MIPRE.Background.LIDT.Co.Commutativity.Transport.FullSlice.Bridges.QSDD
public import MIPRE.Background.LIDT.Co.Commutativity.Transport.FullSlice.ZeroBounds
public import MIPRE.Background.LIDT.Co.Commutativity.Transport.EvaluationSpecialization
public import MIPRE.Background.LIDT.Co.Commutativity.EvaluatedSliceCommutation.Averages

@[expose] public section

/-!
# Section 11 commutativity: scalar marginalization lemmas

Schwartz–Zippel marginalization helpers (`eq:evaluate-gcom-at-points`, `eq:gcom4-diff`) used in
the final full-slice commutation theorem: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/Main/Auxiliary/ScalarMarginalization.lean` in
the port of `planning/c6b-plan.md` (milestone M7, section "Port conventions").

The public lemmas `fullSlice_scalar_marginalize_x` and `fullSlice_scalar_marginalize_y` are pure
scalar inequalities. Their proofs compose the tensor-form comparisons over the tensor averages of
`Co/Commutativity/Transport/FullSlice/Averages.lean`, with `closenessOfIP` at cost `√ζ` each (the
scalar/tensor decision is recorded upstream in `docs/decisions/713-scalar-tensor-decision.md`).

The vendored hypothesis `hnorm : strategy.state.IsNormalized` is dropped from both public
lemmas: normalization is a theorem of the model (`VecState.ev_one_of_isNormalized`), and the
ported `Preliminaries.switchSandwich` and transport bridges no longer take it. The two
summation helpers take the model `S : SymModel 𝔓 K` as an explicit first argument, where the
vendored ones take `ψ`; `avgOver_slice_total_left_sandwich_eq` takes it after `params`, as the
vendored one takes `ψ`.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Commutativity

open MIPStarRE.LDT (Parameters FieldModel Point Fq pointHeight avgOver avgOver_congr avgOver_sum
  avgOver_uniform_prod uniformDistribution uniformDistribution_weight_sum_le_one)
open MIPStarRE.LDT.Commutativity (FullSliceOutcome)
open MIPStarRE.LDT.CommutativityPoints (avgOver_uniform_pointNext_height)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The evaluated point family viewed as a projective submeasurement family. -/
noncomputable def evaluatedPointProj
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) :
    IdxProjSubMeas (Point params.next) (Fq params) 𝔓 :=
  fun u =>
    { toSubMeas := evaluatedPointFamily params family u
      proj := evaluatedPointFamily_outcome_proj params family u }

/-- Triangle inequality with explicit bounds for an intermediate point. -/
lemma abs_sub_le_of_two_step
    {a b c e₁ e₂ : ℝ}
    (hab : |a - b| ≤ e₁) (hbc : |b - c| ≤ e₂) :
    |a - c| ≤ e₁ + e₂ :=
  (abs_sub_le a b c).trans (add_le_add hab hbc)

/-- Summing the inner outcome in an `ABA` expectation turns it into the
submeasurement total. -/
lemma sum_ev_leftTensor_sandwich_total
    {α : Type*} [Fintype α]
    (S : SymModel 𝔓 K) (A : 𝔓) (B : SubMeas α 𝔓) :
    (∑ b : α, S.ev (S.L (A * B.outcome b * A))) = S.ev (S.L (A * B.total * A)) := by
  rw [← B.sum_eq_total, Finset.mul_sum, Finset.sum_mul, ← S.leftTensor_finset_sum,
    S.ev_finset_sum]

/-- Summing the right-register outcome in the middle switch-sandwich term turns
it into the submeasurement total. -/
lemma sum_ev_middle_total
    {α : Type*} [Fintype α]
    (S : SymModel 𝔓 K) (G : 𝔓) (A : SubMeas α 𝔓) :
    (∑ a : α, S.ev (S.L G * S.R (A.outcome a))) = S.ev (S.L G * S.R A.total) := by
  rw [← A.sum_eq_total, ← S.rightTensor_finset_sum, Finset.mul_sum, S.ev_finset_sum]

/-- Averaging the middle total in an `ABA` sandwich produces the averaged
slice operator `G = E_y Gʸ`. -/
lemma avgOver_slice_total_left_sandwich_eq
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓) (A : 𝔓) :
    avgOver (uniformDistribution (Fq params))
        (fun y => S.ev (S.L (A * (family.meas y).total * A))) =
      S.ev (S.L A * S.L (IdxPolyFamily.averagedSubMeas family).total * S.L A) := by
  rw [← S.ev_leftTensor_averageOperatorOverDistribution,
    averageOperatorOverDistribution_mul_left_right, S.leftTensor_mul_leftTensor,
    S.leftTensor_mul_leftTensor]
  rfl

/-- Full-slice cubic first term as the left switch-sandwich expectation. -/
lemma fullSliceABAAvg_eq_leftSandwichExpectation
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓) :
    fullSliceABAAvg params strategy family =
      Preliminaries.leftSandwichExpectation strategy.state
        (uniformDistribution (Fq params)) family.meas
        ((IdxPolyFamily.averagedSubMeas family).total) := by
  unfold fullSliceABAAvg Preliminaries.leftSandwichExpectation
  rw [avgOver_uniform_prod (f := fun x y => ∑ gh : FullSliceOutcome params,
    strategy.state.ev (strategy.state.L ((family.meas x).toSubMeas.outcome gh.1 *
      (family.meas y).toSubMeas.outcome gh.2 * (family.meas x).toSubMeas.outcome gh.1)))]
  refine avgOver_congr _ _ _ fun x => ?_
  simp only [Fintype.sum_prod_type]
  rw [avgOver_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← avgOver_slice_total_left_sandwich_eq params strategy.state family]
  exact avgOver_congr _ _ _ fun y =>
    sum_ev_leftTensor_sandwich_total strategy.state _ (family.meas y).toSubMeas

/-- Evaluated-slice cubic first term as the evaluated left switch-sandwich expectation. -/
lemma evaluatedSliceABAAvg_eq_leftSandwichExpectation
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓) :
    evaluatedSliceABAAvg params strategy family =
      Preliminaries.leftSandwichExpectation strategy.state
        (uniformDistribution (Point params.next))
        (evaluatedPointProj params family)
        ((IdxPolyFamily.averagedSubMeas family).total) := by
  unfold evaluatedSliceABAAvg Preliminaries.leftSandwichExpectation
  refine (avgOver_uniform_prod (α := Point params.next) (β := Point params.next)
    fun u v => ∑ ab : Fq params × Fq params,
      evaluatedSliceABATerm params strategy family (u, v) ab).trans ?_
  refine avgOver_congr _ _ _ fun u => ?_
  simp only [Fintype.sum_prod_type]
  rw [avgOver_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← avgOver_slice_total_left_sandwich_eq params strategy.state family,
    ← avgOver_uniform_pointNext_height params]
  exact avgOver_congr _ _ _ fun v => sum_ev_leftTensor_sandwich_total strategy.state
    ((evaluatedPointFamily params family u).outcome a) (evaluatedPointFamily params family v)

/-- The full and evaluated switch-sandwich middle terms are the same `G ⊗ G` average. -/
lemma fullSlice_middleSandwichExpectation_eq_evaluated
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓) :
    Preliminaries.middleSandwichExpectation strategy.state
        (uniformDistribution (Fq params)) family.meas
        ((IdxPolyFamily.averagedSubMeas family).total) =
      Preliminaries.middleSandwichExpectation strategy.state
        (uniformDistribution (Point params.next))
        (evaluatedPointProj params family)
        ((IdxPolyFamily.averagedSubMeas family).total) := by
  unfold Preliminaries.middleSandwichExpectation
  let G : 𝔓 := (IdxPolyFamily.averagedSubMeas family).total
  calc
    _ = avgOver (uniformDistribution (Fq params))
          (fun x => strategy.state.ev (strategy.state.L G *
            strategy.state.R (family.meas x).total)) :=
        avgOver_congr _ _ _ fun x =>
          sum_ev_middle_total strategy.state G (family.meas x).toSubMeas
    _ = avgOver (uniformDistribution (Point params.next))
          (fun u => strategy.state.ev (strategy.state.L G *
            strategy.state.R (evaluatedPointFamily params family u).total)) :=
        (avgOver_uniform_pointNext_height params _).symm
    _ = _ :=
        avgOver_congr _ _ _ fun u =>
          (sum_ev_middle_total strategy.state G (evaluatedPointFamily params family u)).symm

/-- Paper first-term switch-sandwich transport
(`commutativity-G.tex` lines 295--305), stated in the public scalar API.

The paper does not use an `md/q` Schwartz--Zippel step for the cubic first term.
Instead, both the full and evaluated cubic terms are compared to the common
`G ⊗ G` switch-sandwich center, costing `2√ζ` on each side. -/
lemma fullSlice_scalar_marginalize_x
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (zeta : ℝ)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    |fullSliceABAAvg params strategy family -
        evaluatedSliceABAAvg params strategy family| ≤
      4 * Real.sqrt zeta := by
  let G : 𝔓 := (IdxPolyFamily.averagedSubMeas family).total
  have hG : Preliminaries.OpBounded01 G :=
    ⟨(IdxPolyFamily.averagedSubMeas family).total_nonneg,
      sub_nonneg.mpr (IdxPolyFamily.averagedSubMeas family).total_le_one⟩
  have hfull := (Preliminaries.switchSandwich strategy.state
    (uniformDistribution (Fq params)) (uniformDistribution_weight_sum_le_one (Fq params))
    family.meas G hG zeta
    ⟨hself.sliceSelfConsistency.squaredDistanceBound⟩).leftSandwichTransfer
  have heval := (Preliminaries.switchSandwich strategy.state
    (uniformDistribution (Point params.next))
    (uniformDistribution_weight_sum_le_one (Point params.next))
    (evaluatedPointProj params family) G hG zeta
    ⟨(evaluatedPointFamily_selfConsistency_of_stronglySelfConsistent
      params strategy family zeta hself).squaredDistanceBound⟩).leftSandwichTransfer
  rw [← fullSliceABAAvg_eq_leftSandwichExpectation,
    fullSlice_middleSandwichExpectation_eq_evaluated] at hfull
  rw [← evaluatedSliceABAAvg_eq_leftSandwichExpectation, abs_sub_comm] at heval
  linarith [abs_sub_le_of_two_step hfull heval]

/-- Paper-faithful second-term transport bound.

The proved x-prefix (`eq:gcom4` plus `eq:gcom4-diff`, paper lines 332--354)
costs `md/q + √ζ`; the proved line-359 `closenessOfIP` comparison costs `√ζ`;
the line-360 scalar↔tensor comparison is proved in
`xEvaluatedFullSliceABABAvg_to_xEvaluatedFullSliceABABtensorAvg` and costs
another `√ζ`; and the proved y-tail uses y-Schwartz--Zippel marginalization
(paper lines 369--385) plus the `√ζ` doubly-evaluated scalar↔tensor comparison. Thus
the whole scalar second-term comparison costs `2·md/q + 4√ζ`. -/
lemma fullSlice_scalar_marginalize_y
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (zeta : ℝ)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    |fullSliceABABAvg params strategy family -
        evaluatedSliceABABAvg params strategy family| ≤
      (2 * ((↑params.m : ℝ) * ↑params.d / ↑params.q) + 4 * Real.sqrt zeta) := by
  have hclose := abs_sub_le_of_two_step
    (xEvaluatedSliceBABAtensor_to_xEvaluatedFullSliceABABAvg params strategy family zeta hself)
    (xEvaluatedFullSliceABABAvg_to_xEvaluatedFullSliceABABtensorAvg
      params strategy family zeta hself)
  have h := abs_sub_le_of_two_step (abs_sub_le_of_two_step
    (fullSliceABAB_to_xEvaluatedSliceBABAtensorAvg params strategy family zeta hself) hclose)
    (xEvaluatedFullSliceABABtensor_to_evaluatedSliceABABAvg params strategy family zeta hself)
  linarith

end MIPRE.LIDT.Co.Commutativity

end
