/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
SelfImprovement/Defs.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored
file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.GlobalVariance.Defs.Families
public import MIPRE.Background.LIDT.Co.MainInductionStep.Defs
public import MIPRE.Background.LIDT.Co.MakingMeasurementsProjective.Projectivization
public import MIPStarRE.LDT.SelfImprovement.Defs

@[expose] public section

/-!
# Section 9 — Definitions

The paper's SDP witnesses, the averaged point operators `A_g = E_u A^u_{g(u)}`, the SDP operators
built from them, and the pointwise and averaged sandwiched submeasurements
`H^u_h = A^u_{h(u)} T_h A^u_{h(u)}` and `H_h = E_u H^u_h` of `thm:self-improvement`: the
counterpart of `MIPRE/Background/LIDT/MIPStarRE/LDT/SelfImprovement/Defs.lean` in the port of
`planning/c6b-plan.md` (milestone M10, section "Port conventions").

A strategy is a `SymStrat params 𝔓 K` (`Co/Test/StrategyCore.lean`), and every operator of this
file is local: the primal witness `T`, the dual witness `Z`, the averaged point operators and the
sandwiched submeasurements live in the C*-algebra `𝔓` (the vendored `Op ι`). The vendored
matrix steps become generic ones: `Matrix.PosSemidef.one.nonneg` is `zero_le_one`, the
`Matrix.sum_mul`/`Matrix.mul_sum` regrouping is `Finset.sum_mul`/`Finset.mul_sum`, and the
sandwich bound is `IsSelfAdjoint.conjugate_le_conjugate` in `𝔓`.

The vendored file imports `MakingMeasurementsProjective/NaimarkCore.lean`, which M8 did not port
(its finite-dimensional orthonormalization is replaced by T1). No `NaimarkCore` declaration is
named anywhere in `SelfImprovement` outside the matrix realization, which is not ported either;
what `SelfImprovement` reaches through that import is the `ProjSubMeas`/`zeroProjSubMeas` API and
`orthonormalizationError`. So this file imports the ported
`Co/MakingMeasurementsProjective/Projectivization.lean` in its place, which brings the former, and
through `Co/MakingMeasurementsProjective/Statements.lean` the vendored
`MakingMeasurementsProjective/Defs.lean` with the latter.

The classical declarations of the vendored file (the distinguished polynomial, the strict primal
weight, the `add-in-u` selections and the six error terms) are imported from it and named through
an explicit `open MIPStarRE.LDT.SelfImprovement (…)` list. The two threshold files of the
vendored directory, `SelfImprovement/Theorems/Thresholds/Helper.lean` and
`SelfImprovement/Theorems/Thresholds/Final.lean`, are wholly classical (scalar error
bookkeeping): they get no Co file, and the ported files that need them import them, as M3 imports
`Preliminaries/Polynomials.lean`.

## Not ported

- `sdpDistinguishedPolynomial`: classical, imported.
- `sdpStrictPrimalWeight`: classical, imported.
- `AddInUSelection`: classical, imported.
- `addInUSelectionPairs`: classical, imported.
- `selfImprovementVarianceError`: classical, imported.
- `addInUError`: classical, imported.
- `selfImprovementHelperError`: classical, imported.
- `selfImprovementOrthogonalizationError`: classical, imported.
- `selfImprovementDataProcessingError`: classical, imported.
- `selfImprovementError`: classical, imported.
- `sdpPrimalObjective`: the real part of the matrix trace of `sdpPrimalObjectiveOperator`; the
  model has no trace, and nothing in the vendored tree outside the matrix realization consumes it.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/self_improvement.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.SelfImprovement

open MIPStarRE.LDT (Parameters FieldModel Point Fq uniformDistribution polynomial_sum_fiberwise)
open MIPStarRE.LDT.SelfImprovement (sdpDistinguishedPolynomial sdpStrictPrimalWeight)
open MIPRE.LIDT.Co.GlobalVariance (pointConditionedOutcomeOperatorAtPolynomial)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [PartialOrder 𝔓] [StarOrderedRing 𝔓] in
/-- Paper origin: `references/ldt-paper/self_improvement.tex:168-176`
(`\label{lem:sdp}` strict feasible primal witness
`T_g = (2 |\polyfunc{m}{q}{d}|)^{-1} I`).

The constant strict primal effects have total mass `(1/2)I`. This is the
scalar identity behind the paper's strict feasible primal witness. -/
theorem sdpStrictPrimalConstantSum (params : Parameters) [FieldModel params.q] :
    ∑ _ : MIPStarRE.LDT.Polynomial params, sdpStrictPrimalWeight params • (1 : 𝔓) =
      (1 / 2 : ℝ) • (1 : 𝔓) := by
  have hdenom : (2 * (Fintype.card (MIPStarRE.LDT.Polynomial params) : ℝ)) ≠ 0 := by
    positivity
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  unfold sdpStrictPrimalWeight
  field_simp

/-- The paper's strict-feasible primal SDP witness
`T_g = (2 |\polyfunc{m}{q}{d}|)^{-1} I`. -/
noncomputable def sdpStrictPrimalSubMeas (params : Parameters) [FieldModel params.q] :
    SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓 where
  outcome := fun _ => sdpStrictPrimalWeight params • (1 : 𝔓)
  total := ∑ _ : MIPStarRE.LDT.Polynomial params, sdpStrictPrimalWeight params • (1 : 𝔓)
  outcome_pos := fun _ => smul_nonneg (by unfold sdpStrictPrimalWeight; positivity) zero_le_one
  sum_eq_total := rfl
  total_le_one := (sdpStrictPrimalConstantSum params).trans_le
    ((smul_le_smul_of_nonneg_right (show (1 / 2 : ℝ) ≤ 1 by norm_num) zero_le_one).trans_eq
      (one_smul ℝ 1))

/-- The paper's uniform strict-feasible primal witness has total mass
`(1 / 2) • I`. -/
@[simp] theorem sdpStrictPrimalSubMeas_total (params : Parameters) [FieldModel params.q] :
    (sdpStrictPrimalSubMeas (𝔓 := 𝔓) params).total = (1 / 2 : ℝ) • (1 : 𝔓) :=
  sdpStrictPrimalConstantSum params

/-- Paper origin: `references/ldt-paper/self_improvement.tex:168-176`
(`\label{lem:sdp}` strict feasible dual witness `Z = 2I`);
blueprint `\label{lem:sdp-uniform-feasible-witness}`.

The paper's strict-feasible dual SDP witness `Z = 2I`. -/
noncomputable def sdpStrictDualWitness : 𝔓 :=
  (2 : ℝ) • (1 : 𝔓)

/-- The paper's strict-feasible dual witness `2I` is positive. -/
@[simp] theorem sdpStrictDualWitness_nonneg : 0 ≤ (sdpStrictDualWitness : 𝔓) :=
  smul_nonneg (by norm_num) zero_le_one

/-- The paper's strict-feasible dual witness dominates the identity: `I ≤ 2I`. -/
theorem one_le_sdpStrictDualWitness : (1 : 𝔓) ≤ sdpStrictDualWitness :=
  (one_smul ℝ (1 : 𝔓)).symm.trans_le
    (smul_le_smul_of_nonneg_right (show (1 : ℝ) ≤ 2 by norm_num) zero_le_one)

/-- The averaged point operator `A_g = E_u A^u_{g(u)}`. -/
noncomputable def averagedPointOperator (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K) (g : MIPStarRE.LDT.Polynomial params) : 𝔓 :=
  averageOperatorOverDistribution (uniformDistribution (Point params))
    (pointConditionedOutcomeOperatorAtPolynomial params strategy g)

/-- The averaged point operator `A_g` is positive. -/
theorem averagedPointOperator_nonneg (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K) (g : MIPStarRE.LDT.Polynomial params) :
    0 ≤ averagedPointOperator params strategy g :=
  averageOperatorOverDistribution_nonneg _ _
    fun u => (strategy.pointMeasurement u).toSubMeas.outcome_pos (g u)

/--
The operator `T_g A_g` contributing to the primal SDP objective.

We take `T` to be a `SubMeas` rather than a full `Measurement` because the
paper's Section 9 primal only assumes `∑_g T_g ≤ I`.
-/
noncomputable def sdpPrimalContributionOperator (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K) (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (g : MIPStarRE.LDT.Polynomial params) : 𝔓 :=
  T.outcome g * averagedPointOperator params strategy g

/-- The formal primal objective operator `Σ_g T_g A_g`. -/
noncomputable def sdpPrimalObjectiveOperator (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K) (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) : 𝔓 :=
  ∑ g : MIPStarRE.LDT.Polynomial params, sdpPrimalContributionOperator params strategy T g

/-- The dual slack operator `Z - A_g`. -/
noncomputable def sdpDualSlackOperator (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K) (Z : 𝔓) (g : MIPStarRE.LDT.Polynomial params) : 𝔓 :=
  Z - averagedPointOperator params strategy g

/-- Dual feasibility already implies that the dual operator is positive, since every averaged
point operator `A_g` is positive. -/
theorem sdpDualPositive_of_dualFeasible (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K) (Z : 𝔓)
    (hdual : ∀ g : MIPStarRE.LDT.Polynomial params,
      0 ≤ sdpDualSlackOperator params strategy Z g) :
    0 ≤ Z :=
  -- Any polynomial would suffice here; the distinguished one is only a
  -- convenient fixed element of the finite polynomial type.
  (averagedPointOperator_nonneg params strategy (sdpDistinguishedPolynomial params)).trans
    (sub_nonneg.mp (hdual (sdpDistinguishedPolynomial params)))

/-- The complementary-slackness equation `T_g Z = T_g A_g`. -/
def sdpComplementarySlacknessEquation (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K) (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (Z : 𝔓) (g : MIPStarRE.LDT.Polynomial params) : Prop :=
  T.outcome g * Z = T.outcome g * averagedPointOperator params strategy g

/-- The pointwise sandwiched operator `H^u_h = A^u_{h(u)} T_h A^u_{h(u)}`. -/
noncomputable def sandwichedPolynomialOutcomeOperatorAt (params : Parameters)
    [FieldModel params.q] (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (u : Point params) (h : MIPStarRE.LDT.Polynomial params) : 𝔓 :=
  let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
  Au * (T.outcome h) * Au

/-- The sum of the pointwise sandwiched operators is bounded above by the identity: regrouped
by the value `a = h(u)`, it is `∑_a A^u_a (∑_{h(u) = a} T_h) A^u_a ≤ ∑_a A^u_a = 1`. -/
theorem sandwichedPolynomialOutcomeOperatorAt_sum_le_one (params : Parameters)
    [FieldModel params.q] (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) (u : Point params) :
    ∑ h : MIPStarRE.LDT.Polynomial params,
      sandwichedPolynomialOutcomeOperatorAt params strategy T u h ≤ 1 := by
  let Au := strategy.pointMeasurement u
  rw [polynomial_sum_fiberwise params u]
  calc
    ∑ a : Fq params, ∑ h ∈ Finset.univ.filter
          (fun h : MIPStarRE.LDT.Polynomial params => h u = a),
        sandwichedPolynomialOutcomeOperatorAt params strategy T u h
      = ∑ a : Fq params, Au.toSubMeas.outcome a *
          (∑ h ∈ Finset.univ.filter (fun h : MIPStarRE.LDT.Polynomial params => h u = a),
            T.outcome h) * Au.toSubMeas.outcome a := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun h hh => ?_
        simp only [sandwichedPolynomialOutcomeOperatorAt,
          pointConditionedOutcomeOperatorAtPolynomial, (Finset.mem_filter.1 hh).2, Au]
    _ ≤ ∑ a : Fq params, Au.toSubMeas.outcome a := by
        refine Finset.sum_le_sum fun a _ => ?_
        have hle : ∑ h ∈ Finset.univ.filter
            (fun h : MIPStarRE.LDT.Polynomial params => h u = a), T.outcome h ≤ 1 :=
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun h _ _ => T.outcome_pos h).trans (T.sum_eq_total.trans_le T.total_le_one)
        simpa [Au.proj a] using
          IsSelfAdjoint.conjugate_le_conjugate hle (Au.outcome_hermitian a)
    _ = 1 := Au.toSubMeas.sum_eq_total.trans Au.total_eq_one

/-- The pointwise sandwiched submeasurement `H^u = {H^u_h}`. -/
noncomputable def sandwichedPolynomialSubMeasAt (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K) (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (u : Point params) : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓 where
  outcome := sandwichedPolynomialOutcomeOperatorAt params strategy T u
  total := ∑ h : MIPStarRE.LDT.Polynomial params,
    sandwichedPolynomialOutcomeOperatorAt params strategy T u h
  outcome_pos := fun h =>
    IsSelfAdjoint.conjugate_nonneg (T.outcome_pos h)
      ((strategy.pointMeasurement u).toSubMeas.outcome_hermitian (h u))
  sum_eq_total := rfl
  total_le_one := sandwichedPolynomialOutcomeOperatorAt_sum_le_one params strategy T u

/-- The average of the total pointwise sandwiched operators is bounded by the identity. -/
theorem averagedSandwichedPolynomialSubMeas_total_le_one (params : Parameters)
    [FieldModel params.q] (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    ∑ h : MIPStarRE.LDT.Polynomial params,
      averageOperatorOverDistribution (uniformDistribution (Point params))
        (fun u => sandwichedPolynomialOutcomeOperatorAt params strategy T u h) ≤ 1 :=
  (averageOperatorOverDistribution_sum (uniformDistribution (Point params))
      (fun u h => sandwichedPolynomialOutcomeOperatorAt params strategy T u h)).symm.trans_le
    (averageOperatorOverDistribution_uniform_le_one _ fun u =>
      sandwichedPolynomialOutcomeOperatorAt_sum_le_one params strategy T u)

/-- The averaged sandwiched submeasurement `H_h = E_u H^u_h`. -/
noncomputable def averagedSandwichedPolynomialSubMeas (params : Parameters)
    [FieldModel params.q] (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓 where
  outcome := fun h =>
    averageOperatorOverDistribution (uniformDistribution (Point params))
      (fun u => sandwichedPolynomialOutcomeOperatorAt params strategy T u h)
  total := ∑ h : MIPStarRE.LDT.Polynomial params,
    averageOperatorOverDistribution (uniformDistribution (Point params))
      (fun u => sandwichedPolynomialOutcomeOperatorAt params strategy T u h)
  outcome_pos := fun h => averageOperatorOverDistribution_nonneg _ _
    fun u => (sandwichedPolynomialSubMeasAt params strategy T u).outcome_pos h
  sum_eq_total := rfl
  total_le_one := averagedSandwichedPolynomialSubMeas_total_le_one params strategy T

end MIPRE.LIDT.Co.SelfImprovement

end
