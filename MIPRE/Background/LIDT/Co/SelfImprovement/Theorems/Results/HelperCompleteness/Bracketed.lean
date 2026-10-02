/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
SelfImprovement/Theorems/Results/HelperCompleteness/Bracketed.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.HelperCompleteness.Linearized
public import MIPRE.Background.LIDT.Co.GlobalVariance.Theorems.MainTheorems
public import MIPRE.Background.LIDT.Co.Doubling.Sdp

@[expose] public section

/-!
# Helper completeness: bracketed mass identities, the SDP, and reduced reductions

The exact bracketed reindexing of the helper-stage mass, the paper-shaped completeness
assemblies, the SDP statement `lem:sdp` with complementary slackness, and the reduced `addInU`
reduction used by the surrounding self-improvement theorem: the counterpart of the vendored
`SelfImprovement/Theorems/Results/HelperCompleteness/Bracketed.lean` (under
`MIPRE/Background/LIDT/MIPStarRE/LDT/`) in the port of `planning/c6b-plan.md` (milestone M10,
section "Port conventions").

A strategy is a `SymStrat params 𝔓 K`; `T`, `Hhat` and `Z` are local, in `𝔓`, and the joint
operators are `strategy.state.L` and `strategy.state.R` in `K →L[ℂ] K`. The vendored
`Hhat.liftLeft` is `Hhat.liftLeft strategy.state`, and `subMeasMass`, `ConsRel`,
`BipartiteSSCRel` and `CompletenessAtLeast` are those of the state. The vendored
`Matrix.sum_mul`/`Matrix.mul_sum` regrouping is `Finset.sum_mul`/`Finset.mul_sum`, and the
averaging step of `helper_mass_eq_avg_pointwise_sandwich_sum` is the keystone's
`ev_leftTensor_averageOperatorOverDistribution`, in place of the vendored
`ev_opTensor_averageOperatorOverDistribution_left` at `B = 1`. The vendored file has no swap or
density hypotheses.

**The SDP producer.** The vendored `sdp_statement_with_slackness` is unconditional: it is
finite-dimensional Slater duality, through the canonical block SDP of the matrix realization and
the bridge `SelfImprovement/Theorems/Results/SdpMatrixBridge.lean`. Here it is M9's summed
semidefinite form: Theorem 10 (`MIPRE/Foundations/SummedSdp.lean`,
`MIPRE/Background/Orthonormalization/SdpMaximizer.lean`), pulled back to the first player's
algebra by `Doubling.exists_isSummedSdp_A` (`Co/Doubling/Sdp.lean`) and read as the SDP statement
by `SdpStatementWithSlackness.of_isSummedSdp` (`Co/SelfImprovement/Theorems/Statements.lean`).
Theorem 10 maximizes over the faithful trace of a finite pair (`reports/c6b-paper-proofs.md`,
§5.1 and §5.3), so `sdp_statement_with_slackness` and `sdp_slackness_measurement` take
`hS : strategy.state.toBipartite.IsFinitePair` after `strategy`. Neither needs the absence of
abelian projections, `ζ > 0` or the doubling.

**Dropped vendored files.** The pairing script reads only ported files, so the two vendored
inputs of the SDP producer that have no Co file are recorded here.
- `SelfImprovement/Theorems/Results/SdpMatrixBridge.lean` (313 lines), the bridge from the
  finite-dimensional matrix SDP to `SdpStatementWithSlackness`. Its declarations
  `matrixSdpPointRealizationOfStrategy`, `matrixAveragedPointOperator_ofPointRealization`,
  `matrixSdpDualSlackOperator_ofPointRealization`, `MatrixSdpCanonicalOptimalPair`,
  `ofFeasibleStrongDualitySaturateSlackBlock`, `toMatrixSdpStatementWithSlackness`,
  `toSdpOptimalPairWithSlackness`, `toSdpStatementWithSlackness`,
  `matrixSdpPointRealization_canonicalOptimalPair` and
  `matrixSdpPointRealization_statementWithSlackness` are not ported: they are replaced by M9's
  summed form through `SdpStatementWithSlackness.of_isSummedSdp` and
  `Doubling.exists_isSummedSdp_A`.
- `SelfImprovement/MatrixRealization/` (7 files, 3,667 lines, among them `Canonical/Saturated`
  and `Canonical/StrongDuality/Separation`, the two modules `SdpMatrixBridge` imports): the
  canonical block SDP, Slater strong duality and slack-block saturation. Its only importer is
  `SdpMatrixBridge`, whose only importer is this file. It is replaced by Theorem 10
  (`MIPRE/Foundations/SummedSdp.lean`, `MIPRE/Background/Orthonormalization/SdpMaximizer.lean`).

"Dropped" means that no Co declaration uses these files, which a constant-closure walk over the
built oleans confirms. They stay in the build's import closure through the classical imports:
Co `AddInUStep34AndTransfer/{Factored,Selected,Transfer,Variance}`, `AddInUPointConsistency` and
`HelperSSC/Core` import their vendored counterparts for classical lemmas, and each of those reaches
the vendored `AddInUStep34AndTransfer/Factored`, which imports the vendored version of this file,
which imports `SdpMatrixBridge` and through it `MatrixRealization/Canonical/Saturated` …
`MatrixRealization/Base`. Likewise `MakingMeasurementsProjective/NaimarkCore`, dropped by M8, stays
in the closure through Co `SelfImprovement/Defs` → vendored `SelfImprovement/Defs`. Moving those
classical declarations into modules that import neither would remove them
(`planning/c6b-plan.md`, "Departures in M10 and M11").

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/self_improvement.tex` lines 62--190 and 354--414
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.SelfImprovement

open MIPStarRE.LDT (Parameters FieldModel Point Fq avgOver uniformDistribution avgOver_congr
  avgOver_sum polynomial_sum_fiberwise)
open MIPStarRE.LDT.SelfImprovement (sdpDistinguishedPolynomial selfImprovementHelperError
  selfImprovementVarianceError)
open MIPRE.LIDT.Co.GlobalVariance (pointConditionedOutcomeOperatorAtPolynomial
  globalVarianceOfPointsFromTransportChainBound localVarianceTransportChainBound)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Exact `Hhat` reindexing for the helper-stage left-placed mass.

Expanding `Hhat = E_u H^u` through `subMeasMass (Hhat.liftLeft S) = ev (L Hhat.total)`,
swapping the placement through the polynomial sum, and pulling the `ev` through
the per-outcome point average gives the paper identity

  `⟨ψ| Hhat ⊗ I |ψ⟩ = E_u Σ_h ⟨ψ| H^u_h ⊗ I |ψ⟩`,

where `H^u_h = A^u_{h(u)} · T_h · A^u_{h(u)}` is
`sandwichedPolynomialOutcomeOperatorAt`. This is the algebraic opening of the
helper-stage completeness chain at
`references/ldt-paper/self_improvement.tex`, lines 354--356.

The conclusion is exact (not approximate) and depends on no input-consistency
or SDP hypotheses. -/
theorem helper_mass_eq_avg_pointwise_sandwich_sum
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    strategy.state.subMeasMass
        ((averagedSandwichedPolynomialSubMeas params strategy T).liftLeft strategy.state) =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : MIPStarRE.LDT.Polynomial params,
          strategy.state.ev
            (strategy.state.L
              (sandwichedPolynomialOutcomeOperatorAt params strategy T u h))) := by
  rw [avgOver_sum]
  refine (strategy.state.ev_leftTensor_total_eq_sum_outcome _).trans
    (Finset.sum_congr rfl fun h _ => ?_)
  exact strategy.state.ev_leftTensor_averageOperatorOverDistribution _ _

/-- Operator-level fiberwise reindexing identity for the per-point sandwich
operator. Inside each fiber `{h : h u = a}` the inner `A^u_{h(u)}` is constant
(equal to `A^u_a`), and `Finset.sum_mul`/`Finset.mul_sum` pull this constant
factor through the sum over `T_h`. Mirrors the operator-level computation in
`sandwichedPolynomialOutcomeOperatorAt_sum_le_one`. -/
lemma sandwichedPolynomialOutcomeOperatorAt_sum_eq_bracketed
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) (u : Point params) :
    (∑ h : MIPStarRE.LDT.Polynomial params,
        sandwichedPolynomialOutcomeOperatorAt params strategy T u h) =
      ∑ a : Fq params,
        (strategy.pointMeasurement u).outcome a *
          (∑ h ∈ Finset.univ.filter (fun h : MIPStarRE.LDT.Polynomial params => h u = a),
            T.outcome h) *
          (strategy.pointMeasurement u).outcome a := by
  rw [polynomial_sum_fiberwise params u]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun h hh => ?_
  simp only [sandwichedPolynomialOutcomeOperatorAt,
    pointConditionedOutcomeOperatorAtPolynomial, (Finset.mem_filter.1 hh).2]

/-- Per-point bracketing identity for the helper-stage left-placed mass.

Fiberwise reindexing by `h ↦ h(u)` and pulling `A^u_a · _ · A^u_a` through the
sum, the placement, and `ev` give the paper identity at a fixed point `u`:

  `Σ_h ⟨ψ| H^u_h ⊗ I |ψ⟩
    = Σ_a ⟨ψ| (A^u_a · T_{[h(u) = a]} · A^u_a) ⊗ I |ψ⟩`,

where `H^u_h = A^u_{h(u)} · T_h · A^u_{h(u)}` is
`sandwichedPolynomialOutcomeOperatorAt`, and the bracketed
`T_{[h(u) = a]} = Σ_{h : h u = a} T_h` is the inner fiber sum.

This is the identity `eq:bracketize-the-expression` of
`references/ldt-paper/self_improvement.tex`, lines 356--358, at a fixed
point `u` (before averaging). The conclusion is exact and depends on no
input-consistency, SDP, or self-consistency hypotheses. -/
theorem helper_pointwise_sandwich_sum_eq_bracketed
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) (u : Point params) :
    (∑ h : MIPStarRE.LDT.Polynomial params,
        strategy.state.ev
          (strategy.state.L
            (sandwichedPolynomialOutcomeOperatorAt params strategy T u h))) =
      ∑ a : Fq params,
        strategy.state.ev
          (strategy.state.L
            ((strategy.pointMeasurement u).outcome a *
              (∑ h ∈ Finset.univ.filter (fun h : MIPStarRE.LDT.Polynomial params => h u = a),
                T.outcome h) *
              (strategy.pointMeasurement u).outcome a)) := by
  rw [← strategy.state.ev_finset_sum, strategy.state.leftTensor_finset_sum,
    sandwichedPolynomialOutcomeOperatorAt_sum_eq_bracketed, ← strategy.state.leftTensor_finset_sum,
    strategy.state.ev_finset_sum]

/-- Bracketed form of the helper-stage `Hhat ⊗ I` mass identity.

Combines `helper_mass_eq_avg_pointwise_sandwich_sum` with the per-point
bracketing identity `helper_pointwise_sandwich_sum_eq_bracketed`:

  `⟨ψ| Hhat ⊗ I |ψ⟩
    = E_u Σ_a ⟨ψ| (A^u_a · T_{[h(u) = a]} · A^u_a) ⊗ I |ψ⟩`,

where `T_{[h(u) = a]} = Σ_{h : h u = a} T_h`. This is the second equality in the
displayed completeness chain at `references/ldt-paper/self_improvement.tex`,
lines 354--358, composed with `eq:bracketize-the-expression`. The conclusion
is exact and depends on no input-consistency, SDP, or self-consistency
hypotheses. -/
theorem helper_mass_eq_avg_pointwise_bracketed_sum
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    strategy.state.subMeasMass
        ((averagedSandwichedPolynomialSubMeas params strategy T).liftLeft strategy.state) =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ a : Fq params,
          strategy.state.ev
            (strategy.state.L
              ((strategy.pointMeasurement u).outcome a *
                (∑ h ∈ Finset.univ.filter (fun h : MIPStarRE.LDT.Polynomial params => h u = a),
                  T.outcome h) *
                (strategy.pointMeasurement u).outcome a))) := by
  rw [helper_mass_eq_avg_pointwise_sandwich_sum]
  exact avgOver_congr (uniformDistribution (Point params)) _ _ fun u =>
    helper_pointwise_sandwich_sum_eq_bracketed params strategy T u

/-- The named bracketed helper-completeness quantity is exactly the
helper-stage `Hhat ⊗ I` mass for the averaged sandwiched family.

This is the Lean form of the equality labelled
`eq:bracketize-the-expression`, after composing the fiberwise reindexing with
the preceding expansion of `Hhat` as the average of the pointwise sandwiched
submeasurements. -/
theorem helperBracketedCompletenessQuantity_eq_mass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    helperBracketedCompletenessQuantity params strategy T =
      strategy.state.subMeasMass
        ((averagedSandwichedPolynomialSubMeas params strategy T).liftLeft strategy.state) :=
  (helper_mass_eq_avg_pointwise_bracketed_sum params strategy T).symm

/-- The paper-shaped `Hhat`-versus-`Z` comparison assembled from the bracketed
expression, the two Cauchy--Schwarz estimates, and complementary slackness.

The first Cauchy--Schwarz hypothesis moves from the bracketed expression
`E_u Σ_a ⟨ψ, (A^u_a T_[h(u)=a] A^u_a) ⊗ I ψ⟩` to
`helperFirstMovedCompletenessQuantity`.  The second removes the remaining
right-register copy of `A^u_a`, giving `helperLinearizedCompletenessQuantity`.
The latter is then identified with the dual mass by the SDP
complementary-slackness equation. -/
theorem helper_hhat_vs_z_of_bracketed_cauchy_schwarz_and_complementary_slackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    {T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Z : 𝔓}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hmove_left :
      |helperFirstMovedCompletenessQuantity params strategy T.toSubMeas -
        helperBracketedCompletenessQuantity params strategy T.toSubMeas| ≤
        2 * Real.sqrt delta)
    (hremove_right :
      |helperLinearizedCompletenessQuantity params strategy T.toSubMeas -
        helperFirstMovedCompletenessQuantity params strategy T.toSubMeas| ≤
        Real.sqrt delta)
    (hslack :
      ∀ h : MIPStarRE.LDT.Polynomial params,
        T.toSubMeas.outcome h * averagedPointOperator params strategy h =
          T.toSubMeas.outcome h * Z) :
    strategy.state.ev (strategy.state.L Z) - 3 * Real.sqrt delta ≤
      strategy.state.subMeasMass (Hhat.liftLeft strategy.state) := by
  have hbracket_mass :
      helperBracketedCompletenessQuantity params strategy T.toSubMeas =
        strategy.state.subMeasMass (Hhat.liftLeft strategy.state) := by
    rw [hhelper.averagedConstruction]
    exact helperBracketedCompletenessQuantity_eq_mass params strategy T.toSubMeas
  refine
    helper_hhat_vs_z_of_cauchy_schwarz_and_complementary_slackness
      params strategy eps delta hhelper ?_ hremove_right hslack
  rwa [← hbracket_mass]

/-- The `Hhat`-versus-`Z` comparison from point self-consistency and
complementary slackness.

This is the helper-completeness comparison at
`eq:gonna-use-this-later-H-versus-Z` with the two Cauchy--Schwarz estimates
supplied internally by `helper_first_move_abs_sub_bracketed_le_two_sqrt_delta`
and `helper_second_move_abs_sub_first_moved_le_sqrt_delta`. -/
theorem helper_hhat_vs_z_of_self_consistency_and_complementary_slackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    {T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Z : 𝔓}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hssc : strategy.state.BipartiteSSCRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hslack :
      ∀ h : MIPStarRE.LDT.Polynomial params,
        T.toSubMeas.outcome h * averagedPointOperator params strategy h =
          T.toSubMeas.outcome h * Z) :
    strategy.state.ev (strategy.state.L Z) - 3 * Real.sqrt delta ≤
      strategy.state.subMeasMass (Hhat.liftLeft strategy.state) :=
  helper_hhat_vs_z_of_bracketed_cauchy_schwarz_and_complementary_slackness
    params strategy eps delta hhelper
    (helper_first_move_abs_sub_bracketed_le_two_sqrt_delta
      params strategy T.toSubMeas delta hssc)
    (helper_second_move_abs_sub_first_moved_le_sqrt_delta
      params strategy T.toSubMeas delta hssc)
    hslack

/-- Helper-stage completeness from the paper-shaped Cauchy--Schwarz estimates,
complementary slackness, and input consistency.

Compared with `helper_completeness_of_cauchy_schwarz_input_consistency`, this
version names the expression before the first Cauchy--Schwarz move exactly as
it appears in `eq:bracketize-the-expression`; the equality with the
`Hhat`-mass is supplied internally by
`helperBracketedCompletenessQuantity_eq_mass`. -/
theorem helper_completeness_of_bracketed_cauchy_schwarz_input_consistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓)
    (eps delta nu : ℝ)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    {T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Z : 𝔓}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hmove_left :
      |helperFirstMovedCompletenessQuantity params strategy T.toSubMeas -
        helperBracketedCompletenessQuantity params strategy T.toSubMeas| ≤
        2 * Real.sqrt delta)
    (hremove_right :
      |helperLinearizedCompletenessQuantity params strategy T.toSubMeas -
        helperFirstMovedCompletenessQuantity params strategy T.toSubMeas| ≤
        Real.sqrt delta)
    (hslack :
      ∀ h : MIPStarRE.LDT.Polynomial params,
        T.toSubMeas.outcome h * averagedPointOperator params strategy h =
          T.toSubMeas.outcome h * Z)
    (hcons : strategy.state.ConsRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas) nu) :
    strategy.state.CompletenessAtLeast (Hhat.liftLeft strategy.state)
      ((1 - nu) - selfImprovementHelperError params eps delta) :=
  helper_completeness_of_input_consistency params strategy G eps delta nu
    heps hdelta hhelper
    (helper_hhat_vs_z_of_bracketed_cauchy_schwarz_and_complementary_slackness
      params strategy eps delta hhelper hmove_left hremove_right hslack)
    hcons

/-- Helper-stage completeness from point self-consistency, complementary
slackness, and input consistency.

This theorem removes the two external Cauchy--Schwarz hypotheses from
`helper_completeness_of_bracketed_cauchy_schwarz_input_consistency`; both are
proved from the single point-measurement self-consistency hypothesis. -/
theorem helper_completeness_of_self_consistency_complementary_slackness_input_consistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓)
    (eps delta nu : ℝ)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    {T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Z : 𝔓}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hssc : strategy.state.BipartiteSSCRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hslack :
      ∀ h : MIPStarRE.LDT.Polynomial params,
        T.toSubMeas.outcome h * averagedPointOperator params strategy h =
          T.toSubMeas.outcome h * Z)
    (hcons : strategy.state.ConsRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas) nu) :
    strategy.state.CompletenessAtLeast (Hhat.liftLeft strategy.state)
      ((1 - nu) - selfImprovementHelperError params eps delta) :=
  helper_completeness_of_bracketed_cauchy_schwarz_input_consistency
    params strategy G eps delta nu heps hdelta hhelper
    (helper_first_move_abs_sub_bracketed_le_two_sqrt_delta
      params strategy T.toSubMeas delta hssc)
    (helper_second_move_abs_sub_first_moved_le_sqrt_delta
      params strategy T.toSubMeas delta hssc)
    hslack hcons

/-- Extract the orientation of complementary slackness used by the helper
completeness proof from the strengthened helper conclusion. -/
theorem helper_slackness_eq_of_helper_with_slackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    {T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Z : 𝔓}
    (hhelper :
      SelfImprovementHelperConclusionWithSlackness params strategy T Hhat Z eps delta)
    (h : MIPStarRE.LDT.Polynomial params) :
    T.toSubMeas.outcome h * averagedPointOperator params strategy h =
      T.toSubMeas.outcome h * Z :=
  (hhelper.complementarySlackness h).symm

/-- The `Hhat`-versus-`Z` comparison from point self-consistency and a helper
conclusion carrying SDP complementary slackness.

This is the version of `eq:gonna-use-this-later-H-versus-Z` whose inputs are a
single strengthened helper conclusion and point-measurement self-consistency,
rather than a separate family of slackness equations. -/
theorem helper_hhat_vs_z_of_self_consistency_and_helper_slackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    {T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Z : 𝔓}
    (hhelper :
      SelfImprovementHelperConclusionWithSlackness params strategy T Hhat Z eps delta)
    (hssc : strategy.state.BipartiteSSCRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta) :
    strategy.state.ev (strategy.state.L Z) - 3 * Real.sqrt delta ≤
      strategy.state.subMeasMass (Hhat.liftLeft strategy.state) :=
  helper_hhat_vs_z_of_self_consistency_and_complementary_slackness
    params strategy eps delta hhelper.toHelperConclusion hssc
    (helper_slackness_eq_of_helper_with_slackness params strategy eps delta hhelper)

/-- Helper-stage completeness from point self-consistency, a helper conclusion
carrying SDP complementary slackness, and input consistency.

This theorem removes the standalone `hslack` hypothesis from
`helper_completeness_of_self_consistency_complementary_slackness_input_consistency`;
the slackness equations are read from
`SelfImprovementHelperConclusionWithSlackness`. -/
theorem helper_completeness_of_self_consistency_helper_slackness_input_consistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓)
    (eps delta nu : ℝ)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    {T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Hhat : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓}
    {Z : 𝔓}
    (hhelper :
      SelfImprovementHelperConclusionWithSlackness params strategy T Hhat Z eps delta)
    (hssc : strategy.state.BipartiteSSCRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hcons : strategy.state.ConsRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas) nu) :
    strategy.state.CompletenessAtLeast (Hhat.liftLeft strategy.state)
      ((1 - nu) - selfImprovementHelperError params eps delta) :=
  helper_completeness_of_self_consistency_complementary_slackness_input_consistency
    params strategy G eps delta nu heps hdelta hhelper.toHelperConclusion hssc
    (helper_slackness_eq_of_helper_with_slackness params strategy eps delta hhelper)
    hcons

/-- Paper-origin statement for `lem:sdp` with complementary slackness.

Paper origin: `references/ldt-paper/self_improvement.tex` lines 62--88 state
`\label{lem:sdp}` for the primal/dual SDP pair and assert optimal witnesses
`{T_g}`, `Z` with `∑ g, T_g = I` and `T_g Z = T_g A_g`.  Lines 168--190 prove
this by Slater strong duality and complementary slackness.

The vendored statement is unconditional: its proof is finite-dimensional Slater duality, through
the canonical block SDP of the matrix realization. Here the proof is M9's summed semidefinite
form: Theorem 10 (`MIPRE.Orthonormalization.exists_isSummedSdp_finitePairA`) maximizes over the
faithful trace of a finite pair (`reports/c6b-paper-proofs.md`, §5.1 and §5.3), so the port needs
`hS`, that the model's bipartite reading is a finite pair. `Doubling.exists_isSummedSdp_A` pulls
the solution back to `𝔓` for `A_g = averagedPointOperator params strategy g`, which is positive,
hence self-adjoint, and `SdpStatementWithSlackness.of_isSummedSdp` reads it as the statement. -/
theorem sdp_statement_with_slackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (hS : strategy.state.toBipartite.IsFinitePair) :
    SdpStatementWithSlackness params strategy := by
  have : Nonempty (MIPStarRE.LDT.Polynomial params) := ⟨sdpDistinguishedPolynomial params⟩
  obtain ⟨T, h⟩ := Doubling.exists_isSummedSdp_A hS (averagedPointOperator params strategy)
    fun g => IsSelfAdjoint.of_nonneg (averagedPointOperator_nonneg params strategy g)
  exact SdpStatementWithSlackness.of_isSummedSdp h

/-- Displayed measurement and complementary-slackness conclusion of `lem:sdp`.

Paper origin: `references/ldt-paper/self_improvement.tex` lines 82--88 state
that the Section 9 SDP admits a primal family `{T_g}` with `∑ g, T_g = I` and
a dual operator `Z` satisfying `T_g Z = T_g A_g` for every polynomial `g`.
This theorem extracts exactly that complete-measurement and slackness form from
`sdp_statement_with_slackness`. As there, the vendored theorem is unconditional (finite-dimensional
Slater duality), and the port takes `hS`, that the model's bipartite reading is a finite pair,
because Theorem 10 uses the faithful trace of a finite pair (`reports/c6b-paper-proofs.md`, §5.1
and §5.3). -/
theorem sdp_slackness_measurement
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (hS : strategy.state.toBipartite.IsFinitePair) :
    ∃ T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓,
      ∃ Z : 𝔓,
        0 ≤ Z ∧
        (∀ g : MIPStarRE.LDT.Polynomial params,
          0 ≤ sdpDualSlackOperator params strategy Z g) ∧
        ∀ g : MIPStarRE.LDT.Polynomial params,
          sdpComplementarySlacknessEquation params strategy T.toSubMeas Z g :=
  (sdp_statement_with_slackness params strategy hS).exists_measurement_witness

/-- Reduced version of `lem:add-in-u`.

This keeps only the global-variance consequence used downstream, derived from the
post-triangle six-step edge-transport chain bound via
`globalVarianceOfPointsFromTransportChainBound` and `localVarianceTransportChainBound`. The
`gamma` and `hgood` arguments are retained so that this reduced theorem matches the surrounding
self-improvement API and can be strengthened back to the full paper statement without a
caller-wide signature change. The selection-dependent transfer inequality from the paper,
together with its dependence on an auxiliary family `M` and the averaged family `H`, is not
formalized here. -/
lemma addInU
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (T : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓) :
    AddInUStatement params strategy T eps delta :=
  ⟨by simpa [selfImprovementVarianceError] using
    (globalVarianceOfPointsFromTransportChainBound params strategy eps delta gamma hgood
      T.toSubMeas
      (localVarianceTransportChainBound params strategy eps delta gamma hgood
        T.toSubMeas)).averagedGlobalVarianceBound⟩

end MIPRE.LIDT.Co.SelfImprovement

end
