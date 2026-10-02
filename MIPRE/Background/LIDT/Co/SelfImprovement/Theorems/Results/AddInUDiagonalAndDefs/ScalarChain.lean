/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
SelfImprovement/Theorems/Results/AddInUDiagonalAndDefs/ScalarChain.lean, to the symmetric model
of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.AddInUDiagonalAndDefs.Selection

@[expose] public section

/-!
# Scalar chain for the diagonal add-in-u transfer

The selected and diagonal `Q₀`--`Q₄` scalar chains used for the projection-simplified diagonal
add-in-`u` transfer, together with the endpoint identifications needed by the helper
strong-self-consistency proof: the counterpart of the vendored
`SelfImprovement/Theorems/Results/AddInUDiagonalAndDefs/ScalarChain.lean` (under
`MIPRE/Background/LIDT/MIPStarRE/LDT/`) in the port of `planning/c6b-plan.md` (milestone M10,
section "Port conventions").

A strategy is a `SymStrat params 𝔓 K`; the measurements `M`, `T` and the point projectors live
in `𝔓`, and every scalar of the chain is `strategy.state.ev` of a joint operator
`strategy.state.opTensor X Y`. The statements are the vendored ones, translated:

- `addInU_pointMeasurement_snd_selfConsistency` places with `IdxSubMeas.liftLeft strategy.state`
  and `IdxSubMeas.liftRight strategy.state`. The vendored proof passes `strategy.permInvState` to
  `Preliminaries.twoNotionsOfSelfConsistencyAfterEvaluation` with the identity postprocessing;
  here the ported `Preliminaries.twoNotionsOfSelfConsistency`, which has no swap hypothesis, is
  applied directly.
- `addInU_filtered_sandwiched_tensor_sum_le_one` bounds a joint operator, `≤ (1 : K →L[ℂ] K)`,
  through `SubMeas.opTensor_sum_filter_le_one strategy.state`.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/self_improvement.tex` lines 247--252
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.SelfImprovement

open MIPStarRE.LDT (Parameters FieldModel Point Fq avgOver uniformDistribution avgOver_congr
  avgOver_sum avgOver_finset_sum avgOver_uniform_prod avgOver_uniform_const avgOver_uniform_fst
  avgOver_uniform_snd)
open MIPStarRE.LDT.SelfImprovement (AddInUSelection addInUSelectionPairs)
open MIPRE.LIDT.Co.GlobalVariance (pointConditionedOutcomeOperatorAtPolynomial)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ### Scalar chain for the projection-simplified diagonal add-in-u transfer -/

/-- Strong self-consistency for the point measurement, pulled back to the second
coordinate of the independent `(u, v)` average used by the add-in-`u` scalar
chain.

This is the distributional self-consistency input for the `A^v_{h(v)}` moves in
`self_improvement.tex`, lines 255--297: the point measurement sampled at `v`
has the same `2δ` left/right state-dependent distance after the product average
over `(u, v)`. -/
lemma addInU_pointMeasurement_snd_selfConsistency
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (delta : ℝ)
    (hssc : strategy.state.BipartiteSSCRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta) :
    strategy.state.SDDRel (uniformDistribution (Point params × Point params))
      (IdxSubMeas.liftLeft strategy.state
        (fun uv : Point params × Point params =>
          (strategy.pointMeasurement uv.2).toSubMeas))
      (IdxSubMeas.liftRight strategy.state
        (fun uv : Point params × Point params =>
          (strategy.pointMeasurement uv.2).toSubMeas))
      (2 * delta) :=
  Preliminaries.twoNotionsOfSelfConsistency strategy.state
    (uniformDistribution (Point params × Point params))
    (fun uv : Point params × Point params => (strategy.pointMeasurement uv.2).toSubMeas) delta
    ⟨(avgOver_uniform_snd (α := Point params) (β := Point params)
      (fun v => strategy.state.qBipartiteSSCDefect (strategy.pointMeasurement v).toSubMeas)).trans_le
      hssc.overlapBound⟩

/-- The grouped tensor mass over a fiber `h(v)=a` is a contraction.

This is the submeasurement bound used inside the first Cauchy--Schwarz square
root in `self_improvement.tex`, lines 267--272: after grouping by the value
`a = h(v)`, the selected operators
`H^u_h ⊗ T_h` are dominated by the total mass of the sandwiched polynomial
submeasurement at `u`, hence by `I`. -/
lemma addInU_filtered_sandwiched_tensor_sum_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (u v : Point params) (a : Fq params) :
    ∑ h ∈ Finset.univ.filter (fun h : MIPStarRE.LDT.Polynomial params => h v = a),
        strategy.state.opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
          (T.outcome h) ≤
      (1 : K →L[ℂ] K) :=
  SubMeas.opTensor_sum_filter_le_one strategy.state
    (sandwichedPolynomialSubMeasAt params strategy T u) T
    (fun h : MIPStarRE.LDT.Polynomial params => h v = a)

/-! ### Selection-parametrized add-in-u scalar chain

The paper proves `lem:add-in-u` for an arbitrary outcome family `M` and
selection `S_u ⊆ 𝒪 × polyfunc`.  The diagonal helper strong-self-consistency
application below is one specialization of this statement.  The following
definitions record the same five scalar quantities before specializing to the
diagonal case, so that the off-diagonal point-consistency selection can reuse
the Cauchy--Schwarz chain rather than restating the transfer hypothesis. -/

/-- The selected-chain left endpoint `Q₀`.

For a selected pair `(o, h) ∈ S_u`, this is the expectation of
`M^u_o ⊗ H^v_h`, where `H^v_h = A^v_{h(v)} T_h A^v_{h(v)}`. -/
noncomputable def addInUSelectedCSChainQ0
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (M : IdxSubMeas (Point params) Outcome 𝔓)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (S : AddInUSelection params Outcome) : ℝ :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ ah ∈ addInUSelectionPairs params S uv.1,
      strategy.state.ev
        (strategy.state.opTensor ((M uv.1).outcome ah.1)
          ((sandwichedPolynomialSubMeasAt params strategy T uv.2).outcome ah.2)))

/-- The selected-chain scalar `Q₁`, after moving the right point projector
`A^v_{h(v)}` to the left tensor factor once. -/
noncomputable def addInUSelectedCSChainQ1
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (M : IdxSubMeas (Point params) Outcome 𝔓)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (S : AddInUSelection params Outcome) : ℝ :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ ah ∈ addInUSelectionPairs params S uv.1,
      let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
      strategy.state.ev
        (strategy.state.opTensor (Av * (M uv.1).outcome ah.1) (T.outcome ah.2 * Av)))

/-- The selected-chain scalar `Q₂`, after moving both right point projectors to
the left tensor factor. -/
noncomputable def addInUSelectedCSChainQ2
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (M : IdxSubMeas (Point params) Outcome 𝔓)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (S : AddInUSelection params Outcome) : ℝ :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ ah ∈ addInUSelectionPairs params S uv.1,
      let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
      strategy.state.ev
        (strategy.state.opTensor (Av * (M uv.1).outcome ah.1 * Av) (T.outcome ah.2)))

/-- The selected-chain scalar `Q₃`, after replacing the first point projector
at `v` by the corresponding point projector at `u`. -/
noncomputable def addInUSelectedCSChainQ3
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (M : IdxSubMeas (Point params) Outcome 𝔓)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (S : AddInUSelection params Outcome) : ℝ :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ ah ∈ addInUSelectionPairs params S uv.1,
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
      let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
      strategy.state.ev
        (strategy.state.opTensor (Au * (M uv.1).outcome ah.1 * Av) (T.outcome ah.2)))

/-- The selected-chain scalar `Q₄`, after replacing both point projectors at
`v` by the corresponding point projectors at `u`. -/
noncomputable def addInUSelectedCSChainQ4
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (M : IdxSubMeas (Point params) Outcome 𝔓)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (S : AddInUSelection params Outcome) : ℝ :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ ah ∈ addInUSelectionPairs params S uv.1,
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
      strategy.state.ev
        (strategy.state.opTensor (Au * (M uv.1).outcome ah.1 * Au) (T.outcome ah.2)))

/-- The selected-chain endpoint `Q₀` is the generic add-in-u left quantity when
the second measurement is the averaged sandwiched polynomial submeasurement. -/
theorem addInUSelectedCSChainQ0_eq_leftQuantity_averagedSandwiched
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (M : IdxSubMeas (Point params) Outcome 𝔓)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (S : AddInUSelection params Outcome) :
    addInULeftQuantity params strategy M
        (averagedSandwichedPolynomialSubMeas params strategy T)
        S =
      addInUSelectedCSChainQ0 params strategy M T S := by
  unfold addInUSelectedCSChainQ0
  rw [avgOver_uniform_prod (α := Point params) (β := Point params)
    (f := fun u v =>
      ∑ ah ∈ addInUSelectionPairs params S u,
        strategy.state.ev
          (strategy.state.opTensor ((M u).outcome ah.1)
            ((sandwichedPolynomialSubMeasAt params strategy T v).outcome ah.2)))]
  refine avgOver_congr (uniformDistribution (Point params)) _ _ fun u => ?_
  refine (strategy.state.ev_finset_sum _ _).trans ?_
  rw [avgOver_finset_sum]
  exact Finset.sum_congr rfl fun ah _ =>
    strategy.state.ev_opTensor_averageOperatorOverDistribution_right
      (uniformDistribution (Point params)) ((M u).outcome ah.1)
      (fun v => (sandwichedPolynomialSubMeasAt params strategy T v).outcome ah.2)

/-- The selected-chain endpoint `Q₄` is the generic add-in-u right quantity. -/
theorem addInUSelectedCSChainQ4_eq_rightQuantity
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (M : IdxSubMeas (Point params) Outcome 𝔓)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (S : AddInUSelection params Outcome) :
    addInURightQuantity params strategy M T S =
      addInUSelectedCSChainQ4 params strategy M T S := by
  unfold addInUSelectedCSChainQ4
  rw [avgOver_uniform_prod (α := Point params) (β := Point params)
    (f := fun u _ =>
      ∑ ah ∈ addInUSelectionPairs params S u,
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 u
        strategy.state.ev
          (strategy.state.opTensor (Au * (M u).outcome ah.1 * Au) (T.outcome ah.2)))]
  refine avgOver_congr (uniformDistribution (Point params)) _ _ fun u => ?_
  exact (strategy.state.ev_finset_sum _ _).trans (avgOver_uniform_const _).symm

/-- The expanded left endpoint `Q₀` of the four-step scalar chain in
`self_improvement.tex`, lines 247--252, after setting `M^u = H^u` and averaging
the second tensor factor `H = E_v H^v`. -/
noncomputable def addInUCSChainQ0
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) : ℝ :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ h : MIPStarRE.LDT.Polynomial params,
      strategy.state.ev
        (strategy.state.opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
          ((sandwichedPolynomialSubMeasAt params strategy T uv.2).outcome h)))

/-- The scalar `Q₁` obtained from `Q₀` by moving the right point projection
`A^v_{h(v)}` to the left tensor factor; this is the target of
`eq:move-one`. -/
noncomputable def addInUCSChainQ1
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) : ℝ :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ h : MIPStarRE.LDT.Polynomial params,
      let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
      strategy.state.ev
        (strategy.state.opTensor
          (Av * (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
          (T.outcome h * Av)))

/-- The scalar `Q₂` obtained from `Q₁` by moving the second right point
projection to the left tensor factor; this is the target of `eq:move-another`. -/
noncomputable def addInUCSChainQ2
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) : ℝ :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ h : MIPStarRE.LDT.Polynomial params,
      let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
      strategy.state.ev
        (strategy.state.opTensor
          (Av * (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h * Av)
          (T.outcome h)))

/-- The scalar `Q₃` obtained from `Q₂` by replacing the first point projection
`A^v_{h(v)}` by `A^u_{h(u)}`; this is the target of `eq:change-one`. -/
noncomputable def addInUCSChainQ3
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) : ℝ :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ h : MIPStarRE.LDT.Polynomial params,
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
      let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
      strategy.state.ev
        (strategy.state.opTensor
          (Au * (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h * Av)
          (T.outcome h)))

/-- The scalar `Q₄` obtained from `Q₃` by replacing the second point projection
`A^v_{h(v)}` by `A^u_{h(u)}`; after the projection collapse, this is the
projection-simplified right endpoint of the diagonal add-in-u transfer. -/
noncomputable def addInUCSChainQ4
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) : ℝ :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ h : MIPStarRE.LDT.Polynomial params,
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
      strategy.state.ev
        (strategy.state.opTensor
          (Au * (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h * Au)
          (T.outcome h)))

/-- The expanded chain endpoint `Q₀` is the existing diagonal match-mass left
side used by `selfConsistencyDiagonalAddInU_of_simplifiedTransfer`. -/
lemma add_in_u_cs_chain_q0_eq_match_mass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    strategy.state.qBipartiteMatchMass
        (averagedSandwichedPolynomialSubMeas params strategy T)
        (averagedSandwichedPolynomialSubMeas params strategy T) =
      addInUCSChainQ0 params strategy T := by
  unfold addInUCSChainQ0
  rw [avgOver_uniform_prod (α := Point params) (β := Point params)
    (f := fun u v =>
      ∑ h : MIPStarRE.LDT.Polynomial params,
        strategy.state.ev
          (strategy.state.opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
            ((sandwichedPolynomialSubMeasAt params strategy T v).outcome h)))]
  simp only [avgOver_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  refine (strategy.state.ev_opTensor_averageOperatorOverDistribution_left _ _ _).trans
    (avgOver_congr _ _ _ fun u => ?_)
  exact strategy.state.ev_opTensor_averageOperatorOverDistribution_right
    (uniformDistribution (Point params))
    ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
    (fun v => (sandwichedPolynomialSubMeasAt params strategy T v).outcome h)

/-- The raw chain endpoint `Q₄` collapses to the projection-simplified scalar
right side used by `selfConsistencyDiagonalAddInU_of_simplifiedTransfer`. -/
lemma add_in_u_cs_chain_q4_eq_simplified_rhs
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    addInUCSChainQ4 params strategy T =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : MIPStarRE.LDT.Polynomial params,
          strategy.state.ev
            (strategy.state.opTensor
              ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
              (T.outcome h))) :=
  (avgOver_congr _ _ _ fun uv => Finset.sum_congr rfl fun h _ =>
    congrArg (fun X => strategy.state.ev (strategy.state.opTensor X (T.outcome h)))
      (proj_outer_sandwich_eq _ (T.outcome h)
        ((strategy.pointMeasurement uv.1).proj (h uv.1)))).trans
    (avgOver_uniform_fst (α := Point params) (β := Point params)
      (fun u =>
        ∑ h : MIPStarRE.LDT.Polynomial params,
          strategy.state.ev
            (strategy.state.opTensor
              ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
              (T.outcome h))))

end MIPRE.LIDT.Co.SelfImprovement

end
