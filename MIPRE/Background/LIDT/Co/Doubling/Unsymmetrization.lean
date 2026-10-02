/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Doubling.Strategy

@[expose] public section

/-!
# Unsymmetrization in the doubled model

Theorem E of `reports/c6b-paper-proofs.md`, §4.2 (Lemma 13), for the doubled model
`Doubling.model hM hψ` of `Co/Doubling/Model.lean` and the symmetric strategy
`Doubling.symmStrat` of `Co/Doubling/Strategy.lean`. The main induction returns one polynomial
measurement `G` of the doubled local algebra `Loc M`; its components are a measurement of `𝒜` and
one of `ℬ`, and the point consistency of `G` in the doubled model bounds each component's point
consistency against the other player's point measurements in `M` by twice as much.

* **The components** `measA hM G : Measurement O 𝒜` and `measB hM G : Measurement O ℬ` of a
  measurement of `Loc M` (the report's `G¹`, `G²`) are measurements: `compA` and `compB` are unital
  `⋆`-homomorphisms. Their submeasurements are `subMeasA` and `subMeasB` of `G`.
* **The pairing** `pairMeasurement hM A B` of a measurement of `𝒜` and one of `ℬ`, translated to
  `Loc M` along `Doubling.equiv`, has the components `A` and `B` (`subMeasA_pairMeasurement`,
  `measA_pairMeasurement`, …), as `pairProjMeas` does for projective measurements.
* **The diagonal identity** `bipartiteConsError_model_diag`: the doubled defect of a family with
  itself is the two-space defect of its two components, exactly. It is the case `X = Y` of the
  halving `bipartiteConsError_model`, and it is lossless, so the self-consistency of a family of
  the doubled model is that of its components in `M`.
* **Evaluation commutes with components** (`polynomialEvaluationFamily_subMeasA`, …,
  `constSubMeasFamily_subMeasA`, …), from `subMeasA_postprocess`.
* **Theorem E** `symmStrat_pointConsistency_unsymmetrize`: if the paired point measurements of the
  symmetric strategy are `σ`-consistent with the evaluations of `G` in the doubled model, then the
  first player's point measurements are `2σ`-consistent with the evaluations of `G`'s second
  component, and the evaluations of `G`'s first component with the second player's point
  measurements, in `M`. These are the constants of the vendored
  `sourceRoleRegisterPointConsistency_ofSymConsistency`
  (`LDT/Test/MainTheorem/SourceRoleRegister/Core.lean`). The proof is the role-average arithmetic
  `bipartiteConsError_components_le_two_mul`.

## New here

This file has no vendored counterpart. Every declaration is new:

- `measA`, `measB`, `measA_toSubMeas`, `measB_toSubMeas`, `measA_outcome`, `measB_outcome`: the
  components of a measurement of the doubled local algebra;
- `pairMeasurement`, `pairMeasurement_outcome`, `subMeasA_pairMeasurement`,
  `subMeasB_pairMeasurement`, `measA_pairMeasurement`, `measB_pairMeasurement`: the paired
  measurement and its components;
- `bipartiteConsError_model_diag`: the lossless diagonal identity;
- `polynomialEvaluationFamily_subMeasA`, `polynomialEvaluationFamily_subMeasB`,
  `constSubMeasFamily_subMeasA`, `constSubMeasFamily_subMeasB`: evaluation and constant families
  commute with taking components;
- `symmStrat_pointConsistency_unsymmetrize`: Theorem E.

## Not ported

This file replaces the vendored `LDT/Test/StrategyBiProjUnsymmetrization.lean`, which is not
ported (the pairing script reads only ported files, so it is recorded here):

- `SubMeas.extractRoleRegisterAlice`/`Bob`, `Measurement.extractRoleRegisterAlice`/`Bob` and
  their `_outcome`, `_total`, `_toSubMeas` and `_postprocess` lemmas: replaced by `subMeasA`,
  `subMeasB` (`Co/Doubling/Strategy.lean`), `measA`, `measB` and `subMeasA_postprocess`;
- the principal blocks `ProjStrat.extractRoleRegisterAliceBlock`/`BobBlock` and their algebra
  lemmas: the doubled local algebra is a product, and `compA`, `compB` are `⋆`-homomorphisms;
- the matrix-trace and Kronecker lemmas on the role register
  (`trace_single_tensor_mul_eq_trace_submatrix`, `rolePairProj_eq_single_pair`, the sector
  embeddings, `trace_rolePairDirectSumCond_mul`, the `opTensor_*_submatrix` identities,
  `trace_heterogeneousSwapDensity_mul_opTensor`, `ev_roleRegisterSymmState_*`): the model has no
  trace; replaced by Theorem C
  (`qBipartiteConsDefect_model`, `Co/Doubling/Halving.lean`);
- `qBipartiteMatchMass_roleRegisterProjMeas_arbitrary_eq_average` and
  `qBipartiteConsDefect_roleRegisterProjMeas_arbitrary_eq_average`: replaced by
  `qBipartiteConsDefect_model_eq` and `bipartiteConsError_model`;
- `qBipartiteConsDefect_extractRoleRegisterAlice_le_two_symm`/`Bob_le_two_symm`: replaced by
  `bipartiteConsError_components_le_two_mul` and Theorem E here;
- `polynomialEvaluationFamily_extractRoleRegisterAlice`/`Bob` and their `_measurement_` forms:
  replaced by `polynomialEvaluationFamily_subMeasA`/`_subMeasB`.

The role-register symmetrization `LDT/Test/StrategyBiProjRoleAverage/Final.lean` is likewise not
ported; it is replaced by `symmStrat` and `symmStrat_isGood_three_mul`.
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Doubling

open MIPStarRE.LDT (Parameters FieldModel Point Distribution uniformDistribution)

section Components

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]
  [PartialOrder ℬ] [StarOrderedRing ℬ] {M : BipartiteModel 𝒞 𝒜 ℬ}
  (hM : M.IsFinitePair) (hψ : ‖M.ψ‖ = 1)

/-! ### The components of a measurement -/

section Meas

variable {O : Type*} [Fintype O]

/-- **The first component of a measurement of the doubled local algebra**, a measurement of `𝒜`
(the report's `G¹`): the image under the unital `⋆`-homomorphism `compA`. -/
noncomputable def measA (G : Measurement O (Loc M)) : Measurement O 𝒜 :=
  G.map (compA (M := M) hM)

/-- **The second component of a measurement of the doubled local algebra**, a measurement of `ℬ`
(the report's `G²`): the image under the unital `⋆`-homomorphism `compB`. -/
noncomputable def measB (G : Measurement O (Loc M)) : Measurement O ℬ :=
  G.map (compB (M := M) hM)

omit [PartialOrder ℬ] [StarOrderedRing ℬ] in
/-- The first component of a measurement, as a submeasurement, is the first component of its
submeasurement. -/
@[simp] theorem measA_toSubMeas (G : Measurement O (Loc M)) :
    (measA hM G).toSubMeas = subMeasA hM G.toSubMeas :=
  rfl

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] in
/-- The second component of a measurement, as a submeasurement, is the second component of its
submeasurement. -/
@[simp] theorem measB_toSubMeas (G : Measurement O (Loc M)) :
    (measB hM G).toSubMeas = subMeasB hM G.toSubMeas :=
  rfl

omit [PartialOrder ℬ] [StarOrderedRing ℬ] in
/-- The outcome operators of the first component are the first components of the outcome
operators. -/
@[simp] theorem measA_outcome (G : Measurement O (Loc M)) (a : O) :
    (measA hM G).outcome a = compA hM (G.outcome a) :=
  rfl

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] in
/-- The outcome operators of the second component are the second components of the outcome
operators. -/
@[simp] theorem measB_outcome (G : Measurement O (Loc M)) (a : O) :
    (measB hM G).outcome a = compB hM (G.outcome a) :=
  rfl

/-! ### The paired measurement -/

/-- **The paired measurement in the doubled model**: the componentwise pairing of a measurement
`A` of `𝒜` and `B` of `ℬ`, translated to the doubled local algebra `Loc M` along
`Doubling.equiv`; the counterpart of `pairProjMeas` for measurements. -/
noncomputable def pairMeasurement (A : Measurement O 𝒜) (B : Measurement O ℬ) :
    Measurement O (Loc M) :=
  (A.prod B).map (equiv hM).toStarAlgHom

/-- The outcomes of a paired measurement are the translated pairs of outcomes. -/
theorem pairMeasurement_outcome (A : Measurement O 𝒜) (B : Measurement O ℬ) (a : O) :
    (pairMeasurement hM A B).outcome a = equiv hM (A.outcome a, B.outcome a) :=
  rfl

/-- The first components of a paired measurement are the first measurement. -/
@[simp] theorem subMeasA_pairMeasurement (A : Measurement O 𝒜) (B : Measurement O ℬ) :
    subMeasA hM (pairMeasurement hM A B).toSubMeas = A.toSubMeas :=
  SubMeas.ext (fun a => compA_equiv hM (A.outcome a, B.outcome a))
    (compA_equiv hM (A.total, B.total))

/-- The second components of a paired measurement are the second measurement. -/
@[simp] theorem subMeasB_pairMeasurement (A : Measurement O 𝒜) (B : Measurement O ℬ) :
    subMeasB hM (pairMeasurement hM A B).toSubMeas = B.toSubMeas :=
  SubMeas.ext (fun a => compB_equiv hM (A.outcome a, B.outcome a))
    (compB_equiv hM (A.total, B.total))

/-- The first component of a paired measurement is the first measurement. -/
@[simp] theorem measA_pairMeasurement (A : Measurement O 𝒜) (B : Measurement O ℬ) :
    measA hM (pairMeasurement hM A B) = A :=
  Measurement.ext fun a => compA_equiv hM (A.outcome a, B.outcome a)

/-- The second component of a paired measurement is the second measurement. -/
@[simp] theorem measB_pairMeasurement (A : Measurement O 𝒜) (B : Measurement O ℬ) :
    measB hM (pairMeasurement hM A B) = B :=
  Measurement.ext fun a => compB_equiv hM (A.outcome a, B.outcome a)

end Meas

/-! ### The diagonal identity -/

/-- **The diagonal identity** (Theorem C at `X = Y`): the doubled consistency error of a family of
the doubled model with itself is the two-space consistency error of its first components against
its second components, exactly. -/
theorem bipartiteConsError_model_diag {Question Outcome : Type*} [Fintype Outcome]
    [DecidableEq Outcome] (𝒟 : Distribution Question) (X : IdxSubMeas Question Outcome (Loc M)) :
    (model hM hψ).bipartiteConsError 𝒟 X X =
      bipartiteConsError M 𝒟 (fun q => subMeasA hM (X q)) (fun q => subMeasB hM (X q)) := by
  rw [bipartiteConsError_model]
  ring

/-! ### Evaluation commutes with taking components -/

section Evaluation

variable {params : Parameters} [FieldModel params.q]

omit [PartialOrder ℬ] [StarOrderedRing ℬ] in
/-- **Evaluation commutes with the first component**: the evaluations of the first component of a
polynomial submeasurement are the first components of its evaluations. -/
theorem polynomialEvaluationFamily_subMeasA
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) (Loc M)) (u : Point params) :
    polynomialEvaluationFamily params (subMeasA hM G) u =
      subMeasA hM (polynomialEvaluationFamily params G u) :=
  (subMeasA_postprocess hM G _).symm

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] in
/-- **Evaluation commutes with the second component**: the evaluations of the second component of
a polynomial submeasurement are the second components of its evaluations. -/
theorem polynomialEvaluationFamily_subMeasB
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) (Loc M)) (u : Point params) :
    polynomialEvaluationFamily params (subMeasB hM G) u =
      subMeasB hM (polynomialEvaluationFamily params G u) :=
  (subMeasB_postprocess hM G _).symm

end Evaluation

omit [PartialOrder ℬ] [StarOrderedRing ℬ] in
/-- The constant family of the first component is the first component of the constant family. -/
theorem constSubMeasFamily_subMeasA {O : Type*} [Fintype O] (A : SubMeas O (Loc M)) (q : Unit) :
    constSubMeasFamily (subMeasA hM A) q = subMeasA hM (constSubMeasFamily A q) :=
  rfl

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] in
/-- The constant family of the second component is the second component of the constant
family. -/
theorem constSubMeasFamily_subMeasB {O : Type*} [Fintype O] (A : SubMeas O (Loc M)) (q : Unit) :
    constSubMeasFamily (subMeasB hM A) q = subMeasB hM (constSubMeasFamily A q) :=
  rfl

end Components

/-! ### Theorem E -/

section TheoremE

variable {params : Parameters} [FieldModel params.q]
  {𝒞 : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞]
  {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  {ℬ : Type*} [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- **Unsymmetrization at the vendored cut** (Theorem E of `reports/c6b-paper-proofs.md`, §4.2,
Lemma 13): if the paired point measurements of the symmetric strategy `symmStrat strategy hM` are
`σ`-consistent with the evaluations of a polynomial measurement `G` of the doubled local algebra,
then in the two-space model `strategy.state` the first player's point measurements are
`2σ`-consistent with the evaluations of `G`'s second component `measB hM G`, and the evaluations
of `G`'s first component `measA hM G` with the second player's point measurements. These are the
constants of the vendored `sourceRoleRegisterPointConsistency_ofSymConsistency`. -/
theorem symmStrat_pointConsistency_unsymmetrize (strategy : ProjStrat params 𝒞 𝒜 ℬ)
    (hM : strategy.state.IsFinitePair)
    (G : Measurement (MIPStarRE.LDT.Polynomial params) (Loc strategy.state)) {σ : ℝ}
    (h : (symmStrat strategy hM).state.ConsRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas (symmStrat strategy hM).pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas) σ) :
    bipartiteConsError strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
        (polynomialEvaluationFamily params (measB hM G).toSubMeas) ≤ 2 * σ ∧
      bipartiteConsError strategy.state (uniformDistribution (Point params))
        (polynomialEvaluationFamily params (measA hM G).toSubMeas)
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB) ≤ 2 * σ := by
  obtain ⟨h1, h2⟩ := bipartiteConsError_components_le_two_mul hM strategy.isNormalized
    (uniformDistribution (Point params))
    (IdxProjMeas.toIdxSubMeas (symmStrat strategy hM).pointMeasurement)
    (polynomialEvaluationFamily params G.toSubMeas) h.offDiagonalBound
  have hpA : (fun u => subMeasA hM
      (IdxProjMeas.toIdxSubMeas (symmStrat strategy hM).pointMeasurement u)) =
        IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA :=
    funext fun u => subMeasA_pairProjMeas hM _ _
  have hpB : (fun u => subMeasB hM
      (IdxProjMeas.toIdxSubMeas (symmStrat strategy hM).pointMeasurement u)) =
        IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB :=
    funext fun u => subMeasB_pairProjMeas hM _ _
  have hgA : (fun u => subMeasA hM (polynomialEvaluationFamily params G.toSubMeas u)) =
      polynomialEvaluationFamily params (measA hM G).toSubMeas :=
    funext fun u => (polynomialEvaluationFamily_subMeasA hM G.toSubMeas u).symm
  have hgB : (fun u => subMeasB hM (polynomialEvaluationFamily params G.toSubMeas u)) =
      polynomialEvaluationFamily params (measB hM G).toSubMeas :=
    funext fun u => (polynomialEvaluationFamily_subMeasB hM G.toSubMeas u).symm
  rw [hpA, hgB] at h1
  rw [hgA, hpB] at h2
  exact ⟨h1, h2⟩

end TheoremE

end MIPRE.LIDT.Co.Doubling

end
