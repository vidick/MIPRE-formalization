/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122),
MIPStarRE/LDT/Test/MainTheorem/ProjectiveConsistency/Evaluation.lean, to the models of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Test.MainTheorem.TwoSpace
public import MIPRE.Background.LIDT.Co.Test.StrategyPolynomialFamilies

@[expose] public section

/-!
# Projective consistency evaluation

The data-processing lemmas which turn polynomial-level projective consistency into pointwise
consistency after evaluation at a sampled point: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Test/MainTheorem/ProjectiveConsistency/Evaluation.lean` in
the port of `planning/c6b-plan.md` (milestone M13, section "Port conventions").

The same-space statements `consRel_constPolynomialEvaluation` and
`projectiveEvaluationConsistency_ofFullPolynomialConsistency` take the symmetric model
`S : SymModel 𝔓 K` in place of the vendored state on `ι × ι`, and go through Co
`Preliminaries.approxToSimeq` and `Preliminaries.consRelDataProcessing_questionDependent`.

**The two `_heterogeneous` theorems are two-space.** Their vendored state is on `ιA × ιB`, with
Alice's polynomial measurement on `ιA` and Bob's on `ιB`, and their callers are the two-space tail
of the main theorem on the strategy's own model. So they are stated over a bipartite model
`M : MIPRE.BipartiteModel 𝒞 𝒜 ℬ`, with `A`, `Q_A` in `𝒜` and `B`, `Q_B` in `ℬ`: consistency is
M2's two-space defect, `bipartiteConsError M 𝒟 A B ≤ δ` for the vendored `ConsRel ψ 𝒟 A B δ`,
and the hypothesis of the projective form is the state-dependent distance of the placements
`TwoSpace.leftPlacedSubMeas M Q_A`, `TwoSpace.rightPlacedSubMeas M Q_B` on the vector state
`TwoSpace.vecState M hψ` (`Co/Test/MainTheorem/TwoSpace.lean`). This departs from the narrowing
rule of "Same-space and bipartite quantities" in the way M8's heterogeneous orthonormalizations
did (`Co/MakingMeasurementsProjective/Orthonormalization.lean`): narrowed to one carrier, they
would repeat their same-space siblings and serve no caller. The proofs are the vendored ones,
through `TwoSpace.consRelDataProcessing_questionDependent` and
`TwoSpace.approxToSimeq_heterogeneous`.

## Not ported

Every declaration of the vendored file has a counterpart here.
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Test

open MIPStarRE.LDT (Parameters FieldModel Point Distribution avgOver avgOver_uniform_const
  uniformDistribution)

/-! ### Over a symmetric model -/

section SameSpace

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A constant full-polynomial consistency statement postprocesses to pointwise polynomial
evaluation with the same error.

This is the data-processing move used after paper line 156: once
`Q^A_g ⊗ I ≃ I ⊗ Q^B_g` is available over the single polynomial question, evaluating both
polynomial outcomes at a point `u` preserves consistency over the uniform point distribution. -/
theorem consRel_constPolynomialEvaluation
    {params : Parameters} [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (A B : Measurement (MIPStarRE.LDT.Polynomial params) 𝔓) {δ : ℝ}
    (h : S.ConsRel (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily B.toSubMeas) δ) :
    S.ConsRel (uniformDistribution (Point params))
      (polynomialEvaluationFamily params A.toSubMeas)
      (polynomialEvaluationFamily params B.toSubMeas) δ := by
  have hconstPoint : S.ConsRel (uniformDistribution (Point params))
      (fun _ => A.toSubMeas) (fun _ => B.toSubMeas) δ := by
    refine ⟨le_of_eq_of_le ?_ h.offDiagonalBound⟩
    show avgOver _ (fun _ => S.qBipartiteConsDefect A.toSubMeas B.toSubMeas) =
      avgOver _ (fun _ => S.qBipartiteConsDefect A.toSubMeas B.toSubMeas)
    rw [avgOver_uniform_const, avgOver_uniform_const]
  exact Preliminaries.consRelDataProcessing_questionDependent S
    (uniformDistribution (Point params)) _ _ δ (fun u g => g u) hconstPoint

/-- Two-space form of `consRel_constPolynomialEvaluation`: the same data-processing argument
when Alice's polynomial measurement lies in the first player's algebra `𝒜` of a bipartite model
`M` and Bob's in the second player's algebra `ℬ`, with M2's two-space defect for the vendored
`ConsRel`. -/
theorem consRel_constPolynomialEvaluation_heterogeneous
    {params : Parameters} [FieldModel params.q]
    {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
    [Algebra ℂ 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]
    [PartialOrder ℬ] [StarOrderedRing ℬ]
    (M : MIPRE.BipartiteModel 𝒞 𝒜 ℬ)
    (A : Measurement (MIPStarRE.LDT.Polynomial params) 𝒜)
    (B : Measurement (MIPStarRE.LDT.Polynomial params) ℬ) {δ : ℝ}
    (h : bipartiteConsError M (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily B.toSubMeas) ≤ δ) :
    bipartiteConsError M (uniformDistribution (Point params))
      (polynomialEvaluationFamily params A.toSubMeas)
      (polynomialEvaluationFamily params B.toSubMeas) ≤ δ := by
  have hconstPoint : bipartiteConsError M (uniformDistribution (Point params))
      (fun _ => A.toSubMeas) (fun _ => B.toSubMeas) ≤ δ := by
    refine le_of_eq_of_le ?_ h
    show avgOver _ (fun _ => qBipartiteConsDefect M A.toSubMeas B.toSubMeas) =
      avgOver _ (fun _ => qBipartiteConsDefect M A.toSubMeas B.toSubMeas)
    rw [avgOver_uniform_const, avgOver_uniform_const]
  exact TwoSpace.consRelDataProcessing_questionDependent M
    (uniformDistribution (Point params)) (fun _ => A.toSubMeas) (fun _ => B.toSubMeas) δ
    (fun u (g : MIPStarRE.LDT.Polynomial params) => g u) hconstPoint

/-- Turn a line-156 projective approximation into the evaluated consistency used in the final
point-consistency triangles.

The proof first applies the projective converse of `prop:simeq-to-approx` at the polynomial
level, then uses question-dependent data processing to evaluate both projective polynomial
measurements at each point. -/
theorem projectiveEvaluationConsistency_ofFullPolynomialConsistency
    {params : Parameters} [FieldModel params.q]
    {S : SymModel 𝔓 K}
    (Q_A Q_B : ProjMeas (MIPStarRE.LDT.Polynomial params) 𝔓) {ζ₃ : ℝ}
    (hline : Preliminaries.BipartiteSDDRel S (uniformDistribution Unit)
      (constSubMeasFamily Q_A.toSubMeas)
      (constSubMeasFamily Q_B.toSubMeas) ζ₃) :
    S.ConsRel (uniformDistribution (Point params))
      (polynomialEvaluationFamily params Q_A.toSubMeas)
      (polynomialEvaluationFamily params Q_B.toSubMeas) (ζ₃ / 2) :=
  consRel_constPolynomialEvaluation S Q_A.toMeasurement Q_B.toMeasurement
    (Preliminaries.approxToSimeq S (uniformDistribution Unit) (fun _ => Q_A) (fun _ => Q_B)
      (ζ₃ / 2) ⟨hline.leftRightSquaredDistanceBound.trans_eq (by ring)⟩)

end SameSpace

/-! ### Over a bipartite model -/

/-- Two-space form of `projectiveEvaluationConsistency_ofFullPolynomialConsistency`: for
projective polynomial measurements `Q_A` of `𝒜` and `Q_B` of `ℬ` whose placements are at
state-dependent distance `ζ₃` on the unit state of `M`, the evaluated families are two-space
consistent at `ζ₃ / 2`.

It first applies the two-space projective converse (`TwoSpace.approxToSimeq_heterogeneous`) to
the placed state-dependent-distance relation, and then evaluates the polynomial outcomes at the
sampled point. -/
theorem projectiveEvaluationConsistency_ofFullPolynomialConsistency_heterogeneous
    {params : Parameters} [FieldModel params.q]
    {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
    [Algebra ℂ 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]
    [PartialOrder ℬ] [StarOrderedRing ℬ]
    {M : MIPRE.BipartiteModel 𝒞 𝒜 ℬ} (hψ : ‖M.ψ‖ = 1)
    (Q_A : ProjMeas (MIPStarRE.LDT.Polynomial params) 𝒜)
    (Q_B : ProjMeas (MIPStarRE.LDT.Polynomial params) ℬ) {ζ₃ : ℝ}
    (hline : (TwoSpace.vecState M hψ).SDDRel (uniformDistribution Unit)
      (constSubMeasFamily (TwoSpace.leftPlacedSubMeas M Q_A.toSubMeas))
      (constSubMeasFamily (TwoSpace.rightPlacedSubMeas M Q_B.toSubMeas)) ζ₃) :
    bipartiteConsError M (uniformDistribution (Point params))
      (polynomialEvaluationFamily params Q_A.toSubMeas)
      (polynomialEvaluationFamily params Q_B.toSubMeas) ≤ ζ₃ / 2 :=
  consRel_constPolynomialEvaluation_heterogeneous M Q_A.toMeasurement Q_B.toMeasurement
    (TwoSpace.approxToSimeq_heterogeneous M hψ (uniformDistribution Unit) (fun _ => Q_A)
      (fun _ => Q_B) (ζ₃ / 2) ⟨hline.squaredDistanceBound.trans_eq (by ring)⟩)

end MIPRE.LIDT.Co.Test

end
