/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
GlobalVariance/Theorems/PolynomialSumBounds.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.GlobalVariance.Theorems.CollisionExpansion

@[expose] public section

/-!
# Polynomial-sum (cardinality-free) bounds for the Section 8 transport

The counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/GlobalVariance/Theorems/PolynomialSumBounds.lean` in the
port of `planning/c6b-plan.md` (milestone M6, section "Port conventions"): the sum over all
polynomials `g` of the `lem:generalize-b` residuals of `CollisionExpansion.lean` is at most
`md/q`, with no factor of the number of polynomials. The line-measurement identity
`∑_f B^ℓ_f = B^ℓ.total` and the submeasurement identity `∑_g G_g = G.total` collapse the joint
tensor mass `∑_g ∑_f ev(B^ℓ_f ⊗ G_g)` to `ev(B^ℓ.total ⊗ G.total) ≤ ev 1 = 1`
(`generalizeBLineCollisionTensorMass_polysum_le_one`), and the per-polynomial Schwartz–Zippel
coefficient bound does the rest.

`opTensor` is `strategy.state.opTensor` and `ev strategy.state` is `strategy.state.ev`. The
normalization `ev 1 = 1` is the keystone's hypothesis-free `ev_one_of_isNormalized`, so the
vendored `strategy.isNormalized` argument disappears; no statement here carries a swap or
normalization hypothesis.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/expansion.tex`, lines 282--289 (proof of `lem:generalize-b`) and
  317--321 (`eq:equivalent-local-variance`)
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.GlobalVariance

open MIPStarRE.LDT (Parameters FieldModel AxisParallelLine AxisLinePolynomial avgOver
  uniformDistribution avgOver_sum avgOver_uniform_le_const)
open MIPStarRE.LDT.GlobalVariance (generalizeBError generalizeBLineCollisionCoefficient_le)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Polynomial-sum analogue of `generalizeBLineCollisionTensorMass_sum_le_one`: the joint tensor
mass `∑_g ∑_f ev(B^ℓ_f ⊗ G_g)` is at most `1`, with no cardinality factor in the polynomial
index, since it equals `ev(B^ℓ.total ⊗ G.total)`. -/
theorem generalizeBLineCollisionTensorMass_polysum_le_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (ℓ : AxisParallelLine params) :
    (∑ g : MIPStarRE.LDT.Polynomial params, ∑ f : AxisLinePolynomial params,
      strategy.state.ev (strategy.state.opTensor
        ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f) (G.outcome g))) ≤ 1 := by
  set B := (strategy.axisParallelMeasurement ℓ).toSubMeas
  calc
    _ = ∑ g : MIPStarRE.LDT.Polynomial params,
          strategy.state.ev (strategy.state.opTensor B.total (G.outcome g)) :=
        Finset.sum_congr rfl fun g _ => by
          rw [← strategy.state.ev_sum, ← strategy.state.opTensor_sum_left_univ, B.sum_eq_total]
    _ = strategy.state.ev (strategy.state.opTensor B.total G.total) := by
        rw [← strategy.state.ev_sum, ← strategy.state.opTensor_sum_right_univ, G.sum_eq_total]
    _ ≤ 1 := by
        rw [← strategy.state.ev_one_of_isNormalized]
        exact strategy.state.ev_mono _ _
          (strategy.state.opTensor_le_one B.total_nonneg B.total_le_one G.total_le_one)

/-- Polynomial-sum analogue of `generalizeBLineCollisionExpansion_le_error`: the line-collision
expansion summed over all polynomials is at most `generalizeBError = md/q`, without the
polynomial cardinality. Each line is bounded by the Schwartz–Zippel coefficient bound and
`generalizeBLineCollisionTensorMass_polysum_le_one`; this is the cardinality-free form of
`expansion.tex`, lines 282--289, underlying `eq:equivalent-local-variance`. -/
theorem generalizeBLineCollisionExpansion_polysum_le_error
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    (∑ g : MIPStarRE.LDT.Polynomial params,
      generalizeBLineCollisionExpansion params strategy strategy.state G g) ≤
      generalizeBError params := by
  have hδ_nonneg : 0 ≤ generalizeBError params := by
    dsimp [generalizeBError]
    positivity
  unfold generalizeBLineCollisionExpansion
  rw [← avgOver_sum]
  refine avgOver_uniform_le_const _ _ fun ℓ => ?_
  calc
    _ ≤ ∑ g : MIPStarRE.LDT.Polynomial params, ∑ f : AxisLinePolynomial params,
          generalizeBError params * strategy.state.ev (strategy.state.opTensor
            ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f) (G.outcome g)) :=
        Finset.sum_le_sum fun g _ => Finset.sum_le_sum fun f _ =>
          mul_le_mul_of_nonneg_right (generalizeBLineCollisionCoefficient_le params g ℓ f)
            (generalizeBLineCollisionTensorMass_nonneg params strategy G g ℓ f)
    _ = generalizeBError params *
          ∑ g : MIPStarRE.LDT.Polynomial params, ∑ f : AxisLinePolynomial params,
            strategy.state.ev (strategy.state.opTensor
              ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f) (G.outcome g)) := by
        simp only [Finset.mul_sum]
    _ ≤ generalizeBError params :=
        mul_le_of_le_one_right hδ_nonneg
          (generalizeBLineCollisionTensorMass_polysum_le_one params strategy G ℓ)

/-- Polynomial-sum analogue of `generalizeBSeedCollisionExpansion_le_error`: the seed/line
expansion identity composed with the polynomial-sum line bound. -/
theorem generalizeBSeedCollisionExpansion_polysum_le_error
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    (∑ g : MIPStarRE.LDT.Polynomial params,
      generalizeBSeedCollisionExpansion params strategy strategy.state G g) ≤
      generalizeBError params :=
  (Finset.sum_congr rfl fun g _ =>
      generalizeBSeedCollisionExpansion_eq_lineCollisionExpansion
        params strategy strategy.state G g).trans_le
    (generalizeBLineCollisionExpansion_polysum_le_error params strategy G)

/-- Polynomial-sum analogue of `generalizeBCollisionResidual_le_error`: the incident-question
reindexing identity composed with the polynomial-sum seed bound. -/
theorem generalizeBCollisionResidual_polysum_le_error
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    (∑ g : MIPStarRE.LDT.Polynomial params,
      generalizeBCollisionResidual params strategy strategy.state G g) ≤
      generalizeBError params :=
  (Finset.sum_congr rfl fun g _ =>
      generalizeBCollisionResidual_eq_seedCollisionExpansion params strategy G g).trans_le
    (generalizeBSeedCollisionExpansion_polysum_le_error params strategy G)

/-- Polynomial-sum analogue of `generalizeBPointwiseSchwartzZippel`: the weighted
Schwartz–Zippel residual summed over all polynomials is at most `md/q`, not `N · md/q`
(`expansion.tex`, lines 282--289). This is the form `eq:equivalent-local-variance` uses for the
two `md/q` steps (3 and 4) of the six-step chain of `lem:local-variance-of-points`. -/
theorem generalizeBDeviationAtPolynomial_polysum_le_error
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    (∑ g : MIPStarRE.LDT.Polynomial params,
      generalizeBDeviationAtPolynomial params strategy strategy.state G g) ≤
      generalizeBError params :=
  (Finset.sum_congr rfl fun g _ =>
      generalizeBDeviationAtPolynomial_eq_collisionResidual
        params strategy strategy.state G g).trans_le
    (generalizeBCollisionResidual_polysum_le_error params strategy G)

end MIPRE.LIDT.Co.GlobalVariance

end
