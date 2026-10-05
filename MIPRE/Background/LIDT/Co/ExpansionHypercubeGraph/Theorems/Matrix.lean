/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
ExpansionHypercubeGraph/Theorems/Matrix.lean, to the symmetric model of `planning/c6b-plan.md`;
not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.ExpansionHypercubeGraph.Theorems.Foundations
public import MIPStarRE.LDT.ExpansionHypercubeGraph.Theorems.Matrix

@[expose] public section

/-!
# Section 7 hypercube graph: closed forms of the variances

The counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/ExpansionHypercubeGraph/Theorems/Matrix.lean` in the port
of `planning/c6b-plan.md` (milestone M5, section "Port conventions").

The vendored file computes, for a matrix realization `model` of an operator family and a density
(`MatrixRealization/`), the squared differences and the closed forms of the global variance and
of the local trace form in the correlations `ev(A_v† A_u)`. Here the realization is the family
`A : Point params → (K →L[ℂ] K)` and the vector state `V` themselves: `corr_symm` and
`sqdiff_eq_corr` keep their vendored names, with `model` replaced by `A` and `V`, and the closed
forms are stated for `globalVariance` and `localVarianceTraceForm` directly. The classical half
of the vendored file (the row and column sums of the edge weights, their symmetry, and the
edge-difference form of the Laplacian) is imported.

## New here

- `sqdiff_eq_diag_corr`: the squared difference in the two diagonal terms and one correlation;
- `globalVariance_eq_closedForm`: the closed form of the global variance, the vendored
  `matrixGlobalVariance_eq_closedForm` without the matrix realization;
- `localVarianceTraceForm_eq_closedForm`: the closed form of the local trace form, the vendored
  `matrixLocalVarianceTraceForm_eq_closedForm` without the matrix realization.

## Not ported

- `orthogonalModeProjector_re_sum`: classical (a scalar identity for any `z`), imported.
- `matrixGlobalVarianceTraceForm_eq_closedForm`: the matrix realization; its content is
  `globalVarianceTraceForm_eq_closedForm` (`Theorems/Foundations.lean`).
- `matrixGlobalVariance_eq_closedForm`: the matrix realization; replaced by
  `globalVariance_eq_closedForm`.
- `rerandomizeCoordWeight_rowSum`: classical, imported.
- `update_eq_fixed_count`: classical, imported.
- `rerandomizeCoordWeight_colSum`: classical, imported.
- `update_swap`: classical, imported.
- `update_value_eq`: classical, imported.
- `rerandomizeCoordWeight_symm`: classical, imported.
- `laplacian_eq_edgeDifferenceForm`: classical, imported.
- `matrixLocalVarianceTraceForm_eq_closedForm`: the matrix realization; replaced by
  `localVarianceTraceForm_eq_closedForm`.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/expansion.tex`
- `blueprint/src/chapter/ch05_expansion.tex`
-/

open scoped BigOperators InnerProductSpace

namespace MIPRE.LIDT.Co.ExpansionHypercubeGraph

open MIPStarRE.LDT (Parameters Point avgOver avgOver_uniform_eq_pmf_sum)
open MIPStarRE.LDT.ExpansionHypercubeGraph (hypercubeVertexCount independentPointPair laplacian
  rerandomizeCoordWeight hypercubeAdjacencyWeight)

/-- Upstream keeps this helper `private` since its Lean-module port (`LionSR/MIPStarRE` at
`5fc363b`); the port carries its own copy, with upstream's proof. -/
theorem hypercubeAdjacencyWeight_eq_rerandomizeCoordWeight (params : Parameters) (u v : Point params) :
    hypercubeAdjacencyWeight params u v = (rerandomizeCoordWeight params u v : ℂ) := by
  unfold hypercubeAdjacencyWeight rerandomizeCoordWeight
  simp_rw [div_eq_mul_inv]
  rw [Nat.cast_mul, Nat.cast_mul]
  apply Complex.ext <;> simp
  ring

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The correlation term is symmetric under swapping the two points. -/
lemma corr_symm (params : Parameters) (A : Point params → K →L[ℂ] K) (V : VecState K)
    (u v : Point params) :
    V.ev (star (A v) * A u) = V.ev (star (A u) * A v) := by
  simpa [star_mul] using (V.ev_conjTranspose (star (A v) * A u)).symm

/-- Expand the squared-difference expectation into diagonal and correlation terms. -/
lemma sqdiff_eq_corr (params : Parameters) (A : Point params → K →L[ℂ] K) (V : VecState K)
    (u v : Point params) :
    V.ev (pointDifferenceSquaredOperator A u v) =
      V.ev (star (A u) * A u) + V.ev (star (A v) * A v) -
        V.ev (star (A u) * A v) - V.ev (star (A v) * A u) := by
  rw [pointDifferenceSquaredOperator, star_sub, sub_mul, mul_sub, mul_sub, VecState.ev_sub,
    VecState.ev_sub, VecState.ev_sub]
  ring

/-- The squared difference in the diagonal terms and one correlation. -/
lemma sqdiff_eq_diag_corr (params : Parameters) (A : Point params → K →L[ℂ] K)
    (V : VecState K) (u v : Point params) :
    V.ev (pointDifferenceSquaredOperator A u v) =
      V.ev (star (A u) * A u) + V.ev (star (A v) * A v) - 2 * V.ev (star (A v) * A u) := by
  rw [sqdiff_eq_corr params A V u v, ← corr_symm params A V u v]
  ring

/-- Closed form for the global variance. -/
lemma globalVariance_eq_closedForm (params : Parameters)
    (A : Point params → K →L[ℂ] K) (V : VecState K) :
    globalVariance params A V =
      (hypercubeVertexCount params : ℝ)⁻¹ * ∑ u, V.ev (star (A u) * A u) -
        (hypercubeVertexCount params : ℝ)⁻¹ * (hypercubeVertexCount params : ℝ)⁻¹ *
          ∑ u, ∑ v, V.ev (star (A v) * A u) := by
  have hM_ne : (hypercubeVertexCount params : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (pow_pos params.hq params.m))
  have hcard : (Fintype.card (Point params) : ℝ) = (hypercubeVertexCount params : ℝ) := by
    simp [hypercubeVertexCount, Fintype.card_fin]
  rw [globalVariance, independentPointPair, avgOver_uniform_eq_pmf_sum, Fintype.sum_prod_type]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, Fintype.card_prod, Nat.cast_mul,
    ENNReal.toReal_mul, ENNReal.toReal_natCast, hcard, sqdiff_eq_diag_corr params A V,
    ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

/-- Closed form for the local-variance trace expression. -/
lemma localVarianceTraceForm_eq_closedForm (params : Parameters)
    (A : Point params → K →L[ℂ] K) (V : VecState K) :
    localVarianceTraceForm params A V =
      (hypercubeVertexCount params : ℝ)⁻¹ * ∑ u, V.ev (star (A u) * A u) -
        ∑ u, ∑ v, rerandomizeCoordWeight params u v * V.ev (star (A v) * A u) := by
  have hL : laplacian params =
      (((hypercubeVertexCount params : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Matrix (Point params) (Point params) ℂ) -
        Matrix.of fun u v => (rerandomizeCoordWeight params u v : ℂ) := by
    ext u v
    change ((hypercubeVertexCount params : ℂ)⁻¹ • (1 : Matrix (Point params) (Point params) ℂ))
      u v - hypercubeAdjacencyWeight params u v = _
    rw [hypercubeAdjacencyWeight_eq_rerandomizeCoordWeight]
    simp [Matrix.one_apply]
  rw [localVarianceTraceForm, hL, combinedTraceForm_sub, Complex.sub_re,
    combinedTraceForm_real_smul, re_combinedTraceForm_one]
  congr 1
  simp only [combinedTraceForm, Matrix.of_apply, Complex.re_sum, Complex.re_ofReal_mul,
    VecState.ev_eq_re_inner]

end MIPRE.LIDT.Co.ExpansionHypercubeGraph

end
