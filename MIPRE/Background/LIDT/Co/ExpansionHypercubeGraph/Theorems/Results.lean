/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
ExpansionHypercubeGraph/Theorems/Results.lean, to the symmetric model of `planning/c6b-plan.md`;
not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.ExpansionHypercubeGraph.Theorems.Matrix
public import MIPStarRE.LDT.ExpansionHypercubeGraph.Theorems.Results

@[expose] public section

/-!
# Section 7 hypercube graph: local-to-global variance theorems

The counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/ExpansionHypercubeGraph/Theorems/Results.lean` in the port
of `planning/c6b-plan.md` (milestone M5, section "Port conventions"): the local and global
variance rewrites (`localRewrite`, `globalRewrite`) and the local-to-global inequality
(`localToGlobal`, and `localToGlobalBipartite` for a family placed by `S.L`).

The vendored proof of `localToGlobal` goes through the matrix realization of the family and the
density: the matrix inequality `gap · P_⊥ ≤ L` is tensored with `ρ`, conjugated by the block
matrix `A_combine`, and traced. Here the same inequality is read through Gram positivity
(`re_combinedTraceForm_nonneg`, `Theorems/Foundations.lean`): `L - gap · P_⊥` is positive
semidefinite (`hypercubeSpectralGap_operator_posSemidef`, imported, scalar), so its trace form
is nonnegative, and the two trace forms are `m ·` the global variance and the local variance
(`traceForm_localToGlobal`). The statements hold for every family `A : Point params → (K →L[ℂ] K)`
and every vector state.

A vendored variance on a weighted state `W ρ Wᴴ` (`GlobalVariance`'s
`weightedPolynomialState`, which is not normalized) is, on a vector state, the variance of the
family `u ↦ A u * W` on `V`: `ev_{WρWᴴ}(X) = ev_ρ(Wᴴ X W)` and
`Wᴴ (A_u - A_v)ᴴ (A_u - A_v) W = pointDifferenceSquaredOperator (fun u => A u * W) u v`. So the
theorems here apply to it unchanged.

## New here

- `localVariance_eq_closedForm`: the closed form of the local variance, the vendored
  `matrixLocalVariance_eq_closedForm` without the matrix realization;
- `traceForm_localToGlobal`: the trace-form inequality by Gram positivity, the vendored
  `matrixTraceForm_localToGlobal` without the matrix realization.

## Not ported

- `avgOver_independentPointPair_eq_uniform_prod`: classical, imported.
- `matrixLocalVariance_eq_closedForm`: the matrix realization; replaced by
  `localVariance_eq_closedForm`.
- `matrixTraceForm_localToGlobal`: the matrix realization (trace monotonicity under conjugation
  by `A_combine`); replaced by Gram positivity, `traceForm_localToGlobal`.
- `matrixLocalToGlobal`: the matrix realization; its content is `localToGlobal`.
- `matrixLocalRewrite`: the matrix realization; its content is `localRewrite`.
- `matrixGlobalRewrite`: the matrix realization; its content is `globalRewrite`.
- `laplacianRewrite`: classical (an identity of scalar vertex matrices), imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/expansion.tex`, `prop:laplacian-rewrite`, `lem:local-rewrite`,
  `lem:global-rewrite` and `lem:local-to-global`
- `blueprint/src/chapter/ch05_expansion.tex`
-/

open scoped BigOperators InnerProductSpace

namespace MIPRE.LIDT.Co.ExpansionHypercubeGraph

open MIPStarRE.LDT (Parameters Point)
open MIPStarRE.LDT.ExpansionHypercubeGraph (hypercubeVertexCount hypercubeSpectralGap
  rerandomizeCoordWeight rerandomizeCoordWeight_rowSum rerandomizeCoordWeight_colSum
  avgOver_rerandomizeCoord_eq_weight_sum orthogonalModeProjectorMatrix
  orthogonalModeProjector_re_sum hypercubeSpectralGap_operator_posSemidef laplacian
  matrixLaplacianOperator)

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Closed form for the local variance: the diagonal expectations averaged over the vertices,
minus the correlations weighted by the edge distribution. -/
lemma localVariance_eq_closedForm (params : Parameters)
    (A : Point params → K →L[ℂ] K) (V : VecState K) :
    localVariance params A V =
      (hypercubeVertexCount params : ℝ)⁻¹ * ∑ u, V.ev (star (A u) * A u) -
        ∑ u, ∑ v, rerandomizeCoordWeight params u v * V.ev (star (A v) * A u) := by
  have hrow : ∑ u, ∑ v, rerandomizeCoordWeight params u v * V.ev (star (A u) * A u) =
      (hypercubeVertexCount params : ℝ)⁻¹ * ∑ u, V.ev (star (A u) * A u) := by
    simp_rw [← Finset.sum_mul, rerandomizeCoordWeight_rowSum, ← Finset.mul_sum]
  have hcol : ∑ u, ∑ v, rerandomizeCoordWeight params u v * V.ev (star (A v) * A v) =
      (hypercubeVertexCount params : ℝ)⁻¹ * ∑ u, V.ev (star (A u) * A u) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, rerandomizeCoordWeight_colSum, ← Finset.mul_sum]
  rw [localVariance, avgOver_rerandomizeCoord_eq_weight_sum, Fintype.sum_prod_type]
  simp only [sqdiff_eq_diag_corr params A V, mul_sub, mul_add, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, mul_left_comm _ (2 : ℝ), ← Finset.mul_sum]
  linear_combination (1 / 2 : ℝ) * hrow + (1 / 2 : ℝ) * hcol

/-- The trace-form inequality behind `lem:local-to-global`, by Gram positivity: the global trace
form is at most `m` times the local one. The vendored `matrixTraceForm_localToGlobal` proves it
on a matrix realization, by tensoring `gap · P_⊥ ≤ L` with the density and tracing. -/
theorem traceForm_localToGlobal (params : Parameters)
    (A : Point params → K →L[ℂ] K) (V : VecState K)
    (decomp : GlobalVarianceDecomposition params A) :
    globalVarianceTraceForm params A V decomp ≤
      (params.m : ℝ) * localVarianceTraceForm params A V := by
  have hpsd := re_combinedTraceForm_nonneg (n := Point params) A V
    (hypercubeSpectralGap_operator_posSemidef params)
  have hsplit : combinedTraceForm (n := Point params) (matrixLaplacianOperator params -
      ((hypercubeSpectralGap params : ℂ) • orthogonalModeProjectorMatrix params)) A V =
      combinedTraceForm (n := Point params) (laplacian params) A V -
        combinedTraceForm (n := Point params) (((hypercubeSpectralGap params : ℝ) : ℂ) •
          id (α := Matrix (Point params) (Point params) ℂ) (orthogonalModeProjectorMatrix params))
          A V :=
    combinedTraceForm_sub _ _ _ _
  replace hpsd := hpsd.trans_eq (congrArg Complex.re hsplit)
  rw [Complex.sub_re, combinedTraceForm_real_smul, sub_nonneg] at hpsd
  have hperp : (combinedTraceForm (n := Point params)
      (id (α := Matrix (Point params) (Point params) ℂ) (orthogonalModeProjectorMatrix params))
        A V).re =
      ∑ u, V.ev (star (A u) * A u) -
        (hypercubeVertexCount params : ℝ)⁻¹ * ∑ u, ∑ v, V.ev (star (A v) * A u) :=
    orthogonalModeProjector_re_sum params fun u v => ⟪V.Ψ, (star (A v) * A u) V.Ψ⟫_ℂ
  have hM_ne : (hypercubeVertexCount params : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (pow_pos params.hq params.m))
  have hm_ne : (params.m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt params.hm)
  have hgap : (hypercubeVertexCount params : ℝ)⁻¹ =
      (params.m : ℝ) * hypercubeSpectralGap params := by
    rw [hypercubeSpectralGap]
    field_simp
  rw [hperp] at hpsd
  rw [globalVarianceTraceForm_eq_closedForm, localVarianceTraceForm]
  calc
    _ = (params.m : ℝ) * (hypercubeSpectralGap params *
          (∑ u, V.ev (star (A u) * A u) -
            (hypercubeVertexCount params : ℝ)⁻¹ * ∑ u, ∑ v, V.ev (star (A v) * A u))) := by
      rw [← mul_assoc, ← hgap]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpsd (Nat.cast_nonneg _)

/-- The local variance for a symmetric model when the operator family acts on the first
player's side: the vendored `localVariance` of `u ↦ leftTensor (A u)` on the bipartite state. -/
noncomputable def bipartiteLocalVariance {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓]
    [StarOrderedRing 𝔓] (params : Parameters) (A : Point params → 𝔓) (S : SymModel 𝔓 K) : ℝ :=
  localVariance params (fun u => S.L (A u)) S

/-- The global variance for a symmetric model when the operator family acts on the first
player's side. -/
noncomputable def bipartiteGlobalVariance {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓]
    [StarOrderedRing 𝔓] (params : Parameters) (A : Point params → 𝔓) (S : SymModel 𝔓 K) : ℝ :=
  globalVariance params (fun u => S.L (A u)) S

/-- `lem:local-rewrite`: the local variance agrees with the Laplacian trace form of the family. -/
lemma localRewrite (params : Parameters)
    (A : Point params → K →L[ℂ] K) (V : VecState K) :
    LocalRewriteStatement params A V :=
  ⟨by rw [localVariance_eq_closedForm, localVarianceTraceForm_eq_closedForm]⟩

/-- `lem:global-rewrite`. The existential witness is `canonicalGlobalVarianceDecomposition`,
whose `averageComponent` is the paper's `A_avg = E_u A^u = (1/M) · ∑_u A^u`. -/
lemma globalRewrite (params : Parameters)
    (A : Point params → K →L[ℂ] K) (V : VecState K) :
    GlobalRewriteStatement params A V :=
  ⟨⟨canonicalGlobalVarianceDecomposition params A, by
    rw [globalVariance_eq_closedForm, globalVarianceTraceForm_eq_closedForm]⟩⟩

/-- General local-to-global inequality for an arbitrary operator family on a vector state: the
global variance over two independent vertices is bounded by `m` times the local variance over the
rerandomized-coordinate edge distribution. -/
lemma localToGlobal (params : Parameters)
    (A : Point params → K →L[ℂ] K) (V : VecState K) :
    globalVariance params A V ≤ (params.m : ℝ) * localVariance params A V := by
  obtain ⟨decomp, hglobal⟩ := (globalRewrite params A V).decomposition
  rw [hglobal, (localRewrite params A V).traceFormula]
  exact traceForm_localToGlobal params A V decomp

/-- `lem:local-to-global`, in bipartite form: the local-to-global variance inequality for the
family `S.L (A u)` (the vendored `A^u ⊗ I`). The spectral estimate holds for every family. -/
lemma localToGlobalBipartite {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
    (params : Parameters) (A : Point params → 𝔓) (S : SymModel 𝔓 K) :
    bipartiteGlobalVariance params A S ≤ (params.m : ℝ) * bipartiteLocalVariance params A S :=
  localToGlobal params (fun u => S.L (A u)) S

end MIPRE.LIDT.Co.ExpansionHypercubeGraph

end
