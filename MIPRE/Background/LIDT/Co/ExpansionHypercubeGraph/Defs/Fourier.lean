/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
ExpansionHypercubeGraph/Defs/Fourier.lean, to the symmetric model of `planning/c6b-plan.md`; not
a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.ExpansionHypercubeGraph.Defs.Core
public import MIPRE.Background.LIDT.MIPStarRE.LDT.ExpansionHypercubeGraph.Defs.Fourier

@[expose] public section

/-!
# Section 7 hypercube graph: the variance decomposition and the trace forms

The counterpart of `MIPRE/Background/LIDT/MIPStarRE/LDT/ExpansionHypercubeGraph/Defs/Fourier.lean`
in the port of `planning/c6b-plan.md` (milestone M5, section "Port conventions").

The Fourier analysis of the vendored file (the additive characters, the Fourier basis of
`ℂ^{F_q^m}`, its orthonormality, and the eigenvalues of the adjacency matrix and the Laplacian) is
scalar and is imported, not ported. What is ported is the operator side of `lem:local-rewrite`
and `lem:global-rewrite`: the decomposition `A^u = A_avg + A_⊥^u` of an operator family (generic
over any complex module, as it uses no product) and the two trace forms. The vendored trace forms
are `Re τ` of a matrix witness `A_combineᴴ (P ⊗ ρ) A_combine`; here they are the real parts of
the sums those traces evaluate to, `combinedTraceForm P A V` (`Defs/Core.lean`), at `P = L` for
the local form and at `P = 1` on the orthogonal residual for the global one.

## Not ported

- `addCharFq`: classical, imported.
- `dotProductFq`: classical, imported.
- `fourierBasisState`: classical, imported.
- `dotProductZMod`: classical, imported.
- `addCharFq_eq_stdAddChar`: classical, imported.
- `addCharFq_dotProduct_eq_stdAddChar_dotProductZMod`: classical, imported.
- `dotProductZMod_update`: classical, imported.
- `sum_stdAddChar_mul_fin`: classical, imported.
- `fourierBasisState_update_sum`: classical, imported.
- `fourierBasisProjector`: classical (a scalar matrix on the vertices), imported.
- `localVarianceTraceWitness`: the matrix `A_combineᴴ (L ⊗ ρ) A_combine`; a vector state has no
  density, and `localVarianceTraceForm` is defined by the sum its trace evaluates to.
- `globalVarianceTraceWitness`: the matrix `A_⊥combineᴴ (1 ⊗ ρ) A_⊥combine`; as
  `localVarianceTraceWitness`, replaced in `globalVarianceTraceForm` by the sum its trace
  evaluates to.
- `frequencyWeight`: classical, imported.
- `frequencyWeight_le_m`: classical, imported.
- `zeroCoordinateCount_eq`: classical, imported.
- `zeroCoordinateContributionSum`: classical, imported.
- `fourierBasisState_total_update_sum`: classical, imported.
- `fourierBasisInnerProduct`: classical, imported.
- `pointAddChar`: classical, imported.
- `pointAddCharRight`: classical, imported.
- `dotProductZMod_single_one`: classical, imported.
- `pointAddChar_eq_zero_iff`: classical, imported.
- `fourierBasisState_inner_product`: classical, imported.
- `eigenvectors_orthonormality`: classical, imported.
- `adjacencyEigenvalue`: classical, imported.
- `laplacianEigenvalue`: classical, imported.
- `hypercubeSpectralGap`: classical, imported.
- `eigenvectors_card`: classical, imported.
- `eigenvectors`: classical, imported.
- `laplacianEigenvalue_eq`: classical, imported.
- `hypercubeSpectralGap_le_laplacianEigenvalue`: classical, imported.
- `laplacianEigenvalue_of_weight_one`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/expansion.tex`, `lem:local-rewrite` and `lem:global-rewrite`
- `blueprint/src/chapter/ch05_expansion.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.ExpansionHypercubeGraph

open MIPStarRE.LDT (Parameters Point)
open MIPStarRE.LDT.ExpansionHypercubeGraph (hypercubeVertexCount laplacian)

section Decomposition

variable {R : Type*} [AddCommGroup R] [Module ℂ R]

/-- A packaged decomposition for `lem:global-rewrite`.

The witness stores the pointwise average `A_avg = E_u A^u` together with the
full residual family `u ↦ A^u - A_avg`. This carries the same geometric content as
writing `A_combine = |φ₀⟩ ⊗ A₀ + |φ_⊥⟩ ⊗ A_⊥`. It uses only the complex module structure of
the operators, so it is stated over any complex module `R` (the vendored `Op ι`). -/
structure GlobalVarianceDecomposition (params : Parameters) (A : Point params → R) where
  /-- The average `A_avg = (1/M) ∑_u A^u`. -/
  averageComponent : R
  /-- The residual family `u ↦ A^u - A_avg`. -/
  orthogonalComponent : Point params → R
  /-- The average component is `(1/M) ∑_u A^u`. -/
  averageComponent_eq :
    averageComponent = ((hypercubeVertexCount params : ℂ)⁻¹) • ∑ u, A u
  /-- The residual family sums to zero. -/
  orthogonal_sum_zero :
    ∑ u, orthogonalComponent u = 0
  /-- Each `A^u` is the average plus its residual. -/
  decomposition :
    ∀ u, A u = averageComponent + orthogonalComponent u

/-- Recover the centered residual as `A^u - A_avg`. -/
lemma GlobalVarianceDecomposition.orthogonalComponent_eq_sub_average
    {params : Parameters} {A : Point params → R}
    (decomp : GlobalVarianceDecomposition params A) (u : Point params) :
    decomp.orthogonalComponent u = A u - decomp.averageComponent := by
  rw [decomp.decomposition u, add_sub_cancel_left]

/-- The centered family `u ↦ A^u - (1/M) ∑_v A^v` sums to zero. -/
lemma centered_sum_eq_zero (params : Parameters) (A : Point params → R) :
    ∑ u, (A u - ((hypercubeVertexCount params : ℂ)⁻¹) • ∑ v, A v) = 0 := by
  have hcard : (hypercubeVertexCount params : ℂ) = ((Fintype.card (Point params) : ℕ) : ℂ) := by
    simp [hypercubeVertexCount, Fintype.card_fin]
  have hM : ((Fintype.card (Point params) : ℕ) : ℂ) ≠ 0 := by
    rw [← hcard]; exact_mod_cast (pow_pos params.hq params.m).ne'
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ,
    hcard, smul_smul, mul_inv_cancel₀ hM, one_smul, sub_self]

/-- The canonical decomposition from `lem:global-rewrite`.

Its `averageComponent` is the paper's `A_avg = E_u A^u = (1/M) · ∑_u A^u`, and its
orthogonal component is the centered family `u ↦ A^u - A_avg`. Equivalently, the
paper's coefficient `A_0 = M^{-1/2} · ∑_u A^u` is `M^{1/2} · A_avg`. -/
noncomputable def canonicalGlobalVarianceDecomposition (params : Parameters)
    (A : Point params → R) : GlobalVarianceDecomposition params A where
  averageComponent := ((hypercubeVertexCount params : ℂ)⁻¹) • ∑ u, A u
  orthogonalComponent := fun u => A u - ((hypercubeVertexCount params : ℂ)⁻¹) • ∑ v, A v
  averageComponent_eq := rfl
  orthogonal_sum_zero := centered_sum_eq_zero params A
  decomposition := fun _ => (add_sub_cancel _ _).symm

end Decomposition

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The local-variance trace expression from `lem:local-rewrite`: the vendored
`Re τ(A_combineᴴ (L ⊗ ρ) A_combine)`, written as the real part of the sum this trace evaluates to,
`∑ u v, L u v · ⟪Ψ, A_v† A_u Ψ⟫`. -/
noncomputable def localVarianceTraceForm (params : Parameters)
    (A : Point params → K →L[ℂ] K) (V : VecState K) : ℝ :=
  (combinedTraceForm (laplacian params) A V).re

/-- The global-variance trace expression from `lem:global-rewrite`: the vendored
`(1/M) Re τ(A_⊥combineᴴ (1 ⊗ ρ) A_⊥combine)` on the orthogonal residual of the decomposition,
written through the sum this trace evaluates to.

The prefactor `1 / hypercubeVertexCount params` is the paper's `1 / M`
normalization from Section 7. -/
noncomputable def globalVarianceTraceForm (params : Parameters)
    (A : Point params → K →L[ℂ] K) (V : VecState K)
    (decomp : GlobalVarianceDecomposition params A) : ℝ :=
  (1 / (hypercubeVertexCount params : ℝ)) *
    (combinedTraceForm (1 : Matrix (Point params) (Point params) ℂ)
      decomp.orthogonalComponent V).re

end MIPRE.LIDT.Co.ExpansionHypercubeGraph

end
