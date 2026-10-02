/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
ExpansionHypercubeGraph/Defs/Core.lean, to the symmetric model of `planning/c6b-plan.md`; not a
vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Basic.QuantumState
public import MIPRE.Background.LIDT.Co.Basic.Distribution
public import MIPRE.Background.LIDT.MIPStarRE.LDT.ExpansionHypercubeGraph.Defs.Core

@[expose] public section

/-!
# Section 7 hypercube graph: core definitions

The counterpart of `MIPRE/Background/LIDT/MIPStarRE/LDT/ExpansionHypercubeGraph/Defs/Core.lean`
in the port of `planning/c6b-plan.md` (milestone M5, section "Port conventions"): the local and
global variances of a family of operators `A : Point params → (K →L[ℂ] K)` on a vector state
`V : VecState K` (the vendored `QuantumState ι`, a state on one space; the variances use only the
state, so they are `VecState` quantities, and the bipartite form `A^u ⊗ 1` is `S.L (A u)`).

The vendored file also writes the trace `τ((L ⊗ ρ) · A_combine A_combineᴴ)` of the paper's
`lem:local-rewrite` through the block matrix `A_combine` (`combinedOperator`). A vector state has
no density and no trace; what that trace evaluates to, the sum `∑ u v, P u v · ⟪Ψ, A_v† A_u Ψ⟫`
for a scalar matrix `P` on the vertices, is `combinedTraceForm P A V` here, and both trace forms
of `Defs/Fourier.lean` are defined through it. Its positivity for a positive semidefinite `P`
(Gram positivity, `Theorems/Foundations.lean`) is what replaces the vendored matrix realization.

The classical half of the vendored file (the hypercube graph, its edge distribution, and the
adjacency and Laplacian matrices, which are scalar matrices on the vertex register and use no
state) is not ported: this file imports the vendored file and names those declarations through
an explicit `open MIPStarRE.LDT.ExpansionHypercubeGraph (…)` list.

## New here

- `combinedTraceForm`: the trace form `Tr(A_combineᴴ (P ⊗ ρ) A_combine)` of a scalar vertex
  matrix `P`, as the sum it evaluates to on a vector state.

## Not ported

- `hypercubeVertexCount`: classical, imported.
- `coordinateDisagreementSet`: classical, imported.
- `coordinateDisagreementCount`: classical, imported.
- `IsHypercubeEdge`: classical, imported.
- `instDecidableIsHypercubeEdge`: classical, imported.
- `instDecidablePredHypercubeEdgePair`: classical, imported.
- `rerandomizeCoordWeight`: classical, imported.
- `RerandomizeCoordSample`: classical, imported.
- `rerandomizeCoordSampleToPair`: classical, imported.
- `rerandomizeCoord`: classical, imported.
- `rerandomizeCoord_isProbability`: classical, imported.
- `rerandomizeCoord_toPMF`: classical, imported.
- `rerandomizeCoord_mass_eq_one`: classical, imported.
- `avgOver_rerandomizeCoord_eq_uniform_sample`: classical, imported.
- `avgOver_rerandomizeCoord_eq_weight_sum`: classical, imported.
- `independentPointPair`: classical, imported.
- `pointHilbertSpace`: classical (the vertex register of the scalar matrices), imported.
- `hypercubeAdjacencyWeight`: classical, imported.
- `matrixAdjacencyOperator`: classical (a scalar matrix on the vertices), imported.
- `matrixLaplacianOperator`: classical (a scalar matrix on the vertices), imported.
- `adjacency`: classical (a scalar matrix on the vertices), imported.
- `laplacian`: classical (a scalar matrix on the vertices), imported.
- `laplacianDifferenceForm`: classical (a scalar matrix on the vertices), imported.
- `combinedColumnIndex`: the index type of the block matrix `A_combine`; replaced by
  `combinedTraceForm`.
- `combinedOperator`: the block matrix `A_combine` of a matrix family; a vector state has no
  trace to evaluate it against, and the trace it serves is `combinedTraceForm`.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/expansion.tex`
- `blueprint/src/chapter/ch05_expansion.tex`
-/

open scoped BigOperators InnerProductSpace

namespace MIPRE.LIDT.Co.ExpansionHypercubeGraph

open MIPStarRE.LDT (Parameters Point avgOver)
open MIPStarRE.LDT.ExpansionHypercubeGraph (rerandomizeCoord independentPointPair)

/-- The squared difference operator `(A^u - A^v)† (A^u - A^v)`. -/
noncomputable def pointDifferenceSquaredOperator {R : Type*} [Ring R] [StarRing R]
    {params : Parameters} (A : Point params → R) (u v : Point params) : R :=
  star (A u - A v) * (A u - A v)

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The local variance from `def:local-and-variance`. -/
noncomputable def localVariance (params : Parameters)
    (A : Point params → K →L[ℂ] K) (V : VecState K) : ℝ :=
  (1 / (2 : ℝ)) *
    avgOver (rerandomizeCoord params)
      (fun uv => V.ev (pointDifferenceSquaredOperator A uv.1 uv.2))

/-- The global variance from `def:local-and-variance`. -/
noncomputable def globalVariance (params : Parameters)
    (A : Point params → K →L[ℂ] K) (V : VecState K) : ℝ :=
  (1 / (2 : ℝ)) *
    avgOver (independentPointPair params)
      (fun uv => V.ev (pointDifferenceSquaredOperator A uv.1 uv.2))

/-- Combined accessor for the local and global variances. -/
noncomputable def localAndVariance (params : Parameters)
    (A : Point params → K →L[ℂ] K) (V : VecState K) : ℝ × ℝ :=
  (localVariance params A V, globalVariance params A V)

/-- The trace form `Tr(A_combineᴴ (P ⊗ ρ) A_combine)` of a scalar matrix `P` on the index set of
an operator family `A`, as the sum it evaluates to on a vector state:
`∑ u v, P u v · ⟪Ψ, A_v† A_u Ψ⟫`. The vendored trace witnesses (`localVarianceTraceWitness`,
`globalVarianceTraceWitness`) are this sum at `P = L` and at `P = 1`. -/
noncomputable def combinedTraceForm {n : Type*} [Fintype n] (P : Matrix n n ℂ)
    (A : n → K →L[ℂ] K) (V : VecState K) : ℂ :=
  ∑ u, ∑ v, P u v * ⟪V.Ψ, (star (A v) * A u) V.Ψ⟫_ℂ

end MIPRE.LIDT.Co.ExpansionHypercubeGraph

end
