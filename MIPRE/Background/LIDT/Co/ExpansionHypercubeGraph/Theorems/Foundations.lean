/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
ExpansionHypercubeGraph/Theorems/Foundations.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.ExpansionHypercubeGraph.Defs.Fourier
public import MIPStarRE.LDT.ExpansionHypercubeGraph.Theorems.Foundations

@[expose] public section

/-!
# Section 7 hypercube graph: trace-form foundations and Gram positivity

The counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/ExpansionHypercubeGraph/Theorems/Foundations.lean` in the
port of `planning/c6b-plan.md` (milestone M5, section "Port conventions"): the statement
structures of `lem:local-rewrite` and `lem:global-rewrite`, and the closed forms of the global
trace form.

The vendored proof of the local-to-global inequality realizes an operator family and its state as
concrete matrices (`MatrixRealization/`), proves the operator inequality `gap · P_⊥ ≤ L` between
scalar vertex matrices, tensors it with the density `ρ`, conjugates by the block matrix
`A_combine` and takes the trace. On a vector state there is no density and no trace, and the
same conclusion is **Gram positivity** (`re_combinedTraceForm_nonneg`): for a positive
semidefinite scalar matrix `P` on the vertices and operators `A_u` on a Hilbert space,

  `Re ∑_{u,v} P u v · ⟪A_v Ψ, A_u Ψ⟫ ≥ 0`,

because `P` is a sum of matrices `star s * s` and for each of them the sum is
`∑_k ‖∑_v conj(s k v) • A_v Ψ‖²`. The scalar inequality `gap · P_⊥ ≤ L` itself is imported from
the vendored matrix realization (`hypercubeSpectralGap_operator_posSemidef`), which is classical.

## New here

- `inner_star_mul_apply`: `⟪Ψ, (star B * A) Ψ⟫ = ⟪B Ψ, A Ψ⟫`;
- `combinedTraceForm_add`, `combinedTraceForm_zero`, `combinedTraceForm_sub`,
  `combinedTraceForm_real_smul`: linearity of the trace form in the scalar matrix;
- `combinedTraceForm_star_mul_self`, `re_combinedTraceForm_nonneg`: Gram positivity, which
  replaces the vendored matrix realization;
- `re_combinedTraceForm_one`: the trace form of the identity is the sum of the diagonal
  expectations.

## Not ported

- `abstractMatrixModel`: the matrix realization of an operator family and a density; there is no
  matrix realization here, the variances being handled by Gram positivity.
- `localVariance_eq_zero_of_isEmpty`: the empty-carrier branch of the matrix realization; a
  Hilbert space with a unit vector is nonempty, and no proof here splits on it.
- `globalVariance_eq_zero_of_isEmpty`: as `localVariance_eq_zero_of_isEmpty`.
- `localVarianceTraceForm_eq_zero_of_isEmpty`: as `localVariance_eq_zero_of_isEmpty`.
- `globalVarianceTraceForm_eq_zero_of_isEmpty`: as `localVariance_eq_zero_of_isEmpty`.
- `sum_reorder_four`: classical, imported.
- `sum_sum_mul_left`: classical, imported.
- `sum_sum_add`: classical, imported.
- `sum_sum_sub`: classical, imported.
- `matrixModelState`: the density of the matrix realization; replaced by the vector state.
- `trace_combined_tensor_eq`: the trace of the combined tensor witness, entrywise; the trace
  forms here are defined by the sum it computes (`combinedTraceForm`).
- `normalizedTrace_combined_tensor_eq`: as `trace_combined_tensor_eq`.

The two files of the vendored `ExpansionHypercubeGraph/MatrixRealization/` directory,
`MatrixRealization/Core.lean` (the matrix realization, the Fourier projectors and the spectral
gap as a matrix inequality) and `MatrixRealization/TraceForms.lean` (the matrix variances, trace
witnesses and trace forms, and the trace monotonicity it uses), have no counterpart in the port:
replaced by Gram positivity. Their scalar facts (`hypercubeSpectralGap_operator_posSemidef`,
`orthogonalModeProjectorMatrix`) are imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/expansion.tex`, `lem:local-rewrite` and `lem:global-rewrite`
- `blueprint/src/chapter/ch05_expansion.tex`
-/

open scoped BigOperators InnerProductSpace ComplexOrder

namespace MIPRE.LIDT.Co.ExpansionHypercubeGraph

open MIPStarRE.LDT (Parameters Point)
open MIPStarRE.LDT.ExpansionHypercubeGraph (hypercubeVertexCount)

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ## Statement structures -/

/-- Paper origin: `references/ldt-paper/expansion.tex:145-178`
(`\label{lem:local-rewrite}`).

Conclusion statement for `lem:local-rewrite`: the local variance is rewritten as a
trace-form expectation in the operator family `A`. -/
structure LocalRewriteStatement (params : Parameters)
    (A : Point params → K →L[ℂ] K) (V : VecState K) : Prop where
  /-- The local variance agrees with the trace form built from the Laplacian. -/
  traceFormula :
    localVariance params A V = localVarianceTraceForm params A V

/-- Paper origin: `references/ldt-paper/expansion.tex:179-269`
(`\label{lem:global-rewrite}`).

Conclusion statement for `lem:global-rewrite`: the global variance is rewritten as a
trace-form expectation along the eigenbasis of the hypercube graph
Laplacian. -/
structure GlobalRewriteStatement (params : Parameters)
    (A : Point params → K →L[ℂ] K) (V : VecState K) : Prop where
  /-- A Fourier-mode decomposition whose trace form recovers the global variance. -/
  decomposition :
    ∃ decomp : GlobalVarianceDecomposition params A,
      globalVariance params A V = globalVarianceTraceForm params A V decomp

/-! ## The trace form: linearity and Gram positivity -/

/-- The expectation of `star B * A` is the inner product of `B Ψ` and `A Ψ`. -/
theorem inner_star_mul_apply (V : VecState K) (A B : K →L[ℂ] K) :
    ⟪V.Ψ, (star B * A) V.Ψ⟫_ℂ = ⟪B V.Ψ, A V.Ψ⟫_ℂ := by
  change ⟪V.Ψ, star B (A V.Ψ)⟫_ℂ = _
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

section Linearity

variable {n : Type*} [Fintype n] (A : n → K →L[ℂ] K) (V : VecState K)

/-- The trace form is additive in the scalar matrix. -/
theorem combinedTraceForm_add (P Q : Matrix n n ℂ) :
    combinedTraceForm (P + Q) A V = combinedTraceForm P A V + combinedTraceForm Q A V := by
  simp only [combinedTraceForm, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

/-- The trace form of the zero matrix vanishes. -/
@[simp] theorem combinedTraceForm_zero : combinedTraceForm (0 : Matrix n n ℂ) A V = 0 := by
  simp [combinedTraceForm]

/-- The trace form is additive in the scalar matrix: differences. -/
theorem combinedTraceForm_sub (P Q : Matrix n n ℂ) :
    combinedTraceForm (P - Q) A V = combinedTraceForm P A V - combinedTraceForm Q A V := by
  simp only [combinedTraceForm, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- A real multiple of the scalar matrix scales the real part of the trace form. -/
theorem combinedTraceForm_real_smul (c : ℝ) (P : Matrix n n ℂ) :
    (combinedTraceForm ((c : ℂ) • P) A V).re = c * (combinedTraceForm P A V).re := by
  simp only [combinedTraceForm, Matrix.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum,
    Complex.re_ofReal_mul]

/-- The trace form of `star s * s` is a sum of squared norms: with
`z_k = ∑_v conj(s k v) • A_v Ψ`, it is `∑_k ⟪z_k, z_k⟫`. -/
theorem combinedTraceForm_star_mul_self (s : Matrix n n ℂ) :
    combinedTraceForm (star s * s) A V =
      ∑ k, ⟪∑ v, star (s k v) • A v V.Ψ, ∑ u, star (s k u) • A u V.Ψ⟫_ℂ := by
  simp only [combinedTraceForm, inner_star_mul_apply, Matrix.mul_apply, Matrix.star_apply,
    sum_inner, inner_sum, inner_smul_left, inner_smul_right, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun _ _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun u _ =>
    Finset.sum_congr rfl fun v _ => ?_
  rw [Complex.star_def, Complex.conj_conj, mul_assoc]

/-- **Gram positivity.** For a positive semidefinite scalar matrix `P` and operators `A_u`, the
real part of `∑_{u,v} P u v · ⟪A_v Ψ, A_u Ψ⟫` is nonnegative. This replaces the vendored matrix
realization of the local-to-global inequality. -/
theorem re_combinedTraceForm_nonneg {P : Matrix n n ℂ} (hP : P.PosSemidef) :
    0 ≤ (combinedTraceForm P A V).re := by
  open scoped MatrixOrder in
  have hP' : P ∈ AddSubmonoid.closure (Set.range fun s : Matrix n n ℂ => star s * s) :=
    StarOrderedRing.nonneg_iff.mp hP.nonneg
  clear hP
  induction hP' using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    rw [combinedTraceForm_star_mul_self, Complex.re_sum]
    exact Finset.sum_nonneg fun k _ => inner_self_nonneg (𝕜 := ℂ)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [combinedTraceForm_add, Complex.add_re]
    exact add_nonneg hx hy

end Linearity

/-- The trace form of the identity matrix is the sum of the diagonal expectations. -/
theorem re_combinedTraceForm_one {n : Type*} [Fintype n] [DecidableEq n]
    (A : n → K →L[ℂ] K) (V : VecState K) :
    (combinedTraceForm (1 : Matrix n n ℂ) A V).re = ∑ u, V.ev (star (A u) * A u) := by
  simp [combinedTraceForm, Matrix.one_apply, VecState.ev_eq_re_inner]

/-! ## Closed forms of the global trace form -/

/-- Closed form of `globalVarianceTraceForm` as the average squared norm of the
orthogonal residual family carried by the decomposition. -/
lemma globalVarianceTraceForm_eq_orthogonalClosedForm (params : Parameters)
    (A : Point params → K →L[ℂ] K) (V : VecState K)
    (decomp : GlobalVarianceDecomposition params A) :
    globalVarianceTraceForm params A V decomp =
      (hypercubeVertexCount params : ℝ)⁻¹ *
        ∑ u, V.ev (star (decomp.orthogonalComponent u) * decomp.orthogonalComponent u) := by
  rw [globalVarianceTraceForm, re_combinedTraceForm_one, one_div]

/-- Closed form of `globalVarianceTraceForm` in centered-correlation coordinates. -/
lemma globalVarianceTraceForm_eq_closedForm (params : Parameters)
    (A : Point params → K →L[ℂ] K) (V : VecState K)
    (decomp : GlobalVarianceDecomposition params A) :
    globalVarianceTraceForm params A V decomp =
      (hypercubeVertexCount params : ℝ)⁻¹ *
          ∑ u, V.ev (star (A u) * A u) -
        (hypercubeVertexCount params : ℝ)⁻¹ *
          (hypercubeVertexCount params : ℝ)⁻¹ *
            ∑ u, ∑ v, V.ev (star (A v) * A u) := by
  set c : ℝ := (hypercubeVertexCount params : ℝ)⁻¹ with hc
  set S : K →L[ℂ] K := ∑ u, A u
  have hM_ne : (hypercubeVertexCount params : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (pow_pos params.hq params.m))
  have havg : decomp.averageComponent = (c : ℂ) • S := by
    rw [decomp.averageComponent_eq, hc]; push_cast; rfl
  -- `∑_u ev(A_u† S) = ∑_u ev(S† A_u) = ∑_u ∑_v ev(A_v† A_u)`.
  have hcross : ∑ u, V.ev (star (A u) * S) = ∑ u, ∑ v, V.ev (star (A v) * A u) := by
    simp only [S, Finset.mul_sum, VecState.ev_sum]
    rw [Finset.sum_comm]
  have hcross' : ∑ u, V.ev (star S * A u) = ∑ u, ∑ v, V.ev (star (A v) * A u) := by
    simp only [S, star_sum, Finset.sum_mul, VecState.ev_sum]
  have hSS : V.ev (star S * S) = ∑ u, ∑ v, V.ev (star (A v) * A u) := by
    rw [← hcross']
    simp only [S, Finset.mul_sum, VecState.ev_sum]
  have hres : ∀ u, star (decomp.orthogonalComponent u) * decomp.orthogonalComponent u =
      star (A u) * A u - (c : ℂ) • (star (A u) * S) - (c : ℂ) • (star S * A u) +
        ((c * c : ℝ) : ℂ) • (star S * S) := by
    intro u
    rw [decomp.orthogonalComponent_eq_sub_average, havg, star_sub, star_smul, Complex.star_def,
      Complex.conj_ofReal]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_sub, smul_smul,
      Complex.ofReal_mul]
    abel
  rw [globalVarianceTraceForm_eq_orthogonalClosedForm]
  simp only [hres, VecState.ev_add, VecState.ev_sub, VecState.ev_scale, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    hcross, hcross', hSS]
  have hcard : (Fintype.card (Point params) : ℝ) = (hypercubeVertexCount params : ℝ) := by
    simp [hypercubeVertexCount, Fintype.card_fin]
  have hcM : c * (hypercubeVertexCount params : ℝ) = 1 := inv_mul_cancel₀ hM_ne
  rw [hcard]
  linear_combination (c ^ 2 * ∑ u, ∑ v, V.ev (star (A v) * A u)) * hcM

end MIPRE.LIDT.Co.ExpansionHypercubeGraph

end
