/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Basic/
OperatorExpectations.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Basic.QuantumState
public import MIPRE.Background.LIDT.Co.Basic.Distribution

@[expose] public section

/-!
# Operator expectation infrastructure for the low individual degree test

This is the counterpart, in the port of the low-individual-degree test to the symmetric model
(`planning/c6b-plan.md`, milestone M0, and its section "Port conventions"), of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/OperatorExpectations.lean`: the triangle,
Cauchy–Schwarz and Jensen inequalities for the expectation `S.ev X = Re ⟪Ψ, X Ψ⟫`, and the
Cauchy–Schwarz inequality for sandwiched product placements.

The vendored proofs go through the density matrix and the cyclicity of the trace. Here the state
is a vector, `S.ev (star M * M) = ‖M Ψ‖²` (`VecState.ev_adjoint_self_eq_norm_sq`), and every
inequality is one of norms in `K`: the triangle inequalities are the triangle inequality of `K`
(the per-term forms of `StateModel.sum_snorm_sq_triangle` and `sum_snorm_sq_triangle3`), and
Cauchy–Schwarz is `StateModel.abs_qform_star_mul_le` (`MIPRE/Foundations/Sandwich.lean`) applied
to the state model `S.toStateModel`, whose quadratic form is `ev` by definition. Every lemma
except the sandwich ones uses only the state, so it is a `VecState` lemma
(`Co/Basic/QuantumState.lean`), which applies as well to `S : SymModel 𝔓 K`.

The linear and positivity lemmas of the vendored file (`ev_add`, `ev_sub`, `ev_scale`,
`ev_real_smul`, `ev_zero`, `ev_opTensor`, `ev_one_of_isNormalized`, `ev_adjoint_self_nonneg`,
`ev_finset_sum`, `ev_sum`, `ev_nonneg_of_psd`, `ev_mono`, `ev_conjTranspose`,
`ev_mul_comm_of_hermitian`, `ev_mul_comm_of_psd`, `ev_conjTranspose_mul_comm`) are ported in
`Co/Basic/QuantumState.lean`, with every positivity fact of the port.

## Not ported

Matrix-only declarations of the vendored file, about the normalized trace of a density matrix,
each replaced by the norm of `K`:

- `normalizedTrace_diff_sq_nonneg`: the model has no trace; `S.ev_adjoint_self_nonneg` is the
  vector form.
- `normalizedTrace_triangle`: the model has no trace; its content is `ev_diff_triangle`, proved
  from the triangle inequality of `K`.
- `normalizedTrace_triangle_three`: the model has no trace; its content is
  `ev_diff_triangle_three`, proved from the triangle inequality of `K`.
- `normalizedTrace_conjTranspose`: the model has no trace; `S.ev_conjTranspose` is the vector
  form.
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co

open MIPStarRE.LDT (Distribution avgOver)

namespace VecState

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (V : VecState K)

/-! ### Operator-level triangle inequality for squared differences -/

/-- Operator-level triangle inequality for expectation of squared differences:
`E[(X-Z)*(X-Z)] ≤ 2*(E[(X-Y)*(X-Y)] + E[(Y-Z)*(Y-Z)])`. This is the per-term inequality of the
repository's `MIPRE.StateModel.sum_snorm_sq_triangle` (`MIPRE/Foundations/StateModel.lean`). -/
theorem ev_diff_triangle (X Y Z : K →L[ℂ] K) :
    V.ev (star (X - Z) * (X - Z)) ≤
      2 * (V.ev (star (X - Y) * (X - Y)) + V.ev (star (Y - Z) * (Y - Z))) := by
  simp only [ev_adjoint_self_eq_norm_sq]
  have h : ‖(X - Z) V.Ψ‖ ≤ ‖(X - Y) V.Ψ‖ + ‖(Y - Z) V.Ψ‖ := by
    rw [show X - Z = (X - Y) + (Y - Z) by abel, _root_.add_apply]
    exact norm_add_le _ _
  nlinarith [norm_nonneg ((X - Z) V.Ψ), sq_nonneg (‖(X - Y) V.Ψ‖ - ‖(Y - Z) V.Ψ‖)]

/-- Three-step operator triangle inequality for squared differences.

If a difference is decomposed as three successive differences, its squared norm is bounded by
`3` times the sum of the three squared norms. This is the `k = 3` case of the paper's
`prop:triangle-inequality-for-vectors-squared`, used by the Step 6 projectivization chain in
`inductive_step.tex:154--158`. This is the per-term inequality of the repository's
`MIPRE.StateModel.sum_snorm_sq_triangle3` (`MIPRE/Foundations/StateModel.lean`). -/
theorem ev_diff_triangle_three (X Y Z W : K →L[ℂ] K) :
    V.ev (star (X - W) * (X - W)) ≤
      3 * (V.ev (star (X - Y) * (X - Y)) + V.ev (star (Y - Z) * (Y - Z)) +
        V.ev (star (Z - W) * (Z - W))) := by
  simp only [ev_adjoint_self_eq_norm_sq]
  have h : ‖(X - W) V.Ψ‖ ≤ ‖(X - Y) V.Ψ‖ + ‖(Y - Z) V.Ψ‖ + ‖(Z - W) V.Ψ‖ := by
    rw [show X - W = (X - Y) + (Y - Z) + (Z - W) by abel, _root_.add_apply,
      _root_.add_apply]
    exact (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
  nlinarith [norm_nonneg ((X - W) V.Ψ), sq_nonneg (‖(X - Y) V.Ψ‖ - ‖(Y - Z) V.Ψ‖),
    sq_nonneg (‖(X - Y) V.Ψ‖ - ‖(Z - W) V.Ψ‖), sq_nonneg (‖(Y - Z) V.Ψ‖ - ‖(Z - W) V.Ψ‖)]

/-! ### Averages -/

/-- Evaluation of an operator average is the average of the evaluations. -/
theorem ev_averageOperatorOverDistribution {α : Type*} (𝒟 : Distribution α)
    (A : α → K →L[ℂ] K) :
    V.ev (averageOperatorOverDistribution 𝒟 A) = avgOver 𝒟 (fun a => V.ev (A a)) :=
  (V.ev_finset_sum _ _).trans (Finset.sum_congr rfl fun a _ => V.ev_real_smul (𝒟.weight a) (A a))

/-! ### Cauchy–Schwarz -/

/-- Cauchy–Schwarz in the absolute-value form with state norms: `|ev (A* B)| ≤ ‖A Ψ‖ ‖B Ψ‖`
(`StateModel.abs_qform_star_mul_le` on `V.toStateModel`). -/
theorem abs_ev_star_mul_le (A B : K →L[ℂ] K) :
    |V.ev (star A * B)| ≤ ‖A V.Ψ‖ * ‖B V.Ψ‖ :=
  V.toStateModel.abs_qform_star_mul_le A B

/-- Cauchy-Schwarz for the state-weighted inner product:
`(ev (A* B))² ≤ ev (A* A) * ev (B* B)`. -/
theorem ev_cauchy_schwarz (A B : K →L[ℂ] K) :
    (V.ev (star A * B)) ^ 2 ≤ V.ev (star A * A) * V.ev (star B * B) := by
  rw [ev_adjoint_self_eq_norm_sq, ev_adjoint_self_eq_norm_sq, ← mul_pow, ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (V.abs_ev_star_mul_le A B) 2

/-- Absolute-value form of Cauchy-Schwarz for `ev`. -/
theorem ev_abs_mul_le_sqrt (A B : K →L[ℂ] K) :
    |V.ev (A * B)| ≤ Real.sqrt (V.ev (A * star A)) * Real.sqrt (V.ev (star B * B)) := by
  have h := V.abs_ev_star_mul_le (star A) B
  rw [star_star] at h
  have hA : V.ev (A * star A) = ‖star A V.Ψ‖ ^ 2 := by
    simpa using V.ev_adjoint_self_eq_norm_sq (star A)
  rw [hA, ev_adjoint_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (norm_nonneg _)]
  exact h

/-- AM-GM for the quadratic form: `2 * ev (A* B) ≤ ev (A* A) + ev (B* B)`. -/
theorem ev_cross_term_le (A B : K →L[ℂ] K) :
    2 * V.ev (star A * B) ≤ V.ev (star A * A) + V.ev (star B * B) := by
  have h := (abs_le.1 (V.abs_ev_star_mul_le A B)).2
  rw [ev_adjoint_self_eq_norm_sq, ev_adjoint_self_eq_norm_sq]
  nlinarith [sq_nonneg (‖A V.Ψ‖ - ‖B V.Ψ‖)]

/-- Jensen inequality for the quadratic form: for a finite family of operators,
`ev ((∑ Xᵢ)* (∑ Xᵢ)) ≤ n * ∑ ev (Xᵢ* Xᵢ)`. -/
theorem ev_sum_conjTranspose_mul_sum_le {α : Type*} [Fintype α] (X : α → K →L[ℂ] K) :
    V.ev (star (∑ a, X a) * (∑ a, X a)) ≤
      (Fintype.card α : ℝ) * ∑ a, V.ev (star (X a) * X a) := by
  simp only [ev_adjoint_self_eq_norm_sq]
  have h : ‖(∑ a, X a) V.Ψ‖ ≤ ∑ a, ‖X a V.Ψ‖ := Op.snorm_sum_le V.Ψ Finset.univ X
  calc ‖(∑ a, X a) V.Ψ‖ ^ 2 ≤ (∑ a, ‖X a V.Ψ‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ ≤ (Fintype.card α : ℝ) * ∑ a, ‖X a V.Ψ‖ ^ 2 := by
        simpa using _root_.sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun a => ‖X a V.Ψ‖)

end VecState

namespace SymModel

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (S : SymModel 𝔓 K)

/-! ### Bipartite-tensor sandwich Cauchy–Schwarz

The lemmas below give the operator/real Cauchy–Schwarz step for expectations of sandwiched
products lifted to the two players. They are a reusable primitive toward the raw `Q₂ → Q₃` and
`Q₃ → Q₄` Cauchy–Schwarz estimates of `self_improvement.tex`, lines 306–311 and 326–332 (the
`eq:change-one-cauchy-schwarz` and `eq:change-another` displays), where the bilinear form is
`⟨X, Y⟩_{M, T} := ev (opTensor (X* · M · Y) T)` with positive `M`, `T`. -/

/-- Bipartite-tensor Cauchy–Schwarz for state expectations.

For positive `M`, `T` and arbitrary local operators `X`, `Y`,
`(ev (opTensor (X* M Y) T))² ≤ ev (opTensor (X* M X) T) * ev (opTensor (Y* M Y) T)`.

The proof factors `M = m* m`, `T = t* t` (the vendored proof uses the square roots of the
continuous functional calculus) and applies `ev_cauchy_schwarz` to `opTensor (m X) t` and
`opTensor (m Y) t`. -/
theorem ev_opTensor_sandwich_cauchy_schwarz (X Y M T : 𝔓) (hM : 0 ≤ M) (hT : 0 ≤ T) :
    (S.ev (S.opTensor (star X * M * Y) T)) ^ 2 ≤
      S.ev (S.opTensor (star X * M * X) T) * S.ev (S.opTensor (star Y * M * Y) T) := by
  obtain ⟨m, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM
  obtain ⟨t, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hT
  have key : ∀ U V : 𝔓, star (S.opTensor (m * U) t) * S.opTensor (m * V) t =
      S.opTensor (star U * (star m * m) * V) (star t * t) := fun U V => by
    rw [conjTranspose_opTensor, opTensor_mul, star_mul, mul_assoc, mul_assoc, mul_assoc]
  have h := S.ev_cauchy_schwarz (S.opTensor (m * X) t) (S.opTensor (m * Y) t)
  rwa [key, key, key] at h

/-- Diagonal sandwich expectation `ev (opTensor (X* M X) T)` is nonneg when `M`, `T` are
positive. -/
theorem ev_opTensor_sandwich_diag_nonneg (X M T : 𝔓) (hM : 0 ≤ M) (hT : 0 ≤ T) :
    0 ≤ S.ev (S.opTensor (star X * M * X) T) :=
  S.ev_nonneg_of_psd _ (S.opTensor_nonneg (star_left_conjugate_nonneg hM X) hT)

/-- Absolute-value form of the bipartite-tensor sandwich Cauchy–Schwarz. -/
theorem ev_opTensor_sandwich_abs_le_sqrt (X Y M T : 𝔓) (hM : 0 ≤ M) (hT : 0 ≤ T) :
    |S.ev (S.opTensor (star X * M * Y) T)| ≤
      Real.sqrt (S.ev (S.opTensor (star X * M * X) T)) *
        Real.sqrt (S.ev (S.opTensor (star Y * M * Y) T)) := by
  rw [← Real.sqrt_mul (S.ev_opTensor_sandwich_diag_nonneg X M T hM hT), ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (S.ev_opTensor_sandwich_cauchy_schwarz X Y M T hM hT)

end SymModel

end MIPRE.LIDT.Co

end
