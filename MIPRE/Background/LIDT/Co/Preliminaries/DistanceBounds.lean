/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122),
MIPStarRE/LDT/Preliminaries/DistanceBounds.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Preliminaries.ComparisonCore

@[expose] public section

/-!
# Preliminary comparison theorems: distance bounds

Triangle-inequality style bounds for `SDDRel` and `SDDOpRel`: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/DistanceBounds.lean` in the port of
`planning/c6b-plan.md` (milestone M0, section "Port conventions").

As in `Co/Preliminaries/Defs.lean`, the declarations live in `MIPRE.LIDT.Co.Preliminaries` and
take the state as an ordinary explicit argument in place of the vendored state `ψ`. The vendored
statements are about a state on a single space, so the state is a vector state
`V : VecState K` (`Co/Basic/QuantumState.lean`; a symmetric model `S` is accepted through its
coercion) and the families are joint, with operators in `K →L[ℂ] K`.

The pointwise core of `questionCabApproxDelta` is the repository's `fact:add-a-proj`,
`MIPRE.StateModel.sum_snorm_sq_mul_le_of_le` (`MIPRE/Foundations/StateModel.lean`) on
`V.toStateModel`, through `VecState.qSDDCore_eq_sum_snorm_sq` of `Co/Test/Defs.lean`; the vendored
proof expands the sandwich and uses `conjTranspose_mul_mono`. The triangle inequalities
`questionSDD_triangle`, `questionSDD_triangle_three` and `questionSDDOp_triangle` are, term by
term, `MIPRE.StateModel.sum_snorm_sq_triangle` and `sum_snorm_sq_triangle3`, through
`VecState.ev_diff_triangle` and `ev_diff_triangle_three` (`Co/Basic/OperatorExpectations.lean`).

## Not ported

- `sddOpRel_leftPlaced_of_ev_eq`: its hypothesis is a second state `φ` on the first tensor factor
  with the marginal identity `ev ψ (leftTensor X) = ev φ X`, a reduced density matrix. The model
  has no local state: the restriction of `S.ev` to `S.L` is a state of `𝔓`, not a vector state on
  a space where the local operators act, and a family placed by `S.L` is measured against `S`
  itself (`V : VecState K` with `V := S`), so the statement has no counterpart; its only vendored
  consumer is the matrix orthonormalization route of
  `MakingMeasurementsProjective/LocalityPreservingRepair.lean`, which the port replaces by the
  dimension-free orthonormalization (`planning/c6b-plan.md`, M8).
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Preliminaries

open MIPStarRE.LDT (Distribution avgOver avgOver_mono avgOver_const_mul avgOver_add)

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ### Infrastructure: triangle inequality for `SDDRel` -/

/-- Atomic mathematical fact: the parallelogram-style inequality for `qSDD`. -/
theorem questionSDD_triangle {Outcome : Type*}
    [Fintype Outcome]
    (V : VecState K) (A B C : SubMeas Outcome (K →L[ℂ] K)) :
    V.qSDD A C ≤
      2 * (V.qSDD A B +
           V.qSDD B C) := by
  simp only [VecState.qSDD, VecState.qSDDCore]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  exact Finset.sum_le_sum fun a _ => V.ev_diff_triangle _ _ _

/-- Atomic mathematical fact: the three-step triangle inequality for `qSDD`.

This is the `k = 3` instance of `prop:triangle-inequality-for-approx_delta`,
with the sharp paper constant `3 * (δ₁ + δ₂ + δ₃)`. -/
theorem questionSDD_triangle_three {Outcome : Type*}
    [Fintype Outcome]
    (V : VecState K) (A B C D : SubMeas Outcome (K →L[ℂ] K)) :
    V.qSDD A D ≤ 3 * (V.qSDD A B + V.qSDD B C + V.qSDD C D) := by
  simp only [VecState.qSDD, VecState.qSDDCore]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  exact Finset.sum_le_sum fun a _ => V.ev_diff_triangle_three _ _ _ _

/-- Triangle inequality for state-dependent distance. -/
theorem stateDependentDistanceRel_triangle
    {Question Outcome : Type*}
    [Fintype Outcome]
    (V : VecState K) (𝒟 : Distribution Question)
    (A B C : IdxSubMeas Question Outcome (K →L[ℂ] K)) (δ₁ δ₂ : ℝ) :
    V.SDDRel 𝒟 A B δ₁ →
    V.SDDRel 𝒟 B C δ₂ →
    V.SDDRel 𝒟 A C (2 * (δ₁ + δ₂)) := by
  intro ⟨h₁⟩ ⟨h₂⟩
  constructor
  calc V.sddError 𝒟 A C
      ≤ avgOver 𝒟
          (fun q => 2 * (V.qSDD (A q) (B q) + V.qSDD (B q) (C q))) :=
        avgOver_mono 𝒟 _ _ fun q => questionSDD_triangle V (A q) (B q) (C q)
    _ = 2 * (V.sddError 𝒟 A B + V.sddError 𝒟 B C) := by
        rw [avgOver_const_mul, avgOver_add]
        rfl
    _ ≤ 2 * (δ₁ + δ₂) := mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) (by norm_num)

/-- Three-step triangle inequality for state-dependent distance. -/
theorem stateDependentDistanceRel_triangle_three {Question Outcome : Type*}
    [Fintype Outcome]
    (V : VecState K) (𝒟 : Distribution Question)
    (A B C D : IdxSubMeas Question Outcome (K →L[ℂ] K)) (δ₁ δ₂ δ₃ : ℝ) :
    V.SDDRel 𝒟 A B δ₁ →
    V.SDDRel 𝒟 B C δ₂ →
    V.SDDRel 𝒟 C D δ₃ →
    V.SDDRel 𝒟 A D (3 * (δ₁ + δ₂ + δ₃)) := by
  intro ⟨hAB⟩ ⟨hBC⟩ ⟨hCD⟩
  constructor
  calc V.sddError 𝒟 A D
      ≤ avgOver 𝒟 (fun q =>
          3 * (V.qSDD (A q) (B q) + V.qSDD (B q) (C q) + V.qSDD (C q) (D q))) :=
        avgOver_mono 𝒟 _ _ fun q => questionSDD_triangle_three V _ _ _ _
    _ = 3 * (V.sddError 𝒟 A B + V.sddError 𝒟 B C + V.sddError 𝒟 C D) := by
        rw [avgOver_const_mul, avgOver_add, avgOver_add]
        rfl
    _ ≤ 3 * (δ₁ + δ₂ + δ₃) := by linarith

/-- Monotonicity: if `SDDRel` holds for `δ`, it holds for any `δ' ≥ δ`. -/
theorem stateDependentDistanceRel_mono
    {Question Outcome : Type*}
    [Fintype Outcome]
    (V : VecState K) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome (K →L[ℂ] K)) (δ δ' : ℝ)
    (hle : δ ≤ δ') :
    V.SDDRel 𝒟 A B δ →
    V.SDDRel 𝒟 A B δ' :=
  fun ⟨h⟩ => ⟨h.trans hle⟩

/-- Left multiplication by a column contraction `C a` (`∑_b (C a b)* C a b ≤ 1`) does not
increase the operator-family squared distance. -/
theorem questionCabApproxDelta
    {Outcome Aux : Type*}
    [Fintype Outcome] [Fintype Aux]
    (V : VecState K)
    (A B : OpFamily Outcome (K →L[ℂ] K))
    (C : Outcome → Aux → K →L[ℂ] K)
    (hC : ∀ a, ∑ b : Aux, star (C a b) * C a b ≤ 1) :
    V.qSDDOp
        ({ outcome := fun ab : Outcome × Aux =>
             C ab.1 ab.2 * A.outcome ab.1
           total := ∑ ab : Outcome × Aux,
             C ab.1 ab.2 * A.outcome ab.1
         } : OpFamily (Outcome × Aux) (K →L[ℂ] K))
        ({ outcome := fun ab : Outcome × Aux =>
             C ab.1 ab.2 * B.outcome ab.1
           total := ∑ ab : Outcome × Aux,
             C ab.1 ab.2 * B.outcome ab.1
         } : OpFamily (Outcome × Aux) (K →L[ℂ] K)) ≤
      V.qSDDOp A B := by
  rw [VecState.qSDDOp, VecState.qSDDOp, V.qSDDCore_eq_sum_snorm_sq,
    V.qSDDCore_eq_sum_snorm_sq, Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun a _ => ?_
  simp only [← mul_sub]
  exact V.toStateModel.sum_snorm_sq_mul_le_of_le (C a) (hC a) (A.outcome a - B.outcome a)

/-- `prop:cab-approx-delta`. -/
theorem cabApproxDelta_raw
    {Question Outcome Aux : Type*}
    [Fintype Outcome] [Fintype Aux]
    (V : VecState K) (𝒟 : Distribution Question)
    (A B : IdxOpFamily Question Outcome (K →L[ℂ] K))
    (C : (q : Question) → Outcome → Aux → K →L[ℂ] K)
    (δ : ℝ) :
    V.SDDOpRel 𝒟 A B δ →
    (∀ q a, ∑ b : Aux, star (C q a b) * C q a b ≤ 1) →
    V.SDDOpRel 𝒟
      (fun q => ({
        outcome := fun ab : Outcome × Aux =>
          C q ab.1 ab.2 * (A q).outcome ab.1
        total := ∑ ab : Outcome × Aux,
          C q ab.1 ab.2 * (A q).outcome ab.1
      } : OpFamily (Outcome × Aux) (K →L[ℂ] K)))
      (fun q => ({
        outcome := fun ab : Outcome × Aux =>
          C q ab.1 ab.2 * (B q).outcome ab.1
        total := ∑ ab : Outcome × Aux,
          C q ab.1 ab.2 * (B q).outcome ab.1
      } : OpFamily (Outcome × Aux) (K →L[ℂ] K)))
      δ :=
  fun ⟨hAB⟩ hC => ⟨(avgOver_mono 𝒟 _ _ fun q =>
    questionCabApproxDelta V (A q) (B q) (C q) (hC q)).trans hAB⟩

/-! ### Infrastructure: triangle inequality for `SDDOpRel` -/

/-- The operator-family squared-distance defect is nonnegative. -/
theorem qSDDOp_nonneg
    {Outcome : Type*} [Fintype Outcome]
    (V : VecState K) (A B : OpFamily Outcome (K →L[ℂ] K)) :
    0 ≤ V.qSDDOp A B :=
  Finset.sum_nonneg fun _ _ => V.ev_adjoint_self_nonneg _

/-- Atomic mathematical fact: the parallelogram-style inequality for `qSDDOp`. -/
theorem questionSDDOp_triangle
    {Outcome : Type*} [Fintype Outcome]
    (V : VecState K) (A B C : OpFamily Outcome (K →L[ℂ] K)) :
    V.qSDDOp A C ≤ 2 * (V.qSDDOp A B + V.qSDDOp B C) := by
  simp only [VecState.qSDDOp, VecState.qSDDCore]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  exact Finset.sum_le_sum fun a _ => V.ev_diff_triangle _ _ _

/-- Triangle inequality for operator-family state-dependent distance. -/
theorem stateDependentDistanceOpRel_triangle
    {Question Outcome : Type*}
    [Fintype Outcome]
    (V : VecState K) (𝒟 : Distribution Question)
    (A B C : IdxOpFamily Question Outcome (K →L[ℂ] K)) (δ₁ δ₂ : ℝ) :
    V.SDDOpRel 𝒟 A B δ₁ →
    V.SDDOpRel 𝒟 B C δ₂ →
    V.SDDOpRel 𝒟 A C (2 * (δ₁ + δ₂)) := by
  intro ⟨h₁⟩ ⟨h₂⟩
  constructor
  calc V.sddErrorOp 𝒟 A C
      ≤ avgOver 𝒟
          (fun q => 2 * (V.qSDDOp (A q) (B q) + V.qSDDOp (B q) (C q))) :=
        avgOver_mono 𝒟 _ _ fun q => questionSDDOp_triangle V (A q) (B q) (C q)
    _ = 2 * (V.sddErrorOp 𝒟 A B + V.sddErrorOp 𝒟 B C) := by
        rw [avgOver_const_mul, avgOver_add]
        rfl
    _ ≤ 2 * (δ₁ + δ₂) := mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) (by norm_num)

/-- Monotonicity of `SDDOpRel` in the error bound. -/
theorem stateDependentDistanceOpRel_mono
    {Question Outcome : Type*}
    [Fintype Outcome]
    (V : VecState K) (𝒟 : Distribution Question)
    (A B : IdxOpFamily Question Outcome (K →L[ℂ] K)) (δ δ' : ℝ)
    (hle : δ ≤ δ') :
    V.SDDOpRel 𝒟 A B δ →
    V.SDDOpRel 𝒟 A B δ' :=
  fun ⟨h⟩ => ⟨h.trans hle⟩

/-- Symmetry of the operator-family state-dependent distance relation. -/
theorem sddOpRel_symm
    {Question Outcome : Type*} [Fintype Outcome]
    (V : VecState K) (𝒟 : Distribution Question)
    (A B : IdxOpFamily Question Outcome (K →L[ℂ] K)) (δ : ℝ) :
    V.SDDOpRel 𝒟 A B δ → V.SDDOpRel 𝒟 B A δ :=
  fun ⟨h⟩ => ⟨(MIPStarRE.LDT.avgOver_congr 𝒟 _ _ fun q =>
    qSDDOp_symm V (B q) (A q)).trans_le h⟩

end MIPRE.LIDT.Co.Preliminaries

end
