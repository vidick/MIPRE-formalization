/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122),
MIPStarRE/LDT/Preliminaries/ConsistencyBridges.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Preliminaries.DistanceBounds

@[expose] public section

/-!
# Preliminary comparison theorems: consistency-to-distance estimates

Estimates converting consistency of a submeasurement and a measurement into
state-dependent distance controls for the diagonal and total sandwich families
of `prop:cons-sub-meas`: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/ConsistencyBridges.lean` in the port of
`planning/c6b-plan.md` (milestone M3, section "Port conventions").

As in `Co/Preliminaries/Defs.lean`, the declarations live in `MIPRE.LIDT.Co.Preliminaries` and
take the state as an ordinary explicit argument in place of the vendored state `ψ`. The
pointwise comparison `consSubMeas_controlHelper` is about joint operators on a single space, so
it takes a vector state `V : VecState K` (a symmetric model is accepted through its coercion);
the consistency statements are bipartite and take `S : SymModel 𝔓 K`.

In both sandwich estimates the difference `X a` of the two families is a product placement
`S.opTensor C D` with `0 ≤ C ≤ 1` and `0 ≤ D ≤ 1` (`A_a ⊗ (I - B_a)`, resp.
`(A - A_a) ⊗ B_a`), so `0 ≤ X a ≤ 1`, hence `X a * X a ≤ X a` (`sq_le_self`), and the sum of
`ev (X a)` is the consistency defect. The vendored proofs obtain `star (X a) = X a` from
positive semidefiniteness of matrices; here it is `IsSelfAdjoint.of_nonneg`.

In the symmetric model both tensor factors are `𝔓`, the general placements
`IdxSubMeas.placeLeft`, `placeRight` are the lifts `liftLeft`, `liftRight`, and the two-space
sandwich families are the same-space ones, all by `rfl`
(`Co/Basic/SubMeasurementFamilies.lean`, `Co/Preliminaries/Defs.lean`). So the
`_heterogeneous` statements are the same-space ones, and their proofs are the same-space
proofs.

## Not ported

Every declaration of the vendored file has a counterpart here.
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Preliminaries

open MIPStarRE.LDT (Distribution avgOver avgOver_mono)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ### Consistency controls for `prop:cons-sub-meas` -/

/-- Pointwise comparison behind `prop:cons-sub-meas`: if each squared difference
`(M_a - N_a)* (M_a - N_a)` has the expectation of `X_a * X_a` for some `0 ≤ X_a ≤ 1`, and the
`X_a` account exactly for the off-diagonal mass of `P` and `Q`, then the squared distance of `M`
and `N` is at most the consistency defect of `P` and `Q`. -/
theorem consSubMeas_controlHelper
    {Outcome : Type*} [Fintype Outcome]
    (V : VecState K)
    (P Q M N : SubMeas Outcome (K →L[ℂ] K))
    (X : Outcome → K →L[ℂ] K)
    (hSq :
      ∀ a : Outcome,
        V.ev (star (M.outcome a - N.outcome a) * (M.outcome a - N.outcome a)) =
          V.ev (X a * X a))
    (hX_nonneg : ∀ a : Outcome, 0 ≤ X a)
    (hX_le_one : ∀ a : Outcome, X a ≤ 1)
    (hSum :
      ∑ a : Outcome, V.ev (X a) =
        V.ev (P.total * Q.total) - V.qMatchMass P Q) :
    V.qSDD M N ≤ V.qConsDefect P Q := by
  have hle : V.qSDD M N ≤ ∑ a : Outcome, V.ev (X a) :=
    Finset.sum_le_sum fun a _ =>
      (hSq a).trans_le (V.ev_mono _ _ (sq_le_self (hX_nonneg a) (hX_le_one a)))
  exact hle.trans (hSum.trans_le (le_max_right 0 _))

/-- `prop:cons-sub-meas`, first estimate: if `A` is consistent with the measurement `B`, then
`A^x_a ⊗ I ≈_γ A^x_a ⊗ B^x_a`. -/
theorem consSubMeas_diagonalControl
    {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome 𝔓)
    (B : IdxMeas Question Outcome 𝔓) (γ : ℝ) :
    S.ConsRel 𝒟 A (IdxMeas.toIdxSubMeas B) γ →
    S.SDDRel 𝒟 (IdxSubMeas.liftLeft S A) (diagonalSandwichFamily S A B) γ := by
  intro ⟨hcons⟩
  refine ⟨(avgOver_mono 𝒟 _ _ fun q => ?_).trans hcons⟩
  let X : Outcome → K →L[ℂ] K := fun a =>
    S.L ((A q).outcome a) - S.L ((A q).outcome a) * S.R ((B q).outcome a)
  have hX_nonneg : ∀ a, 0 ≤ X a := fun a =>
    sub_nonneg.2 (S.opTensor_le_leftTensor ((A q).outcome_pos a)
      (Measurement.outcome_le_one (B q) a))
  have hX_le_one : ∀ a, X a ≤ 1 := fun a =>
    (sub_le_self _ ((diagonalSandwichFamily S A B q).outcome_pos a)).trans
      (S.leftTensor_le_one ((A q).outcome_le_one a))
  refine consSubMeas_controlHelper S.toVecState
    (S.leftPlacedSubMeas (A q)) (S.rightPlacedSubMeas (IdxMeas.toIdxSubMeas B q))
    (IdxSubMeas.liftLeft S A q) (diagonalSandwichFamily S A B q) X
    (fun a => congrArg (fun Y => S.ev (Y * X a)) (IsSelfAdjoint.of_nonneg (hX_nonneg a)).star_eq)
    hX_nonneg hX_le_one ?_
  have htotal : S.L (A q).total * S.R (B q).total = S.L (A q).total := by
    rw [(B q).total_eq_one, S.rightTensor_one, mul_one]
  have hleft : ∑ a, S.ev (S.L ((A q).outcome a)) = S.ev (S.L (A q).total) := by
    rw [← S.ev_sum, S.leftTensor_finset_sum, (A q).sum_eq_total]
  change ∑ a, S.ev (X a) = S.ev (S.L (A q).total * S.R (B q).total) -
    ∑ a, S.ev (S.L ((A q).outcome a) * S.R ((B q).outcome a))
  simp only [X, VecState.ev_sub, Finset.sum_sub_distrib, hleft, htotal]

/-- `prop:cons-sub-meas`, second estimate: if `A` is consistent with the measurement `B`, then
`A^x_a ⊗ B^x_a ≈_γ A^x ⊗ B^x_a`. -/
theorem consSubMeas_sandwichControl
    {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome 𝔓)
    (B : IdxMeas Question Outcome 𝔓) (γ : ℝ) :
    S.ConsRel 𝒟 A (IdxMeas.toIdxSubMeas B) γ →
    S.SDDRel 𝒟 (diagonalSandwichFamily S A B) (totalSandwichFamily S A B) γ := by
  intro ⟨hcons⟩
  refine ⟨(avgOver_mono 𝒟 _ _ fun q => ?_).trans hcons⟩
  let X : Outcome → K →L[ℂ] K := fun a =>
    S.L (A q).total * S.R ((B q).outcome a) - S.L ((A q).outcome a) * S.R ((B q).outcome a)
  have hX_nonneg : ∀ a, 0 ≤ X a := fun a =>
    sub_nonneg.2 (S.opTensor_mono_left ((A q).outcome_le_total a) ((B q).outcome_pos a))
  have hX_le_one : ∀ a, X a ≤ 1 := fun a =>
    (sub_le_self _ ((diagonalSandwichFamily S A B q).outcome_pos a)).trans
      ((S.opTensor_le_leftTensor (A q).total_nonneg (Measurement.outcome_le_one (B q) a)).trans
        (S.leftTensor_le_one (A q).total_le_one))
  refine consSubMeas_controlHelper S.toVecState
    (S.leftPlacedSubMeas (A q)) (S.rightPlacedSubMeas (IdxMeas.toIdxSubMeas B q))
    (diagonalSandwichFamily S A B q) (totalSandwichFamily S A B q) X
    (fun a => ?_) hX_nonneg hX_le_one ?_
  · rw [← neg_sub, star_neg, neg_mul_neg]
    exact congrArg (fun Y => S.ev (Y * X a)) (IsSelfAdjoint.of_nonneg (hX_nonneg a)).star_eq
  have htotal : S.L (A q).total * S.R (B q).total = S.L (A q).total := by
    rw [(B q).total_eq_one, S.rightTensor_one, mul_one]
  have hsum : ∑ a, S.ev (S.L (A q).total * S.R ((B q).outcome a)) = S.ev (S.L (A q).total) := by
    rw [← S.ev_sum, ← Finset.mul_sum, S.rightTensor_finset_sum, (B q).sum_eq,
      S.rightTensor_one, mul_one]
  change ∑ a, S.ev (X a) = S.ev (S.L (A q).total * S.R (B q).total) -
    ∑ a, S.ev (S.L ((A q).outcome a) * S.R ((B q).outcome a))
  simp only [X, VecState.ev_sub, Finset.sum_sub_distrib, hsum, htotal]

/-- `prop:cons-sub-meas`, first estimate, in the two-space form:
`A^x_a ⊗ I ≈_γ A^x_a ⊗ B^x_a`. In the symmetric model this is `consSubMeas_diagonalControl`. -/
theorem consSubMeas_diagonalControl_heterogeneous
    {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome 𝔓)
    (B : IdxMeas Question Outcome 𝔓) (γ : ℝ) :
    S.ConsRel 𝒟 A (IdxMeas.toIdxSubMeas B) γ →
    S.SDDRel 𝒟 (IdxSubMeas.placeLeft S A) (heterogeneousDiagonalSandwichFamily S A B) γ :=
  consSubMeas_diagonalControl S 𝒟 A B γ

/-- `prop:cons-sub-meas`, second estimate, in the two-space form:
`A^x_a ⊗ B^x_a ≈_γ A^x ⊗ B^x_a`. In the symmetric model this is
`consSubMeas_sandwichControl`. -/
theorem consSubMeas_sandwichControl_heterogeneous
    {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome 𝔓)
    (B : IdxMeas Question Outcome 𝔓) (γ : ℝ) :
    S.ConsRel 𝒟 A (IdxMeas.toIdxSubMeas B) γ →
    S.SDDRel 𝒟
      (heterogeneousDiagonalSandwichFamily S A B)
      (heterogeneousTotalSandwichFamily S A B) γ :=
  consSubMeas_sandwichControl S 𝒟 A B γ

/-- `prop:cons-sub-meas`, in the two-space form stated in
`references/ldt-paper/preliminaries.tex` lines 708--744 (upstream `LionSR/MIPStarRE`). -/
theorem consSubMeas_heterogeneous {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome 𝔓)
    (B : IdxMeas Question Outcome 𝔓) (γ : ℝ) :
    S.ConsRel 𝒟 A (IdxMeas.toIdxSubMeas B) γ →
    ConsSubMeasHeterogeneousStmt S 𝒟 A B γ := by
  intro hcons
  have hdc := consSubMeas_diagonalControl_heterogeneous S 𝒟 A B γ hcons
  have hsc := consSubMeas_sandwichControl_heterogeneous S 𝒟 A B γ hcons
  exact {
    diagonalControl := hdc
    sandwichControl := hsc
    combinedControl :=
      stateDependentDistanceRel_mono S.toVecState 𝒟 (IdxSubMeas.placeLeft S A)
        (heterogeneousTotalSandwichFamily S A B) (2 * (γ + γ)) (4 * γ) (by linarith)
        (stateDependentDistanceRel_triangle S.toVecState 𝒟 (IdxSubMeas.placeLeft S A)
          (heterogeneousDiagonalSandwichFamily S A B)
          (heterogeneousTotalSandwichFamily S A B) γ γ hdc hsc)
  }

/-- Same-space specialization of `prop:cons-sub-meas`.

The paper-facing two-space theorem is `consSubMeas_heterogeneous`. -/
theorem consSubMeas {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome 𝔓)
    (B : IdxMeas Question Outcome 𝔓) (γ : ℝ) :
    S.ConsRel 𝒟 A (IdxMeas.toIdxSubMeas B) γ →
    ConsSubMeasStmt S 𝒟 A B γ := by
  intro hcons
  have hdc := consSubMeas_diagonalControl S 𝒟 A B γ hcons
  have hsc := consSubMeas_sandwichControl S 𝒟 A B γ hcons
  exact {
    diagonalControl := hdc
    sandwichControl := hsc
    combinedControl :=
      stateDependentDistanceRel_mono S.toVecState 𝒟 (IdxSubMeas.liftLeft S A)
        (totalSandwichFamily S A B) (2 * (γ + γ)) (4 * γ) (by linarith)
        (stateDependentDistanceRel_triangle S.toVecState 𝒟 (IdxSubMeas.liftLeft S A)
          (diagonalSandwichFamily S A B) (totalSandwichFamily S A B) γ γ hdc hsc)
  }

end MIPRE.LIDT.Co.Preliminaries

end
