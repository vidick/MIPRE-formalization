/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122),
MIPStarRE/LDT/Preliminaries/Defs.lean, to the symmetric model of `planning/c6b-plan.md`; not a
vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Test.Defs
public import MIPRE.Background.LIDT.Co.Tactic.QuantumNonneg

@[expose] public section

/-!
# Preliminary definitions and statement structures

This file collects the lightweight statement and definition layer for the
preliminaries chapter of the LDT development. It records the paper's
consistency, sandwich, and completion statements in a form used by later files.
This is the counterpart of `MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/Defs.lean` in the
port of `planning/c6b-plan.md` (milestone M0, section "Port conventions").

The declarations live in `MIPRE.LIDT.Co.Preliminaries`, mirroring the vendored
`MIPStarRE.LDT.Preliminaries`. Since dot notation on `S : SymModel 𝔓 K` only reaches
`MIPRE.LIDT.Co.SymModel`, the model is an ordinary explicit argument here: it takes the place of
the vendored state `ψ` where the vendored declaration has one (`agreementProbability ψ 𝒟 A B` is
`agreementProbability S 𝒟 A B`), and is a new first explicit argument where it has none
(`diagonalSandwichFamily A B` is `diagonalSandwichFamily S A B`), as for the lifts
`IdxSubMeas.liftLeft S A` of `Co/Basic/SubMeasurementFamilies.lean`.

Local families (the vendored `IdxSubMeas Question Outcome ι`) have their operators in `𝔓`, and
the placed and sandwich families, which act on the joint space, in `K →L[ℂ] K`. The vendored
`CompTransferStmt` is about a state on a single space `ι`, so it takes a vector state
`V : VecState K` (`Co/Basic/QuantumState.lean`) and joint families.

In the symmetric model both tensor factors are `𝔓`, so the "two-space" declarations
(`heterogeneousDiagonalSandwichFamily`, `heterogeneousTotalSandwichFamily`,
`ConsSubMeasHeterogeneousStmt`) have the same types as their same-space versions; they are kept,
with the same bodies, so that the vendored callers of either form port as they stand, and the
families agree by `rfl` (`heterogeneousDiagonalSandwichFamily_eq`,
`heterogeneousTotalSandwichFamily_eq`).

## Main definitions

- `BipartiteSDDRel`: the paper-style left/right state-dependent distance
  relation.
- `ConsAgreement`: the measurement reformulation of consistency.
- `ConsSubMeasStmt`, `SwitchSandwichStmt`, `CompTransferStmt`, and
  `CompletingToMeasStmt`: conclusion statements for the main preliminary
  propositions.
- `completeAtOutcome`: completion of a submeasurement at a distinguished
  outcome.

## New here

- `heterogeneousDiagonalSandwichFamily_eq`, `heterogeneousTotalSandwichFamily_eq`: in the
  symmetric model the two-space sandwich families are the same-space ones (`rfl`).

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

- `references/ldt-paper/preliminaries.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Preliminaries

open MIPStarRE.LDT (Distribution avgOver uniformDistribution)

section Model

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ## Consistency and distance statements -/

/-- Source-style left/right relation `A^x_a ⊗ I ≈_δ I ⊗ B^x_a`. -/
structure BipartiteSDDRel {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome 𝔓) (δ : ℝ) : Prop where
  leftRightSquaredDistanceBound :
    S.sddError 𝒟 (IdxSubMeas.liftLeft S A) (IdxSubMeas.liftRight S B) ≤ δ

/-- Condition `0 ≤ B ≤ I` for the switch-sandwich argument. -/
structure OpBounded01 {R : Type*} [Ring R] [PartialOrder R] (B : R) : Prop where
  nonnegative : 0 ≤ B
  boundedByIdentity : 0 ≤ (1 : R) - B

/-- Agreement probability from `prop:simeq-for-measurements`. -/
noncomputable def agreementProbability {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (𝒟 : Distribution Question)
    (A B : IdxMeas Question Outcome 𝔓) : ℝ :=
  1 - S.bipartiteConsError 𝒟
        (IdxMeas.toIdxSubMeas A)
        (IdxMeas.toIdxSubMeas B)

/-- Conclusion statement for the measurement reformulation of consistency. -/
structure ConsAgreement {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (𝒟 : Distribution Question)
    (A B : IdxMeas Question Outcome 𝔓) (δ : ℝ) : Prop where
  agreementLowerBound : agreementProbability S 𝒟 A B ≥ 1 - δ

/-- A diagonal sandwich family has total operator at most the identity. -/
theorem diagonalSandwichFamily_total_le_one {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (A : IdxSubMeas Question Outcome 𝔓)
    (B : IdxMeas Question Outcome 𝔓) (q : Question) :
    (∑ a : Outcome, S.L ((A q).outcome a) * S.R ((B q).outcome a)) ≤ 1 := by
  calc
    ∑ a : Outcome, S.L ((A q).outcome a) * S.R ((B q).outcome a)
      ≤ ∑ a : Outcome, S.L ((A q).outcome a) :=
          Finset.sum_le_sum fun a _ =>
            S.opTensor_le_leftTensor ((A q).outcome_pos a) (Measurement.outcome_le_one (B q) a)
    _ = S.L ((A q).total) := by
      rw [S.leftTensor_finset_sum Finset.univ (fun a => (A q).outcome a), (A q).sum_eq_total]
    _ ≤ 1 := S.leftTensor_le_one (A q).total_le_one

/-- A total sandwich family has total operator at most the identity. -/
theorem totalSandwichFamily_total_le_one {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (A : IdxSubMeas Question Outcome 𝔓)
    (B : IdxMeas Question Outcome 𝔓) (q : Question) :
    (∑ a : Outcome, S.L ((A q).total) * S.R ((B q).outcome a)) ≤ 1 := by
  calc
    ∑ a : Outcome, S.L ((A q).total) * S.R ((B q).outcome a)
      = S.L ((A q).total) := by
          rw [← Finset.mul_sum, S.rightTensor_finset_sum Finset.univ (fun a => (B q).outcome a),
            (B q).sum_eq, S.rightTensor_one, mul_one]
    _ ≤ 1 := S.leftTensor_le_one (A q).total_le_one

/-- `A_a ⊗ B_a`, the diagonal bipartite family from `prop:cons-sub-meas`.

This same-space version is the specialization used by the existing
main-theorem path.  The paper-facing two-space version is
`heterogeneousDiagonalSandwichFamily`. -/
noncomputable def diagonalSandwichFamily {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K)
    (A : IdxSubMeas Question Outcome 𝔓)
    (B : IdxMeas Question Outcome 𝔓) :
    IdxSubMeas Question Outcome (K →L[ℂ] K) :=
  fun q => {
    outcome := fun a => S.L ((A q).outcome a) * S.R ((B q).outcome a)
    total := ∑ a : Outcome, S.L ((A q).outcome a) * S.R ((B q).outcome a)
    outcome_pos := fun a => by
      sym_nonneg
    sum_eq_total := rfl
    total_le_one := diagonalSandwichFamily_total_le_one S A B q
  }

/-- `A ⊗ B_a`, the total bipartite family from `prop:cons-sub-meas`.

This same-space version is the specialization used by the existing
main-theorem path.  The paper-facing two-space version is
`heterogeneousTotalSandwichFamily`. -/
noncomputable def totalSandwichFamily {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K)
    (A : IdxSubMeas Question Outcome 𝔓)
    (B : IdxMeas Question Outcome 𝔓) :
    IdxSubMeas Question Outcome (K →L[ℂ] K) :=
  fun q => {
    outcome := fun a => S.L ((A q).total) * S.R ((B q).outcome a)
    total := ∑ a : Outcome, S.L ((A q).total) * S.R ((B q).outcome a)
    outcome_pos := fun a => by
      sym_nonneg
    sum_eq_total := rfl
    total_le_one := totalSandwichFamily_total_le_one S A B q
  }

/-- `A_a ⊗ B_a` for the two-space statement of `prop:cons-sub-meas`.

Here `A` acts on the left tensor factor and `B` on the right one (`S.L` and `S.R`). In the
symmetric model both factors are `𝔓`, so this is `diagonalSandwichFamily` by `rfl`
(`heterogeneousDiagonalSandwichFamily_eq`). -/
noncomputable def heterogeneousDiagonalSandwichFamily {Question Outcome : Type*}
    [Fintype Outcome]
    (S : SymModel 𝔓 K)
    (A : IdxSubMeas Question Outcome 𝔓)
    (B : IdxMeas Question Outcome 𝔓) :
    IdxSubMeas Question Outcome (K →L[ℂ] K) :=
  fun q => {
    outcome := fun a => S.L ((A q).outcome a) * S.R ((B q).outcome a)
    total := ∑ a : Outcome, S.L ((A q).outcome a) * S.R ((B q).outcome a)
    outcome_pos := fun a => by
      sym_nonneg
    sum_eq_total := rfl
    total_le_one := diagonalSandwichFamily_total_le_one S A B q
  }

/-- `A ⊗ B_a` for the two-space statement of `prop:cons-sub-meas`.

The total operator `A^x = ∑_a A^x_a` remains on the left tensor factor, while
the measurement outcome `B^x_a` remains on the right tensor factor. In the symmetric model this
is `totalSandwichFamily` by `rfl` (`heterogeneousTotalSandwichFamily_eq`). -/
noncomputable def heterogeneousTotalSandwichFamily {Question Outcome : Type*}
    [Fintype Outcome]
    (S : SymModel 𝔓 K)
    (A : IdxSubMeas Question Outcome 𝔓)
    (B : IdxMeas Question Outcome 𝔓) :
    IdxSubMeas Question Outcome (K →L[ℂ] K) :=
  fun q => {
    outcome := fun a => S.L ((A q).total) * S.R ((B q).outcome a)
    total := ∑ a : Outcome, S.L ((A q).total) * S.R ((B q).outcome a)
    outcome_pos := fun a => by
      sym_nonneg
    sum_eq_total := rfl
    total_le_one := totalSandwichFamily_total_le_one S A B q
  }

/-- In the symmetric model the two-space diagonal sandwich family is the same-space one. -/
theorem heterogeneousDiagonalSandwichFamily_eq {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (A : IdxSubMeas Question Outcome 𝔓) (B : IdxMeas Question Outcome 𝔓) :
    heterogeneousDiagonalSandwichFamily S A B = diagonalSandwichFamily S A B :=
  rfl

/-- In the symmetric model the two-space total sandwich family is the same-space one. -/
theorem heterogeneousTotalSandwichFamily_eq {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (A : IdxSubMeas Question Outcome 𝔓) (B : IdxMeas Question Outcome 𝔓) :
    heterogeneousTotalSandwichFamily S A B = totalSandwichFamily S A B :=
  rfl

/-- Same-space output statement for `prop:cons-sub-meas`.

The paper-facing two-space output statement is
`ConsSubMeasHeterogeneousStmt`. -/
structure ConsSubMeasStmt {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome 𝔓)
    (B : IdxMeas Question Outcome 𝔓) (γ : ℝ) : Prop where
  diagonalControl :
    S.SDDRel 𝒟 (IdxSubMeas.liftLeft S A) (diagonalSandwichFamily S A B) γ
  sandwichControl :
    S.SDDRel 𝒟 (diagonalSandwichFamily S A B) (totalSandwichFamily S A B) γ
  combinedControl :
    S.SDDRel 𝒟 (IdxSubMeas.liftLeft S A) (totalSandwichFamily S A B) (4 * γ)

/-- Two-space output statement for `prop:cons-sub-meas`.

It records the two estimates
`A^x_a ⊗ I ≈_γ A^x_a ⊗ B^x_a` and
`A^x_a ⊗ B^x_a ≈_γ A^x ⊗ B^x_a`, and the resulting
`4γ` estimate from `A^x_a ⊗ I` to `A^x ⊗ B^x_a`. -/
structure ConsSubMeasHeterogeneousStmt {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome 𝔓)
    (B : IdxMeas Question Outcome 𝔓) (γ : ℝ) : Prop where
  /-- `A^x_a ⊗ I` is close to the diagonal family `A^x_a ⊗ B^x_a`. -/
  diagonalControl :
    S.SDDRel 𝒟 (IdxSubMeas.placeLeft S A) (heterogeneousDiagonalSandwichFamily S A B) γ
  /-- The diagonal family `A^x_a ⊗ B^x_a` is close to `A^x ⊗ B^x_a`. -/
  sandwichControl :
    S.SDDRel 𝒟
      (heterogeneousDiagonalSandwichFamily S A B)
      (heterogeneousTotalSandwichFamily S A B) γ
  /-- The two preceding estimates give `A^x_a ⊗ I ≈_{4γ} A^x ⊗ B^x_a`. -/
  combinedControl :
    S.SDDRel 𝒟
      (IdxSubMeas.placeLeft S A)
      (heterogeneousTotalSandwichFamily S A B) (4 * γ)

/-! ## Sandwich expectations -/

/-- Averaged left term `E_x ∑_a ⟨ψ, (A_a B A_a ⊗ I) ψ⟩`. -/
noncomputable def leftSandwichExpectation {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (𝒟 : Distribution Question)
    (A : IdxProjSubMeas Question Outcome 𝔓)
    (B : 𝔓) : ℝ :=
  avgOver 𝒟 fun q =>
    ∑ a, S.ev (S.L ((A q).outcome a) * S.L B * S.L ((A q).outcome a))

/-- Averaged middle term `E_x ∑_a ⟨ψ, (B ⊗ A_a) ψ⟩`. -/
noncomputable def middleSandwichExpectation {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (𝒟 : Distribution Question)
    (A : IdxProjSubMeas Question Outcome 𝔓)
    (B : 𝔓) : ℝ :=
  avgOver 𝒟 fun q =>
    ∑ a, S.ev (S.L B * S.R ((A q).outcome a))

/-- Averaged right term `E_x ∑_a ⟨ψ, (B A_a ⊗ I) ψ⟩`. -/
noncomputable def rightSandwichExpectation {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (𝒟 : Distribution Question)
    (A : IdxProjSubMeas Question Outcome 𝔓)
    (B : 𝔓) : ℝ :=
  avgOver 𝒟 fun q =>
    ∑ a, S.ev (S.L (B * (A q).outcome a))

/-- Conclusion statement for `prop:switch-sandwich`. -/
structure SwitchSandwichStmt {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (𝒟 : Distribution Question)
    (A : IdxProjSubMeas Question Outcome 𝔓)
    (B : 𝔓) (δ : ℝ) : Prop where
  leftSandwichTransfer :
    |leftSandwichExpectation S 𝒟 A B -
      middleSandwichExpectation S 𝒟 A B|
      ≤ 2 * Real.sqrt δ
  rightSandwichTransfer :
    |middleSandwichExpectation S 𝒟 A B -
      rightSandwichExpectation S 𝒟 A B|
      ≤ Real.sqrt δ

/-- Conclusion statement for `prop:completeness-transfer-projective-P`.

The vendored statement is about a state on a single space, so the state is a vector state
`V : VecState K` (a symmetric model is accepted through its coercion) and `A` and `P` are
families of joint operators. -/
structure CompTransferStmt {Question Outcome : Type*} [Fintype Outcome]
    (V : VecState K) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome (K →L[ℂ] K))
    (P : IdxProjSubMeas Question Outcome (K →L[ℂ] K)) (ε : ℝ) : Prop where
  completenessTransfer :
    V.idxSubMeasMass 𝒟 A ≥
      V.idxSubMeasMass 𝒟
        (IdxProjSubMeas.toIdxSubMeas P)
        - 2 * Real.sqrt ε

end Model

/-! ## Completion -/

section Completion

variable {R : Type*} [Ring R] [StarRing R] [PartialOrder R]

/-- The completed outcomes sum to the identity. -/
theorem completeAtOutcome_sum_eq_one {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (B : SubMeas Outcome R) (a0 : Outcome) :
    (∑ a : Outcome,
      if a = a0 then B.outcome a + (1 - B.total) else B.outcome a) = 1 := by
  have hrewrite :
      (∑ a : Outcome, if a = a0 then B.outcome a + (1 - B.total) else B.outcome a) =
        ∑ a : Outcome, (B.outcome a + if a = a0 then 1 - B.total else 0) :=
    Finset.sum_congr rfl fun a _ => by by_cases h : a = a0 <;> simp [h]
  rw [hrewrite, Finset.sum_add_distrib, B.sum_eq_total, Finset.sum_ite_eq' Finset.univ a0]
  simp

variable [StarOrderedRing R]

/-- Canonical completion of `B` by adjoining the residual `I - Σ_a B_a`
to the distinguished outcome `a0`. -/
noncomputable def completeAtOutcome {Outcome : Type*} [Fintype Outcome]
    (B : SubMeas Outcome R) (a0 : Outcome) : Measurement Outcome R := by
  classical
  let residual := 1 - B.total
  exact {
    toSubMeas := {
      outcome := fun a =>
        if h : a = a0 then
          B.outcome a + residual
        else
          B.outcome a
      total := 1
      outcome_pos := fun a => by
        by_cases h : a = a0
        · simpa [h, residual] using
            add_nonneg (B.outcome_pos a0) (sub_nonneg.mpr B.total_le_one)
        · simp [h, B.outcome_pos a]
      sum_eq_total := completeAtOutcome_sum_eq_one B a0
      total_le_one := le_rfl
    }
    total_eq_one := rfl
  }

end Completion

section Model

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Analytic conclusion for `prop:completing-to-measurement` once a witness
`C` has been fixed.

The theorem `completingToMeasurement` separately records that the chosen witness
is the canonical completion `completeAtOutcome B a0`, so this structure stores
only the closeness statement from the paper. -/
structure CompletingToMeasStmt {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K)
    (A : Measurement Outcome 𝔓) (B : SubMeas Outcome 𝔓)
    (C : Measurement Outcome 𝔓) (a0 : Outcome) (δ ζ : ℝ) : Prop where
  closenessAfterCompletion :
    S.SDDRel (uniformDistribution Unit)
      (constSubMeasFamily (A.toSubMeas.liftLeft S))
      (constSubMeasFamily (C.toSubMeas.liftLeft S))
      (2 * δ + 4 * Real.sqrt δ + 2 * ζ)

end Model

end MIPRE.LIDT.Co.Preliminaries

end
