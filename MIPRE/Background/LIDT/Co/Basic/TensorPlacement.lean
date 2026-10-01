/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Basic/
TensorPlacement.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Basic.SubMeasurementCore
public import MIPRE.Background.LIDT.Co.Basic.OperatorExpectations

@[expose] public section

/-!
# Tensor-placement helper lemmas and sandwich tensor estimates

Tensor-sum commutation, positivity/boundedness preservation, factoring lemmas, and
sandwich-residual estimates used in the main induction step and polynomial-agreement arguments:
the counterpart of `MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/TensorPlacement.lean` in the port
of `planning/c6b-plan.md` (milestone M0, section "Port conventions").

The vendored placements `leftTensor A = A ⊗ 1` and `rightTensor A = 1 ⊗ A` are Kronecker
products, and their identities are proved entrywise or through `Matrix.kronecker` lemmas. Here
they are the ⋆-homomorphisms `S.L` and `S.R` of a symmetric model `S`, so each identity is a
`map_*` lemma of a ⋆-homomorphism (linearity in a real or complex scalar, additivity over a
finite sum), and the product placement `S.opTensor A B = S.L A * S.R B` is linear in each factor
by the keystone's `opTensor_*` lemmas. Statements drop the normalization hypothesis
`hnorm : ψ.IsNormalized`, which is a theorem of the model (`VecState.ev_one_of_isNormalized`).

## Ported elsewhere

`leftTensor_finset_sum`, `rightTensor_finset_sum`, `leftTensor_nonneg`, `rightTensor_nonneg`,
`leftTensor_le_one` and `rightTensor_le_one` are ported in `Co/Basic/QuantumState.lean`, with
every operator-positivity fact of the port.

## Not ported

Every other declaration of the vendored file has a counterpart here.
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co

open MIPStarRE.LDT (Distribution avgOver)

namespace SymModel

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (S : SymModel 𝔓 K)

/-- A ⋆-homomorphism into the joint operators commutes with operator averages: it is additive
and real-linear. -/
private theorem map_averageOperatorOverDistribution (f : 𝔓 →⋆ₐ[ℂ] (K →L[ℂ] K)) {α : Type*}
    (𝒟 : Distribution α) (A : α → 𝔓) :
    f (averageOperatorOverDistribution 𝒟 A) =
      averageOperatorOverDistribution 𝒟 (fun a => f (A a)) :=
  (map_sum f _ _).trans <| Finset.sum_congr rfl fun a _ =>
    (congrArg f (Complex.coe_smul (𝒟.weight a) (A a)).symm).trans <|
      (map_smul f _ (A a)).trans (Complex.coe_smul (𝒟.weight a) (f (A a)))

/-! ### Tensor-placement helper lemmas -/

/-- Left tensor placement commutes with operator averages. -/
theorem leftTensor_averageOperatorOverDistribution {α : Type*}
    (𝒟 : Distribution α) (A : α → 𝔓) :
    S.L (averageOperatorOverDistribution 𝒟 A) =
      averageOperatorOverDistribution 𝒟 (fun a => S.L (A a)) :=
  map_averageOperatorOverDistribution S.L 𝒟 A

/-- Expanding the left-tensor mass of a submeasurement on the state as the sum of per-outcome
left-tensor expectations.

This is a generic identity at the level of `S.ev (S.L _)`: applying `SubMeas.sum_eq_total`,
pulling `S.L` through the finite sum via `leftTensor_finset_sum`, and distributing `ev` through
the sum via `ev_finset_sum`. It yields the helper-stage opening
`subMeasMass S (A.liftLeft S) = ∑ a, S.ev (S.L (A.outcome a))` used in the Section 9 /
Section 12 calculations. -/
theorem ev_leftTensor_total_eq_sum_outcome {α : Type*} [Fintype α] (A : SubMeas α 𝔓) :
    S.ev (S.L A.total) = ∑ a : α, S.ev (S.L (A.outcome a)) := by
  rw [← A.sum_eq_total, ← S.leftTensor_finset_sum, S.ev_finset_sum]

/-- Evaluation of a left-placed operator average is the average of the left-placed
evaluations. -/
theorem ev_leftTensor_averageOperatorOverDistribution {α : Type*}
    (𝒟 : Distribution α) (A : α → 𝔓) :
    S.ev (S.L (averageOperatorOverDistribution 𝒟 A)) =
      avgOver 𝒟 (fun a => S.ev (S.L (A a))) := by
  rw [leftTensor_averageOperatorOverDistribution]
  exact S.ev_averageOperatorOverDistribution 𝒟 (fun a => S.L (A a))

/-- Right tensor placement commutes with operator averages. -/
theorem rightTensor_averageOperatorOverDistribution {α : Type*}
    (𝒟 : Distribution α) (A : α → 𝔓) :
    S.R (averageOperatorOverDistribution 𝒟 A) =
      averageOperatorOverDistribution 𝒟 (fun a => S.R (A a)) :=
  map_averageOperatorOverDistribution S.R 𝒟 A

/-- Evaluation of a right-placed operator average is the average of the right-placed
evaluations. -/
theorem ev_rightTensor_averageOperatorOverDistribution {α : Type*}
    (𝒟 : Distribution α) (A : α → 𝔓) :
    S.ev (S.R (averageOperatorOverDistribution 𝒟 A)) =
      avgOver 𝒟 (fun a => S.ev (S.R (A a))) := by
  rw [rightTensor_averageOperatorOverDistribution]
  exact S.ev_averageOperatorOverDistribution 𝒟 (fun a => S.R (A a))

/-- Tensoring on the right commutes with operator averages in the left factor. -/
theorem opTensor_averageOperatorOverDistribution_left {α : Type*}
    (𝒟 : Distribution α) (A : α → 𝔓) (B : 𝔓) :
    S.opTensor (averageOperatorOverDistribution 𝒟 A) B =
      averageOperatorOverDistribution 𝒟 (fun a => S.opTensor (A a) B) :=
  (S.opTensor_sum_left_finset _ _ B).trans <|
    Finset.sum_congr rfl fun a _ => S.opTensor_smul_left_error (𝒟.weight a) (A a) B

/-- Tensoring on the left commutes with operator averages in the right factor. -/
theorem opTensor_averageOperatorOverDistribution_right {α : Type*}
    (𝒟 : Distribution α) (A : 𝔓) (B : α → 𝔓) :
    S.opTensor A (averageOperatorOverDistribution 𝒟 B) =
      averageOperatorOverDistribution 𝒟 (fun a => S.opTensor A (B a)) :=
  (S.opTensor_sum_right_finset A _ _).trans <|
    Finset.sum_congr rfl fun a _ => S.opTensor_smul_right_error (𝒟.weight a) A (B a)

/-- Evaluation of an averaged left tensor factor is the average of the corresponding tensor
expectations. -/
theorem ev_opTensor_averageOperatorOverDistribution_left {α : Type*}
    (𝒟 : Distribution α) (A : α → 𝔓) (B : 𝔓) :
    S.ev (S.opTensor (averageOperatorOverDistribution 𝒟 A) B) =
      avgOver 𝒟 (fun a => S.ev (S.opTensor (A a) B)) := by
  rw [opTensor_averageOperatorOverDistribution_left]
  exact S.ev_averageOperatorOverDistribution 𝒟 (fun a => S.opTensor (A a) B)

/-- Evaluation of an averaged right tensor factor is the average of the corresponding tensor
expectations. -/
theorem ev_opTensor_averageOperatorOverDistribution_right {α : Type*}
    (𝒟 : Distribution α) (A : 𝔓) (B : α → 𝔓) :
    S.ev (S.opTensor A (averageOperatorOverDistribution 𝒟 B)) =
      avgOver 𝒟 (fun a => S.ev (S.opTensor A (B a))) := by
  rw [opTensor_averageOperatorOverDistribution_right]
  exact S.ev_averageOperatorOverDistribution 𝒟 (fun a => S.opTensor A (B a))

/-- A complex scalar on the left register factors out of a product placement.

This is the placement version of bilinearity of `opTensor`: placing `c • A` on the left and
multiplying by the right placement of `B` equals the same scalar multiplying `S.L A * S.R B`. -/
theorem leftTensor_mul_rightTensor_smul_left (c : ℝ) (A B : 𝔓) :
    S.L ((c : ℂ) • A) * S.R B = (c : ℂ) • (S.L A * S.R B) :=
  (congrArg (· * S.R B) (map_smul S.L (c : ℂ) A)).trans (smul_mul_assoc _ _ _)

/-- A complex scalar on the right register factors out of a product placement.

This is the placement version of bilinearity of `opTensor`: placing `c • B` on the right and
multiplying by the left placement of `A` equals the same scalar multiplying `S.L A * S.R B`. -/
theorem leftTensor_mul_rightTensor_smul_right (c : ℝ) (A B : 𝔓) :
    S.L A * S.R ((c : ℂ) • B) = (c : ℂ) • (S.L A * S.R B) :=
  (congrArg (S.L A * ·) (map_smul S.R (c : ℂ) B)).trans (mul_smul_comm _ _ _)

/-- A real scalar on the left register factors out of a product placement.

This restates `leftTensor_mul_rightTensor_smul_left` for the real scalar action used by
`averageOperatorOverDistribution`, coercing the real scalar to `ℂ` on the product. -/
theorem leftTensor_mul_rightTensor_real_smul_left (c : ℝ) (A B : 𝔓) :
    S.L (c • A) * S.R B = (c : ℂ) • (S.L A * S.R B) := by
  rw [← Complex.coe_smul]
  exact S.leftTensor_mul_rightTensor_smul_left c A B

/-- A real scalar on the right register factors out of a product placement.

This restates `leftTensor_mul_rightTensor_smul_right` for the real scalar action used by
`averageOperatorOverDistribution`, coercing the real scalar to `ℂ` on the product. -/
theorem leftTensor_mul_rightTensor_real_smul_right (c : ℝ) (A B : 𝔓) :
    S.L A * S.R (c • B) = (c : ℂ) • (S.L A * S.R B) := by
  rw [← Complex.coe_smul]
  exact S.leftTensor_mul_rightTensor_smul_right c A B

/-- The total left-register expectation of a submeasurement is at most one (the vendored
hypothesis `hnorm : ψ.IsNormalized` is a theorem of the model). -/
theorem sum_ev_leftTensor_outcome_le_one {α : Type*} [Fintype α] (A : SubMeas α 𝔓) :
    ∑ a : α, S.ev (S.L (A.outcome a)) ≤ 1 := by
  rw [← S.ev_leftTensor_total_eq_sum_outcome A, ← S.ev_one_of_isNormalized]
  exact S.ev_mono _ _ (S.leftTensor_le_one A.total_le_one)

end SymModel

namespace SubMeas

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A filtered diagonal product-placement sum of two submeasurements is a contraction.

The estimate uses only positivity and the submeasurement total bound on the left factor,
together with the pointwise `≤ 1` bound on the right factor. (The model `M` is an explicit
argument here; the vendored statement names the carrier instead.) -/
theorem opTensor_sum_filter_le_one {α : Type*} [Fintype α] (M : SymModel 𝔓 K)
    (S T : SubMeas α 𝔓) (P : α → Prop) [DecidablePred P] :
    ∑ x ∈ Finset.univ.filter P, M.opTensor (S.outcome x) (T.outcome x) ≤ 1 :=
  calc
    ∑ x ∈ Finset.univ.filter P, M.opTensor (S.outcome x) (T.outcome x)
      ≤ ∑ x ∈ Finset.univ.filter P, M.L (S.outcome x) :=
          Finset.sum_le_sum fun x _ =>
            M.opTensor_le_leftTensor (S.outcome_pos x) (T.outcome_le_one x)
    _ ≤ ∑ x : α, M.L (S.outcome x) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun x _ _ => M.leftTensor_nonneg (S.outcome_pos x))
    _ = M.L S.total := by rw [M.leftTensor_finset_sum, S.sum_eq_total]
    _ ≤ 1 := M.leftTensor_le_one S.total_le_one

end SubMeas

namespace SymModel

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (S : SymModel 𝔓 K)

/-! ### Sandwich tensor estimates -/

/-- A single tensor summand with a sandwiched left register is nonnegative in expectation.

The left register `Outer_o * Inner_i * Outer_o` is positive by sandwich positivity, and the
right-register outcome is positive, so their product placement is positive. -/
theorem sandwichTensorSummand_nonneg {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (Outer : SubMeas β 𝔓) (Inner : SubMeas α 𝔓) (Right : SubMeas γ 𝔓)
    (o : β) (i : α) (r : γ) :
    0 ≤ S.ev
      (S.L (Outer.outcome o * Inner.outcome i * Outer.outcome o) * S.R (Right.outcome r)) :=
  S.ev_nonneg_of_psd _ <|
    S.opTensor_nonneg
      (IsSelfAdjoint.conjugate_nonneg (Inner.outcome_pos i) (Outer.outcome_hermitian o))
      (Right.outcome_pos r)

/-- The residual tensor sum from a sandwiched left-register submeasurement and an independent
right-register submeasurement is at most one (the vendored hypothesis
`hnorm : ψ.IsNormalized` is a theorem of the model).

The operator under the sum factors as `S.L (∑ o, Outer_o * Inner.total * Outer_o) *
S.R Right.total`; the first factor is bounded by `1` by the submeasurement axioms and sandwich
monotonicity. The second factor is also bounded by `1`. -/
theorem sandwichTensor_residual_sum_le_one {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (Outer : SubMeas β 𝔓) (Inner : SubMeas α 𝔓) (Right : SubMeas γ 𝔓) :
    (∑ ir : α × γ, ∑ o : β,
        S.ev
          (S.L (Outer.outcome o * Inner.outcome ir.1 * Outer.outcome o) *
            S.R (Right.outcome ir.2))) ≤ 1 := by
  have hsandwichTotal_nonneg : 0 ≤ ∑ o : β, Outer.outcome o * Inner.total * Outer.outcome o :=
    Finset.sum_nonneg fun o _ =>
      IsSelfAdjoint.conjugate_nonneg Inner.total_nonneg (Outer.outcome_hermitian o)
  have hsandwichTotal_le_one : ∑ o : β, Outer.outcome o * Inner.total * Outer.outcome o ≤ 1 :=
    calc
      ∑ o : β, Outer.outcome o * Inner.total * Outer.outcome o
        ≤ ∑ o : β, Outer.outcome o :=
          Finset.sum_le_sum fun o _ =>
            ((IsSelfAdjoint.conjugate_le_conjugate Inner.total_le_one
              (Outer.outcome_hermitian o)).trans_eq (by rw [mul_one])).trans
              (sq_le_self (Outer.outcome_pos o) (Outer.outcome_le_one o))
      _ = Outer.total := Outer.sum_eq_total
      _ ≤ 1 := Outer.total_le_one
  have hop_sum :
      (∑ ir : α × γ, ∑ o : β,
          S.L (Outer.outcome o * Inner.outcome ir.1 * Outer.outcome o) *
            S.R (Right.outcome ir.2)) =
        S.L (∑ o : β, Outer.outcome o * Inner.total * Outer.outcome o) *
          S.R Right.total := by
    rw [Fintype.sum_prod_type]
    simp only [← Inner.sum_eq_total, ← Right.sum_eq_total, Finset.mul_sum, Finset.sum_mul,
      map_sum]
    exact Finset.sum_comm.trans (Finset.sum_congr rfl fun r _ => Finset.sum_comm)
  calc
    (∑ ir : α × γ, ∑ o : β,
        S.ev
          (S.L (Outer.outcome o * Inner.outcome ir.1 * Outer.outcome o) *
            S.R (Right.outcome ir.2)))
      = S.ev (∑ ir : α × γ, ∑ o : β,
          S.L (Outer.outcome o * Inner.outcome ir.1 * Outer.outcome o) *
            S.R (Right.outcome ir.2)) := by
          simp only [S.ev_sum]
    _ = S.ev (S.L (∑ o : β, Outer.outcome o * Inner.total * Outer.outcome o) *
          S.R Right.total) := by rw [hop_sum]
    _ ≤ S.ev 1 :=
          S.ev_mono _ _ <|
            S.opTensor_le_one hsandwichTotal_nonneg hsandwichTotal_le_one Right.total_le_one
    _ = 1 := S.ev_one_of_isNormalized

end SymModel

end MIPRE.LIDT.Co

end
