/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.LCS.MagicSquare.Game
import MIPRE.LCS.Strategy.ObservableToProjector
import MIPRE.Foundations.Introspection.Measurements

/-! # The Magic Square extension of an arbitrary anticommuting pair

This is the concrete operator construction needed by the honest Pauli test.
It adds one qubit and retains the original observables at cells zero and four.
The row and column identities use the actual Magic Square layout and parity.
No game completeness statement is assumed.
-/

noncomputable section

namespace MIPRE.Introspection.HonestMagicSquare

open Matrix Finset LCS LCS.MagicSquare
open scoped Kronecker

/-- The actual Magic Square cell, with its fixed nine-cell carrier exposed. -/
def cellIndex (c : Fin layout.r) (j : Fin 3) : Fin 9 := cell c j

variable {I : Type*} [Fintype I] [DecidableEq I]

private theorem observable_kronecker {J : Type*} [Fintype J] [DecidableEq J]
    {A : Matrix I I ℂ} {B : Matrix J J ℂ}
    (hA : IsObservable A) (hB : IsObservable B) : IsObservable (A ⊗ₖ B) where
  involutive := by rw [← mul_kronecker_mul, hA.involutive, hB.involutive, one_kronecker_one]
  self_adjoint := by
    change (A ⊗ₖ B)ᴴ = A ⊗ₖ B
    rw [conjTranspose_kronecker]
    exact congrArg₂ (fun A B => A ⊗ₖ B) hA.self_adjoint hB.self_adjoint

private theorem observable_one : IsObservable (1 : Matrix I I ℂ) :=
  ⟨one_mul _, star_one _⟩

private theorem observable_mul {A B : Matrix I I ℂ}
    (hA : IsObservable A) (hB : IsObservable B) (hc : Commute A B) :
    IsObservable (A * B) where
  involutive := by
    calc A * B * (A * B) = A * (B * A) * B := by simp only [mul_assoc]
      _ = A * (A * B) * B := by rw [hc.eq]
      _ = (A * A) * (B * B) := by simp only [mul_assoc]
      _ = 1 := by rw [hA.involutive, hB.involutive, one_mul]
  self_adjoint := by rw [star_mul, hA.self_adjoint, hB.self_adjoint, hc.eq]

omit [DecidableEq I] in
private theorem tensor_commute {A B : Matrix I I ℂ}
    {C D : Matrix (Fin 2) (Fin 2) ℂ} (hAB : Commute A B) (hCD : Commute C D) :
    Commute (A ⊗ₖ C) (B ⊗ₖ D) := by
  change (A ⊗ₖ C) * (B ⊗ₖ D) = (B ⊗ₖ D) * (A ⊗ₖ C)
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, hAB.eq, hCD.eq]

omit [DecidableEq I] in
private theorem tensor_anticommute {A B : Matrix I I ℂ}
    {C D : Matrix (Fin 2) (Fin 2) ℂ}
    (hAB : A * B = -(B * A)) (hCD : C * D = -(D * C)) :
    Commute (A ⊗ₖ C) (B ⊗ₖ D) := by
  change (A ⊗ₖ C) * (B ⊗ₖ D) = (B ⊗ₖ D) * (A ⊗ₖ C)
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, hAB, hCD]
  ext i j
  exact neg_mul_neg _ _

/-- The nine observables, on the original space tensor one additional qubit. -/
def grid (A B : Matrix I I ℂ) : Fin 9 → Matrix (I × Fin 2) (I × Fin 2) ℂ
  | 0 => A ⊗ₖ 1
  | 1 => 1 ⊗ₖ Pauli.X
  | 2 => A ⊗ₖ Pauli.X
  | 3 => 1 ⊗ₖ Pauli.Z
  | 4 => B ⊗ₖ 1
  | 5 => B ⊗ₖ Pauli.Z
  | 6 => A ⊗ₖ Pauli.Z
  | 7 => B ⊗ₖ Pauli.X
  | 8 => (A * B) ⊗ₖ (Pauli.Z * Pauli.X)

@[simp] theorem grid_zero (A B : Matrix I I ℂ) : grid A B 0 = A ⊗ₖ 1 := rfl
@[simp] theorem grid_four (A B : Matrix I I ℂ) : grid A B 4 = B ⊗ₖ 1 := rfl

private theorem ZX_anticomm : Pauli.Z * Pauli.X = -(Pauli.X * Pauli.Z) := by
  rw [Pauli.X_anticomm_Z]
  simp

theorem grid_isObservable {A B : Matrix I I ℂ}
    (hA : IsObservable A) (hB : IsObservable B) (hAB : A * B = -(B * A))
    (j : Fin 9) : IsObservable (grid A B j) := by
  fin_cases j <;> simp only [grid]
  · exact observable_kronecker hA observable_one
  · exact observable_kronecker observable_one Pauli.isObservable_X
  · exact observable_kronecker hA Pauli.isObservable_X
  · exact observable_kronecker observable_one Pauli.isObservable_Z
  · exact observable_kronecker hB observable_one
  · exact observable_kronecker hB Pauli.isObservable_Z
  · exact observable_kronecker hA Pauli.isObservable_Z
  · exact observable_kronecker hB Pauli.isObservable_X
  · rw [mul_kronecker_mul]
    exact observable_mul (observable_kronecker hA Pauli.isObservable_Z)
      (observable_kronecker hB Pauli.isObservable_X) (tensor_anticommute hAB ZX_anticomm)

/-- The first two observables in each actual row or column commute. -/
theorem first_second_commute {A B : Matrix I I ℂ}
    (hAB : A * B = -(B * A)) (c : Fin layout.r) :
    Commute (grid A B (cellIndex c 0)) (grid A B (cellIndex c 1)) := by
  fin_cases c <;> simp only [cellIndex, cell, cellNat, grid]
  · exact tensor_commute (Commute.one_right _) (Commute.one_left _)
  · exact tensor_commute (Commute.one_left _) (Commute.one_right _)
  · exact tensor_anticommute hAB ZX_anticomm
  · exact tensor_commute (Commute.one_right _) (Commute.one_left _)
  · exact tensor_commute (Commute.one_left _) (Commute.one_right _)
  · exact tensor_anticommute hAB Pauli.X_anticomm_Z

/-- The last cell is the signed product of the first two cells. -/
theorem third_eq (A B : Matrix I I ℂ) (c : Fin layout.r) :
    grid A B (cellIndex c 2) = ((-1 : ℂ) ^ (game.b c).val) •
      (grid A B (cellIndex c 0) * grid A B (cellIndex c 1)) := by
  fin_cases c <;> simp only [cellIndex, cell, cellNat, grid, game]
  all_goals norm_num
  all_goals rw [← mul_kronecker_mul]
  all_goals try simp only [mul_one, one_mul]
  rw [ZX_anticomm]
  ext i j
  exact mul_neg _ _

theorem cells_commute {A B : Matrix I I ℂ}
    (hAB : A * B = -(B * A)) (c : Fin layout.r) (s t : Fin 3) :
    Commute (grid A B (cellIndex c s)) (grid A B (cellIndex c t)) := by
  have h := first_second_commute hAB c
  have h02 : Commute (grid A B (cellIndex c 0)) (grid A B (cellIndex c 2)) := by
    rw [third_eq]
    exact ((Commute.refl _).mul_right h).smul_right _
  have h12 : Commute (grid A B (cellIndex c 1)) (grid A B (cellIndex c 2)) := by
    rw [third_eq]
    exact (h.symm.mul_right (Commute.refl _)).smul_right _
  fin_cases s <;> fin_cases t
  · exact Commute.refl _
  · exact h
  · exact h02
  · exact h.symm
  · exact Commute.refl _
  · exact h12
  · exact h02.symm
  · exact h12.symm
  · exact Commute.refl _

theorem sameEquation_commute {A B : Matrix I I ℂ}
    (hAB : A * B = -(B * A)) (c : Fin layout.r) :
    Pairwise (fun j k : layout.V c => Commute (grid A B j.1) (grid A B k.1)) := by
  intro j k _
  simpa only [cellIndex, cell_cellIdx j.2, cell_cellIdx k.2] using
    cells_commute hAB c (cellIdx c j.1) (cellIdx c k.1)

/-- Every row has even parity and the last column has odd parity. -/
theorem row_product {A B : Matrix I I ℂ}
    (hA : IsObservable A) (hB : IsObservable B) (hAB : A * B = -(B * A))
    (c : Fin layout.r) :
    grid A B (cellIndex c 0) * grid A B (cellIndex c 1) * grid A B (cellIndex c 2) =
      ((-1 : ℂ) ^ (game.b c).val) • (1 : Matrix (I × Fin 2) (I × Fin 2) ℂ) := by
  rw [third_eq, mul_smul_comm]
  congr 1
  exact (observable_mul (grid_isObservable hA hB hAB _) (grid_isObservable hA hB hAB _)
    (first_second_commute hAB c)).involutive

/-- The resulting observable strategy; its input pair occupies the required cells. -/
def observableStrategy {A B : Matrix I I ℂ}
    (hA : IsObservable A) (hB : IsObservable B) (hAB : A * B = -(B * A)) :
    BipartiteObservableStrategy (I × Fin 2) layout where
  obs := grid A B
  isObservable := grid_isObservable hA hB hAB
  sameEquation_comm := sameEquation_commute hAB

/-- The binary measurement of an arbitrary cell. -/
def variableOp (A B : Matrix I I ℂ) (j : Fin 9) (b : ZMod 2) :
    Matrix (I × Fin 2) (I × Fin 2) ℂ := observableToProjector (grid A B j) b

theorem variableOp_isPVM {A B : Matrix I I ℂ}
    (hA : IsObservable A) (hB : IsObservable B) (hAB : A * B = -(B * A)) (j : Fin 9) :
    IsPVM (variableOp A B j) := by
  have h := isMeasurementSystem_observableToProjector _ (grid_isObservable hA hB hAB j)
  exact ⟨h.self_adjoint, h.idempotent, h.sum_one⟩

/-- The joint measurement of the three cells of a row or column. -/
def constraintOp (A B : Matrix I I ℂ) (c : Fin layout.r) (a : Fin 3 → ZMod 2) :
    Matrix (I × Fin 2) (I × Fin 2) ℂ :=
  variableOp A B (cellIndex c 0) (a 0) * variableOp A B (cellIndex c 1) (a 1) *
    variableOp A B (cellIndex c 2) (a 2)

private def tripleEquiv : (Fin 3 → ZMod 2) ≃ (ZMod 2 × ZMod 2) × ZMod 2 where
  toFun a := ((a 0, a 1), a 2)
  invFun a := ![a.1.1, a.1.2, a.2]
  left_inv a := by funext j; fin_cases j <;> rfl
  right_inv a := by rcases a with ⟨⟨a, b⟩, c⟩; rfl

theorem constraintOp_isPVM {A B : Matrix I I ℂ}
    (hA : IsObservable A) (hB : IsObservable B) (hAB : A * B = -(B * A))
    (c : Fin layout.r) : IsPVM (constraintOp A B c) := by
  have hc (s t : Fin 3) (a b : ZMod 2) :
      Commute (variableOp A B (cellIndex c s) a) (variableOp A B (cellIndex c t) b) :=
    commute_observableToProjector (cells_commute hAB c s t) a b
  have h01 := joint_measurement_isPVM _ _ (variableOp_isPVM hA hB hAB (cellIndex c 0))
    (variableOp_isPVM hA hB hAB (cellIndex c 1)) (hc 0 1)
  have h012 := joint_measurement_isPVM _ _ h01 (variableOp_isPVM hA hB hAB (cellIndex c 2))
    (fun a b => (hc 0 2 a.1 b).mul_left (hc 1 2 a.2 b))
  refine ⟨fun a => h012.isSelfAdjoint (tripleEquiv a),
    fun a => h012.idem (tripleEquiv a), ?_⟩
  calc
    _ = ∑ a : (ZMod 2 × ZMod 2) × ZMod 2,
        (variableOp A B (cellIndex c 0) a.1.1 * variableOp A B (cellIndex c 1) a.1.2) *
          variableOp A B (cellIndex c 2) a.2 :=
      Fintype.sum_equiv tripleEquiv _ _ (fun _ => rfl)
    _ = 1 := h012.sum_eq_one

private theorem observable_commute_projector {A B : Matrix I I ℂ} (h : Commute A B)
    (b : ZMod 2) : Commute A (observableToProjector B b) := by
  unfold observableToProjector
  exact ((Commute.one_right _).add_right (h.smul_right _)).smul_right _

theorem variable_constraint_commute {A B : Matrix I I ℂ}
    (hAB : A * B = -(B * A)) (c : Fin layout.r) (j : Fin 3)
    (a : Fin 3 → ZMod 2) (b : ZMod 2) :
    Commute (variableOp A B (cellIndex c j) b) (constraintOp A B c a) := by
  unfold constraintOp
  apply Commute.mul_right
  · exact (commute_observableToProjector (cells_commute hAB c j 0) b (a 0)).mul_right
      (commute_observableToProjector (cells_commute hAB c j 1) b (a 1))
  · exact commute_observableToProjector (cells_commute hAB c j 2) b (a 2)

set_option backward.isDefEq.respectTransparency false in
theorem constraint_eigen {A B : Matrix I I ℂ}
    (hA : IsObservable A) (hB : IsObservable B) (hAB : A * B = -(B * A))
    (c : Fin layout.r) (a : Fin 3 → ZMod 2) (j : Fin 3) :
    grid A B (cellIndex c j) * constraintOp A B c a =
      ((-1 : ℂ) ^ (a j).val) • constraintOp A B c a := by
  have he (j : Fin 3) : grid A B (cellIndex c j) * variableOp A B (cellIndex c j) (a j) =
      ((-1 : ℂ) ^ (a j).val) • variableOp A B (cellIndex c j) (a j) :=
    observable_mul_observableToProjector
      (grid A B (cellIndex c j)) (grid_isObservable hA hB hAB _) (a j)
  have hc (j k : Fin 3) : Commute (grid A B (cellIndex c j))
      (variableOp A B (cellIndex c k) (a k)) :=
    observable_commute_projector (cells_commute hAB c j k) (a k)
  change _ * (_ * _ * _) = _ • (_ * _ * _)
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hj with rfl | rfl | rfl
  · rw [← mul_assoc, ← mul_assoc, he 0, smul_mul_assoc, smul_mul_assoc]
  · calc
      _ = variableOp A B (cellIndex c 0) (a 0) *
          (grid A B (cellIndex c 1) * variableOp A B (cellIndex c 1) (a 1)) *
          variableOp A B (cellIndex c 2) (a 2) := by
        rw [← mul_assoc, ← mul_assoc, (hc 1 0).eq]
        simp only [mul_assoc]
      _ = _ := by rw [he 1, mul_smul_comm, smul_mul_assoc]
  · rw [← mul_assoc, (hc 2 0 |>.mul_right (hc 2 1)).eq, mul_assoc, he 2, mul_smul_comm]

private theorem sign_injective : Function.Injective (fun b : ZMod 2 => (-1 : ℂ) ^ b.val) := by
  intro x y h
  rcases zmod_two_eq_zero_or_one x with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one y with rfl | rfl <;>
      simp_all [ZMod.val_zero, zmod_two_val_one]
  all_goals norm_num at h

/-- A parity-violating constraint answer has zero effect. -/
theorem constraint_wrong_parity {A B : Matrix I I ℂ}
    (hA : IsObservable A) (hB : IsObservable B) (hAB : A * B = -(B * A))
    (c : Fin layout.r) (a : Fin 3 → ZMod 2)
    (ha : a 0 + a 1 + a 2 ≠ game.b c) : constraintOp A B c a = 0 := by
  have h : ((-1 : ℂ) ^ (game.b c).val) • constraintOp A B c a =
      ((-1 : ℂ) ^ (a 0 + a 1 + a 2).val) • constraintOp A B c a := by
    calc
      _ = (grid A B (cellIndex c 0) * grid A B (cellIndex c 1) * grid A B (cellIndex c 2)) *
          constraintOp A B c a := by rw [row_product hA hB hAB, smul_mul_assoc, one_mul]
      _ = _ := by
        simp only [mul_assoc, constraint_eigen hA hB hAB, mul_smul_comm, smul_smul]
        congr 1
        rw [← sign_mul, ← sign_mul]
        ring
  have hs : ((-1 : ℂ) ^ (game.b c).val) - ((-1 : ℂ) ^ (a 0 + a 1 + a 2).val) ≠ 0 := by
    exact sub_ne_zero.mpr (fun hs => ha (sign_injective hs.symm))
  have hz : (((-1 : ℂ) ^ (game.b c).val) - ((-1 : ℂ) ^ (a 0 + a 1 + a 2).val)) •
      constraintOp A B c a = 0 := by rw [sub_smul, h, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left hs

set_option backward.isDefEq.respectTransparency false in
/-- A disagreement on an incident cell has zero joint effect. -/
theorem constraint_disagreement {A B : Matrix I I ℂ}
    (hA : IsObservable A) (hB : IsObservable B) (hAB : A * B = -(B * A))
    (c : Fin layout.r) (a : Fin 3 → ZMod 2) (j : Fin 3) (b : ZMod 2)
    (hab : a j ≠ b) : constraintOp A B c a * variableOp A B (cellIndex c j) b = 0 := by
  have horth := (variableOp_isPVM hA hB hAB (cellIndex c j)).orthogonal hab
  have hc (s t : Fin 3) (u v : ZMod 2) :
      Commute (variableOp A B (cellIndex c s) u) (variableOp A B (cellIndex c t) v) :=
    commute_observableToProjector (cells_commute hAB c s t) u v
  unfold constraintOp
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hj with rfl | rfl | rfl
  · calc
      _ = variableOp A B (cellIndex c 0) (a 0) *
          (variableOp A B (cellIndex c 1) (a 1) *
            (variableOp A B (cellIndex c 2) (a 2) * variableOp A B (cellIndex c 0) b)) := by
        simp only [mul_assoc]
      _ = variableOp A B (cellIndex c 0) (a 0) *
          ((variableOp A B (cellIndex c 1) (a 1) * variableOp A B (cellIndex c 0) b) *
            variableOp A B (cellIndex c 2) (a 2)) := by
        rw [(hc 2 0 (a 2) b).eq, mul_assoc]
      _ = (variableOp A B (cellIndex c 0) (a 0) * variableOp A B (cellIndex c 0) b) *
          variableOp A B (cellIndex c 1) (a 1) * variableOp A B (cellIndex c 2) (a 2) := by
        rw [(hc 1 0 (a 1) b).eq]
        simp only [mul_assoc]
      _ = 0 := by rw [horth, zero_mul, zero_mul]
  · calc
      _ = variableOp A B (cellIndex c 0) (a 0) *
          (variableOp A B (cellIndex c 1) (a 1) *
            (variableOp A B (cellIndex c 2) (a 2) * variableOp A B (cellIndex c 1) b)) := by
        simp only [mul_assoc]
      _ = variableOp A B (cellIndex c 0) (a 0) *
          ((variableOp A B (cellIndex c 1) (a 1) * variableOp A B (cellIndex c 1) b) *
            variableOp A B (cellIndex c 2) (a 2)) := by
        rw [(hc 2 1 (a 2) b).eq, mul_assoc]
      _ = 0 := by rw [horth, zero_mul, mul_zero]
  · rw [mul_assoc, horth, mul_zero]

/-- Both parts of the actual Magic Square incidence check are enforced. -/
theorem constraint_reject_zero {A B : Matrix I I ℂ}
    (hA : IsObservable A) (hB : IsObservable B) (hAB : A * B = -(B * A))
    (c : Fin layout.r) (a : Fin 3 → ZMod 2) (j : Fin 3) (b : ZMod 2)
    (hr : ¬ (a 0 + a 1 + a 2 = game.b c ∧ a j = b)) :
    constraintOp A B c a * variableOp A B (cellIndex c j) b = 0 := by
  by_cases hp : a 0 + a 1 + a 2 = game.b c
  · exact constraint_disagreement hA hB hAB c a j b (fun h => hr ⟨hp, h⟩)
  · rw [constraint_wrong_parity hA hB hAB c a hp, zero_mul]

/-- The first distinguished cell retains the original binary measurement. -/
theorem variableOp_zero (A B : Matrix I I ℂ) (b : ZMod 2) :
    variableOp A B 0 b = observableToProjector A b ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp [variableOp, grid, observableToProjector, smul_kronecker, add_kronecker]

/-- The second distinguished cell retains the original binary measurement. -/
theorem variableOp_four (A B : Matrix I I ℂ) (b : ZMod 2) :
    variableOp A B 4 b = observableToProjector B b ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp [variableOp, grid, observableToProjector, smul_kronecker, add_kronecker]

private theorem projector_measurement (P : ZMod 2 → Matrix I I ℂ)
    (hP : IsMeasurementSystem P) (b : ZMod 2) :
    observableToProjector (observableOfMeasurementSystem P) b = P b := by
  rw [binary_measurement_eq_projector P hP b]
  rcases zmod_two_eq_zero_or_one b with rfl | rfl <;>
    simp [observableToProjector, observableSign]

theorem variableOp_embeds_first (P Q : ZMod 2 → Matrix I I ℂ)
    (hP : IsMeasurementSystem P) (b : ZMod 2) :
    variableOp (observableOfMeasurementSystem P) (observableOfMeasurementSystem Q) 0 b =
      P b ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [variableOp_zero, projector_measurement P hP]

theorem variableOp_embeds_second (P Q : ZMod 2 → Matrix I I ℂ)
    (hQ : IsMeasurementSystem Q) (b : ZMod 2) :
    variableOp (observableOfMeasurementSystem P) (observableOfMeasurementSystem Q) 4 b =
      Q b ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [variableOp_four, projector_measurement Q hQ]

private theorem transpose_X : Pauli.Xᵀ = Pauli.X := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

private theorem transpose_Z : Pauli.Zᵀ = Pauli.Z := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- Symmetric input observables give symmetric operators throughout the extension. -/
theorem grid_transpose {A B : Matrix I I ℂ}
    (hAB : A * B = -(B * A)) (hA : Aᵀ = A) (hB : Bᵀ = B) (j : Fin 9) :
    (grid A B j)ᵀ = grid A B j := by
  fin_cases j <;> simp only [grid, ← kroneckerMap_transpose, transpose_one,
    transpose_mul, hA, hB, transpose_X, transpose_Z]
  rw [hAB, ZX_anticomm]
  ext i j
  exact (neg_mul_neg _ _).symm

theorem variableOp_transpose {A B : Matrix I I ℂ}
    (hAB : A * B = -(B * A)) (hA : Aᵀ = A) (hB : Bᵀ = B)
    (j : Fin 9) (b : ZMod 2) : (variableOp A B j b)ᵀ = variableOp A B j b := by
  simp [variableOp, observableToProjector, transpose_smul, grid_transpose hAB hA hB]

theorem constraintOp_transpose {A B : Matrix I I ℂ}
    (hAB : A * B = -(B * A)) (hA : Aᵀ = A) (hB : Bᵀ = B)
    (c : Fin layout.r) (a : Fin 3 → ZMod 2) :
    (constraintOp A B c a)ᵀ = constraintOp A B c a := by
  have hc (s t : Fin 3) : Commute (variableOp A B (cellIndex c s) (a s))
      (variableOp A B (cellIndex c t) (a t)) :=
    commute_observableToProjector (cells_commute hAB c s t) (a s) (a t)
  simp only [constraintOp, transpose_mul, variableOp_transpose hAB hA hB]
  rw [(hc 1 0).eq, ((hc 2 0).mul_right (hc 2 1)).eq]

end MIPRE.Introspection.HonestMagicSquare
