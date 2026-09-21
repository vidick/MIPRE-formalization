/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.ValueStability

/-! # Transporting a strategy through local isometries

Conjugating a PVM by a rectangular isometry normalizes it only on the
isometry's image. Assigning the image complement to a fixed outcome gives
an actual projective measurement on the whole target space. On the embedded
state this completion preserves all probabilities and every intertwining
identity exactly, including after an outcome map.
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false

section Local
variable {H R A : Type*} [Fintype H] [DecidableEq H]
  [Fintype R] [DecidableEq R] [Fintype A]

/-- Conjugation into the image of a rectangular linear map. -/
def isometricImage (V : Matrix R H ℂ) (M : Matrix H H ℂ) : Matrix R R ℂ :=
  V * M * Vᴴ

theorem isometricImage_mul (V : Matrix R H ℂ) (hV : Vᴴ * V = 1)
    (M N : Matrix H H ℂ) :
    isometricImage V M * isometricImage V N = isometricImage V (M * N) := by
  unfold isometricImage
  calc
    _ = V * M * (Vᴴ * V) * N * Vᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hV]; simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem isometricImage_conjTranspose (V : Matrix R H ℂ) (M : Matrix H H ℂ) :
    (isometricImage V M)ᴴ = isometricImage V Mᴴ := by
  simp only [isometricImage, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- The orthogonal complement of the image of an isometry. -/
def isometricComplement (V : Matrix R H ℂ) : Matrix R R ℂ :=
  1 - isometricImage V 1

theorem isometricComplement_conjTranspose (V : Matrix R H ℂ) :
    (isometricComplement V)ᴴ = isometricComplement V := by
  rw [isometricComplement, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    isometricImage_conjTranspose, Matrix.conjTranspose_one]

theorem isometricComplement_mul_image (V : Matrix R H ℂ) (hV : Vᴴ * V = 1)
    (M : Matrix H H ℂ) : isometricComplement V * isometricImage V M = 0 := by
  rw [isometricComplement, Matrix.sub_mul, Matrix.one_mul,
    isometricImage_mul V hV, Matrix.one_mul, sub_self]

theorem isometricImage_mul_complement (V : Matrix R H ℂ) (hV : Vᴴ * V = 1)
    (M : Matrix H H ℂ) : isometricImage V M * isometricComplement V = 0 := by
  rw [isometricComplement, Matrix.mul_sub, Matrix.mul_one,
    isometricImage_mul V hV, Matrix.mul_one, sub_self]

theorem isometricComplement_idem (V : Matrix R H ℂ) (hV : Vᴴ * V = 1) :
    isometricComplement V * isometricComplement V = isometricComplement V := by
  unfold isometricComplement
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
    isometricImage_mul V hV, Matrix.one_mul, sub_self, sub_zero]

theorem isometricComplement_mul (V : Matrix R H ℂ) (hV : Vᴴ * V = 1) :
    isometricComplement V * V = 0 := by
  rw [isometricComplement, Matrix.sub_mul, Matrix.one_mul, isometricImage,
    Matrix.mul_one, Matrix.mul_assoc, hV, Matrix.mul_one, sub_self]

/-- Put the image complement at one fixed outcome. -/
def isometricEffect (V : Matrix R H ℂ) (a₀ : A)
    (M : A → Matrix H H ℂ) (a : A) : Matrix R R ℂ :=
  isometricImage V (M a) + if a = a₀ then isometricComplement V else 0

/-- Completion of the conjugated effects is a PVM on the whole target. -/
theorem isometricEffect_isPVM (V : Matrix R H ℂ) (hV : Vᴴ * V = 1)
    (a₀ : A) {M : A → Matrix H H ℂ} (hM : IsPVM M) :
    IsPVM (isometricEffect V a₀ M) where
  isSelfAdjoint a := by
    unfold isometricEffect
    split_ifs <;> simp only [Matrix.conjTranspose_add, isometricImage_conjTranspose,
      hM.isSelfAdjoint, isometricComplement_conjTranspose, Matrix.conjTranspose_zero]
  idem a := by
    unfold isometricEffect
    split_ifs
    · rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
        isometricImage_mul V hV, hM.idem, isometricImage_mul_complement V hV,
        isometricComplement_mul_image V hV, isometricComplement_idem V hV,
        add_zero, zero_add]
    · rw [add_zero, isometricImage_mul V hV, hM.idem]
  sum_eq_one := by
    simp only [isometricEffect, sum_add_distrib, sum_ite_eq', mem_univ, if_true]
    rw [show (∑ a, isometricImage V (M a)) = isometricImage V (∑ a, M a) by
      simp only [isometricImage, Matrix.mul_sum, Matrix.sum_mul], hM.sum_eq_one]
    unfold isometricComplement
    abel

/-- The completed measurement intertwines with the original one. -/
theorem isometricEffect_intertwine (V : Matrix R H ℂ) (hV : Vᴴ * V = 1)
    (a₀ : A) (M : A → Matrix H H ℂ) (a : A) :
    isometricEffect V a₀ M a * V = V * M a := by
  unfold isometricEffect
  rw [Matrix.add_mul]
  have hi : isometricImage V (M a) * V = V * M a := by
    rw [isometricImage, Matrix.mul_assoc, hV, Matrix.mul_one]
  rw [hi]
  split_ifs <;> simp only [isometricComplement_mul V hV, Matrix.zero_mul, add_zero]

/-- Compression of the completed effect is precisely the source effect. -/
theorem isometricEffect_compress (V : Matrix R H ℂ) (hV : Vᴴ * V = 1)
    (a₀ : A) (M : A → Matrix H H ℂ) (a : A) :
    Vᴴ * (isometricEffect V a₀ M a * V) = M a := by
  rw [isometricEffect_intertwine V hV, ← Matrix.mul_assoc, hV, Matrix.one_mul]

/-- The concrete projective POVM on the isometry's target. -/
def isometricPOVM (V : Matrix R H ℂ) (hV : Vᴴ * V = 1)
    (a₀ : A) (M : POVM A H) (hM : IsPVM (fun a => (M.mats a).val)) : POVM A R :=
  (isometricEffect_isPVM V hV a₀ hM).toPOVM

theorem isometricPOVM_mats (V : Matrix R H ℂ) (hV : Vᴴ * V = 1)
    (a₀ : A) (M : POVM A H) (hM : IsPVM (fun a => (M.mats a).val)) (a : A) :
    ((isometricPOVM V hV a₀ M hM).mats a).val =
      isometricEffect V a₀ (fun a => (M.mats a).val) a := rfl

theorem isometricPOVM_isPVM (V : Matrix R H ℂ) (hV : Vᴴ * V = 1)
    (a₀ : A) (M : POVM A H) (hM : IsPVM (fun a => (M.mats a).val)) :
    IsPVM (fun a => ((isometricPOVM V hV a₀ M hM).mats a).val) :=
  isometricEffect_isPVM V hV a₀ hM

/-- Relabelled effects retain exact intertwining, including labels that
collect malformed source answers. -/
theorem isometricPOVM_map_intertwine {B : Type*} [Fintype B]
    (V : Matrix R H ℂ) (hV : Vᴴ * V = 1) (a₀ : A)
    (M : POVM A H) (hM : IsPVM (fun a => (M.mats a).val)) (f : A → B) (b : B) :
    (((isometricPOVM V hV a₀ M hM).map f).mats b).val * V =
      V * ((M.map f).mats b).val := by
  rw [POVM.map_mats, POVM.map_mats, Matrix.sum_mul, Matrix.mul_sum]
  simp only [isometricPOVM_mats]
  exact sum_congr rfl fun a _ =>
    isometricEffect_intertwine V hV a₀ (fun a => (M.mats a).val) a

end Local

section Bipartite
variable {H K R S A B X Y : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
  [Fintype A] [Fintype B] [Fintype X] [Fintype Y]

/-- Tensor both local isometries into the actual state vector. -/
def isometricState (V : Matrix R H ℂ) (W : Matrix S K ℂ) (ψ : H × K → ℂ) :
    R × S → ℂ := (V ⊗ₖ W) *ᵥ ψ

theorem isometricTensor_isometry (V : Matrix R H ℂ) (W : Matrix S K ℂ)
    (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1) :
    (V ⊗ₖ W)ᴴ * (V ⊗ₖ W) = 1 := by
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    hV, hW, Matrix.one_kronecker_one]

theorem isometricState_norm (V : Matrix R H ℂ) (W : Matrix S K ℂ)
    (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1) (ψ : H × K → ℂ) :
    ‖evec (isometricState V W ψ)‖ = ‖evec ψ‖ :=
  norm_evec_mulVec_eq (isometricTensor_isometry V W hV hW) ψ

theorem isometricState_unit (V : Matrix R H ℂ) (W : Matrix S K ℂ)
    (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1)
    (ψ : H × K → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) :
    star (isometricState V W ψ) ⬝ᵥ isometricState V W ψ = 1 := by
  rw [isometricState, star_mulVec_dotProduct,
    isometricTensor_isometry V W hV hW, Matrix.one_mulVec, hψ]

/-- Local completion leaves every individual Born probability unchanged. -/
theorem bornProb_isometricState (V : Matrix R H ℂ) (W : Matrix S K ℂ)
    (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1) (ψ : H × K → ℂ)
    (a₀ : A) (b₀ : B) (M : A → Matrix H H ℂ) (N : B → Matrix K K ℂ)
    (a : A) (b : B) :
    bornProb (isometricState V W ψ)
      (isometricEffect V a₀ M a) (isometricEffect W b₀ N b) =
        bornProb ψ (M a) (N b) := by
  rw [bornProb, bornProb, isometricState, dotProduct_mulVec_conj]
  congr 2
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, isometricEffect_compress V hV,
    isometricEffect_compress W hW]

/-- Every game value is exactly preserved by the concrete transported PVMs. -/
theorem povmValue_isometricState (G : Game X Y A B)
    (V : Matrix R H ℂ) (W : Matrix S K ℂ) (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1)
    (ψ : H × K → ℂ) (a₀ : A) (b₀ : B)
    (MA : X → POVM A H) (MB : Y → POVM B K)
    (hMA : ∀ x, IsPVM (fun a => ((MA x).mats a).val))
    (hMB : ∀ y, IsPVM (fun b => ((MB y).mats b).val)) :
    povmValue G (isometricState V W ψ)
      (fun x => isometricPOVM V hV a₀ (MA x) (hMA x))
      (fun y => isometricPOVM W hW b₀ (MB y) (hMB y)) = povmValue G ψ MA MB := by
  unfold povmValue condWin
  simp only [isometricPOVM_mats, bornProb_isometricState V W hV hW]

/-- The exact rectangular deviation vector on Alice's side, against any
target operator. This is the local-isometry form of a Pauli estimate. -/
theorem isometricState_alice_deviation (V : Matrix R H ℂ) (W : Matrix S K ℂ)
    (hV : Vᴴ * V = 1) (ψ : H × K → ℂ)
    (a₀ : A) (M : A → Matrix H H ℂ) (a : A) (T : Matrix R R ℂ) :
    aOp (isometricEffect V a₀ M a - T) *ᵥ isometricState V W ψ =
      ((V * M a - T * V) ⊗ₖ W) *ᵥ ψ := by
  rw [isometricState, Matrix.mulVec_mulVec, aOp, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.sub_mul, isometricEffect_intertwine V hV]

/-- The corresponding exact rectangular deviation vector on Bob's side. -/
theorem isometricState_bob_deviation (V : Matrix R H ℂ) (W : Matrix S K ℂ)
    (hW : Wᴴ * W = 1) (ψ : H × K → ℂ)
    (b₀ : B) (N : B → Matrix K K ℂ) (b : B) (T : Matrix S S ℂ) :
    bOp (isometricEffect W b₀ N b - T) *ᵥ isometricState V W ψ =
      (V ⊗ₖ (W * N b - T * W)) *ᵥ ψ := by
  rw [isometricState, Matrix.mulVec_mulVec, bOp, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.sub_mul, isometricEffect_intertwine W hW]

/-- Alice's same intertwining identity after any answer projection. -/
theorem isometricState_map_alice_deviation {C : Type*} [Fintype C]
    (V : Matrix R H ℂ) (W : Matrix S K ℂ) (hV : Vᴴ * V = 1)
    (ψ : H × K → ℂ) (a₀ : A) (M : POVM A H)
    (hM : IsPVM (fun a => (M.mats a).val)) (f : A → C) (c : C)
    (T : Matrix R R ℂ) :
    aOp ((((isometricPOVM V hV a₀ M hM).map f).mats c).val - T) *ᵥ
        isometricState V W ψ =
      ((V * ((M.map f).mats c).val - T * V) ⊗ₖ W) *ᵥ ψ := by
  rw [isometricState, Matrix.mulVec_mulVec, aOp, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.sub_mul, isometricPOVM_map_intertwine V hV]

/-- Bob's same intertwining identity after any answer projection. -/
theorem isometricState_map_bob_deviation {C : Type*} [Fintype C]
    (V : Matrix R H ℂ) (W : Matrix S K ℂ) (hW : Wᴴ * W = 1)
    (ψ : H × K → ℂ) (b₀ : B) (N : POVM B K)
    (hN : IsPVM (fun b => (N.mats b).val)) (f : B → C) (c : C)
    (T : Matrix S S ℂ) :
    bOp ((((isometricPOVM W hW b₀ N hN).map f).mats c).val - T) *ᵥ
        isometricState V W ψ =
      (V ⊗ₖ (W * ((N.map f).mats c).val - T * W)) *ᵥ ψ := by
  rw [isometricState, Matrix.mulVec_mulVec, bOp, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.sub_mul, isometricPOVM_map_intertwine W hW]

end Bipartite
end MIPRE.Introspection
end
