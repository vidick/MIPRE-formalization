/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.ComposedTwirl
import MIPRE.Foundations.Introspection.CommutatorParseval
import MIPRE.Foundations.Introspection.BlockPOVM
import MIPRE.Foundations.Introspection.EPR

/-! # Approximate Pauli mixing with explicit constants -/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Weyl Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {n : ℕ} {H K A : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] [Fintype A]

/-- The concrete `Z` dephasing is the uniform unitary twirl. -/
theorem dephaseZ_eq_unitaryTwirl
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) :
    dephaseZ M = unitaryTwirl (fun _ : Fin n → F => (Fintype.card (Fin n → F) : ℝ)⁻¹)
      (fun v => aOp (wZ v)) M := by
  simp only [dephaseZ, unitaryTwirl, amplify, ← Finset.smul_sum,
    aOp, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, wZ_conjTranspose,
    Complex.ofReal_inv, Complex.ofReal_natCast]

/-- The concrete kernel averaging is the uniform `X` twirl. -/
theorem averageX_eq_unitaryTwirl (S : Submodule F (Fin n → F))
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) :
    averageX S M = unitaryTwirl (fun _ : S => (Fintype.card S : ℝ)⁻¹)
      (fun v => aOp (wX v.1)) M := by
  simp only [averageX, unitaryTwirl, amplify, ← Finset.smul_sum,
    aOp, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, wX_conjTranspose,
    Complex.ofReal_inv, Complex.ofReal_natCast]

/-- Twirling by all `Z` operators and kernel `X` operators costs four times each commutator error. -/
theorem pauli_twirl_dist_le (L : (Fin n → F) →ₗ[F] (Fin n → F))
    (ξ : H × K → ℂ) (M : POVM A ((Fin n → F) × H)) :
    (∑ a, stateSqNorm (eprWithAux ξ)
      (averageX L.ker (dephaseZ (M.mats a).val) - (M.mats a).val)) ≤
      4 * ((Fintype.card (Fin n → F) : ℝ)⁻¹ * ∑ v : Fin n → F, ∑ a,
        stateSqNorm (eprWithAux ξ) ((M.mats a).val * aOp (wZ v) - aOp (wZ v) * (M.mats a).val)) +
      4 * ((Fintype.card L.ker : ℝ)⁻¹ * ∑ v : L.ker, ∑ a,
        stateSqNorm (eprWithAux ξ) ((M.mats a).val * aOp (wX v.1) - aOp (wX v.1) * (M.mats a).val)) := by
  have h := composed_twirl_dist_le
    (fun _ : Fin n → F => (Fintype.card (Fin n → F) : ℝ)⁻¹)
    (fun _ : L.ker => (Fintype.card L.ker : ℝ)⁻¹)
    (by intros; positivity) (by intros; positivity)
    (by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
    (by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)) (eprWithAux ξ) M
    (fun v => aOp (wZ v)) (fun v : L.ker => aOp (wX v.1))
    (fun v : L.ker => (aOp (wX v.1) : Matrix ((Fin n → F) × K) _ ℂ))
    (fun v => by rw [aOp_conjTranspose, wZ_conjTranspose])
    (fun v => by rw [← aOp_mul, wZ_mul_self, aOp_one])
    (fun v => by rw [aOp_conjTranspose, wX_conjTranspose])
    (fun v => by rw [← aOp_mul, wX_mul_self, aOp_one])
    (fun v => isometry_aOp (by rw [wX_conjTranspose, wX_mul_self]))
    (fun v => eprWithAux_wX_mirror ξ v.1)
  simpa only [← dephaseZ_eq_unitaryTwirl, ← averageX_eq_unitaryTwirl, ← Finset.mul_sum] using h

/-- Fine `Z` readouts transfer to the uniform full-register Pauli error. -/
theorem fine_commutator_parseval
    (ψ : ((Fin n → F) × H) × K → ℂ)
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) :
    (∑ y : Fin n → F, stateSqNorm ψ
      (M * aOp (synOf wZ (LinearMap.id : (Fin n → F) →ₗ[F] (Fin n → F)) y) -
        aOp (synOf wZ (LinearMap.id : (Fin n → F) →ₗ[F] (Fin n → F)) y) * M)) =
    (Fintype.card (Fin n → F) : ℝ)⁻¹ * ∑ v : Fin n → F,
      stateSqNorm ψ (M * aOp (wZ v) - aOp (wZ v) * M) := by
  have h := linear_measurement_commutator_parseval wZ LinearMap.id ψ M
  have htop : CL.perp (LinearMap.id : (Fin n → F) →ₗ[F] (Fin n → F)).ker = ⊤ := by
    ext x
    simp [CL.mem_perp]
  rw [htop] at h
  have hc : Fintype.card (⊤ : Submodule F (Fin n → F)) = Fintype.card (Fin n → F) :=
    Fintype.card_congr (Submodule.topEquiv : (⊤ : Submodule F (Fin n → F)) ≃ₗ[F] _).toEquiv
  rw [hc] at h
  refine h.trans (congrArg (fun r : ℝ => (Fintype.card (Fin n → F) : ℝ)⁻¹ * r) ?_)
  exact Fintype.sum_equiv (Submodule.topEquiv : (⊤ : Submodule F (Fin n → F)) ≃ₗ[F] _).toEquiv
    _ _ (fun _ => rfl)

/-- The `L`-perpendicular readout transfers to the uniform Pauli error on `ker L`. -/
theorem kernel_commutator_parseval
    (L : (Fin n → F) →ₗ[F] (Fin n → F)) (ψ : ((Fin n → F) × H) × K → ℂ)
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) :
    (∑ y : Fin n → F, stateSqNorm ψ
      (M * aOp (synOf wX (CL.lperp L) y) - aOp (synOf wX (CL.lperp L) y) * M)) =
    (Fintype.card L.ker : ℝ)⁻¹ * ∑ v : L.ker,
      stateSqNorm ψ (M * aOp (wX v.1) - aOp (wX v.1) * M) := by
  have h := linear_measurement_commutator_parseval wX (CL.lperp L) ψ M
  let e : CL.perp (CL.lperp L).ker ≃ L.ker :=
    { toFun v := ⟨v.1, by simpa only [CL.ker_lperp, CL.perp_perp] using v.2⟩
      invFun v := ⟨v.1, by simpa only [CL.ker_lperp, CL.perp_perp] using v.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  refine h.trans ?_
  rw [Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e _ _ fun _ => rfl

/-- The twirl error controlled directly by the two projective-readout commutator errors. -/
theorem pauli_twirl_readout_dist_le (L : (Fin n → F) →ₗ[F] (Fin n → F))
    (ξ : H × K → ℂ) (M : POVM A ((Fin n → F) × H)) :
    (∑ a, stateSqNorm (eprWithAux ξ)
      (averageX L.ker (dephaseZ (M.mats a).val) - (M.mats a).val)) ≤
      4 * (∑ a, ∑ y : Fin n → F, stateSqNorm (eprWithAux ξ)
        ((M.mats a).val * aOp (synOf wZ (LinearMap.id : (Fin n → F) →ₗ[F] (Fin n → F)) y) -
          aOp (synOf wZ (LinearMap.id : (Fin n → F) →ₗ[F] (Fin n → F)) y) * (M.mats a).val)) +
      4 * (∑ a, ∑ y : Fin n → F, stateSqNorm (eprWithAux ξ)
        ((M.mats a).val * aOp (synOf wX (CL.lperp L) y) -
          aOp (synOf wX (CL.lperp L) y) * (M.mats a).val)) := by
  simp_rw [fine_commutator_parseval, kernel_commutator_parseval, ← Finset.mul_sum]
  rw [Finset.sum_comm (f := fun a v : _ =>
    stateSqNorm (eprWithAux ξ) ((M.mats a).val * aOp (wZ v) - aOp (wZ v) * (M.mats a).val)),
    Finset.sum_comm (f := fun a (v : L.ker) =>
    stateSqNorm (eprWithAux ξ) ((M.mats a).val * aOp (wX v.1) - aOp (wX v.1) * (M.mats a).val))]
  exact pauli_twirl_dist_le L ξ M

end MIPRE.Introspection

end
