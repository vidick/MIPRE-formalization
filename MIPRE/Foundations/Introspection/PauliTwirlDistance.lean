/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.ComposedTwirl
public import MIPRE.Foundations.Introspection.CommutatorParseval
public import MIPRE.Foundations.Introspection.BlockPOVM
public import MIPRE.Foundations.Introspection.EPR

@[expose] public section

/-! # Approximate Pauli mixing with explicit constants

In the register model (Phase 4 of `planning/mipco-track.md`): the EPR state on the sampled register
adjoined to an ancillary model `Ξ` (`Ξ.reg (Fin n → F)`), with register Paulis `smulKron 1 (wZ v)`
and `smulKron 1 (wX v)`; the Parseval transfers hold on any model whose first player's algebra
carries the register.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Weyl Classical

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {n : ℕ} {A : Type*} [Fintype A]
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [StarModule ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [StarModule ℂ ℬ]

omit [StarModule ℂ ℬ] in
theorem star_smulKron_one_wZ (v : Fin n → F) :
    star (smulKron (1 : 𝒜) (wZ v)) = smulKron 1 (wZ v) := by
  rw [star_smulKron, star_one, wZ_conjTranspose]

omit [StarModule ℂ ℬ] in
theorem star_smulKron_one_wX {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
    (v : Fin n → F) : star (smulKron (1 : R) (wX v)) = smulKron 1 (wX v) := by
  rw [star_smulKron, star_one, wX_conjTranspose]

omit [StarModule ℂ ℬ] in
/-- The concrete `Z` dephasing is the uniform unitary twirl. -/
theorem dephaseZ_eq_unitaryTwirl (M : Matrix (Fin n → F) (Fin n → F) 𝒜) :
    dephaseZ M = unitaryTwirl (fun _ : Fin n → F => (Fintype.card (Fin n → F) : ℝ)⁻¹)
      (fun v => smulKron 1 (wZ v)) M := by
  simp only [dephaseZ, unitaryTwirl, ← Finset.smul_sum, star_smulKron_one_wZ,
    Complex.ofReal_inv, Complex.ofReal_natCast]

omit [StarModule ℂ ℬ] in
/-- The concrete kernel averaging is the uniform `X` twirl. -/
theorem averageX_eq_unitaryTwirl (S : Submodule F (Fin n → F))
    (M : Matrix (Fin n → F) (Fin n → F) 𝒜) :
    averageX S M = unitaryTwirl (fun _ : S => (Fintype.card S : ℝ)⁻¹)
      (fun v => smulKron 1 (wX v.1)) M := by
  simp only [averageX, unitaryTwirl, ← Finset.smul_sum, star_smulKron_one_wX,
    Complex.ofReal_inv, Complex.ofReal_natCast]

theorem smulKron_one_mul_self {R : Type*} [Ring R] [Algebra ℂ R] {P : Matrix (Fin n → F) (Fin n → F) ℂ}
    (hP : P * P = 1) : smulKron (1 : R) P * smulKron 1 P = 1 := by
  rw [smulKron_mul, one_mul, hP, smulKron_one_one]

/-- Twirling by all `Z` operators and kernel `X` operators costs four times each commutator
error. -/
theorem pauli_twirl_dist_le [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜]
    (L : (Fin n → F) →ₗ[F] (Fin n → F)) (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
    (M : POVMIn A (Matrix (Fin n → F) (Fin n → F) 𝒜)) :
    (∑ a, (Ξ.reg (Fin n → F)).stateSqNorm (averageX L.ker (dephaseZ (M.op a)) - M.op a)) ≤
      4 * ((Fintype.card (Fin n → F) : ℝ)⁻¹ * ∑ v : Fin n → F, ∑ a,
        (Ξ.reg (Fin n → F)).stateSqNorm
          (M.op a * smulKron 1 (wZ v) - smulKron 1 (wZ v) * M.op a)) +
      4 * ((Fintype.card L.ker : ℝ)⁻¹ * ∑ v : L.ker, ∑ a,
        (Ξ.reg (Fin n → F)).stateSqNorm
          (M.op a * smulKron 1 (wX v.1) - smulKron 1 (wX v.1) * M.op a)) := by
  have h := composed_twirl_dist_le (Ξ.reg (Fin n → F))
    (fun _ : Fin n → F => (Fintype.card (Fin n → F) : ℝ)⁻¹)
    (fun _ : L.ker => (Fintype.card L.ker : ℝ)⁻¹)
    (by intros; positivity) (by intros; positivity)
    (by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
    (by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)) M
    (fun v => smulKron 1 (wZ v)) (fun v : L.ker => smulKron 1 (wX v.1))
    (fun v : L.ker => smulKron (1 : ℬ) (wX v.1))
    (fun v => star_smulKron_one_wZ v)
    (fun v => smulKron_one_mul_self (wZ_mul_self v))
    (fun v => star_smulKron_one_wX v.1)
    (fun v => smulKron_one_mul_self (wX_mul_self v.1))
    (fun v => by rw [star_smulKron_one_wX, smulKron_one_mul_self (wX_mul_self v.1)])
    (fun v => reg_wX_mirror Ξ v.1)
  simpa only [← dephaseZ_eq_unitaryTwirl, ← averageX_eq_unitaryTwirl, ← Finset.mul_sum] using h

omit [StarModule ℂ 𝒜] [StarModule ℂ ℬ] in
/-- Fine `Z` readouts transfer to the uniform full-register Pauli error. -/
theorem fine_commutator_parseval
    (Ψ : BipartiteModel 𝒞 (Matrix (Fin n → F) (Fin n → F) 𝒜) ℬ)
    (M : Matrix (Fin n → F) (Fin n → F) 𝒜) :
    (∑ y : Fin n → F, Ψ.stateSqNorm
      (M * smulKron 1 (synOf wZ (LinearMap.id : (Fin n → F) →ₗ[F] (Fin n → F)) y) -
        smulKron 1 (synOf wZ (LinearMap.id : (Fin n → F) →ₗ[F] (Fin n → F)) y) * M)) =
    (Fintype.card (Fin n → F) : ℝ)⁻¹ * ∑ v : Fin n → F,
      Ψ.stateSqNorm (M * smulKron 1 (wZ v) - smulKron 1 (wZ v) * M) := by
  have h := linear_measurement_commutator_parseval wZ LinearMap.id Ψ M
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

omit [StarModule ℂ 𝒜] [StarModule ℂ ℬ] in
/-- The `L`-perpendicular readout transfers to the uniform Pauli error on `ker L`. -/
theorem kernel_commutator_parseval (L : (Fin n → F) →ₗ[F] (Fin n → F))
    (Ψ : BipartiteModel 𝒞 (Matrix (Fin n → F) (Fin n → F) 𝒜) ℬ)
    (M : Matrix (Fin n → F) (Fin n → F) 𝒜) :
    (∑ y : Fin n → F, Ψ.stateSqNorm
      (M * smulKron 1 (synOf wX (CL.lperp L) y) - smulKron 1 (synOf wX (CL.lperp L) y) * M)) =
    (Fintype.card L.ker : ℝ)⁻¹ * ∑ v : L.ker,
      Ψ.stateSqNorm (M * smulKron 1 (wX v.1) - smulKron 1 (wX v.1) * M) := by
  have h := linear_measurement_commutator_parseval wX (CL.lperp L) Ψ M
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
theorem pauli_twirl_readout_dist_le [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜]
    (L : (Fin n → F) →ₗ[F] (Fin n → F)) (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
    (M : POVMIn A (Matrix (Fin n → F) (Fin n → F) 𝒜)) :
    (∑ a, (Ξ.reg (Fin n → F)).stateSqNorm (averageX L.ker (dephaseZ (M.op a)) - M.op a)) ≤
      4 * (∑ a, ∑ y : Fin n → F, (Ξ.reg (Fin n → F)).stateSqNorm
        (M.op a * smulKron 1 (synOf wZ (LinearMap.id : (Fin n → F) →ₗ[F] (Fin n → F)) y) -
          smulKron 1 (synOf wZ (LinearMap.id : (Fin n → F) →ₗ[F] (Fin n → F)) y) * M.op a)) +
      4 * (∑ a, ∑ y : Fin n → F, (Ξ.reg (Fin n → F)).stateSqNorm
        (M.op a * smulKron 1 (synOf wX (CL.lperp L) y) -
          smulKron 1 (synOf wX (CL.lperp L) y) * M.op a)) := by
  simp_rw [fine_commutator_parseval, kernel_commutator_parseval, ← Finset.mul_sum]
  rw [Finset.sum_comm (f := fun a v : _ => (Ξ.reg (Fin n → F)).stateSqNorm
      (M.op a * smulKron 1 (wZ v) - smulKron 1 (wZ v) * M.op a)),
    Finset.sum_comm (f := fun a (v : L.ker) => (Ξ.reg (Fin n → F)).stateSqNorm
      (M.op a * smulKron 1 (wX v.1) - smulKron 1 (wX v.1) * M.op a))]
  exact pauli_twirl_dist_le L Ξ M

end MIPRE.Introspection

end

end
