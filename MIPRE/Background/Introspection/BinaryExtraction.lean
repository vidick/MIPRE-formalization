/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.RestrictedProfileSoundness

/-! # Transporting field-register extraction into binary coordinates

This is an exact change of computational basis, using a self-dual field basis.
It neither assumes nor proves the existence of QLD extraction witnesses.
-/

noncomputable section
namespace MIPRE.Introspection.RestrictedSoundness
open Matrix Finset Classical BinaryComplete
open scoped Kronecker
set_option linter.unusedSectionVars false

section Reindex
variable {I J H K R S R' S' : Type*}
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
  [Fintype R'] [DecidableEq R'] [Fintype S'] [DecidableEq S']

private theorem pull_isometry (e : R' ≃ R) (V : Matrix R H ℂ) (hV : Vᴴ * V = 1) :
    (V.submatrix e id)ᴴ * V.submatrix e id = 1 := by
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hV]
  rfl

private theorem image_pull (e : R' ≃ R) (V : Matrix R H ℂ) (M : Matrix H H ℂ) :
    isometricImage (V.submatrix e id) M = registerOp e (isometricImage V M) := by
  unfold isometricImage registerOp
  rw [Matrix.conjTranspose_submatrix]
  change V.submatrix e (Equiv.refl H) * M.submatrix (Equiv.refl H) (Equiv.refl H) *
    Vᴴ.submatrix (Equiv.refl H) e = _
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]

private theorem state_pull (e : R' ≃ R) (f : S' ≃ S)
    (V : Matrix R H ℂ) (W : Matrix S K ℂ) (ψ : H × K → ℂ) :
    isometricState (V.submatrix e id) (W.submatrix f id) ψ =
      isometricState V W ψ ∘ e.prodCongr f := rfl

private theorem registerState_pull (e : J ≃ I) (ξ : H × K → ℂ) :
    registerState I ξ ∘ (e.prodCongr (Equiv.refl H)).prodCongr (e.prodCongr (Equiv.refl K)) =
      registerState J ξ := by
  funext p
  exact congrArg (fun z => z * ξ (p.1.2, p.2.2))
    (congrFun (registerEPR_equiv e) (p.1.1, p.2.1))

private theorem snorm_pull (e : R' ≃ R) (ψ : R → ℂ) (M : Matrix R R ℂ) :
    snorm (ψ ∘ e) (registerOp e M) = snorm ψ M := by
  unfold snorm
  rw [registerOp_mulVec, norm_evec_comp_equiv]

private theorem registerOp_aOp (e : R' ≃ R) (f : S' ≃ S) (M : Matrix R R ℂ) :
    registerOp (e.prodCongr f) (aOp M) = aOp (registerOp e M) := by
  simp only [aOp, registerOp_kronecker, registerOp_one]

private theorem registerOp_bOp (e : R' ≃ R) (f : S' ≃ S) (M : Matrix S S ℂ) :
    registerOp (e.prodCongr f) (bOp M) = bOp (registerOp f M) := by
  simp only [bOp, registerOp_kronecker, registerOp_one]

end Reindex

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] {m t d : ℕ} [NeZero m]

/-- The same three extraction estimates in the field computational basis,
with ideal generalized Pauli projectors and genuine full-register answers. -/
structure FieldExtraction (hm : m ∣ Fintype.card F)
    (R : TensorProductStrategy (QLD.qldGame (d := d) hm)) (δ : ℝ) where
  dA : ℕ
  dB : ℕ
  ξ : Fin dA × Fin dB → ℂ
  ξ_unit : star ξ ⬝ᵥ ξ = 1
  VA : Matrix (QLD.Honest.Register F m × Fin dA) (Fin R.dA) ℂ
  VB : Matrix (QLD.Honest.Register F m × Fin dB) (Fin R.dB) ℂ
  VA_isometry : VAᴴ * VA = 1
  VB_isometry : VBᴴ * VB = 1
  state_error : ‖evec (isometricState VA VB R.ψ -
    registerState (QLD.Honest.Register F m) ξ)‖ ≤ δ
  X_error : ∑ x : QLD.Honest.Register F m,
    snorm (registerState (QLD.Honest.Register F m) ξ) (aOp
      (isometricImage VA (R.PA.M (.pauli .X) (.pauliAns x)) -
        (aOp (Weyl.proj Weyl.wX x) : Matrix (QLD.Honest.Register F m × Fin dA) _ ℂ))) ^ 2 ≤ δ
  Z_error : ∑ z : QLD.Honest.Register F m,
    snorm (registerState (QLD.Honest.Register F m) ξ) (bOp
      (isometricImage VB (R.PB.M (.pauli .Z) (.pauliAns z)) -
        (aOp (Weyl.proj Weyl.wZ z) : Matrix (QLD.Honest.Register F m × Fin dB) _ ℂ))) ^ 2 ≤ δ

/-- Increasing the common error bound leaves the actual extraction data unchanged. -/
def FieldExtraction.mono {hm : m ∣ Fintype.card F}
    {R : TensorProductStrategy (QLD.qldGame (d := d) hm)} {δ δ' : ℝ}
    (w : FieldExtraction hm R δ) (h : δ ≤ δ') : FieldExtraction hm R δ' where
  dA := w.dA
  dB := w.dB
  ξ := w.ξ
  ξ_unit := w.ξ_unit
  VA := w.VA
  VB := w.VB
  VA_isometry := w.VA_isometry
  VB_isometry := w.VB_isometry
  state_error := w.state_error.trans h
  X_error := w.X_error.trans h
  Z_error := w.Z_error.trans h

private theorem binaryX (b : Module.Basis (Fin t) (ZMod 2) F)
    (hb : LowDegree.IsSelfDualBasis b) (x : Seed m t) :
    registerOp (Weyl.binEquiv b).symm
      (Weyl.proj Weyl.wX ((Weyl.binEquiv b).symm x)) = Honest.pauliXReadout (some x) := by
  have h := Weyl.proj_wX_binEquiv hb ((Weyl.binEquiv (n := Fin m → Bool) b).symm x)
  simp only [Equiv.apply_symm_apply] at h
  rw [← h, Honest.pauliXReadout_some]
  exact registerOp_inv (Weyl.binEquiv b) _

private theorem binaryZ (b : Module.Basis (Fin t) (ZMod 2) F)
    (hb : LowDegree.IsSelfDualBasis b) (x : Seed m t) :
    registerOp (Weyl.binEquiv b).symm
      (Weyl.proj Weyl.wZ ((Weyl.binEquiv b).symm x)) =
      readout (some : Seed m t → Option (Seed m t)) (some x) := by
  have h := Weyl.proj_wZ_binEquiv hb ((Weyl.binEquiv (n := Fin m → Bool) b).symm x)
  simp only [Equiv.apply_symm_apply] at h
  rw [← h]
  change registerOp (Weyl.binEquiv b).symm (registerOp (Weyl.binEquiv b) _) = _
  rw [registerOp_inv]
  ext i j
  by_cases hij : i = j <;> simp [hij, Weyl.proj_wZ, Weyl.zProj_apply, readout]

section ErrorTransport
variable {H K H₀ K₀ : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype H₀] [DecidableEq H₀] [Fintype K₀] [DecidableEq K₀]
  (b : Module.Basis (Fin t) (ZMod 2) F) (hb : LowDegree.IsSelfDualBasis b)
  (ξ : H × K → ℂ)

private theorem binary_state_error
    (V : Matrix (QLD.Honest.Register F m × H) H₀ ℂ)
    (W : Matrix (QLD.Honest.Register F m × K) K₀ ℂ) (ψ : H₀ × K₀ → ℂ) :
    ‖evec (isometricState
      (V.submatrix ((Weyl.binEquiv b).symm.prodCongr (Equiv.refl H)) id)
      (W.submatrix ((Weyl.binEquiv b).symm.prodCongr (Equiv.refl K)) id) ψ -
        registerState (Seed m t) ξ)‖ =
      ‖evec (isometricState V W ψ - registerState (QLD.Honest.Register F m) ξ)‖ := by
  rw [state_pull, ← registerState_pull (Weyl.binEquiv b).symm ξ]
  exact norm_evec_comp_equiv
    (((Weyl.binEquiv b).symm.prodCongr (Equiv.refl H)).prodCongr
      ((Weyl.binEquiv b).symm.prodCongr (Equiv.refl K)))
    (isometricState V W ψ - registerState (QLD.Honest.Register F m) ξ)

include hb in
private theorem binary_alice_error
    (V : Matrix (QLD.Honest.Register F m × H) H₀ ℂ) (M : Matrix H₀ H₀ ℂ) (x : Seed m t) :
    snorm (registerState (Seed m t) ξ) (aOp
      (isometricImage (V.submatrix ((Weyl.binEquiv b).symm.prodCongr (Equiv.refl H)) id) M -
        (aOp (Honest.pauliXReadout (some x)) : Matrix (Seed m t × H) _ ℂ))) =
    snorm (registerState (QLD.Honest.Register F m) ξ) (aOp
      (isometricImage V M -
        (aOp (Weyl.proj Weyl.wX ((Weyl.binEquiv b).symm x)) :
          Matrix (QLD.Honest.Register F m × H) _ ℂ))) := by
  rw [image_pull, ← binaryX b hb x,
    ← registerOp_aOp (Weyl.binEquiv b).symm (Equiv.refl H), ← registerOp_sub,
    ← registerState_pull (Weyl.binEquiv b).symm ξ,
    ← registerOp_aOp _ ((Weyl.binEquiv b).symm.prodCongr (Equiv.refl K)), snorm_pull]

include hb in
private theorem binary_bob_error
    (V : Matrix (QLD.Honest.Register F m × K) K₀ ℂ) (M : Matrix K₀ K₀ ℂ) (x : Seed m t) :
    snorm (registerState (Seed m t) ξ) (bOp
      (isometricImage (V.submatrix ((Weyl.binEquiv b).symm.prodCongr (Equiv.refl K)) id) M -
        (aOp (readout (some : Seed m t → Option (Seed m t)) (some x)) :
          Matrix (Seed m t × K) _ ℂ))) =
    snorm (registerState (QLD.Honest.Register F m) ξ) (bOp
      (isometricImage V M -
        (aOp (Weyl.proj Weyl.wZ ((Weyl.binEquiv b).symm x)) :
          Matrix (QLD.Honest.Register F m × K) _ ℂ))) := by
  rw [image_pull, ← binaryZ b hb x,
    ← registerOp_aOp (Weyl.binEquiv b).symm (Equiv.refl K), ← registerOp_sub,
    ← registerState_pull (Weyl.binEquiv b).symm ξ,
    ← registerOp_bOp ((Weyl.binEquiv b).symm.prodCongr (Equiv.refl H)) _, snorm_pull]

end ErrorTransport

/-- Exact field-to-binary conversion of the full extraction witness. State
distance and both valid-answer error sums keep precisely the same bound. -/
def FieldExtraction.toBinary {hm : m ∣ Fintype.card F}
    {R : TensorProductStrategy (QLD.qldGame (d := d) hm)} {δ : ℝ}
    (w : FieldExtraction hm R δ) (b : Module.Basis (Fin t) (ZMod 2) F)
    (hb : LowDegree.IsSelfDualBasis b) : Extraction hm b R δ where
  dA := w.dA
  dB := w.dB
  ξ := w.ξ
  ξ_unit := w.ξ_unit
  VA := w.VA.submatrix ((Weyl.binEquiv b).symm.prodCongr (Equiv.refl (Fin w.dA))) id
  VB := w.VB.submatrix ((Weyl.binEquiv b).symm.prodCongr (Equiv.refl (Fin w.dB))) id
  VA_isometry := pull_isometry _ _ w.VA_isometry
  VB_isometry := pull_isometry _ _ w.VB_isometry
  state_error := by rw [binary_state_error b w.ξ]; exact w.state_error
  X_error := by
    simp only [binary_alice_error b hb w.ξ, validAnswer]
    have he := Equiv.sum_comp (Weyl.binEquiv (n := Fin m → Bool) b).symm
      (fun x => snorm (registerState (QLD.Honest.Register F m) w.ξ) (aOp
        (isometricImage w.VA (R.PA.M (.pauli .X) (.pauliAns x)) -
          (aOp (Weyl.proj Weyl.wX x) : Matrix (QLD.Honest.Register F m × Fin w.dA) _ ℂ))) ^ 2)
    exact he.le.trans w.X_error
  Z_error := by
    simp only [binary_bob_error b hb w.ξ, validAnswer]
    have he := Equiv.sum_comp (Weyl.binEquiv (n := Fin m → Bool) b).symm
      (fun x => snorm (registerState (QLD.Honest.Register F m) w.ξ) (bOp
        (isometricImage w.VB (R.PB.M (.pauli .Z) (.pauliAns x)) -
          (aOp (Weyl.proj Weyl.wZ x) : Matrix (QLD.Honest.Register F m × Fin w.dB) _ ℂ))) ^ 2)
    exact he.le.trans w.Z_error

section SourceSoundness
variable {A I : Type} [Fintype A] [Nonempty A] [DecidableEq A]
  [Fintype I] [DecidableEq I] {ℓ : ℕ}

/-- The original source-game bound, consuming field-register QLD extraction
witnesses directly. The binary-coordinate conversion and padding cost no error. -/
theorem padded_quantumValue_ge_of_field_extraction
    (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
    (hb : LowDegree.IsSelfDualBasis b)
    (e : I ↪ Coord m t) (L : Bool → CL.CLFun (ZMod 2) I ℓ)
    (D : (I → ZMod 2) → (I → ZMod 2) → A → A → Bool)
    (hℓ : 0 < ℓ) (hL : ∀ w, (L w).ExactlyOn univ)
    (χ : F → Fin m) (π : F ≃ F) (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)
    (S : TensorProductStrategy (ExplicitGame.game hm χ π b
      (SourcePadding.depthFamily e L) (BinaryComplete.project (d := d) b)
      (SourcePadding.decider e D)))
    {a β x ε : ℝ} (ha : 1 ≤ a) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hx : 1 ≤ x) (hε : 0 ≤ ε) (hfail : 1 - S.value ≤ ε)
    (extract : ∀ (R : TensorProductStrategy (QLD.qldGame (d := d) hm)) (η : ℝ),
      0 ≤ η → 1 - R.value ≤ η →
      Nonempty (FieldExtraction hm R (errorProfile a β x η))) :
    1 - errorProfile (profileCoefficient ℓ a β) (β * rootExponent (6 * ℓ + 2)) x ε ≤
      quantumValue (Honest.sourceGame L D) := by
  apply padded_quantumValue_ge_of_qld_errorProfile hm b e L D hℓ hL χ π hχ S
    ha hβ0 hβ1 hx hε hfail
  intro R η hη hR
  obtain ⟨w⟩ := extract R η hη hR
  exact ⟨w.toBinary b hb⟩

end SourceSoundness

end MIPRE.Introspection.RestrictedSoundness
end
