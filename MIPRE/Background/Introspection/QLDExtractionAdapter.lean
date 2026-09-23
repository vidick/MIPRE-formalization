/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.BinaryExtraction
import MIPRE.Foundations.Introspection.PauliErrorParameters
import MIPRE.Background.QLD.Soundness

/-! # Actual QLD soundness witnesses in the introspection interface

QLD reads all wrongly formatted Pauli answers as zero. The interface used by
introspection instead records the genuine full-register answer effects. Legal
Pauli support identifies those effects exactly, including at the zero register.
The ancillary spaces returned by QLD are then numbered without changing errors.
-/

noncomputable section
namespace MIPRE.Introspection.RestrictedSoundness
open Matrix Finset Classical
open scoped Kronecker
set_option linter.unusedSectionVars false

section Reindex
variable {I H K H' K' R S : Type*}
  [Fintype I] [DecidableEq I]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype H'] [DecidableEq H'] [Fintype K'] [DecidableEq K']
  [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]

private theorem aux_pull_isometry (e : H' ≃ H) (V : Matrix H R ℂ)
    (hV : Vᴴ * V = 1) : (V.submatrix e id)ᴴ * V.submatrix e id = 1 := by
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hV]
  rfl

private theorem aux_image_pull (e : H' ≃ H) (V : Matrix H R ℂ) (M : Matrix R R ℂ) :
    isometricImage (V.submatrix e id) M = registerOp e (isometricImage V M) := by
  unfold isometricImage registerOp
  rw [Matrix.conjTranspose_submatrix]
  change V.submatrix e (Equiv.refl R) * M.submatrix (Equiv.refl R) (Equiv.refl R) *
    Vᴴ.submatrix (Equiv.refl R) e = _
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]

private theorem aux_snorm_pull (e : H' ≃ H) (ψ : H → ℂ) (M : Matrix H H ℂ) :
    snorm (ψ ∘ e) (registerOp e M) = snorm ψ M := by
  unfold snorm
  rw [registerOp_mulVec, norm_evec_comp_equiv]

private theorem aux_registerOp_aOp (e : H' ≃ H) (f : K' ≃ K) (M : Matrix H H ℂ) :
    registerOp (e.prodCongr f) (aOp M) = aOp (registerOp e M) := by
  simp only [aOp, registerOp_kronecker, registerOp_one]

private theorem aux_registerOp_bOp (e : H' ≃ H) (f : K' ≃ K) (M : Matrix K K ℂ) :
    registerOp (e.prodCongr f) (bOp M) = bOp (registerOp f M) := by
  simp only [bOp, registerOp_kronecker, registerOp_one]

private theorem aux_registerState (e : H' ≃ H) (f : K' ≃ K) (ξ : H × K → ℂ) :
    registerState I (ξ ∘ e.prodCongr f) = registerState I ξ ∘
      ((Equiv.refl I).prodCongr e).prodCongr ((Equiv.refl I).prodCongr f) := rfl

private theorem aux_state_error (e : H' ≃ H) (f : K' ≃ K)
    (ξ : H × K → ℂ) (V : Matrix (I × H) R ℂ) (W : Matrix (I × K) S ℂ)
    (ψ : R × S → ℂ) :
    ‖evec (isometricState (V.submatrix ((Equiv.refl I).prodCongr e) id)
      (W.submatrix ((Equiv.refl I).prodCongr f) id) ψ -
      registerState I (ξ ∘ e.prodCongr f))‖ =
      ‖evec (isometricState V W ψ - registerState I ξ)‖ := by
  rw [aux_registerState]
  exact norm_evec_comp_equiv
    (((Equiv.refl I).prodCongr e).prodCongr ((Equiv.refl I).prodCongr f))
    (isometricState V W ψ - registerState I ξ)

private theorem aux_alice_error (e : H' ≃ H) (f : K' ≃ K)
    (ξ : H × K → ℂ) (V : Matrix (I × H) R ℂ) (M : Matrix R R ℂ)
    (P : Matrix I I ℂ) :
    snorm (registerState I (ξ ∘ e.prodCongr f)) (aOp
      (isometricImage (V.submatrix ((Equiv.refl I).prodCongr e) id) M -
        (aOp P : Matrix (I × H') _ ℂ))) =
      snorm (registerState I ξ) (aOp
        (isometricImage V M - (aOp P : Matrix (I × H) _ ℂ))) := by
  have hP : (aOp P : Matrix (I × H') _ ℂ) =
      registerOp ((Equiv.refl I).prodCongr e) (aOp P) := by
    rw [aux_registerOp_aOp]
    rfl
  rw [aux_image_pull, hP, ← registerOp_sub, aux_registerState,
    ← aux_registerOp_aOp _ ((Equiv.refl I).prodCongr f), aux_snorm_pull]

private theorem aux_bob_error (e : H' ≃ H) (f : K' ≃ K)
    (ξ : H × K → ℂ) (V : Matrix (I × K) S ℂ) (M : Matrix S S ℂ)
    (P : Matrix I I ℂ) :
    snorm (registerState I (ξ ∘ e.prodCongr f)) (bOp
      (isometricImage (V.submatrix ((Equiv.refl I).prodCongr f) id) M -
        (aOp P : Matrix (I × K') _ ℂ))) =
      snorm (registerState I ξ) (bOp
        (isometricImage V M - (aOp P : Matrix (I × K) _ ℂ))) := by
  have hP : (aOp P : Matrix (I × K') _ ℂ) =
      registerOp ((Equiv.refl I).prodCongr f) (aOp P) := by
    rw [aux_registerOp_aOp]
    rfl
  rw [aux_image_pull, hP, ← registerOp_sub, aux_registerState,
    ← aux_registerOp_bOp ((Equiv.refl I).prodCongr e) _, aux_snorm_pull]

end Reindex

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] {m d : ℕ} [NeZero m]

/-- Only the two full-register measurements require legal support. -/
def PauliSupported {H : Type*} [Fintype H] [DecidableEq H]
    (M : QLD.Question F m → POVM (QLD.Answer F m d) H) : Prop :=
  ∀ W a, (QLD.Question.pauli W).fmtOk a = false → ((M (.pauli W)).mats a).val = 0

/-- The stronger parsed support property furnished by the executable decoder. -/
def ParsedPauliSupported {V A J H : Type*} [Fintype V] [Fintype A] [Fintype J]
    [Fintype H] [DecidableEq H] {ℓ : ℕ}
    (M : (QuestionType QLD.Ty ℓ × (J → ZMod 2)) →
      POVM (ParsedAnswer V A (QLD.Answer F m d)) H) : Prop :=
  ∀ W a, ((M (.inl (.pauli W),0)).mats a).val ≠ 0 →
    ∃ x, a = .pauli (.pauliAns x)

/-- Scalar completion has no malformed mass when the parsed measurement only
has genuine full-register outcomes. -/
theorem completePauliPOVM_invalid_of_supported
    {V A H : Type*} [Fintype V] [Fintype A] [Fintype H] [DecidableEq H]
    (M : POVM (ParsedAnswer V A (QLD.Answer F m d)) H)
    (hM : ∀ a, (M.mats a).val ≠ 0 → ∃ x, a = .pauli (.pauliAns x))
    (W : QLD.Bas) (a : QLD.Answer F m d)
    (ha : (QLD.Question.pauli W).fmtOk a = false) :
    ((completePauliPOVM (.val 0) M).mats a).val = 0 := by
  rw [completePauliPOVM_mats]
  apply Finset.sum_eq_zero
  intro c hc
  by_contra hn
  obtain ⟨x,rfl⟩ := hM c hn
  have he : QLD.Answer.pauliAns x = a := (Finset.mem_filter.mp hc).2
  rw [← he] at ha
  cases ha

theorem rdPauliVec_mats_of_supported {H : Type*} [Fintype H] [DecidableEq H]
    (M : QLD.Question F m → POVM (QLD.Answer F m d) H)
    (hM : PauliSupported M) (W : QLD.Bas) (x : QLD.Honest.Register F m) :
    (((M (.pauli W)).map QLD.rdPauliVec).mats x).val =
      ((M (.pauli W)).mats (.pauliAns x)).val := by
  rw [POVM.map_mats]
  refine Finset.sum_eq_single (s := univ.filter (fun a : QLD.Answer F m d => QLD.rdPauliVec a = x))
    (f := fun a => ((M (.pauli W)).mats a).val) (.pauliAns x) ?_ ?_
  · intro a ha hne
    have hx := (Finset.mem_filter.mp ha).2
    cases a <;> try exact hM W _ rfl
    simp only [QLD.rdPauliVec] at hx
    exact (hne (congrArg QLD.Answer.pauliAns hx)).elim
  · intro hn
    exact (hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)).elim

private theorem projective_toPOVM_mats {X B H : Type*} [Fintype X] [Fintype B]
    [Fintype H] [DecidableEq H] (P : ProjectiveMeasurement X B (Matrix H H ℂ))
    (q : X) (a : B) : ((P.toPOVM q).mats a).val = P.M q a := rfl

/-- Number arbitrary finite ancillary spaces, preserving every extraction bound. -/
def fieldExtractionOfWitness {hm : m ∣ Fintype.card F}
    {R : TensorProductStrategy (QLD.qldGame (d := d) hm)} {δ : ℝ}
    {HA HB : Type} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
    (VA : Matrix (QLD.Honest.Register F m × HA) (Fin R.dA) ℂ)
    (VB : Matrix (QLD.Honest.Register F m × HB) (Fin R.dB) ℂ) (ξ : HA × HB → ℂ)
    (hVA : VAᴴ * VA = 1) (hVB : VBᴴ * VB = 1) (hξ : ‖evec ξ‖ = 1)
    (hstate : ‖evec (isometricState VA VB R.ψ -
      registerState (QLD.Honest.Register F m) ξ)‖ ≤ δ)
    (hX : ∑ x : QLD.Honest.Register F m,
      snorm (registerState (QLD.Honest.Register F m) ξ) (aOp
        (isometricImage VA (R.PA.M (.pauli .X) (.pauliAns x)) -
          (aOp (Weyl.proj Weyl.wX x) : Matrix (QLD.Honest.Register F m × HA) _ ℂ))) ^ 2 ≤ δ)
    (hZ : ∑ x : QLD.Honest.Register F m,
      snorm (registerState (QLD.Honest.Register F m) ξ) (bOp
        (isometricImage VB (R.PB.M (.pauli .Z) (.pauliAns x)) -
          (aOp (Weyl.proj Weyl.wZ x) : Matrix (QLD.Honest.Register F m × HB) _ ℂ))) ^ 2 ≤ δ) :
    FieldExtraction hm R δ where
  dA := Fintype.card HA
  dB := Fintype.card HB
  ξ := ξ ∘ (Fintype.equivFin HA).symm.prodCongr (Fintype.equivFin HB).symm
  ξ_unit := by
    rw [dotProduct_star_self, norm_evec_comp_equiv, hξ]
    norm_num
  VA := VA.submatrix ((Equiv.refl _).prodCongr (Fintype.equivFin HA).symm) id
  VB := VB.submatrix ((Equiv.refl _).prodCongr (Fintype.equivFin HB).symm) id
  VA_isometry := aux_pull_isometry _ VA hVA
  VB_isometry := aux_pull_isometry _ VB hVB
  state_error := by rw [aux_state_error]; exact hstate
  X_error := by simpa only [aux_alice_error] using hX
  Z_error := by simpa only [aux_bob_error] using hZ

/-- Universal QLD constants yield the genuine-answer extraction interface for
every strategy supported on correctly formatted Pauli answers. -/
theorem exists_fieldExtraction :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧
      ∀ {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
        {m d : ℕ} [NeZero m] (hm : m ∣ Fintype.card F), 1 ≤ d →
      ∀ (R : TensorProductStrategy (QLD.qldGame (d := d) hm)),
        PauliSupported R.PA.toPOVM → PauliSupported R.PB.toPOVM →
      ∀ {ε : ℝ}, 0 ≤ ε → 1 - R.value ≤ ε →
        Nonempty (FieldExtraction hm R (QLD.errShape a b ε m d (Fintype.card F))) := by
  obtain ⟨a,b,ha,hb0,hb1,hqld⟩ := QLD.qld_soundness
  refine ⟨a,b,ha,hb0,hb1,?_⟩
  intro F _ _ _ _ m d _ hm hd R hA hB ε hε hfail
  obtain ⟨HA,HB,iA,jA,iB,jB,VA,VB,ξ,hVA,hVB,hξ,hstate,hW⟩ :=
    hqld hm hd R.ψ R.ψ_unit R.PA.toPOVM R.PB.toPOVM hε
      (by simpa only [← TensorProductStrategy.value_eq_povmValue] using hfail)
  let := iA
  let := jA
  let := iB
  let := jB
  refine ⟨fieldExtractionOfWitness VA VB ξ hVA hVB hξ hstate ?_ ?_⟩
  · simpa only [rdPauliVec_mats_of_supported R.PA.toPOVM hA,
      projective_toPOVM_mats, QLD.weylOf] using (hW .X).1
  · simpa only [rdPauliVec_mats_of_supported R.PB.toPOVM hB,
      projective_toPOVM_mats, QLD.weylOf] using (hW .Z).2

/-- The degree-one specialization has exactly the error used by the canonical
parameter estimates, with no change to the QLD exponent or tail. -/
theorem exists_degreeOne_fieldExtraction :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧
      ∀ {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
        {m : ℕ} [NeZero m] (hm : m ∣ Fintype.card F),
      ∀ (R : TensorProductStrategy (QLD.qldGame (d := 1) hm)),
        PauliSupported R.PA.toPOVM → PauliSupported R.PB.toPOVM →
      ∀ {ε : ℝ}, 0 ≤ ε → 1 - R.value ≤ ε →
        Nonempty (FieldExtraction hm R
          (PauliErrorParameters.qldError a b m (Fintype.card F) ε)) := by
  obtain ⟨a,b,ha,hb0,hb1,h⟩ := exists_fieldExtraction
  refine ⟨a,b,ha,hb0,hb1,?_⟩
  intro F _ _ _ _ m _ hm R hA hB ε hε hfail
  simpa only [QLD.errShape, PauliErrorParameters.qldError, Nat.cast_one, mul_one, neg_mul]
    using h hm le_rfl R hA hB hε hfail

/-- Fix the universal QLD constants once, before any verifier parameters. -/
def qldCoefficient : ℝ := exists_fieldExtraction.choose
def qldExponent : ℝ := exists_fieldExtraction.choose_spec.choose

theorem qldCoefficient_one_le : 1 ≤ qldCoefficient :=
  exists_fieldExtraction.choose_spec.choose_spec.1

theorem qldExponent_pos : 0 < qldExponent :=
  exists_fieldExtraction.choose_spec.choose_spec.2.1

theorem qldExponent_lt_one : qldExponent < 1 :=
  exists_fieldExtraction.choose_spec.choose_spec.2.2.1

/-- The proved QLD theorem, with its universal constants fixed globally. -/
theorem fieldExtraction_exists (hm : m ∣ Fintype.card F) (hd : 1 ≤ d)
    (R : TensorProductStrategy (QLD.qldGame (d := d) hm))
    (hA : PauliSupported R.PA.toPOVM) (hB : PauliSupported R.PB.toPOVM)
    {ε : ℝ} (hε : 0 ≤ ε) (hfail : 1 - R.value ≤ ε) :
    Nonempty (FieldExtraction hm R
      (QLD.errShape qldCoefficient qldExponent ε m d (Fintype.card F))) :=
  exists_fieldExtraction.choose_spec.choose_spec.2.2.2 hm hd R hA hB hε hfail

theorem degreeOne_fieldExtraction_exists (hm : m ∣ Fintype.card F)
    (R : TensorProductStrategy (QLD.qldGame (d := 1) hm))
    (hA : PauliSupported R.PA.toPOVM) (hB : PauliSupported R.PB.toPOVM)
    {ε : ℝ} (hε : 0 ≤ ε) (hfail : 1 - R.value ≤ ε) :
    Nonempty (FieldExtraction hm R
      (PauliErrorParameters.qldError qldCoefficient qldExponent m (Fintype.card F) ε)) := by
  simpa only [QLD.errShape, PauliErrorParameters.qldError, Nat.cast_one, mul_one, neg_mul]
    using fieldExtraction_exists hm le_rfl R hA hB hε hfail

end MIPRE.Introspection.RestrictedSoundness
end
