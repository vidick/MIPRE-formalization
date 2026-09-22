/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.CompleteGame
import MIPRE.Foundations.WeylBinary

/-! # The honest Pauli measurements on the binary source register

A self-dual field basis transports the actual quantum projectors to qubit
coordinates. The original CL functions remain binary; they are not assumed
to arise by downsizing field-linear CL functions.
-/

noncomputable section
namespace MIPRE.Introspection.BinaryComplete
open Matrix Finset Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false

abbrev Coord (m t : ℕ) := (Fin m → Bool) × Fin t
abbrev Seed (m t : ℕ) := Coord m t → ZMod 2
abbrev Answer (F A : Type*) (m t d : ℕ) := ParsedAnswer (Seed m t) A (QLD.Answer F m d)

variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] {m d ℓ t : ℕ} [NeZero m]
  (b : Module.Basis (Fin t) (ZMod 2) F)
  (L : Bool → CL.CLFun (ZMod 2) (Coord m t) ℓ)
  (D : Seed m t → Seed m t → A → A → Bool)
  (R : SyncStrategy (Honest.sourceGame L D).doubled)

def project : QLD.Answer F m d → Seed m t
  | .pauliAns x => binEquiv b x
  | _ => 0

abbrev Space := (Seed m t × Fin R.d) × Fin 2

def shuffle : Space L D R ≃ (QLD.Honest.Space F m × Fin R.d) where
  toFun x := (((binEquiv b).symm x.1.1, x.2), x.1.2)
  invFun x := ((binEquiv b x.1.1, x.2), x.1.2)
  left_inv x := by simp
  right_inv x := by simp

def pauliLift (M : Matrix (QLD.Honest.Space F m) (QLD.Honest.Space F m) ℂ) :
    Matrix (Space L D R) (Space L D R) ℂ :=
  registerOp (shuffle b L D R) (aOp (HB := Fin R.d) M)

@[simp] theorem pauliLift_zero : pauliLift b L D R 0 = 0 := by
  rw [pauliLift, aOp_zero]
  rfl

theorem pauliLift_mul (M N : Matrix (QLD.Honest.Space F m) (QLD.Honest.Space F m) ℂ) :
    pauliLift b L D R (M * N) = pauliLift b L D R M * pauliLift b L D R N := by
  simp only [pauliLift, aOp_mul, registerOp_mul]

theorem pauliLift_isPVM {B : Type*} [Fintype B] [DecidableEq B]
    {M : B → Matrix (QLD.Honest.Space F m) (QLD.Honest.Space F m) ℂ} (hM : IsPVM M) :
    IsPVM (fun a => pauliLift b L D R (M a)) := registerOp_isPVM _ hM.aOp

theorem pauliLift_register (M : Matrix (QLD.Honest.Register F m) (QLD.Honest.Register F m) ℂ) :
    pauliLift b L D R (M ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
      aOp (HB := Fin 2) (registerOp (binEquiv b).symm M ⊗ₖ
        (1 : Matrix (Fin R.d) (Fin R.d) ℂ)) := by
  ext i j
  simp only [pauliLift, registerOp_apply, shuffle, Equiv.coe_fn_mk, aOp, kroneckerMap_apply]
  ring

def pauliOp (hm : m ∣ Fintype.card F) (q : QLD.Question F m) :
    Answer F A m t d → Matrix (Space L D R) (Space L D R) ℂ :=
  Honest.parsedPauliOp (fun a => pauliLift b L D R (QLD.Honest.answerOp hm q a))

theorem pauliOp_isPVM (hm : m ∣ Fintype.card F) (q : QLD.Question F m) :
    IsPVM (pauliOp (d := d) b L D R hm q) :=
  Honest.parsedPauliOp_isPVM _ (pauliLift_isPVM b L D R (QLD.Honest.answerOp_isPVM hm q))

def auxOp (hL : ∀ w, (L w).SupportedOn univ) (q : Honest.AuxQuestion ℓ)
    (a : Answer F A m t d) : Matrix (Space L D R) (Space L D R) ℂ :=
  aOp (HB := Fin 2) (Honest.auxOp L D R hL q a)

theorem auxOp_isPVM (hL : ∀ w, (L w).SupportedOn univ) (q : Honest.AuxQuestion ℓ) :
    IsPVM (auxOp (F := F) (d := d) L D R hL q) := (Honest.auxOp_isPVM L D R hL q).aOp

theorem pauliOp_wrong (hm : m ∣ Fintype.card F) (W : QLD.Bas)
    (a : QLD.Answer F m d) (ha : (QLD.Question.pauli W).fmtOk a = false) :
    pauliOp b L D R hm (.pauli W) (.pauli a : Answer F A m t d) = 0 := by
  change pauliLift b L D R (QLD.Honest.answerOp hm (.pauli W) a) = 0
  rw [QLD.Honest.answerOp_format_zero hm _ _ ha, pauliLift_zero]

theorem pauliOp_X (hb : LowDegree.IsSelfDualBasis b) (hm : m ∣ Fintype.card F)
    (x : QLD.Honest.Register F m) :
    pauliOp b L D R hm (.pauli .X) (.pauli (.pauliAns x) : Answer F A m t d) =
      aOp (HB := Fin 2) (Honest.pauliXOp L D R (binEquiv b x)) := by
  change pauliLift b L D R (QLD.Honest.answerOp hm (.pauli .X) (.pauliAns x)) = _
  rw [QLD.Honest.answerOp_pauli]
  change pauliLift b L D R (proj wX x ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) = _
  rw [pauliLift_register]
  have hx : registerOp (binEquiv b).symm (proj wX x) = proj wX (binEquiv b x) := by
    have he := congrArg (registerOp (binEquiv (n := Fin m → Bool) b).symm) (proj_wX_binEquiv hb x)
    change registerOp (binEquiv b).symm (registerOp (binEquiv b) _) = _ at he
    rw [registerOp_inv] at he
    exact he.symm
  rw [hx]
  rfl

theorem pauliOp_Z (hb : LowDegree.IsSelfDualBasis b) (hm : m ∣ Fintype.card F)
    (x : QLD.Honest.Register F m) :
    pauliOp b L D R hm (.pauli .Z) (.pauli (.pauliAns x) : Answer F A m t d) =
      aOp (HB := Fin 2) (Honest.pauliZOp L D R (binEquiv b x)) := by
  change pauliLift b L D R (QLD.Honest.answerOp hm (.pauli .Z) (.pauliAns x)) = _
  rw [QLD.Honest.answerOp_pauli]
  change pauliLift b L D R (proj wZ x ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) = _
  rw [pauliLift_register]
  have hz : registerOp (binEquiv b).symm (proj wZ x) = proj wZ (binEquiv b x) := by
    have he := congrArg (registerOp (binEquiv (n := Fin m → Bool) b).symm) (proj_wZ_binEquiv hb x)
    change registerOp (binEquiv b).symm (registerOp (binEquiv b) _) = _ at he
    rw [registerOp_inv] at he
    exact he.symm
  rw [hz]
  congr 1
  congr 1
  ext i j
  by_cases hij : i = j <;> simp [hij, proj_wZ, zProj_apply, readout]

end MIPRE.Introspection.BinaryComplete
end
