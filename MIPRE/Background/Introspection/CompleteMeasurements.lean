/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.HonestPauliMeasurements
import MIPRE.Background.QLD.CLBinary
import MIPRE.Foundations.Introspection.HonestCompleteGame
import MIPRE.Foundations.Introspection.HonestPauliEdges

/-! # A common carrier for all honest introspection measurements

The concrete Pauli measurements and the full auxiliary family share the same
field register, original strategy register, and one extra qubit. The permutation
below moves that qubit past the original strategy register; it does not change
any measurement or require a completeness premise for the Pauli test.
-/

noncomputable section
namespace MIPRE.Introspection.Complete
open Matrix Finset Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false

variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] {m d ℓ t : ℕ} [NeZero m]

abbrev Seed (F : Type*) (m : ℕ) := QLD.Honest.Register F m
abbrev Answer (F A : Type*) (m d : ℕ) := ParsedAnswer (Seed F m) A (QLD.Answer F m d)

/-- The actual full Pauli answer carries the seed; other formats have a fixed
projection and zero effect at the distinguished Pauli questions. -/
def project : QLD.Answer F m d → Seed F m
  | .pauliAns x => x
  | _ => 0

variable (L : Bool → CL.CLFun F (Fin m → Bool) ℓ)
  (D : Seed F m → Seed F m → A → A → Bool)
  (R : SyncStrategy (Honest.sourceGame L D).doubled)

abbrev Space := (Seed F m × Fin R.d) × Fin 2

def shuffle : Space L D R ≃ (QLD.Honest.Space F m × Fin R.d) where
  toFun x := ((x.1.1, x.2), x.1.2)
  invFun x := ((x.1.1, x.2), x.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

def pauliLift (M : Matrix (QLD.Honest.Space F m) (QLD.Honest.Space F m) ℂ) :
    Matrix (Space L D R) (Space L D R) ℂ :=
  registerOp (shuffle L D R) (aOp (HB := Fin R.d) M)

@[simp] theorem pauliLift_zero : pauliLift L D R 0 = 0 := by
  rw [pauliLift, aOp_zero]
  rfl

theorem pauliLift_mul (M N : Matrix (QLD.Honest.Space F m) (QLD.Honest.Space F m) ℂ) :
    pauliLift L D R (M * N) = pauliLift L D R M * pauliLift L D R N := by
  simp only [pauliLift, aOp_mul, registerOp_mul]

theorem pauliLift_isPVM {B : Type*} [Fintype B] [DecidableEq B]
    {M : B → Matrix (QLD.Honest.Space F m) (QLD.Honest.Space F m) ℂ} (hM : IsPVM M) :
    IsPVM (fun a => pauliLift L D R (M a)) :=
  registerOp_isPVM _ hM.aOp

theorem pauliLift_register (M : Matrix (Seed F m) (Seed F m) ℂ) :
    pauliLift L D R (M ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
      aOp (HB := Fin 2) (M ⊗ₖ (1 : Matrix (Fin R.d) (Fin R.d) ℂ)) := by
  ext i j
  simp only [pauliLift, registerOp_apply, shuffle, Equiv.coe_fn_mk, aOp,
    kroneckerMap_apply]
  ring

def pauliOp (hm : m ∣ Fintype.card F) (q : QLD.Question F m) :
    Answer F A m d → Matrix (Space L D R) (Space L D R) ℂ :=
  Honest.parsedPauliOp (fun a => pauliLift L D R (QLD.Honest.answerOp hm q a))

theorem pauliOp_isPVM (hm : m ∣ Fintype.card F) (q : QLD.Question F m) :
    IsPVM (pauliOp (d := d) L D R hm q) :=
  Honest.parsedPauliOp_isPVM _ (pauliLift_isPVM L D R (QLD.Honest.answerOp_isPVM hm q))

def auxOp (hL : ∀ w, (L w).SupportedOn univ) (q : Honest.AuxQuestion ℓ)
    (a : Answer F A m d) : Matrix (Space L D R) (Space L D R) ℂ :=
  aOp (HB := Fin 2) (Honest.auxOp L D R hL q a)

theorem auxOp_isPVM (hL : ∀ w, (L w).SupportedOn univ) (q : Honest.AuxQuestion ℓ) :
    IsPVM (auxOp (d := d) L D R hL q) := (Honest.auxOp_isPVM L D R hL q).aOp

theorem pauliOp_pauliAns (hm : m ∣ Fintype.card F) (W : QLD.Bas) (x : Seed F m) :
    pauliOp L D R hm (.pauli W) (.pauli (.pauliAns x) : Answer F A m d) =
      aOp (HB := Fin 2) (QLD.Honest.pauliOp W x ⊗ₖ
        (1 : Matrix (Fin R.d) (Fin R.d) ℂ)) := by
  change pauliLift L D R (QLD.Honest.answerOp hm (.pauli W) (.pauliAns x)) = _
  rw [QLD.Honest.answerOp_pauli]
  exact pauliLift_register L D R _

theorem pauliOp_wrong (hm : m ∣ Fintype.card F) (W : QLD.Bas)
    (a : QLD.Answer F m d) (ha : (QLD.Question.pauli W).fmtOk a = false) :
    pauliOp L D R hm (.pauli W) (.pauli a : Answer F A m d) = 0 := by
  change pauliLift L D R (QLD.Honest.answerOp hm (.pauli W) a) = 0
  rw [QLD.Honest.answerOp_format_zero hm _ _ ha, pauliLift_zero]

theorem pauliOp_X (hm : m ∣ Fintype.card F) (x : Seed F m) :
    pauliOp L D R hm (.pauli .X) (.pauli (.pauliAns x) : Answer F A m d) =
      aOp (HB := Fin 2) (Honest.pauliXOp L D R x) :=
  pauliOp_pauliAns L D R hm .X x

theorem pauliOp_Z (hm : m ∣ Fintype.card F) (x : Seed F m) :
    pauliOp L D R hm (.pauli .Z) (.pauli (.pauliAns x) : Answer F A m d) =
      aOp (HB := Fin 2) (Honest.pauliZOp L D R x) := by
  rw [pauliOp_pauliAns]
  congr 1
  congr 1
  ext i j
  by_cases hij : i = j <;> simp [hij, QLD.Honest.pauliOp, QLD.Honest.basis, proj_wZ, zProj_apply,
    readout]

end MIPRE.Introspection.Complete
end
