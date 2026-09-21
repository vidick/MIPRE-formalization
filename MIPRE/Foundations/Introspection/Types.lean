/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.DeriveFintype
import MIPRE.Foundations.Cost.Encoding

/-! # The introspection question types

The source's type set consists of the Pauli types and two copies of
`Introspect`, `Sample`, `Read`, and `Hide₁, ..., Hideℓ`. The Pauli type is a
parameter so the foundational construction can be instantiated with the
concrete Pauli test without importing a Background module.
-/

namespace MIPRE.Introspection

/-- The additional tests, before specifying the original player's role. -/
inductive AuxType (ℓ : ℕ)
  | introspect
  | sample
  | read
  /-- `k : Fin ℓ` represents the paper's hiding level `k + 1`. -/
  | hide (k : Fin ℓ)
  deriving DecidableEq, Fintype

namespace AuxType

/-- Three fixed tests followed by the hiding levels. -/
def equivOption (ℓ : ℕ) : AuxType ℓ ≃ Option (Option (Option (Fin ℓ))) where
  toFun
    | .introspect => none
    | .sample => some none
    | .read => some (some none)
    | .hide k => some (some (some k))
  invFun
    | none => .introspect
    | some none => .sample
    | some (some none) => .read
    | some (some (some k)) => .hide k
  left_inv t := by cases t <;> rfl
  right_inv t := by rcases t with _ | (_ | (_ | k)) <;> rfl

/-- There are exactly `ℓ + 3` auxiliary types for either original player. -/
theorem card (ℓ : ℕ) : Fintype.card (AuxType ℓ) = ℓ + 3 := by
  rw [Fintype.card_congr (equivOption ℓ)]
  simp

/-- The auxiliary type's binary code, with the three fixed tags first. -/
def toNat {ℓ : ℕ} : AuxType ℓ → ℕ
  | .introspect => 0
  | .sample => 1
  | .read => 2
  | .hide k => k.val + 3

/-- Out-of-range hiding labels are rejected by the decoder. -/
def ofNat (ℓ : ℕ) : ℕ → Option (AuxType ℓ)
  | 0 => some .introspect
  | 1 => some .sample
  | 2 => some .read
  | k + 3 => if h : k < ℓ then some (.hide ⟨k, h⟩) else none

@[simp] theorem ofNat_toNat {ℓ : ℕ} (t : AuxType ℓ) : ofNat ℓ t.toNat = some t := by
  cases t with
  | introspect => rfl
  | sample => rfl
  | read => rfl
  | hide k => simp [toNat, ofNat, k.isLt]

instance {ℓ : ℕ} : Cost.SizedEncoding (AuxType ℓ) where
  encode t := Cost.encode t.toNat
  decode d := (Cost.decode d : Option ℕ).bind (ofNat ℓ)
  decode_encode t := by simp [Cost.SizedEncoding.decode_encode]

/-- The tag encoding has logarithmic size in the number of hiding levels. -/
theorem esize_le {ℓ : ℕ} (t : AuxType ℓ) :
    Cost.esize t ≤ 4 * Nat.size (ℓ + 3) + 1 := by
  have ht : t.toNat ≤ ℓ + 3 := by cases t <;> simp only [toNat] <;> omega
  exact (Cost.esize_nat_le t.toNat).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 4 (Nat.size_le_size ht)) 1)

end AuxType

/-- Pauli types together with the introspection tests for the two original players. -/
abbrev QuestionType (PauliType : Type*) (ℓ : ℕ) := PauliType ⊕ (AuxType ℓ × Bool)

namespace QuestionType

variable {PauliType : Type*} {ℓ : ℕ}

abbrev pauli (p : PauliType) : QuestionType PauliType ℓ := .inl p
abbrev introspect (w : Bool) : QuestionType PauliType ℓ := .inr (.introspect, w)
abbrev sample (w : Bool) : QuestionType PauliType ℓ := .inr (.sample, w)
abbrev read (w : Bool) : QuestionType PauliType ℓ := .inr (.read, w)
abbrev hide (w : Bool) (k : Fin ℓ) : QuestionType PauliType ℓ := .inr (.hide k, w)

/-- Introspection contributes exactly `2ℓ + 6` vertices. -/
theorem card [Fintype PauliType] (ℓ : ℕ) :
    Fintype.card (QuestionType PauliType ℓ) = Fintype.card PauliType + 2 * ℓ + 6 := by
  simp only [QuestionType, Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, AuxType.card]
  omega

/-- The paper's 26 Pauli types give `2ℓ + 32` introspection types. -/
theorem card_of_pauli_card [Fintype PauliType] (h : Fintype.card PauliType = 26) (ℓ : ℕ) :
    Fintype.card (QuestionType PauliType ℓ) = 2 * ℓ + 32 := by
  rw [card, h]
  omega

/-- A type exists independently of the Pauli type set and of the number of hiding levels. -/
instance : Nonempty (QuestionType PauliType ℓ) := ⟨introspect false⟩

section Encoding

open Cost

variable [SizedEncoding PauliType]

/-- A single bit distinguishes Pauli labels from role-tagged auxiliary labels. -/
def toData : QuestionType PauliType ℓ → Data
  | .inl p => .cons (encode false) (encode p)
  | .inr t => .cons (encode true) (encode t)

def ofData : Data → Option (QuestionType PauliType ℓ)
  | .nil => none
  | .cons tag payload => (decode tag : Option Bool).bind fun b =>
      if b then (decode payload : Option (AuxType ℓ × Bool)).map Sum.inr
      else (decode payload : Option PauliType).map Sum.inl

@[simp] theorem ofData_toData (t : QuestionType PauliType ℓ) : ofData (toData t) = some t := by
  cases t <;> simp [toData, ofData, SizedEncoding.decode_encode]

instance : SizedEncoding (QuestionType PauliType ℓ) where
  encode := toData
  decode := ofData
  decode_encode := ofData_toData

/-- Existing Pauli encodings are extended with constant overhead. -/
theorem esize_pauli (p : PauliType) : esize (pauli (ℓ := ℓ) p) = esize p + 2 := by
  change 1 + esize p + 1 = _
  omega

/-- The complete encoding of an auxiliary type has logarithmic size in `ℓ`. -/
theorem esize_aux_le (t : AuxType ℓ) (w : Bool) :
    esize (.inr (t, w) : QuestionType PauliType ℓ) ≤ 4 * Nat.size (ℓ + 3) + 9 := by
  have ht := AuxType.esize_le t
  have hw : esize w ≤ 3 := Data.size_ofBool w
  change 3 + (esize t + esize w + 1) + 1 ≤ _
  omega

end Encoding

end QuestionType
end MIPRE.Introspection
