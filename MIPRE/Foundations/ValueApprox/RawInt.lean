/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Complex.Basic

/-!
# Integers and Gaussian integers as pairs of naturals

Mathlib's `Primrec` has no arithmetic on `ℤ` (and no `Primcodable ℤ`), so the enumeration behind
`lem:value-lower-approx` carries its integers as pairs of naturals: `PInt := ℕ × ℕ` denotes
`a - b`, and `GInt := PInt × PInt` denotes the Gaussian integer `m + n i`. Equality and order are
the semantic ones (`PInt.Eq'`, `PInt.Lt'`, `GInt.Eq'`), decidable and primitive recursive;
`PInt.toInt` and `GInt.toC` read the values off and commute with the operations provided. Every
function here is primitive recursive, with the proof next to the definition.
-/

namespace MIPRE.ValueApprox

/-! ## Integers -/

/-- An integer `a - b`, as the pair `(a, b)` of naturals. -/
abbrev PInt := ℕ × ℕ

namespace PInt

/-- The integer denoted. -/
def toInt (x : PInt) : ℤ := (x.1 : ℤ) - x.2

def zero : PInt := (0, 0)
def ofNat (n : ℕ) : PInt := (n, 0)
def ofInt (m : ℤ) : PInt := (m.toNat, (-m).toNat)
def add (x y : PInt) : PInt := (x.1 + y.1, x.2 + y.2)
def neg (x : PInt) : PInt := (x.2, x.1)
def mul (x y : PInt) : PInt := (x.1 * y.1 + x.2 * y.2, x.1 * y.2 + x.2 * y.1)
def sum (l : List PInt) : PInt := l.foldr add zero

/-- Semantic equality of the denoted integers. -/
def Eq' (x y : PInt) : Prop := x.1 + y.2 = y.1 + x.2

/-- Semantic strict order of the denoted integers. -/
def Lt' (x y : PInt) : Prop := x.1 + y.2 < y.1 + x.2

instance : DecidableRel Eq' := fun x y => inferInstanceAs (Decidable (x.1 + y.2 = y.1 + x.2))
instance : DecidableRel Lt' := fun x y => inferInstanceAs (Decidable (x.1 + y.2 < y.1 + x.2))

@[simp] theorem toInt_zero : zero.toInt = 0 := by simp [toInt, zero]
@[simp] theorem toInt_ofNat (n : ℕ) : (ofNat n).toInt = n := by simp [toInt, ofNat]
@[simp] theorem toInt_ofInt (m : ℤ) : (ofInt m).toInt = m := by
  simp [toInt, ofInt]
@[simp] theorem toInt_add (x y : PInt) : (add x y).toInt = x.toInt + y.toInt := by
  simp [toInt, add]; ring
@[simp] theorem toInt_neg (x : PInt) : (neg x).toInt = -x.toInt := by simp [toInt, neg]
@[simp] theorem toInt_mul (x y : PInt) : (mul x y).toInt = x.toInt * y.toInt := by
  simp [toInt, mul]; ring
@[simp] theorem toInt_sum (l : List PInt) : (sum l).toInt = (l.map toInt).sum := by
  induction l with
  | nil => simp [sum]
  | cons a l ih => simp only [sum, List.foldr_cons, List.map_cons, List.sum_cons] at ih ⊢
                   rw [toInt_add, ih]

theorem eq'_iff {x y : PInt} : Eq' x y ↔ x.toInt = y.toInt := by
  simp only [Eq', toInt]; omega
theorem lt'_iff {x y : PInt} : Lt' x y ↔ x.toInt < y.toInt := by
  simp only [Lt', toInt]; omega

theorem primrec_ofNat : Primrec ofNat := Primrec.pair Primrec.id (Primrec.const 0)
theorem primrec_add : Primrec₂ add :=
  Primrec.pair (Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
    (Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
theorem primrec_neg : Primrec neg := Primrec.pair Primrec.snd Primrec.fst
theorem primrec_mul : Primrec₂ mul :=
  Primrec.pair
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.nat_mul.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)))
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
      (Primrec.nat_mul.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)))
theorem primrec_sum : Primrec sum :=
  Primrec.list_foldr Primrec.id (Primrec.const zero)
    (primrec_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
theorem primrecRel_eq' : PrimrecRel Eq' :=
  Primrec.eq.comp (Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst))
theorem primrecRel_lt' : PrimrecRel Lt' :=
  Primrec.nat_lt.comp
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst))

end PInt

/-! ## Gaussian integers -/

/-- A Gaussian integer `m + n i`, as a pair of `PInt`s. -/
abbrev GInt := PInt × PInt

namespace GInt

/-- The complex number denoted. -/
def toC (z : GInt) : ℂ := (z.1.toInt : ℂ) + (z.2.toInt : ℂ) * Complex.I

def zero : GInt := (PInt.zero, PInt.zero)
def ofNat (n : ℕ) : GInt := (PInt.ofNat n, PInt.zero)
def ofInt (m n : ℤ) : GInt := (PInt.ofInt m, PInt.ofInt n)
def add (x y : GInt) : GInt := (PInt.add x.1 y.1, PInt.add x.2 y.2)
def mul (x y : GInt) : GInt :=
  (PInt.add (PInt.mul x.1 y.1) (PInt.neg (PInt.mul x.2 y.2)),
    PInt.add (PInt.mul x.1 y.2) (PInt.mul x.2 y.1))
def conj (x : GInt) : GInt := (x.1, PInt.neg x.2)
def sum (l : List GInt) : GInt := l.foldr add zero

/-- Semantic equality of the denoted Gaussian integers. -/
def Eq' (x y : GInt) : Prop := PInt.Eq' x.1 y.1 ∧ PInt.Eq' x.2 y.2

instance : DecidableRel Eq' := fun x y =>
  inferInstanceAs (Decidable (PInt.Eq' x.1 y.1 ∧ PInt.Eq' x.2 y.2))

@[simp] theorem re_toC (z : GInt) : (toC z).re = z.1.toInt := by simp [toC]
@[simp] theorem im_toC (z : GInt) : (toC z).im = z.2.toInt := by simp [toC]
@[simp] theorem toC_zero : toC zero = 0 := by simp [toC, zero]
@[simp] theorem toC_ofNat (n : ℕ) : toC (ofNat n) = n := by simp [toC, ofNat]
@[simp] theorem toC_ofInt (m n : ℤ) : toC (ofInt m n) = m + n * Complex.I := by
  simp [toC, ofInt]
@[simp] theorem toC_add (x y : GInt) : toC (add x y) = toC x + toC y := by
  apply Complex.ext <;> simp [add]
@[simp] theorem toC_mul (x y : GInt) : toC (mul x y) = toC x * toC y := by
  apply Complex.ext <;> simp [mul, Complex.mul_re, Complex.mul_im]
  ring
@[simp] theorem toC_conj (x : GInt) : toC (conj x) = star (toC x) := by
  apply Complex.ext <;> simp [conj]
@[simp] theorem toC_sum (l : List GInt) : toC (sum l) = (l.map toC).sum := by
  induction l with
  | nil => simp [sum]
  | cons a l ih => simp only [sum, List.foldr_cons, List.map_cons, List.sum_cons] at ih ⊢
                   rw [toC_add, ih]

theorem eq'_iff {x y : GInt} : Eq' x y ↔ toC x = toC y := by
  rw [Eq', PInt.eq'_iff, PInt.eq'_iff, Complex.ext_iff, re_toC, re_toC, im_toC, im_toC,
    Int.cast_inj, Int.cast_inj]

theorem primrec_ofNat : Primrec ofNat := Primrec.pair PInt.primrec_ofNat (Primrec.const PInt.zero)
theorem primrec_add : Primrec₂ add :=
  Primrec.pair (PInt.primrec_add.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
    (PInt.primrec_add.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
theorem primrec_mul : Primrec₂ mul :=
  Primrec.pair
    (PInt.primrec_add.comp
      (PInt.primrec_mul.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (PInt.primrec_neg.comp
        (PInt.primrec_mul.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))))
    (PInt.primrec_add.comp
      (PInt.primrec_mul.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
      (PInt.primrec_mul.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)))
theorem primrec_conj : Primrec conj := Primrec.pair Primrec.fst (PInt.primrec_neg.comp Primrec.snd)
theorem primrec_sum : Primrec sum :=
  Primrec.list_foldr Primrec.id (Primrec.const zero)
    (primrec_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
theorem primrecRel_eq' : PrimrecRel Eq' :=
  PrimrecPred.and (PInt.primrecRel_eq'.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
    (PInt.primrecRel_eq'.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))

end GInt

end MIPRE.ValueApprox
