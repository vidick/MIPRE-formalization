/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.SAT.Pcp
import MIPRE.Foundations.SAT.FmlLib
import MIPRE.Foundations.Cost.BinaryArithmetic

/-! # The executable seed enumeration for Pauli sampling

Field elements are numbered by their canonical little-endian bit strings.
For `m = 2^j` and a field of size `2^k`, the selector keeps the highest `j`
bits. This is the paper's equal-block selector for this explicit enumeration;
it does not identify the enumeration with `Fintype.equivFin`.
-/

noncomputable section
namespace MIPRE.Introspection.SeedProgram
open Cost Cost.PolyTimeFun SAT

def fieldIndex {k : ℕ} (E : BinField k) (a : E.carrier) : Fin (2 ^ k) :=
  ⟨bitsVal (E.toBits a), by simpa only [E.length_toBits] using SAT.bitsVal_lt (E.toBits a)⟩

theorem fieldIndex_injective {k : ℕ} (E : BinField k) : Function.Injective (fieldIndex E) := by
  intro a b h
  have he : E.toBits a = E.toBits b :=
    SAT.bitsVal_injective (by rw [E.length_toBits, E.length_toBits]) (congrArg Fin.val h)
  have hd := congrArg E.ofBits he
  simpa only [E.ofBits_toBits] using hd

/-- A genuine field enumeration, with forward direction given by canonical
binary rank. Only its inverse uses finite choice. -/
def fieldEnumeration {k : ℕ} (E : BinField k) : E.carrier ≃ Fin (2 ^ k) :=
  Equiv.ofBijective (fieldIndex E)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fieldIndex_injective E, by simp only [Fintype.card_fin, E.card_carrier]⟩)

theorem fieldEnumeration_val {k : ℕ} (E : BinField k) (a : E.carrier) :
    (fieldEnumeration E a).val = bitsVal (E.toBits a) := rfl

def selector {k : ℕ} (E : BinField k) (j : ℕ) (hj : j ≤ k) (a : E.carrier) : Fin (2 ^ j) :=
  ⟨(fieldIndex E a).val / 2 ^ (k - j), Nat.div_lt_of_lt_mul (by
    rw [← pow_add, Nat.sub_add_cancel hj]
    exact (fieldIndex E a).isLt)⟩

theorem bitsVal_drop (l : BitStr) (n : ℕ) :
    bitsVal (l.drop n) = bitsVal l / 2 ^ n := by
  induction n generalizing l with
  | zero => simp
  | succ n ih =>
    cases l with
    | nil => simp
    | cons b l =>
      rw [List.drop_succ_cons, ih, SAT.bitsVal_cons', pow_succ,
        Nat.mul_comm (2 ^ n) 2, ← Nat.div_div_eq_div_mul]
      have h : (2 * bitsVal l + b.toNat) / 2 = bitsVal l := by
        cases b
        · simp
        · simp only [Bool.toNat_true]; omega
      rw [h]

/-- The exact connection between the equal-block selector and its bit scan. -/
theorem selector_eq_bits {k : ℕ} (E : BinField k) (j : ℕ) (hj : j ≤ k) (a : E.carrier) :
    (selector E j hj a).val = bitsVal ((E.toBits a).drop (k - j)) := by
  rw [bitsVal_drop]
  rfl

def seedCoordinates {k : ℕ} (E : BinField k) (j : ℕ) (hj : j ≤ k) :
    E.carrier ≃ Fin (2 ^ j) × Fin (2 ^ (k - j)) :=
  ((fieldEnumeration E).trans (finCongr (by rw [← pow_add, Nat.add_sub_of_le hj]))).trans
    finProdFinEquiv.symm

theorem seedCoordinates_fst {k : ℕ} (E : BinField k) (j : ℕ) (hj : j ≤ k) (a : E.carrier) :
    (seedCoordinates E j hj a).1 = selector E j hj a := by
  apply Fin.ext
  rfl

/-- Every direction index occurs exactly `2^(k-j)` times. -/
theorem card_selector_fiber {k : ℕ} (E : BinField k) (j : ℕ) (hj : j ≤ k) (i : Fin (2 ^ j)) :
    Fintype.card {a : E.carrier // selector E j hj a = i} = 2 ^ (k - j) := by
  let e := seedCoordinates E j hj
  let f : {a : E.carrier // selector E j hj a = i} ≃ Fin (2 ^ (k - j)) :=
    { toFun := fun a => (e a.val).2
      invFun := fun r => ⟨e.symm (i, r), by
        rw [← seedCoordinates_fst]
        exact congrArg Prod.fst (e.apply_symm_apply (i, r))⟩
      left_inv := fun a => by
        apply Subtype.ext
        apply e.injective
        rw [e.apply_symm_apply]
        apply Prod.ext
        · exact a.property.symm.trans (seedCoordinates_fst E j hj a.val).symm
        · rfl
      right_inv := fun r => congrArg Prod.snd (e.apply_symm_apply (i, r)) }
  rw [Fintype.card_congr f, Fintype.card_fin]

/-- `k`, `j`, and the raw seed are supplied explicitly. The computation never
constructs a unary representation of the field size. -/
def selectorProg : PolyTimeFun (Unary × Unary × BitStr) ℕ :=
  bitsValue.comp (drop.comp ((snd.comp snd).pair
    (drop.comp (fst.pair (fst.comp snd)))))

theorem selectorProg_apply (k j : Unary) (s : BitStr) :
    selectorProg (k, j, s) = bitsVal (s.drop (k.length - j.length)) := by
  change bitsVal (s.drop (k.drop j.length).length) = _
  rw [List.length_drop]

theorem selectorProg_correct {k : ℕ} (E : BinField k) (j : ℕ) (hj : j ≤ k) (a : E.carrier) :
    selectorProg (unary k, unary j, E.toBits a) = (selector E j hj a).val := by
  rw [selectorProg_apply, length_unary, length_unary, selector_eq_bits]

theorem selectorProg_runs (x : Unary × Unary × BitStr) :
    ∃ r ≤ selectorProg.timeBound.eval (esize x),
      selectorProg.code.Runs (encode x) (encode (selectorProg x)) r :=
  selectorProg.computes x

end MIPRE.Introspection.SeedProgram
end
