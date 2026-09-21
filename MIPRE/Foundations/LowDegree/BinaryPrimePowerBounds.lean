/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryPrimePowerLift

/-! # Finite-field bounds that certify auxiliary root-lifting termination -/

namespace MIPRE.LowDegree.BinaryPolynomial

open Polynomial

/-- Canonical quotient coordinates determine the binary quotient cardinality. -/
theorem card_adjoinRoot_binary (f : Polynomial (ZMod 2)) (hf : f.Monic) :
    Nat.card (AdjoinRoot f) = 2 ^ f.natDegree := by
  rw [Nat.card_congr (BinaryQuotient.coordinateEquiv f hf).toEquiv]
  simp

/-- The primitive order of a binary root divides its field's multiplicative cardinality. -/
theorem primitive_root_order_dvd_card (f : Polynomial (ZMod 2)) (hf : f.Monic)
    (hi : Irreducible f) (n : ℕ) (hn : n ≠ 0)
    (hr : IsPrimitiveRoot (AdjoinRoot.root f) n) : n ∣ 2 ^ f.natDegree - 1 := by
  let : Fact (Irreducible f) := ⟨hi⟩
  let : Fintype (AdjoinRoot f) :=
    Fintype.ofEquiv (Fin f.natDegree → ZMod 2) (BinaryQuotient.coordinateEquiv f hf).symm.toEquiv
  have hd := hr.dvd_of_pow_eq_one (Fintype.card (AdjoinRoot f) - 1)
    (FiniteField.pow_card_sub_one_eq_one _ (hr.ne_zero hn))
  simpa only [← Nat.card_eq_fintype_card, card_adjoinRoot_binary f hf] using hd

/-- An odd prime cannot be lifted more often than the auxiliary binary degree. -/
theorem prime_power_lift_bound (f : Polynomial (ZMod 2)) (hf : f.Monic)
    (hi : Irreducible f) (q s : ℕ) (hq : q.Prime)
    (hr : IsPrimitiveRoot (AdjoinRoot.root f) (q ^ s)) : s ≤ f.natDegree := by
  have hd := primitive_root_order_dvd_card f hf hi (q ^ s) (pow_ne_zero _ hq.ne_zero) hr
  have hpos : 0 < 2 ^ f.natDegree - 1 := by
    have hx : 1 < 2 ^ f.natDegree := one_lt_pow₀ (by decide) hi.natDegree_pos.ne'
    omega
  have hle := Nat.le_of_dvd hpos hd
  have hq2 : 2 ≤ q := hq.two_le
  have hp : 2 ^ s ≤ q ^ s := Nat.pow_le_pow_left hq2 s
  have hlt : 2 ^ s < 2 ^ f.natDegree := by omega
  exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hlt |>.le

end MIPRE.LowDegree.BinaryPolynomial
