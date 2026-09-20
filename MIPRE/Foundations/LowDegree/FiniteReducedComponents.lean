/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.SelfDualize
import Mathlib.Tactic.Ring

/-!
# Primitive components of a finite ring with bijective squaring

This supplies the algebraic justification for splitting the binary cyclic group
algebra by its fixed vectors. The computations need only multiplication and
linear algebra; the finite permutation argument below is a correctness proof,
not an enumeration performed by the algorithm.
-/

namespace MIPRE.LowDegree

variable {R : Type*} [CommRing R] [Finite R]

/-- Bijective squaring on a finite ring makes every element periodic under squaring. -/
theorem exists_pow_succ_eq_self_of_square_bijective
    (hsq : Function.Bijective (fun x : R => x * x)) (x : R) :
    ∃ n : ℕ, 0 < n ∧ x ^ (n + 1) = x := by
  classical
  let e : Equiv.Perm R := Equiv.ofBijective (fun x : R => x * x) hsq
  have ho : 0 < orderOf e := orderOf_pos e
  have hp : ((fun x : R => x * x)^[orderOf e]) x = x := by
    have hf : (e : R → R) = (fun x : R => x * x) := rfl
    have h := congrArg (fun f : Equiv.Perm R => f x) (pow_orderOf_eq_one e)
    simpa only [Equiv.Perm.coe_pow, Equiv.Perm.coe_one, Function.id_def, hf] using h
  have he (n : ℕ) : ((fun x : R => x * x)^[n]) x = x ^ (2 ^ n) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, ← pow_two, ← pow_mul, pow_succ]
  rw [he] at hp
  refine ⟨2 ^ orderOf e - 1, ?_, ?_⟩
  · have htwo : 2 ≤ 2 ^ orderOf e := by
      exact Nat.le_pow ho
    omega
  · rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ (by decide))]
    exact hp

/-- A primitive nonzero idempotent sees every idempotent as either zero or itself. -/
def PrimitiveBinaryComponent (e : R) : Prop :=
  e ≠ 0 ∧ e * e = e ∧ ∀ u : R, u * u = u → e * u = 0 ∨ e * u = e

/-- Every nonzero element supported on a primitive component has an inverse in that component. -/
theorem PrimitiveBinaryComponent.exists_mul_eq
    (hsq : Function.Bijective (fun x : R => x * x)) {e : R}
    (he : PrimitiveBinaryComponent e) (x : R) (hx : x ≠ 0) (hex : e * x = x) :
    ∃ y : R, x * y = e := by
  obtain ⟨n, hn, hp⟩ := exists_pow_succ_eq_self_of_square_bijective hsq x
  have hid : x ^ n * x ^ n = x ^ n := by
    have h : x ^ (n + n) = x ^ n := by
      calc
        x ^ (n + n) = x ^ (n + 1) * x ^ (n - 1) := by
          rw [← pow_add]
          congr 1
          omega
        _ = x * x ^ (n - 1) := by rw [hp]
        _ = x ^ n := by rw [← pow_succ', Nat.sub_add_cancel hn]
    simpa only [pow_add] using h
  have hne : x ^ n ≠ 0 := by
    intro hz
    rw [pow_succ, hz, zero_mul] at hp
    exact hx hp.symm
  have hepow : e * x ^ n = x ^ n := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rw [pow_succ']
    calc
      e * (x * x ^ m) = (e * x) * x ^ m := (mul_assoc ..).symm
      _ = x * x ^ m := by rw [hex]
  have hu : x ^ n = e := by
    rcases he.2.2 (x ^ n) hid with h | h
    · exact (hne (hepow.symm.trans h)).elim
    · exact hepow.symm.trans h
  refine ⟨x ^ (n - 1), ?_⟩
  rw [← pow_succ', Nat.sub_add_cancel hn, hu]

end MIPRE.LowDegree
