/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryFiniteFieldDegree

/-! # Exact degrees of sums with coprime binary field degrees -/

noncomputable section

namespace MIPRE.LowDegree.BinaryFiniteField

open Polynomial

variable {R : Type*} [CommRing R] [CharP R 2]

private theorem frobenius_comm (a b : ℕ) (x : R) :
    iterateFrobenius R 2 a (iterateFrobenius R 2 b x) =
      iterateFrobenius R 2 b (iterateFrobenius R 2 a x) := by
  rw [← iterateFrobenius_add_apply, Nat.add_comm a b, iterateFrobenius_add_apply]

omit [CharP R 2] in
private theorem iterate_add_delta (F : R →+ R) (x d : R)
    (hx : F x = x + d) (hd : F d = d) (n : ℕ) : F^[n] x = x + n • d := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, map_add, map_nsmul, hx, hd, succ_nsmul]
    abel

omit [CharP R 2] in
private theorem nsmul_delta_eq_zero (F : R →+ R) (x : R) (n : ℕ)
    (hd : F (F x - x) = F x - x) (hx : F^[n] x = x) : n • (F x - x) = 0 := by
  have h := iterate_add_delta F x (F x - x) (by abel) hd n
  rw [hx] at h
  exact (add_left_cancel (show x + n • (F x - x) = x + 0 by simpa using h.symm))

/-- A period of a sum is a period of both summands when their given periods are coprime. -/
theorem frobenius_period_add_of_coprime (x y : R) (a b n : ℕ) (hab : a.Coprime b)
    (hx : iterateFrobenius R 2 a x = x) (hy : iterateFrobenius R 2 b y = y)
    (hs : iterateFrobenius R 2 n (x + y) = x + y) :
    iterateFrobenius R 2 n x = x ∧ iterateFrobenius R 2 n y = y := by
  let d := iterateFrobenius R 2 n x - x
  have hd : d = y - iterateFrobenius R 2 n y := by
    rw [map_add] at hs
    dsimp [d]
    linear_combination hs
  have hda : iterateFrobenius R 2 a d = d := by
    dsimp [d]
    rw [map_sub, frobenius_comm a n, hx]
  have hdb : iterateFrobenius R 2 b d = d := by
    rw [hd, map_sub, frobenius_comm b n, hy]
  have hpa : Function.IsPeriodicPt (frobenius R 2) a d := by
    change (frobenius R 2)^[a] d = d
    rw [iterate_frobenius]
    exact hda
  have hpb : Function.IsPeriodicPt (frobenius R 2) b d := by
    change (frobenius R 2)^[b] d = d
    rw [iterate_frobenius]
    exact hdb
  have hfix : Function.IsFixedPt (frobenius R 2) d := by
    have h := hpa.gcd hpb
    rw [hab.gcd_eq_one] at h
    simpa only [Function.IsPeriodicPt, Function.iterate_one] using h
  have hdn : iterateFrobenius R 2 n d = d := by
    rw [coe_iterateFrobenius]
    exact hfix.iterate n
  have hnx : (iterateFrobenius R 2 n)^[a] x = x := by
    rw [← iterateFrobenius_mul_apply, Nat.mul_comm n a, iterateFrobenius_mul_apply]
    exact Function.IsFixedPt.iterate hx n
  have hny : (iterateFrobenius R 2 n)^[b] y = y := by
    rw [← iterateFrobenius_mul_apply, Nat.mul_comm n b, iterateFrobenius_mul_apply]
    exact Function.IsFixedPt.iterate hy n
  have hax : a • d = 0 := nsmul_delta_eq_zero (iterateFrobenius R 2 n).toAddMonoidHom x a hdn hnx
  have hby : b • d = 0 := by
    have he : iterateFrobenius R 2 n y - y = -d := by rw [hd]; abel
    have hz := nsmul_delta_eq_zero (iterateFrobenius R 2 n).toAddMonoidHom y b
      (by
        change iterateFrobenius R 2 n (iterateFrobenius R 2 n y - y) =
          iterateFrobenius R 2 n y - y
        rw [he, map_neg, hdn]) hny
    change b • (iterateFrobenius R 2 n y - y) = 0 at hz
    simpa only [he, smul_neg, neg_eq_zero] using hz
  have hz : d = 0 := by
    apply AddMonoid.addOrderOf_eq_one_iff.mp
    apply Nat.dvd_one.mp
    rw [← hab.gcd_eq_one]
    exact Nat.dvd_gcd (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hax)
      (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hby)
  refine ⟨sub_eq_zero.mp hz, ?_⟩
  rw [hd] at hz
  exact (sub_eq_zero.mp hz).symm

variable {L : Type*} [Field L] [Algebra (ZMod 2) L]

/-- Binary minimal degree divides exactly the Frobenius periods of an integral element. -/
theorem minpoly_natDegree_dvd_iff_frobenius (x : L) (hx : IsIntegral (ZMod 2) x) (n : ℕ) :
    (minpoly (ZMod 2) x).natDegree ∣ n ↔ x ^ (2 ^ n) = x := by
  rw [(minpoly.irreducible hx).natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X, minpoly.dvd_iff]
  simp only [map_sub, map_pow, aeval_X, Nat.card_eq_fintype_card, ZMod.card, sub_eq_zero]

/-- Summing algebraic binary elements of coprime degrees multiplies their exact degrees. -/
theorem minpoly_natDegree_add_of_coprime (x y : L)
    (hx : IsIntegral (ZMod 2) x) (hy : IsIntegral (ZMod 2) y)
    (hab : (minpoly (ZMod 2) x).natDegree.Coprime (minpoly (ZMod 2) y).natDegree) :
    (minpoly (ZMod 2) (x + y)).natDegree =
      (minpoly (ZMod 2) x).natDegree * (minpoly (ZMod 2) y).natDegree := by
  let : CharP L 2 := charP_of_injective_ringHom (algebraMap (ZMod 2) L).injective 2
  let a := (minpoly (ZMod 2) x).natDegree
  let b := (minpoly (ZMod 2) y).natDegree
  let n := (minpoly (ZMod 2) (x + y)).natDegree
  have hsum := hx.add hy
  have hax : iterateFrobenius L 2 a x = x :=
    (minpoly_natDegree_dvd_iff_frobenius x hx a).mp dvd_rfl
  have hby : iterateFrobenius L 2 b y = y :=
    (minpoly_natDegree_dvd_iff_frobenius y hy b).mp dvd_rfl
  have hns : iterateFrobenius L 2 n (x + y) = x + y :=
    (minpoly_natDegree_dvd_iff_frobenius (x + y) hsum n).mp dvd_rfl
  obtain ⟨hnx, hny⟩ := frobenius_period_add_of_coprime x y a b n hab hax hby hns
  have han : a ∣ n := (minpoly_natDegree_dvd_iff_frobenius x hx n).mpr hnx
  have hbn : b ∣ n := (minpoly_natDegree_dvd_iff_frobenius y hy n).mpr hny
  have h₁ : a * b ∣ n := hab.mul_dvd_of_dvd_of_dvd han hbn
  have h₂ : n ∣ a * b := by
    apply (minpoly_natDegree_dvd_iff_frobenius (x + y) hsum (a * b)).mpr
    change iterateFrobenius L 2 (a * b) (x + y) = x + y
    rw [map_add]
    have hpx : iterateFrobenius L 2 (a * b) x = x := by
      rw [iterateFrobenius_mul_apply]
      exact Function.IsFixedPt.iterate hax b
    have hpy : iterateFrobenius L 2 (a * b) y = y := by
      rw [Nat.mul_comm a b, iterateFrobenius_mul_apply]
      exact Function.IsFixedPt.iterate hby a
    rw [hpx, hpy]
  exact Nat.dvd_antisymm h₂ h₁

end MIPRE.LowDegree.BinaryFiniteField

end
