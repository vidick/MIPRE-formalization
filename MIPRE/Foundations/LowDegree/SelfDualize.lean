/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.Finite.Basic

/-!
# Self-dualization in characteristic two

The step that turns a normal basis into a *self-dual* normal basis (blueprint
`lem:self-dual-basis`, ledger nodes `1.1.6.1.7` and `1.1.6.1.8`).

Written in the group algebra, where the whole step is two short lemmas. If `α` is a normal
element of `K / F` with Galois group `G`, the Gram matrix of its orbit is circulant, i.e. it is
the element `c ∈ F[G]` with `c g = tr(α · g α)`; it is a unit, and it is fixed by the involution
`τ` induced by `g ↦ g⁻¹`. Replacing `α` by `a • α` replaces `c` by `a · τ a · c`, so a self-dual
normal basis is exactly a solution `a` of `a · τ a = c⁻¹`.

* `exists_mul_involute_eq` — that equation is solvable in any commutative ring on which
  squaring is bijective: take the square root of the right-hand side, which is unique and
  therefore fixed by `τ` because the right-hand side is.
* `sq_bijective` — and squaring *is* bijective on `F[G]` when `F` is a finite field of
  characteristic two and `G` is a finite abelian group of odd order, because squaring is then
  the composite of the Frobenius of `F` on coefficients with the doubling bijection of `G` on
  indices.

Between them they replace the circulant Gram manipulation the campaign's two nodes carry.
Nothing here is about fields yet: `MIPRE/Foundations/LowDegree/SelfDual.lean` has the
definitions `IsSelfDualBasis` and `IsNormalBasis`, and assembling these lemmas into a basis is
the remaining work of issue #105.
-/

namespace MIPRE.LowDegree

open Finset

/-! ## The equation `a · τ a = u` -/

/-- **Self-dualization, abstractly.** In a commutative ring on which squaring is bijective,
every element fixed by a ring involution is of the form `a · τ a`. The square root of `u` is
unique, and `τ` of it is another square root, so it is fixed by `τ` as well. -/
theorem exists_mul_involute_eq {R : Type*} [CommRing R] (τ : R ≃+* R)
    (hinj : ∀ x y : R, x * x = y * y → x = y) (hsurj : ∀ y : R, ∃ x : R, x * x = y)
    {u : R} (hu : τ u = u) : ∃ a : R, a * τ a = u := by
  obtain ⟨b, hb⟩ := hsurj u
  have hbτ : τ b = b := hinj _ _ (by rw [← map_mul, hb, hu, ← hb])
  exact ⟨b, by rw [hbτ, hb]⟩

/-! ## Squaring on a group algebra of odd order in characteristic two -/

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- In a finite abelian group of odd order, doubling is injective. -/
theorem add_self_injective (hG : Odd (Fintype.card G)) :
    Function.Injective fun g : G => g + g := by
  intro a b hab
  simp only at hab
  have h2 : (a - b) + (a - b) = 0 := by
    have e : (a - b) + (a - b) = (a + a) - (b + b) := by abel
    rw [e, hab, sub_self]
  have hord : addOrderOf (a - b) ∣ 2 :=
    addOrderOf_dvd_of_nsmul_eq_zero (by rw [two_nsmul]; exact h2)
  have hcard : addOrderOf (a - b) ∣ Fintype.card G := addOrderOf_dvd_card
  have hcop : Nat.Coprime 2 (Fintype.card G) := Nat.coprime_two_left.mpr hG
  have hdvd : addOrderOf (a - b) ∣ 1 := hcop ▸ Nat.dvd_gcd hord hcard
  exact sub_eq_zero.mp (AddMonoid.addOrderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd))

/-- In a finite abelian group of odd order, doubling is bijective. -/
theorem add_self_bijective (hG : Odd (Fintype.card G)) :
    Function.Bijective fun g : G => g + g :=
  Finite.injective_iff_bijective.mp (add_self_injective hG)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq G]

omit [Fintype G] [Fintype F] [DecidableEq G] in
private theorem two_eq_zero (hF : CharP F 2) : (2 : AddMonoidAlgebra F G) = 0 := by
  have : ((2 : ℕ) : F) = 0 := by
    have := hF
    exact CharP.cast_eq_zero F 2
  rw [show (2 : AddMonoidAlgebra F G) = AddMonoidAlgebra.single 0 (2 : F) from rfl,
    show (2 : F) = ((2 : ℕ) : F) from by norm_num, this, AddMonoidAlgebra.single_zero]

/-- In characteristic two, squaring is additive. -/
theorem add_mul_self_char_two {R : Type*} [CommRing R] (h2 : (2 : R) = 0) (x y : R) :
    (x + y) * (x + y) = x * x + y * y := by
  have e : (x + y) * (x + y) = x * x + y * y + 2 * (x * y) := by ring
  rw [e, h2, zero_mul, add_zero]

omit [Fintype F] in
/-- The coefficient of a square, at a doubled index: squaring `F[G]` is the Frobenius of `F`
on coefficients composed with doubling on indices. -/
theorem coeff_mul_self (hF : CharP F 2) (hG : Odd (Fintype.card G))
    (z : AddMonoidAlgebra F G) (g : G) :
    (z * z).coeff (g + g) = z.coeff g * z.coeff g := by
  have h2 : (2 : F) = 0 := by
    have := hF
    have := CharP.cast_eq_zero F 2
    rwa [show ((2 : ℕ) : F) = (2 : F) from by norm_num] at this
  induction z using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [add_mul_self_char_two (two_eq_zero (G := G) hF), AddMonoidAlgebra.coeff_add,
        Finsupp.add_apply, hx, hy, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
      have : ∀ a b : F, (a + b) * (a + b) = a * a + b * b :=
        add_mul_self_char_two h2
      rw [this]
  | single m r =>
      rw [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.coeff_single,
        AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Finsupp.single_apply]
      by_cases h : m = g
      · simp [h]
      · rw [if_neg h, if_neg (fun he => h (add_self_injective hG he)), mul_zero]

/-- **Squaring is bijective on `F[G]`** when `F` has characteristic two and `G` is a finite
abelian group of odd order. -/
theorem mul_self_bijective (hF : CharP F 2) (hG : Odd (Fintype.card G)) :
    Function.Bijective fun x : AddMonoidAlgebra F G => x * x := by
  have : Finite (AddMonoidAlgebra F G) :=
    Finite.of_injective AddMonoidAlgebra.coeff AddMonoidAlgebra.coeff_injective
  refine Finite.injective_iff_bijective.mp fun x y hxy => ?_
  have hz : (x - y) * (x - y) = 0 := by
    have e : (x - y) * (x - y) = x * x - y * y - 2 * (x * y) + 2 * (y * y) := by ring
    rw [e, hxy, sub_self, two_eq_zero (G := G) hF, zero_mul, zero_mul, zero_sub, neg_zero,
      add_zero]
  refine sub_eq_zero.mp (AddMonoidAlgebra.coeff_injective (Finsupp.ext fun g => ?_))
  have := coeff_mul_self hF hG (x - y) g
  rw [hz] at this
  simpa using (mul_self_eq_zero.mp this.symm)

/-- **Self-dualization in the group algebra**: if `F` has characteristic two and `G` is a
finite abelian group of odd order, every element of `F[G]` fixed by a ring involution `τ` is
of the form `a · τ a`. -/
theorem exists_mul_involute_eq_of_charTwo (hF : CharP F 2) (hG : Odd (Fintype.card G))
    (τ : AddMonoidAlgebra F G ≃+* AddMonoidAlgebra F G) {u : AddMonoidAlgebra F G}
    (hu : τ u = u) : ∃ a : AddMonoidAlgebra F G, a * τ a = u :=
  exists_mul_involute_eq τ (fun _ _ h => (mul_self_bijective hF hG).injective h)
    (fun y => (mul_self_bijective hF hG).surjective y) hu

end MIPRE.LowDegree
