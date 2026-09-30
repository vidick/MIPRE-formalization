/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Complex.Basic
public import MIPRE.Tactics

@[expose] public section

/-!
# The order of a matrix algebra over an ordered `⋆`-ring

The extension of a bipartite model by a finite register (`MIPRE.BipartiteModel.expand`) gives each
player the `n × n` matrices over the player's algebra. The analyses measure with positive operator
valued measures in the players' algebras (`MIPRE.POVMIn`), which need those algebras to be ordered;
matrices over an abstract ordered `⋆`-ring are not, in Mathlib. This file orders them the way a
`⋆`-algebra is ordered: `X ≤ Y` when `Y - X` is a sum of elements `Z⋆ Z` (`MatrixStar.instPartialOrderStar`,
with `StarOrderedRing` holding by construction).

That the relation is antisymmetric needs the entries' ring to be **proper** (`StarProper`):
`x⋆ x = 0` only for `x = 0`. Then an element of the cone has nonnegative diagonal entries, and a
vanishing diagonal entry kills its row and its column; so an element of the cone whose negative is
in the cone vanishes. The matrices are then proper again (`MatrixStar.instStarProper`), so the
construction iterates, which is what registers adjoined to registers need.

C⋆-algebras and their `⋆`-subalgebras are proper (`StarProper.of_cstarRing`,
`StarSubalgebra.instStarProper`), which covers the algebras of the commuting-operator model; the
complex matrices are (`MatrixStar.instStarProperComplex`), which covers the tensor-product model. The
order on the complex matrices themselves is Mathlib's positive semidefinite order
(`MatrixOrder`), not this one: `ℂ` is not given a `StarProper` instance, so this construction never
applies to `Matrix n n ℂ`.
-/

namespace MIPRE

/-- **A proper `⋆`-ring**: `x⋆ x = 0` only for `x = 0`. -/
class StarProper (R : Type*) [Mul R] [Star R] [Zero R] : Prop where
  /-- `x⋆ x = 0` forces `x = 0`. -/
  eq_zero_of_star_mul_self_eq_zero : ∀ x : R, star x * x = 0 → x = 0

theorem StarProper.of_cstarRing {R : Type*} [NonUnitalNormedRing R] [StarRing R] [CStarRing R] :
    StarProper R :=
  ⟨fun x h => (CStarRing.star_mul_self_eq_zero_iff x).mp h⟩

instance StarSubalgebra.instStarProper {A : Type*} [NormedRing A] [StarRing A] [CStarRing A]
    [NormedAlgebra ℂ A] [StarModule ℂ A] (S : StarSubalgebra ℂ A) : StarProper S :=
  ⟨fun x h => Subtype.ext ((CStarRing.star_mul_self_eq_zero_iff (x : A)).mp
    (congrArg Subtype.val h))⟩

namespace MatrixStar

open Finset Matrix

variable {n : Type*} [Fintype n]

open scoped ComplexOrder in
/-- **The complex matrices are proper**: `Xᴴ X = 0` forces `X = 0`. -/
instance instStarProperComplex [DecidableEq n] : StarProper (Matrix n n ℂ) :=
  ⟨fun X h => by
    rw [star_eq_conjTranspose] at h
    exact conjTranspose_mul_self_eq_zero.mp h⟩

variable {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]

omit [Fintype n] in
private theorem eq_zero_of_nonneg_of_add {a b : R} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b = 0) :
    a = 0 :=
  le_antisymm (by simpa [h] using le_add_of_nonneg_right (a := a) hb) ha

/-- The positive cone of the matrix algebra: the sums of elements `Z⋆ Z`. -/
abbrev cone (n R : Type*) [Fintype n] [Ring R] [StarRing R] : AddSubmonoid (Matrix n n R) :=
  AddSubmonoid.closure (Set.range fun Z : Matrix n n R => star Z * Z)

variable [StarProper R]

/-- **An element of the cone has nonnegative diagonal entries, and a vanishing diagonal entry
kills its row and its column.** -/
theorem diag_of_mem_cone {c : Matrix n n R} (hc : c ∈ cone n R) (i : n) :
    0 ≤ c i i ∧ (c i i = 0 → ∀ j, c i j = 0 ∧ c j i = 0) := by
  induction hc using AddSubmonoid.closure_induction with
  | mem c hc =>
    obtain ⟨Z, rfl⟩ := hc
    dsimp only
    have hterm : ∀ k, 0 ≤ star (Z k i) * Z k i := fun k => star_mul_self_nonneg _
    have hdiag : (star Z * Z) i i = ∑ k, star (Z k i) * Z k i := by
      simp only [Matrix.mul_apply, Matrix.star_apply]
    refine ⟨hdiag ▸ sum_nonneg fun k _ => hterm k, fun h0 j => ?_⟩
    rw [hdiag] at h0
    have hz : ∀ k, Z k i = 0 := fun k => StarProper.eq_zero_of_star_mul_self_eq_zero _
      ((sum_eq_zero_iff_of_nonneg fun k _ => hterm k).mp h0 k (mem_univ k))
    constructor
    · simp only [Matrix.mul_apply, Matrix.star_apply, hz, star_zero, zero_mul, sum_const_zero]
    · simp only [Matrix.mul_apply, Matrix.star_apply, hz, mul_zero, sum_const_zero]
  | zero => exact ⟨le_rfl, fun _ j => ⟨rfl, rfl⟩⟩
  | add a b _ _ ha hb =>
    refine ⟨by simpa only [Matrix.add_apply] using add_nonneg ha.1 hb.1, fun h0 j => ?_⟩
    rw [Matrix.add_apply] at h0
    have ha0 := eq_zero_of_nonneg_of_add ha.1 hb.1 h0
    have hb0 : b i i = 0 := by rwa [ha0, zero_add] at h0
    obtain ⟨ha1, ha2⟩ := ha.2 ha0 j
    obtain ⟨hb1, hb2⟩ := hb.2 hb0 j
    exact ⟨by rw [Matrix.add_apply, ha1, hb1, add_zero], by rw [Matrix.add_apply, ha2, hb2, add_zero]⟩

/-- An element of the cone whose negative is in the cone vanishes. -/
theorem eq_zero_of_mem_cone_of_add {p q : Matrix n n R} (hp : p ∈ cone n R) (hq : q ∈ cone n R)
    (h : p + q = 0) : p = 0 := by
  ext i j
  have hii : p i i = 0 :=
    eq_zero_of_nonneg_of_add (diag_of_mem_cone hp i).1 (diag_of_mem_cone hq i).1
      (by rw [← Matrix.add_apply, h, Matrix.zero_apply])
  exact ((diag_of_mem_cone hp i).2 hii j).1

/-- **The order of the matrix algebra over a proper ordered `⋆`-ring**: `X ≤ Y` when `Y - X` is
a sum of elements `Z⋆ Z`. -/
instance instPartialOrderStar : PartialOrder (Matrix n n R) where
  le X Y := ∃ p, p ∈ cone n R ∧ Y = X + p
  le_refl X := ⟨0, zero_mem _, (add_zero X).symm⟩
  le_trans X Y W := by
    rintro ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
    exact ⟨p + q, add_mem hp hq, add_assoc _ _ _⟩
  le_antisymm X Y := by
    rintro ⟨p, hp, rfl⟩ ⟨q, hq, hq'⟩
    have hpq : p + q = 0 := by
      have := congrArg (· - X) hq'
      simpa [add_assoc] using this.symm
    rw [eq_zero_of_mem_cone_of_add hp hq hpq, add_zero]

instance instStarOrderedRing : StarOrderedRing (Matrix n n R) where
  le_iff _ _ := Iff.rfl

/-- **The matrices over a proper ordered `⋆`-ring are proper.** -/
instance instStarProper : StarProper (Matrix n n R) :=
  ⟨fun Z h => by
    ext k i
    have hterm : ∀ k, 0 ≤ star (Z k i) * Z k i := fun k => star_mul_self_nonneg _
    have hdiag : (star Z * Z) i i = ∑ k, star (Z k i) * Z k i := by
      simp only [Matrix.mul_apply, Matrix.star_apply]
    rw [h, Matrix.zero_apply] at hdiag
    exact StarProper.eq_zero_of_star_mul_self_eq_zero _
      ((sum_eq_zero_iff_of_nonneg fun k _ => hterm k).mp hdiag.symm k (mem_univ k))⟩

end MatrixStar

end MIPRE

end
