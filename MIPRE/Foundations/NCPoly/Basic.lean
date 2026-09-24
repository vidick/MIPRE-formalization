/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Complex.Module

/-!
# Noncommutative polynomials with the conjugate-linear star

`MIPRE.NCPoly G` is the free complex algebra on the letters `G`: finite complex combinations of
words in `G`, multiplied by concatenation. It is a type synonym (a `def`, not an `abbrev`) for
`MonoidAlgebra ℂ (FreeMonoid G)`, and carries the involution of the free `*`-algebra on
self-adjoint generators, `(Σ_w c_w w)⋆ = Σ_w conj(c_w) reverse(w)`: conjugate the coefficients
and reverse the words (`MIPRE.NCPoly.coeff_star_apply`, `MIPRE.NCPoly.star_single`). With it
`NCPoly G` is a `StarRing` and a `StarModule ℂ`, and every letter `NCPoly.gen g` is
self-adjoint.

This is the algebra of the Tsirelson route (`planning/tsirelson-campaign.md`, §3.1): the
quadratic module of the measurement relations lives in it (`MIPRE.Foundations.NCPoly.Cone`),
and strategies are evaluations of it on a Hilbert space.

## Why a new star, and why a `def`

* Mathlib's `FreeAlgebra ℂ G` has a star (`Mathlib.Algebra.Star.Free`), but it reverses words
  *`ℂ`-linearly*: it fixes the scalars, `star (algebraMap ℂ _ c) = algebraMap ℂ _ c`. It is not
  a `StarModule ℂ` for the conjugation of `ℂ`, so `star (i • 1) ≠ -i • 1`, and hermitian
  squares `s⋆ s` would not be hermitian in the sense the route needs. It cannot be used.
* Mathlib has no `Star` instance on `MonoidAlgebra`. Declaring one on
  `MonoidAlgebra ℂ (FreeMonoid G)` itself (as an `abbrev` would) would make the
  conjugate-reverse star a global instance on a Mathlib type, so `NCPoly G` is a `def`. Its
  `Ring` and `Algebra ℂ` structures are those of the monoid algebra (`inferInstanceAs`), and
  its real structure is `Module.complexToReal`, so `(r : ℝ) • z = (r : ℂ) • z` holds by `rfl`
  and no diamond arises. (`Mathlib.Algebra.Star.Free` also puts a `StarMul` on `FreeMonoid G`,
  word reversal; this file does not import it and writes `FreeMonoid.reverse` throughout.)
* Since `NCPoly G` is not reducible to the monoid algebra, the lemmas about it are restated
  here, as a small transport API (`coeff`, `ofCoeff`, `single`, `ext`, `induction_linear`,
  `single_mul_single`, `one_def`, `smul_single`, `basis`, `lift`, …); downstream files use this
  API and never the `MonoidAlgebra` lemmas.

## Main declarations

* `MIPRE.NCPoly G`, with its `Ring` and `Algebra ℂ` instances;
* the transport API: `NCPoly.coeff`, `NCPoly.ofCoeff`, `NCPoly.single`, `NCPoly.ext`,
  `NCPoly.coeff_injective`, `NCPoly.induction_linear`, `NCPoly.single_mul_single`,
  `NCPoly.coeff_mul`, `NCPoly.one_def`, `NCPoly.smul_single`, `NCPoly.sum_single`, the
  monomial basis `NCPoly.basis`, and the universal property `NCPoly.lift`
  (`NCPoly.lift_single`, `NCPoly.algHom_ext`);
* its `Star`, `StarRing` and `StarModule ℂ` instances, with `NCPoly.coeff_star_apply` and
  `NCPoly.star_single`;
* `NCPoly.gen g`, the degree-one monomial of a letter, with `NCPoly.star_gen` and
  `NCPoly.isSelfAdjoint_gen`;
* `NCPoly.eval f : NCPoly G →ₐ[ℂ] A`, evaluation at an assignment `f : G → A` of the letters,
  built from `NCPoly.lift` and `FreeMonoid.lift` (`NCPoly.eval_single`, `NCPoly.eval_gen`);
* `NCPoly.eval_star`: evaluation at self-adjoint letters commutes with the stars;
* `NCPoly.evalStar f hf : NCPoly G →⋆ₐ[ℂ] A`, the same evaluation as a `⋆`-algebra hom.

At the pinned Mathlib `MonoidAlgebra` is a structure with constructor `ofCoeff` and field
`coeff`, so the star is defined on coefficients and transported.
-/

noncomputable section

open ComplexConjugate

namespace MIPRE

/-- Noncommutative polynomials over `ℂ` in the letters `G`: the monoid algebra of the free
monoid, with the conjugate-linear, word-reversing star declared below. A `def`, so that the star
is not an instance on `MonoidAlgebra`. -/
def NCPoly (G : Type*) : Type _ := MonoidAlgebra ℂ (FreeMonoid G)

namespace NCPoly

variable {G : Type*}

/-- The ring structure of the monoid algebra. -/
instance instRing : Ring (NCPoly G) := inferInstanceAs (Ring (MonoidAlgebra ℂ (FreeMonoid G)))

/-- The complex algebra structure of the monoid algebra. -/
instance instAlgebra : Algebra ℂ (NCPoly G) :=
  inferInstanceAs (Algebra ℂ (MonoidAlgebra ℂ (FreeMonoid G)))

/-- `NCPoly G` is inhabited, by `0`. -/
instance : Inhabited (NCPoly G) := ⟨0⟩

/-- `NCPoly G` is nontrivial: `0 ≠ 1`. -/
instance : Nontrivial (NCPoly G) :=
  inferInstanceAs (Nontrivial (MonoidAlgebra ℂ (FreeMonoid G)))

/-! ## The transport API -/

/-- The coefficients of a polynomial, as a finitely supported function on words. -/
def coeff (x : NCPoly G) : FreeMonoid G →₀ ℂ := MonoidAlgebra.coeff x

/-- The polynomial with prescribed coefficients. -/
def ofCoeff (f : FreeMonoid G →₀ ℂ) : NCPoly G := MonoidAlgebra.ofCoeff f

/-- The monomial `c w` of a word `w` with coefficient `c`. -/
def single (w : FreeMonoid G) (c : ℂ) : NCPoly G := MonoidAlgebra.single w c

/-- The coefficients of `ofCoeff f` are `f`. -/
@[simp] theorem coeff_ofCoeff (f : FreeMonoid G →₀ ℂ) : (ofCoeff f).coeff = f := rfl

/-- A polynomial is recovered from its coefficients. -/
@[simp] theorem ofCoeff_coeff (x : NCPoly G) : ofCoeff x.coeff = x := rfl

/-- A polynomial is determined by its coefficients. -/
theorem coeff_injective : Function.Injective (coeff : NCPoly G → FreeMonoid G →₀ ℂ) :=
  MonoidAlgebra.coeff_injective

/-- Equality of coefficient functions. -/
@[simp] theorem coeff_inj {x y : NCPoly G} : x.coeff = y.coeff ↔ x = y :=
  coeff_injective.eq_iff

/-- Extensionality: two polynomials with the same coefficient on every word are equal. -/
@[ext] theorem ext {x y : NCPoly G} (h : ∀ w, x.coeff w = y.coeff w) : x = y :=
  coeff_injective (Finsupp.ext h)

/-- The coefficients of `0`. -/
@[simp] theorem coeff_zero : (0 : NCPoly G).coeff = 0 := rfl

/-- The coefficients of a sum. -/
@[simp] theorem coeff_add (x y : NCPoly G) : (x + y).coeff = x.coeff + y.coeff := rfl

/-- The coefficients of a negation. -/
@[simp] theorem coeff_neg (x : NCPoly G) : (-x).coeff = -x.coeff := rfl

/-- The coefficients of a difference. -/
@[simp] theorem coeff_sub (x y : NCPoly G) : (x - y).coeff = x.coeff - y.coeff := rfl

/-- The coefficients of a complex multiple. -/
@[simp] theorem coeff_smul (c : ℂ) (x : NCPoly G) : (c • x).coeff = c • x.coeff := rfl

/-- The coefficients of a real multiple. -/
@[simp] theorem coeff_real_smul (r : ℝ) (x : NCPoly G) : (r • x).coeff = (r : ℂ) • x.coeff := rfl

/-- The coefficients of a finite sum. -/
@[simp] theorem coeff_sum {ι : Type*} (s : Finset ι) (f : ι → NCPoly G) :
    (∑ i ∈ s, f i).coeff = ∑ i ∈ s, (f i).coeff :=
  MonoidAlgebra.coeff_sum s f

/-- The coefficients of a monomial. -/
@[simp] theorem coeff_single (w : FreeMonoid G) (c : ℂ) :
    (single w c).coeff = Finsupp.single w c := rfl

/-- The coefficient of a monomial at a word. -/
theorem coeff_single_apply (w v : FreeMonoid G) (c : ℂ) [Decidable (w = v)] :
    (single w c).coeff v = if w = v then c else 0 :=
  Finsupp.single_apply

/-- A monomial with coefficient `0` vanishes. -/
@[simp] theorem single_zero (w : FreeMonoid G) : single w (0 : ℂ) = 0 :=
  MonoidAlgebra.single_zero w

/-- `single w` is additive. -/
theorem single_add (w : FreeMonoid G) (c c' : ℂ) : single w (c + c') = single w c + single w c' :=
  MonoidAlgebra.single_add w c c'

/-- `single w` commutes with negation. -/
theorem single_neg (w : FreeMonoid G) (c : ℂ) : single w (-c) = -single w c := by
  ext v; simp [Finsupp.single_neg]

/-- `single w` commutes with subtraction. -/
theorem single_sub (w : FreeMonoid G) (c c' : ℂ) :
    single w (c - c') = single w c - single w c' := by
  rw [sub_eq_add_neg, single_add, single_neg, ← sub_eq_add_neg]

/-- A complex multiple of a monomial. -/
@[simp] theorem smul_single (c' : ℂ) (w : FreeMonoid G) (c : ℂ) :
    c' • single w c = single w (c' * c) :=
  MonoidAlgebra.smul_single' c' w c

/-- A monomial is a multiple of the monomial with coefficient `1`. -/
theorem single_eq_smul_single_one (w : FreeMonoid G) (c : ℂ) : single w c = c • single w 1 := by
  rw [smul_single, mul_one]

/-- The unit is the empty word. -/
theorem one_def : (1 : NCPoly G) = single 1 1 := rfl

/-- The coefficients of the unit. -/
theorem coeff_one : (1 : NCPoly G).coeff = Finsupp.single 1 1 := rfl

/-- The product of two monomials concatenates the words. -/
@[simp] theorem single_mul_single (w w' : FreeMonoid G) (c c' : ℂ) :
    single w c * single w' c' = single (w * w') (c * c') :=
  MonoidAlgebra.single_mul_single w w' c c'

/-- The coefficients of a product: the coefficient of `w` in `x y` is the sum of the
`x_u y_v` over the factorizations `w = u v`. -/
theorem coeff_mul [DecidableEq (FreeMonoid G)] (x y : NCPoly G) (w : FreeMonoid G) :
    (x * y).coeff w =
      x.coeff.sum fun u a => y.coeff.sum fun v b => if u * v = w then a * b else 0 :=
  MonoidAlgebra.coeff_mul x y w

/-- The scalars: `algebraMap ℂ (NCPoly G) c` is the monomial of the empty word. -/
theorem algebraMap_apply (c : ℂ) : algebraMap ℂ (NCPoly G) c = single 1 c := rfl

/-- Every polynomial is the sum of its monomials. -/
@[simp] theorem sum_single (x : NCPoly G) : x.coeff.sum single = x :=
  MonoidAlgebra.sum_coeff_single x

/-- Every polynomial is the sum of its monomials, over the support of its coefficients. -/
theorem sum_support_single (x : NCPoly G) :
    ∑ w ∈ x.coeff.support, single w (x.coeff w) = x :=
  sum_single x

/-- Induction on polynomials: a property that holds at `0`, is closed under sums and holds on
monomials holds everywhere. -/
@[elab_as_elim]
theorem induction_linear {motive : NCPoly G → Prop} (x : NCPoly G) (zero : motive 0)
    (add : ∀ x y : NCPoly G, motive x → motive y → motive (x + y))
    (single : ∀ w c, motive (single w c)) : motive x :=
  MonoidAlgebra.induction_linear (motive := motive) x zero add single

/-- The monomial basis of `NCPoly G`, indexed by words. -/
def basis : Module.Basis (FreeMonoid G) ℂ (NCPoly G) := MonoidAlgebra.basis (FreeMonoid G) ℂ

/-- The monomial basis vector of a word is the monomial with coefficient `1`. -/
@[simp] theorem basis_apply (w : FreeMonoid G) : basis w = single w 1 := rfl

/-- The coordinates in the monomial basis are the coefficients. -/
@[simp] theorem basis_repr (x : NCPoly G) : basis.repr x = x.coeff := rfl

section Lift

variable {A : Type*} [Semiring A] [Algebra ℂ A]

/-- The universal property: a monoid hom from the words into a complex algebra `A` extends to
a `ℂ`-algebra hom `NCPoly G →ₐ[ℂ] A`. -/
def lift : (FreeMonoid G →* A) ≃ (NCPoly G →ₐ[ℂ] A) := MonoidAlgebra.lift ℂ A (FreeMonoid G)

/-- The lift of a monoid hom on a monomial. -/
@[simp] theorem lift_single (F : FreeMonoid G →* A) (w : FreeMonoid G) (c : ℂ) :
    lift F (single w c) = c • F w :=
  MonoidAlgebra.lift_single F w c

/-- Two algebra homs out of `NCPoly G` that agree on words are equal. -/
theorem algHom_ext {φ ψ : NCPoly G →ₐ[ℂ] A} (h : ∀ w, φ (single w 1) = ψ (single w 1)) :
    φ = ψ :=
  lift.symm.injective (MonoidHom.ext h)

end Lift

/-! ## The star -/

/-- Word reversal, as an involutive permutation of `FreeMonoid G`. -/
def revEquiv : FreeMonoid G ≃ FreeMonoid G :=
  Function.Involutive.toPerm FreeMonoid.reverse fun _ => FreeMonoid.reverse_reverse

/-- Word reversal, applied. -/
@[simp] theorem revEquiv_apply (w : FreeMonoid G) : revEquiv w = w.reverse := rfl

/-- Word reversal is its own inverse. -/
@[simp] theorem revEquiv_symm_apply (w : FreeMonoid G) : revEquiv.symm w = w.reverse := rfl

/-- The empty word is its own reversal. -/
@[simp] theorem freeMonoid_reverse_one : (1 : FreeMonoid G).reverse = 1 := rfl

/-- The star on coefficient functions: conjugate the coefficients, reverse the words. -/
def starCoeff (f : FreeMonoid G →₀ ℂ) : FreeMonoid G →₀ ℂ :=
  (f.mapRange (starRingEnd ℂ) (map_zero _)).equivMapDomain revEquiv

/-- The star of `NCPoly G`: `(Σ_w c_w w)⋆ = Σ_w conj(c_w) reverse(w)`. -/
instance : Star (NCPoly G) := ⟨fun x => ofCoeff (starCoeff x.coeff)⟩

/-- The coefficient formula for the star: the coefficient of `w` in `x⋆` is the conjugate of the
coefficient of the reversed word in `x`. -/
@[simp] theorem coeff_star_apply (x : NCPoly G) (w : FreeMonoid G) :
    (star x).coeff w = conj (x.coeff w.reverse) := rfl

/-- The star of a monomial. -/
theorem star_single (w : FreeMonoid G) (c : ℂ) :
    star (single w c) = single w.reverse (conj c) := by
  apply coeff_injective
  change starCoeff (Finsupp.single w c) = Finsupp.single w.reverse (conj c)
  simp [starCoeff, Finsupp.mapRange_single, Finsupp.equivMapDomain_single]

private theorem star_add' (x y : NCPoly G) : star (x + y) = star x + star y := by
  ext w; simp

private theorem star_zero' : star (0 : NCPoly G) = 0 := by
  ext w; simp

private theorem star_star' (x : NCPoly G) : star (star x) = x := by
  ext w; simp

private theorem star_mul' (x y : NCPoly G) : star (x * y) = star y * star x := by
  induction x using induction_linear with
  | zero => simp [star_zero']
  | add a b ha hb => rw [add_mul, star_add', ha, hb, star_add', mul_add]
  | single m r =>
    induction y using induction_linear with
    | zero => simp [star_zero']
    | add a b ha hb => rw [mul_add, star_add', ha, hb, star_add', add_mul]
    | single n s =>
      rw [single_mul_single, star_single, star_single, star_single, single_mul_single,
        FreeMonoid.reverse_mul, map_mul, mul_comm (conj r)]

/-- `NCPoly G` is a `⋆`-ring: the star is additive, involutive and reverses products. -/
instance : StarRing (NCPoly G) where
  star_involutive := star_star'
  star_mul := star_mul'
  star_add := star_add'

/-- The star is conjugate-linear: `(c • x)⋆ = conj c • x⋆`. -/
instance : StarModule ℂ (NCPoly G) where
  star_smul c x := by ext w; simp

/-- The star of a monomial with coefficient `1`. -/
@[simp] theorem star_single_one (w : FreeMonoid G) :
    star (single w 1 : NCPoly G) = single w.reverse 1 := by
  simp [star_single]

/-! ## Generators -/

/-- The generator of a letter: the degree-one monomial `single (FreeMonoid.of g) 1`. -/
def gen (g : G) : NCPoly G := single (FreeMonoid.of g) 1

/-- Generators are fixed by the star. -/
@[simp] theorem star_gen (g : G) : star (gen g) = gen g := by
  simp [gen, star_single]

/-- Generators are self-adjoint. -/
theorem isSelfAdjoint_gen (g : G) : IsSelfAdjoint (gen g) := star_gen g

/-- A word `g w` is the product of the generator `g` and the word `w`. -/
theorem single_of_mul (g : G) (w : FreeMonoid G) (c : ℂ) :
    single (FreeMonoid.of g * w) c = gen g * single w c := by
  rw [gen, single_mul_single, one_mul]

/-! ## Evaluation -/

/-- On a word, the star of the evaluation at self-adjoint letters is the evaluation of the
reversed word. -/
theorem star_lift_eq_lift_reverse {M : Type*} [Monoid M] [StarMul M] (f : G → M)
    (hf : ∀ g, IsSelfAdjoint (f g)) (w : FreeMonoid G) :
    star (FreeMonoid.lift f w) = FreeMonoid.lift f w.reverse := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | of_mul g w ih =>
    rw [map_mul, star_mul, ih, FreeMonoid.reverse_mul, map_mul, FreeMonoid.reverse_of,
      FreeMonoid.lift_eval_of, (hf g).star_eq]

section Eval

variable {A : Type*} [Semiring A] [Algebra ℂ A]

/-- Evaluation of noncommutative polynomials at an assignment `f : G → A` of the letters, as a
`ℂ`-algebra hom: a word goes to the product of the images of its letters. -/
def eval (f : G → A) : NCPoly G →ₐ[ℂ] A :=
  lift (FreeMonoid.lift f)

/-- Evaluation of a monomial. -/
@[simp] theorem eval_single (f : G → A) (w : FreeMonoid G) (c : ℂ) :
    eval f (single w c) = c • FreeMonoid.lift f w :=
  lift_single _ _ _

/-- Evaluation of a generator. -/
@[simp] theorem eval_gen (f : G → A) (g : G) : eval f (gen g) = f g := by
  simp [gen]

variable [StarRing A] [StarModule ℂ A]

/-- Evaluation at self-adjoint letters commutes with the stars. -/
theorem eval_star (f : G → A) (hf : ∀ g, IsSelfAdjoint (f g)) (x : NCPoly G) :
    eval f (star x) = star (eval f x) := by
  induction x using induction_linear with
  | zero => simp
  | add a b ha hb => rw [star_add, map_add, ha, hb, map_add, star_add]
  | single w c =>
    rw [star_single, eval_single, eval_single, star_smul, star_lift_eq_lift_reverse f hf]
    rfl

/-- Evaluation at self-adjoint letters, as a `⋆`-algebra hom. -/
def evalStar (f : G → A) (hf : ∀ g, IsSelfAdjoint (f g)) : NCPoly G →⋆ₐ[ℂ] A :=
  { eval f with map_star' := eval_star f hf }

/-- The `⋆`-algebra hom of an evaluation is the evaluation. -/
@[simp] theorem evalStar_apply (f : G → A) (hf : ∀ g, IsSelfAdjoint (f g)) (x : NCPoly G) :
    evalStar f hf x = eval f x := rfl

end Eval

end NCPoly

end MIPRE
