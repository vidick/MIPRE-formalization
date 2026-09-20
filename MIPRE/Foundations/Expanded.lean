/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.CrossConsistency
import MIPRE.Foundations.PVM

/-!
# The expanded state, and an inert ancilla

The expansion stage of the Pauli appendix (`sec:expanding`) adjoins a maximally entangled pair of
ancilla registers to each player and then **re-bipartitions**: Alice's party becomes her own
register together with her half of the ancilla, and Bob's becomes his register together with the
*other* half. This file is that construction, for an arbitrary ancilla state.

## The one thing it has to support

Every statement of the expansion stage is a norm on the expanded state, and the operators that
appear are of the form `M (x) N` --- the strategy's own operator on the original register, the
ancilla's on the adjoined one. Two facts carry all of them:

* `mulVec_kron_expVec`: such an operator acts on a product state factor by factor, so the whole
  computation splits;
* `norm_evec_expVec`: the norm of a product state is the product of the norms.

Together they say that an operator with an **inert ancilla**, `M (x) Id`, has the same state-norm
on the expanded state as `M` has on the original one, provided the ancilla state is a unit vector
(`norm_stateVec_expVec_kron_one`). That is what lets a bound proved before the expansion be used
after it, which is how the expansion stage consumes `lem:qld-obs-commutation`.
-/

noncomputable section

namespace MIPRE

open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder

variable {dA dB anc anc' : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  [Fintype anc] [DecidableEq anc] [Fintype anc'] [DecidableEq anc']

set_option linter.unusedSectionVars false

/-- **The expanded state**: the strategy's state on the original registers, tensored with an
ancilla state whose two halves go to the two *different* parties. -/
def expVec (ψ : dA × dB → ℂ) (e : anc × anc' → ℂ) : (dA × anc) × (dB × anc') → ℂ :=
  fun p => ψ (p.1.1, p.2.1) * e (p.1.2, p.2.2)

/-- The reindexing that separates the two systems from the two parties. -/
def expEquiv (dA dB anc anc' : Type*) :
    ((dA × anc) × (dB × anc')) ≃ ((dA × dB) × (anc × anc')) where
  toFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  invFun q := ((q.1.1, q.2.1), (q.1.2, q.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- A product of sums as a sum over the product. -/
theorem sum_prod_mul {X Y M : Type*} [Fintype X] [Fintype Y] [CommRing M] (f : X → M)
    (g : Y → M) : ∑ q : X × Y, f q.1 * g q.2 = (∑ x, f x) * ∑ y, g y := by
  rw [Finset.sum_mul_sum, Fintype.sum_prod_type]

/-- **The norm of a product state is the product of the norms.** -/
theorem norm_evec_expVec (u : dA × dB → ℂ) (v : anc × anc' → ℂ) :
    ‖evec (expVec u v)‖ = ‖evec u‖ * ‖evec v‖ := by
  classical
  rw [evec, evec, evec, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq,
    ← Real.sqrt_mul (Finset.sum_nonneg fun _ _ => by positivity)]
  congr 1
  rw [show (∑ p : (dA × anc) × (dB × anc'), ‖(WithLp.toLp 2 (expVec u v)).ofLp p‖ ^ 2)
      = ∑ q : (dA × dB) × (anc × anc'),
          (fun x : dA × dB => ‖u x‖ ^ 2) q.1 * (fun y : anc × anc' => ‖v y‖ ^ 2) q.2 from
    Fintype.sum_equiv (expEquiv dA dB anc anc') _ _ fun p => by
      show ‖expVec u v p‖ ^ 2 = ‖u (p.1.1, p.2.1)‖ ^ 2 * ‖v (p.1.2, p.2.2)‖ ^ 2
      rw [expVec, norm_mul, mul_pow],
    ]
  exact sum_prod_mul (fun x : dA × dB => ‖u x‖ ^ 2) fun y : anc × anc' => ‖v y‖ ^ 2

/-- The expanded state's norm splits, so it is a unit vector when both factors are. -/
theorem expVec_dotProduct (ψ : dA × dB → ℂ) (e : anc × anc' → ℂ) :
    star (expVec ψ e) ⬝ᵥ expVec ψ e = (star ψ ⬝ᵥ ψ) * (star e ⬝ᵥ e) := by
  classical
  rw [dotProduct, dotProduct, dotProduct, ← sum_prod_mul]
  refine Fintype.sum_equiv (expEquiv dA dB anc anc') _ _ fun p => ?_
  obtain ⟨⟨a, x⟩, ⟨b, y⟩⟩ := p
  simp only [expEquiv, Equiv.coe_fn_mk, Pi.star_apply, expVec, star_mul']
  ring

theorem expVec_unit {ψ : dA × dB → ℂ} {e : anc × anc' → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (he : star e ⬝ᵥ e = 1) : star (expVec ψ e) ⬝ᵥ expVec ψ e = 1 := by
  rw [expVec_dotProduct, hψ, he, mul_one]

/-- **An operator of product form acts on the expanded state factor by factor.** -/
theorem mulVec_kron_expVec (ψ : dA × dB → ℂ) (e : anc × anc' → ℂ) (M : Matrix dA dA ℂ)
    (N : Matrix anc anc ℂ) :
    (((M ⊗ₖ N) ⊗ₖ (1 : Matrix (dB × anc') (dB × anc') ℂ)) *ᵥ expVec ψ e)
      = expVec ((M ⊗ₖ (1 : Matrix dB dB ℂ)) *ᵥ ψ) ((N ⊗ₖ (1 : Matrix anc' anc' ℂ)) *ᵥ e) := by
  classical
  rw [show (1 : Matrix (dB × anc') (dB × anc') ℂ)
      = (1 : Matrix dB dB ℂ) ⊗ₖ (1 : Matrix anc' anc' ℂ) from Matrix.one_kronecker_one.symm]
  funext p
  obtain ⟨⟨a, x⟩, ⟨b, y⟩⟩ := p
  show ∑ q : (dA × anc) × (dB × anc'),
      ((M ⊗ₖ N) ⊗ₖ ((1 : Matrix dB dB ℂ) ⊗ₖ (1 : Matrix anc' anc' ℂ)))
        ((a, x), (b, y)) q * expVec ψ e q
    = (∑ q : dA × dB, (M ⊗ₖ (1 : Matrix dB dB ℂ)) (a, b) q * ψ q)
      * ∑ q : anc × anc', (N ⊗ₖ (1 : Matrix anc' anc' ℂ)) (x, y) q * e q
  rw [← sum_prod_mul]
  refine Fintype.sum_equiv (expEquiv dA dB anc anc') _ _ fun q => ?_
  obtain ⟨⟨a₁, x₁⟩, ⟨b₁, y₁⟩⟩ := q
  simp only [expEquiv, Equiv.coe_fn_mk]
  show (M a a₁ * N x x₁) * ((1 : Matrix dB dB ℂ) b b₁ * (1 : Matrix anc' anc' ℂ) y y₁)
      * (ψ (a₁, b₁) * e (x₁, y₁))
    = (M a a₁ * (1 : Matrix dB dB ℂ) b b₁) * ψ (a₁, b₁)
      * ((N x x₁ * (1 : Matrix anc' anc' ℂ) y y₁) * e (x₁, y₁))
  ring

/-- **A unitary on the ancilla is invisible to the state-norm.** `D (x) U = (Id (x) U)(D (x) Id)`
and the front factor is unitary on the whole space. -/
theorem norm_stateVec_kron_unitary (v : (dA × anc) × (dB × anc') → ℂ) (D : Matrix dA dA ℂ)
    {U : Matrix anc anc ℂ} (hU : Uᴴ * U = 1) :
    ‖stateVec v (D ⊗ₖ U)‖ = ‖stateVec v (D ⊗ₖ (1 : Matrix anc anc ℂ))‖ := by
  have hfac : (D ⊗ₖ U) = ((1 : Matrix dA dA ℂ) ⊗ₖ U) * (D ⊗ₖ (1 : Matrix anc anc ℂ)) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  have hiso : (((1 : Matrix dA dA ℂ) ⊗ₖ U))ᴴ * ((1 : Matrix dA dA ℂ) ⊗ₖ U) = 1 := by
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, hU, Matrix.one_kronecker_one]
  rw [norm_stateVec_eq_snorm, norm_stateVec_eq_snorm, snorm, snorm, hfac, aOp_mul,
    ← Matrix.mulVec_mulVec]
  exact norm_evec_mulVec_of_isometry (isometry_aOp hiso) _

/-- **An inert ancilla changes nothing**: a bound proved before the expansion survives it. -/
theorem norm_stateVec_expVec_kron_one (ψ : dA × dB → ℂ) {e : anc × anc' → ℂ}
    (he : ‖evec e‖ = 1) (M : Matrix dA dA ℂ) :
    ‖stateVec (expVec ψ e) (M ⊗ₖ (1 : Matrix anc anc ℂ))‖ = ‖stateVec ψ M‖ := by
  rw [stateVec, show (WithLp.toLp 2 (((M ⊗ₖ (1 : Matrix anc anc ℂ))
      ⊗ₖ (1 : Matrix (dB × anc') (dB × anc') ℂ)) *ᵥ expVec ψ e)
      : EuclideanSpace ℂ ((dA × anc) × (dB × anc'))) = evec _ from rfl,
    mulVec_kron_expVec, norm_evec_expVec]
  rw [show ((1 : Matrix anc anc ℂ) ⊗ₖ (1 : Matrix anc' anc' ℂ)) *ᵥ e = e from by
      rw [Matrix.one_kronecker_one, Matrix.one_mulVec], he, mul_one]
  rfl

/-! ## Born probabilities on the expanded state

The expansion stage's consistency statements are about a measurement of product form, and what
they need is that its Born probabilities *factorize*. That is the same computation as
`mulVec_kron_expVec` with an operator on each party, plus the observation that both factors are
real because both operators are positive. -/

theorem expVec_dotProduct_of_pair (u u' : dA × dB → ℂ) (v v' : anc × anc' → ℂ) :
    star (expVec u v) ⬝ᵥ expVec u' v' = (star u ⬝ᵥ u') * (star v ⬝ᵥ v') := by
  classical
  rw [dotProduct, dotProduct, dotProduct, ← sum_prod_mul]
  refine Fintype.sum_equiv (expEquiv dA dB anc anc') _ _ fun p => ?_
  obtain ⟨⟨a, x⟩, ⟨b, y⟩⟩ := p
  simp only [expEquiv, Equiv.coe_fn_mk, Pi.star_apply, expVec, star_mul']
  ring

/-- **An operator of product form on each party acts factor by factor.** -/
theorem mulVec_kron_kron_expVec (ψ : dA × dB → ℂ) (e : anc × anc' → ℂ) (X : Matrix dA dA ℂ)
    (Y : Matrix anc anc ℂ) (X' : Matrix dB dB ℂ) (Y' : Matrix anc' anc' ℂ) :
    (((X ⊗ₖ Y) ⊗ₖ (X' ⊗ₖ Y')) *ᵥ expVec ψ e)
      = expVec ((X ⊗ₖ X') *ᵥ ψ) ((Y ⊗ₖ Y') *ᵥ e) := by
  classical
  funext p
  obtain ⟨⟨a, x⟩, ⟨b, y⟩⟩ := p
  show ∑ q : (dA × anc) × (dB × anc'),
      ((X ⊗ₖ Y) ⊗ₖ (X' ⊗ₖ Y')) ((a, x), (b, y)) q * expVec ψ e q
    = (∑ q : dA × dB, (X ⊗ₖ X') (a, b) q * ψ q)
      * ∑ q : anc × anc', (Y ⊗ₖ Y') (x, y) q * e q
  rw [← sum_prod_mul]
  refine Fintype.sum_equiv (expEquiv dA dB anc anc') _ _ fun q => ?_
  obtain ⟨⟨a₁, x₁⟩, ⟨b₁, y₁⟩⟩ := q
  simp only [expEquiv, Equiv.coe_fn_mk]
  show (X a a₁ * Y x x₁) * (X' b b₁ * Y' y y₁) * (ψ (a₁, b₁) * e (x₁, y₁))
    = (X a a₁ * X' b b₁) * ψ (a₁, b₁) * ((Y x x₁ * Y' y y₁) * e (x₁, y₁))
  ring

/-- **The Born probability of a product measurement on the expanded state factorizes.** Only the
ancilla's two operators need to be positive: that is what makes their quadratic form real, which is
what lets the real part of the product split. -/
theorem bornProb_expVec_kron (ψ : dA × dB → ℂ) (e : anc × anc' → ℂ) {X : Matrix dA dA ℂ}
    {Y : Matrix anc anc ℂ} {X' : Matrix dB dB ℂ} {Y' : Matrix anc' anc' ℂ}
    (hY : Y.PosSemidef) (hY' : Y'.PosSemidef) :
    bornProb (expVec ψ e) (X ⊗ₖ Y) (X' ⊗ₖ Y') = bornProb ψ X X' * bornProb e Y Y' := by
  have hre : ∀ (Z : Matrix (anc × anc') (anc × anc') ℂ), Z.PosSemidef →
      (star e ⬝ᵥ (Z *ᵥ e)).im = 0 :=
    fun Z hZ => ((Complex.nonneg_iff.mp (hZ.dotProduct_mulVec_nonneg e)).2).symm
  rw [bornProb, mulVec_kron_kron_expVec, expVec_dotProduct_of_pair, bornProb, bornProb,
    Complex.mul_re, hre _ (hY.kronecker hY'), mul_zero, sub_zero]

/-! ## Data processing, at the Born level

The state-dependent distance has **no** data-processing inequality --- NW19 states theirs for the
consistency distance and the remark following it gives a counterexample for `approx`. What is true,
and what every coarse-graining in the appendix uses, is that applying the *same* post-processing to
both players can only increase the probability that they agree. That is a statement about Born
probabilities, and it is proved here so that no consumer is tempted by the other form. -/

theorem bornProb_sum_sum {ι : Type*} (ψ : dA × dB → ℂ) (s t : Finset ι)
    (A : ι → Matrix dA dA ℂ) (B : ι → Matrix dB dB ℂ) :
    bornProb ψ (∑ i ∈ s, A i) (∑ j ∈ t, B j)
      = ∑ i ∈ s, ∑ j ∈ t, bornProb ψ (A i) (B j) := by
  classical
  simp only [bornProb]
  rw [sum_kronecker_left, sum_quadForm ψ _ _, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [kronecker_sum_right, sum_quadForm ψ _ _, Complex.re_sum]

/-- **Coarse-graining both players the same way can only increase agreement.** -/
theorem sum_bornProb_le_map {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (ψ : dA × dB → ℂ) (P : POVM ι dA) (Q : POVM ι dB) (f : ι → κ) :
    ∑ i, bornProb ψ ((P.mats i).val) ((Q.mats i).val)
      ≤ ∑ k, bornProb ψ (((P.map f).mats k).val) (((Q.map f).mats k).val) := by
  classical
  have hfib : ∀ k : κ, bornProb ψ (((P.map f).mats k).val) (((Q.map f).mats k).val)
      = ∑ i ∈ univ.filter fun i => f i = k, ∑ j ∈ univ.filter fun j => f j = k,
          bornProb ψ ((P.mats i).val) ((Q.mats j).val) := by
    intro k
    rw [show (((P.map f).mats k).val)
        = ∑ i ∈ univ.filter fun i => f i = k, ((P.mats i).val) from
      AddSubmonoidClass.coe_finsetSum _ _,
      show (((Q.map f).mats k).val)
        = ∑ j ∈ univ.filter fun j => f j = k, ((Q.mats j).val) from
      AddSubmonoidClass.coe_finsetSum _ _, bornProb_sum_sum]
  rw [Finset.sum_congr rfl fun k (_ : k ∈ univ) => hfib k]
  have hdiag : ∀ k : κ, ∑ i ∈ univ.filter fun i => f i = k,
        bornProb ψ ((P.mats i).val) ((Q.mats i).val)
      ≤ ∑ i ∈ univ.filter fun i => f i = k, ∑ j ∈ univ.filter fun j => f j = k,
          bornProb ψ ((P.mats i).val) ((Q.mats j).val) := by
    intro k
    refine Finset.sum_le_sum fun i hi => ?_
    exact Finset.single_le_sum
      (fun j _ => bornProb_nonneg ψ (P.posSemidef i) (Q.posSemidef j)) hi
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum fun k (_ : k ∈ univ) => hdiag k)
  exact (Finset.sum_fiberwise (univ : Finset ι) f
    (fun i => bornProb ψ ((P.mats i).val) ((Q.mats i).val))).symm

/-! ## The product measurement -/

/-- **The product of two POVMs**, on the two systems of one party: outcomes the pairs, elements the
Kronecker products. -/
def POVM.kron {ι κ : Type*} [Fintype ι] [Fintype κ] (P : POVM ι dA) (Q : POVM κ anc) :
    POVM (ι × κ) (dA × anc) where
  mats p := ⟨((P.mats p.1).val) ⊗ₖ ((Q.mats p.2).val), by
    rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
      ← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose, (P.mats p.1).2,
      (Q.mats p.2).2]⟩
  nonneg p := Subtype.coe_le_coe.mp (Matrix.nonneg_iff_posSemidef.mpr
    ((P.posSemidef p.1).kronecker (Q.posSemidef p.2)))
  normalized := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    show ∑ p : ι × κ, ((P.mats p.1).val) ⊗ₖ ((Q.mats p.2).val) = 1
    rw [Fintype.sum_prod_type]
    rw [show (∑ i : ι, ∑ j : κ, ((P.mats i).val) ⊗ₖ ((Q.mats j).val))
        = ∑ i : ι, ((P.mats i).val) ⊗ₖ (∑ j : κ, ((Q.mats j).val)) from
      Finset.sum_congr rfl fun i _ => (kronecker_sum_right _ _ _).symm]
    rw [show (∑ j : κ, ((Q.mats j).val)) = 1 from by
        rw [← AddSubmonoidClass.coe_finsetSum, Q.normalized]; rfl]
    rw [← sum_kronecker_left, show (∑ i : ι, ((P.mats i).val)) = 1 from by
        rw [← AddSubmonoidClass.coe_finsetSum, P.normalized]; rfl,
      Matrix.one_kronecker_one]

@[simp] theorem POVM.kron_mats {ι κ : Type*} [Fintype ι] [Fintype κ] (P : POVM ι dA)
    (Q : POVM κ anc) (p : ι × κ) :
    (((P.kron Q).mats p).val) = ((P.mats p.1).val) ⊗ₖ ((Q.mats p.2).val) := rfl

/-- **Relabelling the two factors is relabelling the product.** -/
theorem POVM.kron_map {ι κ ι' κ' : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype ι'] [DecidableEq ι'] [Fintype κ'] [DecidableEq κ']
    (P : POVM ι dA) (Q : POVM κ anc) (f : ι → ι') (g : κ → κ') :
    (P.map f).kron (Q.map g) = (P.kron Q).map (fun p => (f p.1, g p.2)) := by
  classical
  refine POVM.ext' fun b => ?_
  have hfil : (Finset.univ.filter fun p : ι × κ => (f p.1, g p.2) = b)
      = (Finset.univ.filter fun i => f i = b.1) ×ˢ (Finset.univ.filter fun j => g j = b.2) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, Prod.ext_iff]
  rw [POVM.kron_mats, POVM.map_mats, POVM.map_mats, POVM.map_mats, hfil, Finset.sum_product,
    sum_kronecker_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [POVM.kron_mats]
  exact kronecker_sum_right _ _ _

/-! ## Projectivity of the constructions

The expansion stage's measurements are products of a strategy measurement with an ancilla
measurement, coarse-grained by adding the two outcomes, and the arguments downstream need them to
be **projective**. Two closures give that: a product of projective measurements is projective, and
so is any coarse-graining of one (`IsPVM.coarse`). -/

/-- **A product of projective measurements is projective.** -/
theorem isPVM_kron {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {P : ι → Matrix dA dA ℂ} {Q : κ → Matrix anc anc ℂ} (hP : IsPVM P) (hQ : IsPVM Q) :
    IsPVM (fun p : ι × κ => P p.1 ⊗ₖ Q p.2) where
  isSelfAdjoint p := by
    rw [Matrix.conjTranspose_kronecker, hP.isSelfAdjoint, hQ.isSelfAdjoint]
  idem p := by
    rw [← Matrix.mul_kronecker_mul, hP.idem, hQ.idem]
  sum_eq_one := by
    rw [Fintype.sum_prod_type,
      show (∑ i : ι, ∑ j : κ, P i ⊗ₖ Q j) = ∑ i : ι, P i ⊗ₖ (∑ j : κ, Q j) from
        Finset.sum_congr rfl fun i _ => (kronecker_sum_right _ _ _).symm,
      hQ.sum_eq_one, ← sum_kronecker_left, hP.sum_eq_one, Matrix.one_kronecker_one]

/-- **A coarse-graining of a projective POVM is projective**, in the `POVM.map` form the games
use. -/
theorem isPVM_povm_map {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (M : POVM A dA) (h : IsPVM fun a => ((M.mats a).val)) (f : A → B) :
    IsPVM fun b => (((M.map f).mats b).val) := by
  have hval : ∀ b : B, (((M.map f).mats b).val)
      = ∑ a ∈ Finset.univ.filter fun a => f a = b, ((M.mats a).val) := fun b =>
    AddSubmonoidClass.coe_finsetSum _ _
  simpa only [hval] using h.coarse f

/-- **A product of projective POVMs is projective**, in the `POVM.kron` form the expansion uses. -/
theorem isPVM_povm_kron {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (P : POVM ι dA) (Q : POVM κ anc) (hP : IsPVM fun i => ((P.mats i).val))
    (hQ : IsPVM fun j => ((Q.mats j).val)) :
    IsPVM fun p => (((P.kron Q).mats p).val) :=
  isPVM_kron hP hQ

end MIPRE

end
