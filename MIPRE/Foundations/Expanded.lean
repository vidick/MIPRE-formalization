/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.CrossConsistency

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
open scoped Kronecker

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

end MIPRE

end
