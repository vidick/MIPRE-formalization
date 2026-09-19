/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Games

/-!
# The value of a POVM strategy, and its conditional failures

`MIPRE.TensorProductStrategy` is projective by construction, which is the right definition of
the quantum value (`lem:povm-value-eq` says allowing POVMs changes nothing). But a *soundness*
argument often has to start from an arbitrary POVM strategy --- blueprint
`lem:ms-direct-anticomm` is stated for one, and its whole point is that no projectivity is
assumed --- so this file gives the unbundled value of a POVM strategy and the conditional
failure probabilities that soundness arguments actually consume.

Nothing here is bundled into a structure: the data is a state and two question-indexed families
of POVMs on arbitrary finite local spaces, which is how it arrives.

## Main definitions

- `MIPRE.bornProb`: `⟨ψ| E_A ⊗ E_B |ψ⟩`, as a real;
- `MIPRE.povmValue`: the value of a POVM strategy;
- `MIPRE.condFail`: the failure probability *conditioned* on a question pair.

## Main statements

- `MIPRE.sum_bornProb`: the Born probabilities of a pair of POVMs sum to one on a unit vector;
- `MIPRE.one_sub_povmValue_eq`: the failure probability is the average of the conditional ones;
- `MIPRE.condFail_le_div`: a conditional failure is at most the failure probability divided by
  the question pair's weight. This is the step that turns "fails with probability `ε`" into a
  bound on each subtest, and the division by the weight is why soundness constants carry the
  number of subtests.
-/

noncomputable section

namespace MIPRE

open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder

/-! ## Linearity of the quadratic form and of the Kronecker product

Mathlib states neither over a `Finset` sum. -/

theorem sum_quadForm {N ι : Type*} [Fintype N] (ψ : N → ℂ) (s : Finset ι)
    (f : ι → Matrix N N ℂ) :
    star ψ ⬝ᵥ ((∑ i ∈ s, f i) *ᵥ ψ) = ∑ i ∈ s, star ψ ⬝ᵥ ((f i) *ᵥ ψ) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Matrix.add_mulVec, dotProduct_add, ih, Finset.sum_insert hi]

theorem kronecker_sum_right {dA dB ι : Type*} (M : Matrix dA dA ℂ) (s : Finset ι)
    (f : ι → Matrix dB dB ℂ) : M ⊗ₖ (∑ i ∈ s, f i) = ∑ i ∈ s, M ⊗ₖ f i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Matrix.kronecker_add, ih, Finset.sum_insert hi]

theorem sum_kronecker_left {dA dB ι : Type*} (s : Finset ι) (f : ι → Matrix dA dA ℂ)
    (N : Matrix dB dB ℂ) : (∑ i ∈ s, f i) ⊗ₖ N = ∑ i ∈ s, f i ⊗ₖ N := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Matrix.add_kronecker, ih, Finset.sum_insert hi]

/-- A POVM's elements sum to the identity matrix (its own `normalized` lives in the
self-adjoint subalgebra). -/
theorem POVM.sum_val {A d : Type*} [Fintype A] [Fintype d] [DecidableEq d] (M : POVM A d) :
    ∑ a, ((M.mats a).val) = (1 : Matrix d d ℂ) := by
  rw [← AddSubmonoidClass.coe_finsetSum, M.normalized]
  rfl

/-- A POVM's elements are positive semidefinite, as bare matrices. -/
theorem POVM.posSemidef {A d : Type*} [Fintype A] [Fintype d] [DecidableEq d] (M : POVM A d)
    (a : A) : ((M.mats a).val).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (Subtype.coe_le_coe.mpr (M.nonneg a))

/-- Each POVM element is at most the identity. -/
theorem POVM.le_one {A d : Type*} [Fintype A] [Fintype d] [DecidableEq d] (M : POVM A d)
    (p : A) : ((M.mats p).val) ≤ (1 : Matrix d d ℂ) := by
  rw [← POVM.sum_val M]
  exact Finset.single_le_sum (fun a _ => Subtype.coe_le_coe.mpr (M.nonneg a)) (Finset.mem_univ p)

/-- **The difference of two POVM elements is a self-adjoint contraction.** This is what makes a
two-outcome coarse-graining of a POVM a `±1`-observable in every estimate: `X† = X` and
`X† X ≤ 1`, with no projectivity. Outcomes other than the two chosen contribute nothing. -/
theorem POVM.sub_mul_self_le_one {A d : Type*} [Fintype A] [Fintype d] [DecidableEq d]
    (M : POVM A d) (p q : A) :
    (((M.mats p).val - (M.mats q).val) * ((M.mats p).val - (M.mats q).val))
      ≤ (1 : Matrix d d ℂ) := by
  set X := ((M.mats p).val - (M.mats q).val) with hX
  have h1 : (0 : Matrix d d ℂ) ≤ 1 - X := by
    have hsplit : (1 : Matrix d d ℂ) - X = (1 - (M.mats p).val) + (M.mats q).val := by
      rw [hX]; abel
    rw [hsplit]
    exact add_nonneg (sub_nonneg.mpr (M.le_one p)) (Subtype.coe_le_coe.mpr (M.nonneg q))
  have h2 : (0 : Matrix d d ℂ) ≤ 1 + X := by
    have hsplit : (1 : Matrix d d ℂ) + X = (1 - (M.mats q).val) + (M.mats p).val := by
      rw [hX]; abel
    rw [hsplit]
    exact add_nonneg (sub_nonneg.mpr (M.le_one q)) (Subtype.coe_le_coe.mpr (M.nonneg p))
  have hc : Commute ((1 : Matrix d d ℂ) - X) (1 + X) := by
    show ((1 : Matrix d d ℂ) - X) * (1 + X) = (1 + X) * (1 - X)
    noncomm_ring
  have hprod : (0 : Matrix d d ℂ) ≤ ((1 : Matrix d d ℂ) - X) * (1 + X) := hc.mul_nonneg h1 h2
  have heq : ((1 : Matrix d d ℂ) - X) * (1 + X) = 1 - X * X := by noncomm_ring
  rw [heq] at hprod
  exact sub_nonneg.mp hprod

/-- The difference of two POVM elements is self-adjoint. -/
theorem POVM.sub_conjTranspose {A d : Type*} [Fintype A] [Fintype d] [DecidableEq d]
    (M : POVM A d) (p q : A) :
    (((M.mats p).val - (M.mats q).val))ᴴ = ((M.mats p).val - (M.mats q).val) := by
  rw [Matrix.conjTranspose_sub, ← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose,
    (M.mats p).2, (M.mats q).2]

/-! ## Born probabilities -/

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-- `⟨ψ| E_A ⊗ E_B |ψ⟩`, the Born-rule probability of an outcome pair. -/
def bornProb (ψ : dA × dB → ℂ) (EA : Matrix dA dA ℂ) (EB : Matrix dB dB ℂ) : ℝ :=
  (star ψ ⬝ᵥ ((EA ⊗ₖ EB) *ᵥ ψ)).re

omit [DecidableEq dA] [DecidableEq dB] in
theorem bornProb_nonneg (ψ : dA × dB → ℂ) {EA : Matrix dA dA ℂ} {EB : Matrix dB dB ℂ}
    (hA : EA.PosSemidef) (hB : EB.PosSemidef) : 0 ≤ bornProb ψ EA EB :=
  (Complex.nonneg_iff.mp ((hA.kronecker hB).dotProduct_mulVec_nonneg ψ)).1

/-- **The Born probabilities of a pair of POVMs sum to one.** -/
theorem sum_bornProb {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (MA : POVM A dA)
    (MB : POVM B dB) :
    ∑ a, ∑ b, bornProb ψ (((MA.mats a).val)) (((MB.mats b).val)) = 1 := by
  classical
  have hker : ∑ a, ∑ b, (((MA.mats a).val) ⊗ₖ ((MB.mats b).val))
      = (1 : Matrix (dA × dB) (dA × dB) ℂ) := by
    have hb : ∀ a, ∑ b, (((MA.mats a).val) ⊗ₖ ((MB.mats b).val))
        = (((MA.mats a).val) ⊗ₖ (1 : Matrix dB dB ℂ)) := fun a => by
      rw [← kronecker_sum_right, POVM.sum_val]
    rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => hb a, ← sum_kronecker_left,
      POVM.sum_val, Matrix.one_kronecker_one]
  have h := sum_quadForm ψ (univ : Finset A)
    fun a => ∑ b, (((MA.mats a).val) ⊗ₖ ((MB.mats b).val))
  rw [hker, Matrix.one_mulVec, hψ] at h
  have h2 : ∀ a, (star ψ ⬝ᵥ ((∑ b, (((MA.mats a).val) ⊗ₖ ((MB.mats b).val))) *ᵥ ψ))
      = ∑ b, star ψ ⬝ᵥ ((((MA.mats a).val) ⊗ₖ ((MB.mats b).val)) *ᵥ ψ) :=
    fun a => sum_quadForm ψ _ _
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => h2 a] at h
  have h3 := congrArg Complex.re h
  rw [Complex.re_sum, Complex.one_re] at h3
  have hgoal : ∑ a, ∑ b, bornProb ψ (((MA.mats a).val)) (((MB.mats b).val))
      = ∑ a, (∑ b, star ψ ⬝ᵥ ((((MA.mats a).val) ⊗ₖ ((MB.mats b).val)) *ᵥ ψ)).re :=
    Finset.sum_congr rfl fun a _ => (Complex.re_sum _ _).symm
  rw [hgoal, ← h3]

/-! ## The value and the conditional failures -/

/-- The accepted probability at a fixed question pair. -/
def condWin (G : Game X Y A B) (ψ : dA × dB → ℂ) (MA : X → POVM A dA) (MB : Y → POVM B dB)
    (x : X) (y : Y) : ℝ :=
  ∑ a, ∑ b, (if G.D x y a b then 1 else 0)
    * bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val)

/-- **The value of a POVM strategy**: the average over question pairs of the accepted
probability. For a projective strategy this is `TensorProductStrategy.value`. -/
def povmValue (G : Game X Y A B) (ψ : dA × dB → ℂ) (MA : X → POVM A dA)
    (MB : Y → POVM B dB) : ℝ :=
  ∑ x, ∑ y, G.μ x y * condWin G ψ MA MB x y

/-- The failure probability *conditioned* on the question pair `(x, y)`. -/
def condFail (G : Game X Y A B) (ψ : dA × dB → ℂ) (MA : X → POVM A dA) (MB : Y → POVM B dB)
    (x : X) (y : Y) : ℝ :=
  1 - condWin G ψ MA MB x y

variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}

theorem condWin_nonneg (x : X) (y : Y) : 0 ≤ condWin G ψ MA MB x y :=
  Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by
    refine mul_nonneg (by split_ifs <;> norm_num) ?_
    exact bornProb_nonneg ψ ((MA x).posSemidef a) ((MB y).posSemidef b)

theorem condWin_le_one (hψ : star ψ ⬝ᵥ ψ = 1) (x : X) (y : Y) :
    condWin G ψ MA MB x y ≤ 1 := by
  rw [← sum_bornProb hψ (MA x) (MB y)]
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  have hb : 0 ≤ bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val) :=
    bornProb_nonneg ψ ((MA x).posSemidef a) ((MB y).posSemidef b)
  by_cases h : G.D x y a b
  · rw [if_pos h, one_mul]
  · rw [if_neg h, zero_mul]
    exact hb

theorem condFail_nonneg (hψ : star ψ ⬝ᵥ ψ = 1) (x : X) (y : Y) :
    0 ≤ condFail G ψ MA MB x y :=
  sub_nonneg.mpr (condWin_le_one hψ x y)

/-- **The failure probability is the average of the conditional failures.** -/
theorem one_sub_povmValue_eq :
    1 - povmValue G ψ MA MB = ∑ x, ∑ y, G.μ x y * condFail G ψ MA MB x y := by
  have h : ∑ x, ∑ y, G.μ x y * condFail G ψ MA MB x y
      = (∑ x, ∑ y, G.μ x y) - ∑ x, ∑ y, G.μ x y * condWin G ψ MA MB x y := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => by rw [condFail]; ring
  rw [h, G.μ_sum_one, povmValue]

/-- **From a failure bound to a bound on one subtest.** -/
theorem condFail_le_div (hψ : star ψ ⬝ᵥ ψ = 1) {ε : ℝ} (hfail : 1 - povmValue G ψ MA MB ≤ ε)
    {x : X} {y : Y} (hμ : 0 < G.μ x y) :
    condFail G ψ MA MB x y ≤ ε / G.μ x y := by
  have hterm : G.μ x y * condFail G ψ MA MB x y ≤ ∑ x', ∑ y', G.μ x' y' * condFail G ψ MA MB x' y' := by
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun x' => ∑ y', G.μ x' y' * condFail G ψ MA MB x' y') ?_ (Finset.mem_univ x))
    · exact Finset.single_le_sum
        (f := fun y' => G.μ x y' * condFail G ψ MA MB x y')
        (fun y' _ => mul_nonneg (G.μ_nonneg x y') (condFail_nonneg hψ x y')) (Finset.mem_univ y)
    · exact fun x' _ => Finset.sum_nonneg fun y' _ =>
        mul_nonneg (G.μ_nonneg x' y') (condFail_nonneg hψ x' y')
  rw [← one_sub_povmValue_eq] at hterm
  rw [le_div_iff₀ hμ, mul_comm]
  exact le_trans hterm hfail

end MIPRE

end
