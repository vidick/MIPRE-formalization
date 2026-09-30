/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.BipartiteModel
public import MIPRE.Foundations.Games
public import MIPRE.Foundations.Measurement

@[expose] public section

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

/-! ## Matrix POVMs are POVMs in the matrix algebra -/

/-- **A matrix POVM is a POVM in the matrix algebra** (`MIPRE/Foundations/Measurement.lean`):
the same three fields. -/
def POVM.toIn {A d : Type*} [Fintype A] [Fintype d] [DecidableEq d] (M : POVM A d) :
    POVMIn A (Matrix d d ℂ) :=
  ⟨M.mats, M.nonneg, M.normalized⟩

@[simp]
theorem POVM.toIn_op {A d : Type*} [Fintype A] [Fintype d] [DecidableEq d] (M : POVM A d)
    (a : A) : M.toIn.op a = (M.mats a).val :=
  rfl

/-- A POVM's elements sum to the identity matrix (its own `normalized` lives in the
self-adjoint subalgebra). -/
theorem POVM.sum_val {A d : Type*} [Fintype A] [Fintype d] [DecidableEq d] (M : POVM A d) :
    ∑ a, ((M.mats a).val) = (1 : Matrix d d ℂ) :=
  M.toIn.sum_op

/-- A POVM's elements are positive semidefinite, as bare matrices. -/
theorem POVM.posSemidef {A d : Type*} [Fintype A] [Fintype d] [DecidableEq d] (M : POVM A d)
    (a : A) : ((M.mats a).val).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (Subtype.coe_le_coe.mpr (M.nonneg a))

/-- Each POVM element is at most the identity. -/
theorem POVM.le_one {A d : Type*} [Fintype A] [Fintype d] [DecidableEq d] (M : POVM A d)
    (p : A) : ((M.mats p).val) ≤ (1 : Matrix d d ℂ) :=
  M.toIn.op_le_one p

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

/-! ## Born probabilities, values and conditional failures in a bipartite model -/

namespace BipartiteModel

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] (M : BipartiteModel 𝒞 𝒜 ℬ)

/-- `⟨ψ| πA a πB b |ψ⟩`, the Born-rule probability of an outcome pair. -/
def bornProb (a : 𝒜) (b : ℬ) : ℝ := M.qform (M.πA a * M.πB b)

theorem bornProb_sum_left {ι : Type*} (s : Finset ι) (f : ι → 𝒜) (b : ℬ) :
    M.bornProb (∑ i ∈ s, f i) b = ∑ i ∈ s, M.bornProb (f i) b := by
  unfold bornProb
  rw [map_sum, Finset.sum_mul, M.qform_sum]

theorem bornProb_sum_right {ι : Type*} (a : 𝒜) (s : Finset ι) (g : ι → ℬ) :
    M.bornProb a (∑ i ∈ s, g i) = ∑ i ∈ s, M.bornProb a (g i) := by
  unfold bornProb
  rw [map_sum, Finset.mul_sum, M.qform_sum]

/-- **Exchanging the players exchanges the two factors of a Born probability**, because the two
players' operators commute. -/
theorem bornProb_swap (a : 𝒜) (b : ℬ) : M.swap.bornProb b a = M.bornProb a b := by
  show M.qform (M.πB b * M.πA a) = M.qform (M.πA a * M.πB b)
  rw [(M.commute a b).eq]

section Order

variable [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ]

omit [PartialOrder ℬ] [StarOrderedRing ℬ] in
/-- A nonnegative element of the first player's algebra is represented by a positive
operator. -/
theorem π_πA_nonneg {a : 𝒜} (ha : 0 ≤ a) : 0 ≤ M.π (M.πA a) :=
  map_nonneg (M.π.comp M.πA) ha

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] in
/-- A nonnegative element of the second player's algebra is represented by a positive
operator. -/
theorem π_πB_nonneg {b : ℬ} (hb : 0 ≤ b) : 0 ≤ M.π (M.πB b) :=
  map_nonneg (M.π.comp M.πB) hb

/-- **Born probabilities of nonnegative elements are nonnegative**: the two players'
positive operators commute, so their product is positive. -/
theorem bornProb_nonneg {a : 𝒜} {b : ℬ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ M.bornProb a b := by
  have hc : Commute (M.π (M.πA a)) (M.π (M.πB b)) := (M.commute a b).map M.π
  refine M.qform_nonneg ?_
  rw [map_mul]
  exact hc.mul_nonneg (M.π_πA_nonneg ha) (M.π_πB_nonneg hb)

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

omit [StarOrderedRing 𝒜] [StarOrderedRing ℬ] in
/-- **The Born probabilities of a pair of POVMs sum to one** on a unit vector. -/
theorem sum_bornProb (hψ : ‖M.ψ‖ = 1) (MA : POVMIn A 𝒜) (MB : POVMIn B ℬ) :
    ∑ a, ∑ b, M.bornProb (MA.op a) (MB.op b) = 1 := by
  have hsum : ∑ a, ∑ b, M.πA (MA.op a) * M.πB (MB.op b) = 1 := by
    simp_rw [← Finset.mul_sum, ← map_sum, MB.sum_op, map_one, mul_one, ← map_sum, MA.sum_op,
      map_one]
  unfold bornProb
  simp_rw [← M.qform_sum]
  rw [hsum, M.qform_one hψ]

/-- The accepted probability at a fixed question pair. -/
def condWin (G : Game X Y A B) (MA : X → POVMIn A 𝒜) (MB : Y → POVMIn B ℬ) (x : X) (y : Y) :
    ℝ :=
  ∑ a, ∑ b, (if G.D x y a b then 1 else 0) * M.bornProb ((MA x).op a) ((MB y).op b)

/-- **The value of a POVM strategy** in the model. -/
def povmValue (G : Game X Y A B) (MA : X → POVMIn A 𝒜) (MB : Y → POVMIn B ℬ) : ℝ :=
  ∑ x, ∑ y, G.μ x y * M.condWin G MA MB x y

/-- The failure probability *conditioned* on the question pair `(x, y)`. -/
def condFail (G : Game X Y A B) (MA : X → POVMIn A 𝒜) (MB : Y → POVMIn B ℬ) (x : X) (y : Y) :
    ℝ :=
  1 - M.condWin G MA MB x y

variable {G : Game X Y A B} {MA : X → POVMIn A 𝒜} {MB : Y → POVMIn B ℬ}

theorem condWin_nonneg (x : X) (y : Y) : 0 ≤ M.condWin G MA MB x y :=
  Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
    mul_nonneg (by split_ifs <;> norm_num)
      (M.bornProb_nonneg ((MA x).op_nonneg a) ((MB y).op_nonneg b))

theorem condWin_le_one (hψ : ‖M.ψ‖ = 1) (x : X) (y : Y) : M.condWin G MA MB x y ≤ 1 := by
  rw [← M.sum_bornProb hψ (MA x) (MB y)]
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  have hb := M.bornProb_nonneg ((MA x).op_nonneg a) ((MB y).op_nonneg b)
  by_cases h : G.D x y a b
  · rw [ite_eq_left h, one_mul]
  · rw [ite_eq_right h, zero_mul]
    exact hb

theorem condFail_nonneg (hψ : ‖M.ψ‖ = 1) (x : X) (y : Y) : 0 ≤ M.condFail G MA MB x y :=
  sub_nonneg.mpr (M.condWin_le_one hψ x y)

omit [StarOrderedRing 𝒜] [StarOrderedRing ℬ] in
/-- **The failure probability is the average of the conditional failures.** -/
theorem one_sub_povmValue_eq :
    1 - M.povmValue G MA MB = ∑ x, ∑ y, G.μ x y * M.condFail G MA MB x y := by
  have h : ∑ x, ∑ y, G.μ x y * M.condFail G MA MB x y
      = (∑ x, ∑ y, G.μ x y) - ∑ x, ∑ y, G.μ x y * M.condWin G MA MB x y := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => by rw [condFail]; ring
  rw [h, G.μ_sum_one, povmValue]

/-- **From a failure bound to a bound on one subtest.** -/
theorem condFail_le_div (hψ : ‖M.ψ‖ = 1) {ε : ℝ} (hfail : 1 - M.povmValue G MA MB ≤ ε)
    {x : X} {y : Y} (hμ : 0 < G.μ x y) :
    M.condFail G MA MB x y ≤ ε / G.μ x y := by
  have hterm : G.μ x y * M.condFail G MA MB x y ≤
      ∑ x', ∑ y', G.μ x' y' * M.condFail G MA MB x' y' := by
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun x' => ∑ y', G.μ x' y' * M.condFail G MA MB x' y') ?_ (Finset.mem_univ x))
    · exact Finset.single_le_sum
        (f := fun y' => G.μ x y' * M.condFail G MA MB x y')
        (fun y' _ => mul_nonneg (G.μ_nonneg x y') (M.condFail_nonneg hψ x y'))
        (Finset.mem_univ y)
    · exact fun x' _ => Finset.sum_nonneg fun y' _ =>
        mul_nonneg (G.μ_nonneg x' y') (M.condFail_nonneg hψ x' y')
  rw [← M.one_sub_povmValue_eq] at hterm
  rw [le_div_iff₀ hμ, mul_comm]
  exact le_trans hterm hfail

end Order

end BipartiteModel

/-! ## Born probabilities of matrices

The matrix Born probabilities, values and conditional failures are those of the tensor-product
model (`bornProb_eq_tensor`, `condWin_eq_tensor`, `povmValue_eq_tensor`, `condFail_eq_tensor`),
and their rules are the model's. -/

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-- `⟨ψ| E_A ⊗ E_B |ψ⟩`, the Born-rule probability of an outcome pair. -/
def bornProb (ψ : dA × dB → ℂ) (EA : Matrix dA dA ℂ) (EB : Matrix dB dB ℂ) : ℝ :=
  (star ψ ⬝ᵥ ((EA ⊗ₖ EB) *ᵥ ψ)).re

/-- **The matrix Born probability is that of the tensor-product model.** -/
theorem bornProb_eq_tensor (ψ : dA × dB → ℂ) (EA : Matrix dA dA ℂ) (EB : Matrix dB dB ℂ) :
    bornProb ψ EA EB = (BipartiteModel.tensor ψ).bornProb EA EB := by
  rw [BipartiteModel.bornProb, BipartiteModel.tensor_πA, BipartiteModel.tensor_πB,
    BipartiteModel.qform_tensor, qform, bornProb, aOp, bOp, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one, Matrix.one_mul]

/-- A unit vector of `ℂ^N`, as a unit vector of `EuclideanSpace ℂ N`. -/
theorem norm_evec_eq_one {N : Type*} [Fintype N] {ψ : N → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) :
    ‖evec ψ‖ = 1 := by
  have h := norm_evec_sq ψ
  rw [hψ, Complex.one_re] at h
  nlinarith [norm_nonneg (evec ψ)]

omit [DecidableEq dA] [DecidableEq dB] in
theorem bornProb_nonneg (ψ : dA × dB → ℂ) {EA : Matrix dA dA ℂ} {EB : Matrix dB dB ℂ}
    (hA : EA.PosSemidef) (hB : EB.PosSemidef) : 0 ≤ bornProb ψ EA EB := by
  classical
  rw [bornProb_eq_tensor]
  exact (BipartiteModel.tensor ψ).bornProb_nonneg (Matrix.nonneg_iff_posSemidef.mpr hA)
    (Matrix.nonneg_iff_posSemidef.mpr hB)

/-- **The Born probabilities of a pair of POVMs sum to one.** -/
theorem sum_bornProb {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (MA : POVM A dA)
    (MB : POVM B dB) :
    ∑ a, ∑ b, bornProb ψ (((MA.mats a).val)) (((MB.mats b).val)) = 1 := by
  simp only [bornProb_eq_tensor]
  exact (BipartiteModel.tensor ψ).sum_bornProb (norm_evec_eq_one hψ) MA.toIn MB.toIn

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

theorem condWin_eq_tensor (x : X) (y : Y) :
    condWin G ψ MA MB x y =
      (BipartiteModel.tensor ψ).condWin G (fun x => (MA x).toIn) (fun y => (MB y).toIn) x y := by
  simp only [condWin, BipartiteModel.condWin, bornProb_eq_tensor, POVM.toIn_op]

theorem povmValue_eq_tensor :
    povmValue G ψ MA MB =
      (BipartiteModel.tensor ψ).povmValue G (fun x => (MA x).toIn) (fun y => (MB y).toIn) := by
  simp only [povmValue, BipartiteModel.povmValue, condWin_eq_tensor]

theorem condFail_eq_tensor (x : X) (y : Y) :
    condFail G ψ MA MB x y =
      (BipartiteModel.tensor ψ).condFail G (fun x => (MA x).toIn) (fun y => (MB y).toIn) x y := by
  simp only [condFail, BipartiteModel.condFail, condWin_eq_tensor]

theorem condWin_nonneg (x : X) (y : Y) : 0 ≤ condWin G ψ MA MB x y := by
  rw [condWin_eq_tensor]
  exact (BipartiteModel.tensor ψ).condWin_nonneg x y

theorem condWin_le_one (hψ : star ψ ⬝ᵥ ψ = 1) (x : X) (y : Y) :
    condWin G ψ MA MB x y ≤ 1 := by
  rw [condWin_eq_tensor]
  exact (BipartiteModel.tensor ψ).condWin_le_one (norm_evec_eq_one hψ) x y

theorem condFail_nonneg (hψ : star ψ ⬝ᵥ ψ = 1) (x : X) (y : Y) :
    0 ≤ condFail G ψ MA MB x y := by
  rw [condFail_eq_tensor]
  exact (BipartiteModel.tensor ψ).condFail_nonneg (norm_evec_eq_one hψ) x y

/-- **The failure probability is the average of the conditional failures.** -/
theorem one_sub_povmValue_eq :
    1 - povmValue G ψ MA MB = ∑ x, ∑ y, G.μ x y * condFail G ψ MA MB x y := by
  simp only [povmValue_eq_tensor, condFail_eq_tensor]
  exact (BipartiteModel.tensor ψ).one_sub_povmValue_eq

/-- **From a failure bound to a bound on one subtest.** -/
theorem condFail_le_div (hψ : star ψ ⬝ᵥ ψ = 1) {ε : ℝ} (hfail : 1 - povmValue G ψ MA MB ≤ ε)
    {x : X} {y : Y} (hμ : 0 < G.μ x y) :
    condFail G ψ MA MB x y ≤ ε / G.μ x y := by
  rw [condFail_eq_tensor]
  rw [povmValue_eq_tensor] at hfail
  exact (BipartiteModel.tensor ψ).condFail_le_div (norm_evec_eq_one hψ) hfail hμ

/-! ## The value of a commuting-operator strategy is a value in its model

A commuting-operator strategy's measurements are POVMs in the two players' algebras of its model
(`CommutingOperatorStrategy.toModel`), and its value is the model's value of them. So `ω_co` is
the supremum of `povmValue` over the models of commuting-operator strategies, which is how every
statement about `povmValue` in a model becomes one about `ω_co`. -/

namespace CommutingOperatorStrategy

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The first player's measurement at a question, as a POVM in the first player's algebra of the
strategy's model. -/
noncomputable def aliceMeas (S : CommutingOperatorStrategy X Y A B) (x : X) :
    POVMIn A S.aliceAlg where
  mats a := ⟨⟨S.E x a, S.E_mem_aliceAlg x a⟩,
    selfAdjoint.mem_iff.mpr (Subtype.ext (S.E_pos x a).isSelfAdjoint.star_eq)⟩
  nonneg a := Subtype.coe_le_coe.mp (Subtype.coe_le_coe.mp
    (ContinuousLinearMap.nonneg_iff_isPositive.2 (S.E_pos x a)))
  normalized := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact S.E_sum x

/-- The second player's measurement at a question, as a POVM in the second player's algebra of
the strategy's model. -/
noncomputable def bobMeas (S : CommutingOperatorStrategy X Y A B) (y : Y) :
    POVMIn B S.bobAlg where
  mats b := ⟨⟨S.F y b, S.F_mem_bobAlg y b⟩,
    selfAdjoint.mem_iff.mpr (Subtype.ext (S.F_pos y b).isSelfAdjoint.star_eq)⟩
  nonneg b := Subtype.coe_le_coe.mp (Subtype.coe_le_coe.mp
    (ContinuousLinearMap.nonneg_iff_isPositive.2 (S.F_pos y b)))
  normalized := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact S.F_sum y

@[simp]
theorem aliceMeas_op (S : CommutingOperatorStrategy X Y A B) (x : X) (a : A) :
    ((S.aliceMeas x).op a : S.H →L[ℂ] S.H) = S.E x a := rfl

@[simp]
theorem bobMeas_op (S : CommutingOperatorStrategy X Y A B) (y : Y) (b : B) :
    ((S.bobMeas y).op b : S.H →L[ℂ] S.H) = S.F y b := rfl

/-- **The correlation of a strategy is the Born probability of its model.** -/
theorem correlation_eq_bornProb (S : CommutingOperatorStrategy X Y A B) (x : X) (y : Y) (a : A)
    (b : B) :
    S.correlation x y a b = S.toModel.bornProb ((S.aliceMeas x).op a) ((S.bobMeas y).op b) :=
  rfl

/-- **The value of a commuting-operator strategy is the value of its measurements in its
model.** -/
theorem value_eq_povmValue (S : CommutingOperatorStrategy X Y A B) (G : Game X Y A B) :
    S.value G = S.toModel.povmValue G S.aliceMeas S.bobMeas := by
  unfold value BipartiteModel.povmValue BipartiteModel.condWin
  simp only [Finset.mul_sum, mul_assoc]
  rfl

end CommutingOperatorStrategy

/-- **`ω_co` is the supremum of the model values of commuting-operator strategies.** -/
theorem commutingOperatorValue_eq_iSup_povmValue {X Y A B : Type*} [Fintype X] [Fintype Y]
    [Fintype A] [Fintype B] (G : Game X Y A B) :
    commutingOperatorValue G
      = ⨆ S : CommutingOperatorStrategy X Y A B, S.toModel.povmValue G S.aliceMeas S.bobMeas :=
  congrArg iSup (funext fun S => S.value_eq_povmValue G)

end MIPRE

end

end
