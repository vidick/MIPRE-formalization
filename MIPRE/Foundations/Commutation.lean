/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.CrossConsistency
public import MIPRE.Foundations.PVM

@[expose] public section

/-!
# The commutation analysis

Blueprint `lem:commutation-analysis` (the paper's, in `games.tex`), and the two facts it runs on.
It is the step that turns *consistency with a joint measurement on the other side* into
*approximate commutation on one side*, and it is the only place in the Pauli appendix where
projectivity of a measurement is genuinely used.

## The shape

Alice has two POVMs `A_b` and `C_c`; Bob has one **projective** measurement `P_{b,c}` whose
outcome is the pair. If each of Alice's is cross-party close to the corresponding marginal of
Bob's, then Alice's two commute on the state:

```
A_b (x) Id ~ Id (x) P_b   and   C_c (x) Id ~ Id (x) P_c    =>    [A_b, C_c] (x) Id ~ 0 .
```

The proof moves both products to the *same* operator on Bob's side, `Id (x) P_{b,c}`, and that is
where projectivity enters: for a projective measurement with a product outcome set the two
marginals commute and multiply to the joint element (`IsPVM.marg_mul_marg`). Nothing else about
`P` is used.

## What the steps need

Each step multiplies a known deviation by an operator *in front*. The fact that lets it is the
paper's `fact:add-a-proj`: if `sum_i F_i^dag F_i <= Id` then `sum_i ||F_i v||^2 <= ||v||^2`, so
putting a family in front of a deviation costs nothing and *adds* its index to the sum. For a
POVM that hypothesis is `A_b^2 <= A_b` and `sum_b A_b = Id`, with no projectivity
(`sum_aOp_conjTranspose_mul_self_le_one`).

The constant is `16 delta`: each side of the commutator reaches `Id (x) P_{b,c}` in two steps
(`4 delta` after one triangle inequality), and the commutator is one more triangle
(`2 * 4 + 2 * 4`). No square root anywhere.

## In a model

The steps are proved for a state model (`StateModel`), with the families in its algebra and the
hypothesis `sum_i F_i^dag F_i <= Id` on the represented operators
(`StateModel.IsColContraction`); the analysis for a bipartite model
(`BipartiteModel.commutation_analysis`), two POVMs in the first player's algebra against a
projective measurement in the second player's. The matrix statements are their instances in the
matrix and tensor-product models.
-/

noncomputable section

namespace MIPRE

open Finset Matrix
open scoped ComplexOrder MatrixOrder

-- Every statement here mentions both factors of the joint space, and the two `DecidableEq`s are
-- needed for matrix multiplication on it; omitting them declaration by declaration would be a
-- dozen `omit` lines with no consumer.
set_option linter.unusedSectionVars false

/-! ## The steps in a state model -/

namespace StateModel

variable {𝒞 : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] (M : StateModel 𝒞)

/-- **A projective measurement is a column contraction**, with equality. -/
theorem isColContraction_of_isPVMIn {ι : Type*} [Fintype ι] {Q : ι → 𝒞} (h : IsPVMIn Q) :
    M.IsColContraction Q := by
  refine le_of_eq ?_
  have hterm : ∀ i, star (M.π (Q i)) * M.π (Q i) = M.π (Q i) := fun i => by
    rw [← map_star, ← map_mul, h.star_eq, h.idem]
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← map_sum, h.sum_eq_one, map_one]

/-- **A sum of mutually orthogonal projections times arbitrary operators has orthogonal terms.**
The cross terms carry `P i * P j = 0`, so the squared state norm is additive --- exactly, and with
no appeal to the size of the index set. -/
theorem snorm_sq_sum_proj_mul {ι : Type*} [DecidableEq ι] {P : ι → 𝒞}
    (hPsa : ∀ i, star (P i) = P i) (horth : ∀ i j, i ≠ j → P i * P j = 0) (W : ι → 𝒞)
    (s : Finset ι) :
    M.snorm (∑ i ∈ s, P i * W i) ^ 2 = ∑ i ∈ s, M.snorm (P i * W i) ^ 2 := by
  rw [M.snorm_sq_eq_qform, star_sum, Finset.sum_mul, M.qform_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mul_sum, M.qform_sum, Finset.sum_eq_single_of_mem i hi fun j _ hji => ?_,
    M.snorm_sq_eq_qform]
  rw [star_mul, hPsa,
    show star (W i) * P i * (P j * W j) = star (W i) * (P i * P j) * W j by noncomm_ring,
    horth i j (Ne.symm hji), mul_zero, zero_mul, M.qform_zero]

/-- **`lem:cool-closeness-fact`, in its partition form.** A projective measurement `A` that is
`δ`-close to a family `B` stays `δ`-close to it after multiplying each element by `A`'s own
element and summing over the fibres of an outcome map, simultaneously over all the fibres:
projectivity kills the cross terms inside a fibre (`snorm_sq_sum_proj_mul`), and each `A i` is a
contraction. -/
theorem sum_snorm_sq_cool {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {A : ι → 𝒞} (hA : IsPVMIn A) (B : ι → 𝒞) (f : ι → κ) :
    ∑ k : κ, M.snorm (∑ i ∈ univ.filter fun i => f i = k, (A i - A i * B i)) ^ 2
      ≤ ∑ i, M.snorm (A i - B i) ^ 2 := by
  have hterm : ∀ i, A i - A i * B i = A i * (A i - B i) := fun i => by
    rw [mul_sub, hA.idem]
  have hfib : ∀ k : κ, M.snorm (∑ i ∈ univ.filter fun i => f i = k, (A i - A i * B i)) ^ 2
      = ∑ i ∈ univ.filter fun i => f i = k, M.snorm (A i * (A i - B i)) ^ 2 := by
    intro k
    rw [Finset.sum_congr rfl fun i (_ : i ∈ univ.filter fun i => f i = k) => hterm i]
    exact M.snorm_sq_sum_proj_mul hA.star_eq (fun i j hij => hA.orthogonal hij) _ _
  rw [Finset.sum_congr rfl fun k (_ : k ∈ univ) => hfib k]
  refine le_trans (le_of_eq (Finset.sum_fiberwise (univ : Finset ι) f
    fun i => M.snorm (A i * (A i - B i)) ^ 2)) (Finset.sum_le_sum fun i _ => ?_)
  have h := M.snorm_mul_le (M.bnd_one_of_isStarProjection (hA.isStarProjection i)) (A i - B i)
  rw [one_mul] at h
  exact pow_le_pow_left₀ (M.snorm_nonneg _) h 2

/-- The weighted three-term triangle inequality, over a set of questions: the shape every item
of `lem:qld-win` is stated in. -/
theorem sum_weighted_snorm_sq_triangle3 {ι κ : Type*} [Fintype κ] {w : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) (S : Finset ι) (P Q R T : ι → κ → 𝒞) :
    ∑ i ∈ S, w i * ∑ o, M.snorm (P i o - T i o) ^ 2
      ≤ 3 * ∑ i ∈ S, w i * ∑ o, M.snorm (P i o - Q i o) ^ 2
        + 3 * ∑ i ∈ S, w i * ∑ o, M.snorm (Q i o - R i o) ^ 2
        + 3 * ∑ i ∈ S, w i * ∑ o, M.snorm (R i o - T i o) ^ 2 := by
  have hstep : ∀ i ∈ S, w i * ∑ o, M.snorm (P i o - T i o) ^ 2
      ≤ 3 * (w i * ∑ o, M.snorm (P i o - Q i o) ^ 2)
        + 3 * (w i * ∑ o, M.snorm (Q i o - R i o) ^ 2)
        + 3 * (w i * ∑ o, M.snorm (R i o - T i o) ^ 2) := by
    intro i _
    have h := M.sum_snorm_sq_triangle3 univ (P i) (Q i) (R i) (T i)
    nlinarith [hw i]
  refine le_trans (Finset.sum_le_sum hstep) (le_of_eq ?_)
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]

section Analysis

variable {B C : Type*} [Fintype B] [Fintype C] {δ : ℝ}

/-- Putting a family in front, with the front index in the first component of the pair. -/
theorem sum_prod_snorm_sq_mul_le_fst (F : B → 𝒞) (hF : M.IsColContraction F) (T : C → 𝒞) :
    ∑ p : B × C, M.snorm (F p.1 * T p.2) ^ 2 ≤ ∑ c, M.snorm (T c) ^ 2 := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  exact Finset.sum_le_sum fun c _ => M.sum_snorm_sq_mul_le F hF (T c)

/-- Putting a family in front, with the front index in the second component. -/
theorem sum_prod_snorm_sq_mul_le_snd (F : C → 𝒞) (hF : M.IsColContraction F) (T : B → 𝒞) :
    ∑ p : B × C, M.snorm (F p.2 * T p.1) ^ 2 ≤ ∑ b, M.snorm (T b) ^ 2 := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_le_sum fun b _ => M.sum_snorm_sq_mul_le F hF (T b)

/-- **The commutation analysis, in one algebra.** `alpha` and `gamma` are the two families that
are to commute; `betaB`, `betaC` are what they are respectively close to, and `betaBC` is the
joint operator both products reach. -/
theorem commutation_analysis_abstract (alpha : B → 𝒞) (gamma : C → 𝒞) (betaB : B → 𝒞)
    (betaC : C → 𝒞) (betaBC : B × C → 𝒞)
    (halpha : M.IsColContraction alpha) (hgamma : M.IsColContraction gamma)
    (hbetaB : M.IsColContraction betaB) (hbetaC : M.IsColContraction betaC)
    (hcomm : ∀ b c, alpha b * betaC c = betaC c * alpha b)
    (hcomm' : ∀ b c, gamma c * betaB b = betaB b * gamma c)
    (hmul : ∀ b c, betaC c * betaB b = betaBC (b, c))
    (hmul' : ∀ b c, betaB b * betaC c = betaBC (b, c))
    (hA : ∑ b, M.snorm (alpha b - betaB b) ^ 2 ≤ δ)
    (hC : ∑ c, M.snorm (gamma c - betaC c) ^ 2 ≤ δ) :
    ∑ p : B × C, M.snorm (alpha p.1 * gamma p.2 - gamma p.2 * alpha p.1) ^ 2 ≤ 16 * δ := by
  -- `alpha_b gamma_c` reaches `betaBC` in two steps
  have s1 : ∑ p : B × C, M.snorm (alpha p.1 * gamma p.2 - alpha p.1 * betaC p.2) ^ 2 ≤ δ := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_))
      (le_trans (M.sum_prod_snorm_sq_mul_le_fst alpha halpha
        (fun c => gamma c - betaC c)) hC)
    rw [mul_sub]
  have s2 : ∑ p : B × C, M.snorm (alpha p.1 * betaC p.2 - betaBC p) ^ 2 ≤ δ := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_))
      (le_trans (M.sum_prod_snorm_sq_mul_le_snd betaC hbetaC
        (fun b => alpha b - betaB b)) hA)
    rw [mul_sub, ← hcomm p.1 p.2, hmul p.1 p.2]
  have h1 : ∑ p : B × C, M.snorm (alpha p.1 * gamma p.2 - betaBC p) ^ 2 ≤ 4 * δ := by
    refine le_trans (M.sum_snorm_sq_triangle univ _ (fun p => alpha p.1 * betaC p.2) _) ?_
    linarith
  -- `gamma_c alpha_b` reaches the same operator
  have s3 : ∑ p : B × C, M.snorm (gamma p.2 * alpha p.1 - gamma p.2 * betaB p.1) ^ 2 ≤ δ := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_))
      (le_trans (M.sum_prod_snorm_sq_mul_le_snd gamma hgamma
        (fun b => alpha b - betaB b)) hA)
    rw [mul_sub]
  have s4 : ∑ p : B × C, M.snorm (gamma p.2 * betaB p.1 - betaBC p) ^ 2 ≤ δ := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_))
      (le_trans (M.sum_prod_snorm_sq_mul_le_fst betaB hbetaB
        (fun c => gamma c - betaC c)) hC)
    rw [mul_sub, ← hcomm' p.1 p.2, hmul' p.1 p.2]
  have h2 : ∑ p : B × C, M.snorm (gamma p.2 * alpha p.1 - betaBC p) ^ 2 ≤ 4 * δ := by
    refine le_trans (M.sum_snorm_sq_triangle univ _ (fun p => gamma p.2 * betaB p.1) _) ?_
    linarith
  have h2' : ∑ p : B × C, M.snorm (betaBC p - gamma p.2 * alpha p.1) ^ 2 ≤ 4 * δ := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_)) h2
    rw [M.snorm_sub_comm]
  refine le_trans (M.sum_snorm_sq_triangle univ _ betaBC _) ?_
  linarith

end Analysis

end StateModel

/-! ## The analysis in a bipartite model -/

namespace BipartiteModel

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] (M : BipartiteModel 𝒞 𝒜 ℬ)

/-- **Replacing the first player's operator by a nearby one on its own side**, inside a
cross-party deviation: one triangle inequality, at the usual cost of a factor two. -/
theorem sum_xSqNorm_le_of_two_step {κ : Type*} [Fintype κ] (Q Q' : κ → 𝒜) (R : κ → ℬ)
    {a b : ℝ} (h1 : ∑ o, M.stateSqNorm (Q o - Q' o) ≤ a)
    (h2 : ∑ o, M.xSqNorm (Q' o) (R o) ≤ b) :
    ∑ o, M.xSqNorm (Q o) (R o) ≤ 2 * a + 2 * b := by
  have hkey := M.sum_snorm_sq_triangle univ (fun o => M.πA (Q o)) (fun o => M.πA (Q' o))
    (fun o => M.πB (R o))
  have e2 : ∑ o, M.snorm (M.πA (Q o) - M.πA (Q' o)) ^ 2 = ∑ o, M.stateSqNorm (Q o - Q' o) :=
    Finset.sum_congr rfl fun o _ => by
      show _ = M.snorm (M.πA (Q o - Q' o)) ^ 2
      rw [map_sub]
  have h2' : ∑ o, M.snorm (M.πA (Q' o) - M.πB (R o)) ^ 2 ≤ b := h2
  rw [e2] at hkey
  show ∑ o, M.snorm (M.πA (Q o) - M.πB (R o)) ^ 2 ≤ 2 * a + 2 * b
  linarith

/-- **A POVM of the first player is a column contraction** on the Hilbert space: `t² ≤ t` for
each element, on the represented operator, and the elements sum to one. No projectivity. -/
theorem isColContraction_πA [PartialOrder 𝒜] [StarOrderedRing 𝒜] {ι : Type*} [Fintype ι]
    (P : POVMIn ι 𝒜) : M.IsColContraction fun i => M.πA (P.op i) := by
  have hterm : ∀ i, star (M.π (M.πA (P.op i))) * M.π (M.πA (P.op i)) ≤ M.π (M.πA (P.op i)) :=
    fun i => by
      rw [(IsSelfAdjoint.of_nonneg (M.π_πA_nonneg (P.op_nonneg i))).star_eq]
      exact Op.mul_self_le_self (M.π_πA_nonneg (P.op_nonneg i)) (M.π_πA_le_one (P.op_le_one i))
  refine (Finset.sum_le_sum fun i _ => hterm i).trans (le_of_eq ?_)
  rw [← map_sum, ← map_sum, P.sum_op, map_one, map_one]

/-- A POVM of the second player is a column contraction. -/
theorem isColContraction_πB [PartialOrder ℬ] [StarOrderedRing ℬ] {ι : Type*} [Fintype ι]
    (P : POVMIn ι ℬ) : M.IsColContraction fun i => M.πB (P.op i) :=
  M.swap.isColContraction_πA P

/-- **The commutation analysis** (`lem:commutation-analysis`) in a bipartite model: two POVMs of
the first player, each cross-party close to the corresponding marginal of one **projective**
measurement of the second player, commute on the state at `16 δ`. -/
theorem commutation_analysis [PartialOrder 𝒜] [StarOrderedRing 𝒜] {B C : Type*} [Fintype B]
    [Fintype C] {A : POVMIn B 𝒜} {Cm : POVMIn C 𝒜} {P : B × C → ℬ} (hP : IsPVMIn P) {δ : ℝ}
    (hA : ∑ b, M.xSqNorm (A.op b) (∑ c, P (b, c)) ≤ δ)
    (hC : ∑ c, M.xSqNorm (Cm.op c) (∑ b, P (b, c)) ≤ δ) :
    ∑ p : B × C, M.stateSqNorm (A.op p.1 * Cm.op p.2 - Cm.op p.2 * A.op p.1) ≤ 16 * δ := by
  have h := M.commutation_analysis_abstract (fun b => M.πA (A.op b)) (fun c => M.πA (Cm.op c))
    (fun b => M.πB (∑ c, P (b, c))) (fun c => M.πB (∑ b, P (b, c))) (fun p => M.πB (P p))
    (M.isColContraction_πA A) (M.isColContraction_πA Cm)
    (M.isColContraction_of_isPVMIn (hP.marg_left.map M.πB))
    (M.isColContraction_of_isPVMIn (hP.marg_right.map M.πB))
    (fun b c => (M.commute _ _).eq) (fun b c => (M.commute _ _).eq)
    (fun b c => by rw [← map_mul, hP.marg_mul_marg b c])
    (fun b c => by rw [← map_mul, hP.marg_mul_marg' b c])
    hA hC
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_)) h
  show M.snorm (M.πA (A.op p.1 * Cm.op p.2 - Cm.op p.2 * A.op p.1)) ^ 2 = _
  rw [map_sub, map_mul, map_mul]

end BipartiteModel

/-! ## The quadratic form is monotone -/

section Qform

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem qform_nonneg_of_nonneg (v : N → ℂ) {Z : Matrix N N ℂ}
    (hZ : (0 : Matrix N N ℂ) ≤ Z) : 0 ≤ qform v Z := by
  rw [qform_eq_mat]
  exact (StateModel.mat v).qform_nonneg_of_nonneg hZ

theorem qform_le_of_le (v : N → ℂ) {X Y : Matrix N N ℂ} (h : X ≤ Y) :
    qform v X ≤ qform v Y := by
  rw [qform_eq_mat, qform_eq_mat]
  exact (StateModel.mat v).qform_mono h

end Qform

/-! ## Adding an operator in front

`fact:add-a-proj`. Stated on the norm rather than on a distance, because that is the form both
uses need: the family in front contributes its own index to the sum, and the deviation it is
applied to does not change. -/

section AddInFront

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- **A family of operators with `sum_i F_i^dag F_i <= Id` costs nothing in front.** -/
theorem sum_snorm_sq_mul_le {ι : Type*} [Fintype ι] (v : N → ℂ)
    (F : ι → Matrix N N ℂ) (hF : ∑ i, (F i)ᴴ * F i ≤ (1 : Matrix N N ℂ))
    (M : Matrix N N ℂ) :
    ∑ i, snorm v (F i * M) ^ 2 ≤ snorm v M ^ 2 :=
  (StateModel.mat v).sum_snorm_sq_mul_le_of_le F hF M

/-- **A contraction in front costs nothing.** The one-operator case of `sum_snorm_sq_mul_le`. -/
theorem snorm_sq_mul_le_of_contraction (v : N → ℂ) {P : Matrix N N ℂ}
    (hP : Pᴴ * P ≤ (1 : Matrix N N ℂ)) (M : Matrix N N ℂ) :
    snorm v (P * M) ^ 2 ≤ snorm v M ^ 2 :=
  (StateModel.mat v).snorm_sq_mul_le_of_contraction hP M

/-- **A sum of mutually orthogonal projections times arbitrary operators has orthogonal terms.**
The cross terms carry `P i * P j = 0`, so the squared state norm is additive --- exactly, and with
no appeal to the size of the index set. -/
theorem snorm_sq_sum_proj_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (v : N → ℂ)
    {P : ι → Matrix N N ℂ} (hPsa : ∀ i, (P i)ᴴ = P i)
    (horth : ∀ i j, i ≠ j → P i * P j = 0) (W : ι → Matrix N N ℂ) (s : Finset ι) :
    snorm v (∑ i ∈ s, P i * W i) ^ 2 = ∑ i ∈ s, snorm v (P i * W i) ^ 2 :=
  (StateModel.mat v).snorm_sq_sum_proj_mul hPsa horth W s

/-- **`lem:cool-closeness-fact`, in its partition form.** A projective measurement `A` that is
`delta`-close to a family `B` stays `delta`-close to it after multiplying each element by `A`'s own
element and summing over the fibres of an outcome map --- *simultaneously* over all the fibres,
which is what the consumers need: the single-subset form applied to the `q` fibres of an outcome
map one at a time would cost a factor `q`. -/
theorem sum_snorm_sq_cool {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (v : N → ℂ) {A : ι → Matrix N N ℂ} (hA : IsPVM A) (B : ι → Matrix N N ℂ) (f : ι → κ) :
    ∑ k : κ, snorm v (∑ i ∈ univ.filter fun i => f i = k, (A i - A i * B i)) ^ 2
      ≤ ∑ i, snorm v (A i - B i) ^ 2 :=
  (StateModel.mat v).sum_snorm_sq_cool hA.toIn B f

/-- The triangle inequality for a family of deviations, at the usual cost of a factor two. -/
theorem sum_snorm_sq_triangle' {ι : Type*} [Fintype ι] (v : N → ℂ)
    (P Q R : ι → Matrix N N ℂ) :
    ∑ i, snorm v (P i - R i) ^ 2
      ≤ 2 * ∑ i, snorm v (P i - Q i) ^ 2 + 2 * ∑ i, snorm v (Q i - R i) ^ 2 :=
  (StateModel.mat v).sum_snorm_sq_triangle univ P Q R

/-- The three-term triangle inequality for a family of deviations. -/
theorem sum_snorm_sq_triangle3 {κ : Type*} [Fintype κ] (v : N → ℂ)
    (P Q R T : κ → Matrix N N ℂ) :
    ∑ o, snorm v (P o - T o) ^ 2
      ≤ 3 * ∑ o, snorm v (P o - Q o) ^ 2 + 3 * ∑ o, snorm v (Q o - R o) ^ 2
        + 3 * ∑ o, snorm v (R o - T o) ^ 2 :=
  (StateModel.mat v).sum_snorm_sq_triangle3 univ P Q R T

/-- The weighted form, over a set of questions: the shape every item of `lem:qld-win` is stated
in. -/
theorem sum_weighted_snorm_sq_triangle3 {ι κ : Type*} [Fintype κ] (v : N → ℂ)
    {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (S : Finset ι) (P Q R T : ι → κ → Matrix N N ℂ) :
    ∑ i ∈ S, w i * ∑ o, snorm v (P i o - T i o) ^ 2
      ≤ 3 * ∑ i ∈ S, w i * ∑ o, snorm v (P i o - Q i o) ^ 2
        + 3 * ∑ i ∈ S, w i * ∑ o, snorm v (Q i o - R i o) ^ 2
        + 3 * ∑ i ∈ S, w i * ∑ o, snorm v (R i o - T i o) ^ 2 :=
  (StateModel.mat v).sum_weighted_snorm_sq_triangle3 hw S P Q R T

end AddInFront

/-! ## A projective measurement is a POVM -/

/-- **A projective measurement, as a POVM.** The same bridge as
`ProjectiveMeasurement.toPOVM`, for the bare-family form `IsPVM` that the rigidity arguments
produce. -/
def IsPVM.toPOVM {n Λ : Type*} [Fintype n] [DecidableEq n] [Fintype Λ] [DecidableEq Λ]
    {P : Λ → Matrix n n ℂ} (h : IsPVM P) : POVM Λ n where
  mats a := ⟨P a, by
    rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose, h.isSelfAdjoint]⟩
  nonneg a := Subtype.coe_le_coe.mp (h.nonneg a)
  normalized := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact h.sum_eq_one

@[simp] theorem IsPVM.toPOVM_mats {n Λ : Type*} [Fintype n] [DecidableEq n] [Fintype Λ]
    [DecidableEq Λ] {P : Λ → Matrix n n ℂ} (h : IsPVM P) (a : Λ) :
    ((h.toPOVM.mats a).val) = P a := rfl

/-! ## Replacing one side of a cross-party deviation -/

section TwoStep

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-- **Replacing Alice's operator by a nearby one on her own factor**, inside a cross-party
deviation: one triangle inequality, at the usual cost of a factor two. -/
theorem sum_xSqNorm_le_of_two_step {κ : Type*} [Fintype κ] {ψ : dA × dB → ℂ}
    (Q Q' : κ → Matrix dA dA ℂ) (R : κ → Matrix dB dB ℂ) {a b : ℝ}
    (h1 : ∑ o, stateSqNorm ψ (Q o - Q' o) ≤ a) (h2 : ∑ o, xSqNorm ψ (Q' o) (R o) ≤ b) :
    ∑ o, xSqNorm ψ (Q o) (R o) ≤ 2 * a + 2 * b := by
  simp only [xSqNorm_eq_tensor] at h2 ⊢
  exact (BipartiteModel.tensor ψ).sum_xSqNorm_le_of_two_step Q Q' R h1 h2

end TwoStep

/-! ## Marginals of a coarse-grained POVM -/

section MapMarginal

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- **The marginal of a jointly coarse-grained POVM is the coarse-graining of one component.**
`sum_c (M.map (f, g))_{b,c} = (M.map f)_b`: the fibres of `(f, g)` over `{b} x C` partition the
fibre of `f` over `b`. -/
theorem POVM.sum_mats_map_prod {ι B C : Type*} [Fintype ι] [DecidableEq ι] [Fintype B]
    [DecidableEq B] [Fintype C] [DecidableEq C] (M : POVM ι d) (f : ι → B) (g : ι → C) (b : B) :
    ∑ c, (((M.map fun a => (f a, g a)).mats (b, c)).val) = (((M.map f).mats b).val) :=
  M.toIn.sum_op_map_prod f g b

/-- The other marginal. -/
theorem POVM.sum_mats_map_prod' {ι B C : Type*} [Fintype ι] [DecidableEq ι] [Fintype B]
    [DecidableEq B] [Fintype C] [DecidableEq C] (M : POVM ι d) (f : ι → B) (g : ι → C) (c : C) :
    ∑ b, (((M.map fun a => (f a, g a)).mats (b, c)).val) = (((M.map g).mats c).val) :=
  M.toIn.sum_op_map_prod' f g c

end MapMarginal

/-! ## The two hypotheses of the steps, for the operators they are applied to -/

section Families

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

theorem aOp_mono {X Y : Matrix dA dA ℂ} (h : X ≤ Y) :
    (aOp X : Matrix (dA × dB) _ ℂ) ≤ aOp Y := by
  rw [← sub_nonneg, ← aOp_sub]
  exact aOp_nonneg (sub_nonneg.mpr h)

theorem bOp_mono {X Y : Matrix dB dB ℂ} (h : X ≤ Y) :
    (bOp X : Matrix (dA × dB) _ ℂ) ≤ bOp Y := by
  rw [← sub_nonneg, ← bOp_sub]
  exact bOp_nonneg (sub_nonneg.mpr h)

theorem bOp_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix dB dB ℂ) :
    bOp (∑ i ∈ s, f i) = ∑ i ∈ s, (bOp (f i) : Matrix (dA × dB) _ ℂ) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, bOp, Matrix.kronecker_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, bOp_add, ih, Finset.sum_insert hi]

/-- **A POVM on Alice's factor satisfies the hypothesis of `sum_snorm_sq_mul_le`.** No
projectivity: `A^dag A = A^2 <= A` and the elements sum to one. -/
theorem sum_aOp_conjTranspose_mul_self_le_one {ι : Type*} [Fintype ι] (A : POVM ι dA) :
    ∑ i, ((aOp ((A.mats i).val) : Matrix (dA × dB) _ ℂ))ᴴ * aOp ((A.mats i).val)
      ≤ (1 : Matrix (dA × dB) (dA × dB) ℂ) := by
  have hterm : ∀ i : ι, ((aOp ((A.mats i).val) : Matrix (dA × dB) _ ℂ))ᴴ
      * aOp ((A.mats i).val) = aOp ((A.mats i).val * (A.mats i).val) := by
    intro i
    rw [aOp_conjTranspose, ← aOp_mul, ← Matrix.star_eq_conjTranspose, (A.mats i).2]
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← aOp_sum,
    ← aOp_one (HA := dA) (HB := dB)]
  refine aOp_mono ?_
  rw [← POVM.sum_val A]
  exact Finset.sum_le_sum fun i _ => POVM.mul_self_le_self A i

/-- Bob's version. -/
theorem sum_bOp_conjTranspose_mul_self_le_one {ι : Type*} [Fintype ι] (B : POVM ι dB) :
    ∑ i, ((bOp ((B.mats i).val) : Matrix (dA × dB) _ ℂ))ᴴ * bOp ((B.mats i).val)
      ≤ (1 : Matrix (dA × dB) (dA × dB) ℂ) := by
  have hterm : ∀ i : ι, ((bOp ((B.mats i).val) : Matrix (dA × dB) _ ℂ))ᴴ
      * bOp ((B.mats i).val) = bOp ((B.mats i).val * (B.mats i).val) := by
    intro i
    rw [bOp_conjTranspose, ← bOp_mul, ← Matrix.star_eq_conjTranspose, (B.mats i).2]
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← bOp_sum,
    ← bOp_one (HA := dA) (HB := dB)]
  refine bOp_mono ?_
  rw [← POVM.sum_val B]
  exact Finset.sum_le_sum fun i _ => POVM.mul_self_le_self B i

/-- A projective family on Bob's factor satisfies the hypothesis of `sum_snorm_sq_mul_le` with
equality. -/
theorem sum_bOp_conjTranspose_mul_self_of_isPVM {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Q : ι → Matrix dB dB ℂ} (h : IsPVM Q) :
    ∑ i, ((bOp (Q i) : Matrix (dA × dB) (dA × dB) ℂ))ᴴ * bOp (Q i)
      = (1 : Matrix (dA × dB) (dA × dB) ℂ) := by
  have hterm : ∀ i : ι, ((bOp (Q i) : Matrix (dA × dB) (dA × dB) ℂ))ᴴ * bOp (Q i)
      = bOp (Q i) := by
    intro i
    rw [bOp_conjTranspose, ← bOp_mul, h.isSelfAdjoint, h.idem]
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← bOp_sum, h.sum_eq_one, bOp_one]

end Families

/-! ## The marginals of a projective measurement with a product outcome set -/

section Marginals

variable {N B C : Type*} [Fintype N] [DecidableEq N] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]

/-- **The two marginals of a projective measurement multiply to the joint element.** This is the
whole use of projectivity in the commutation analysis: the off-diagonal terms of the product
vanish by `IsPVM.orthogonal`, and the surviving one is idempotent. -/
theorem IsPVM.marg_mul_marg {P : B × C → Matrix N N ℂ} (h : IsPVM P) (b : B) (c : C) :
    (∑ b', P (b', c)) * (∑ c', P (b, c')) = P (b, c) :=
  h.toIn.marg_mul_marg b c

/-- The marginal over `C`, as the coarse-graining of `P` that forgets the second outcome. -/
theorem IsPVM.sum_marg_left {P : B × C → Matrix N N ℂ} (h : IsPVM P) :
    ∑ b, (∑ c, P (b, c)) = 1 :=
  h.toIn.sum_marg_left

theorem IsPVM.sum_marg_right {P : B × C → Matrix N N ℂ} (h : IsPVM P) :
    ∑ c, (∑ b, P (b, c)) = 1 :=
  h.toIn.sum_marg_right

/-- The marginal of a projective measurement with a product outcome set is projective. -/
theorem IsPVM.marg_left {P : B × C → Matrix N N ℂ} (h : IsPVM P) :
    IsPVM fun b => ∑ c, P (b, c) :=
  h.toIn.marg_left.toIsPVM

theorem IsPVM.marg_right {P : B × C → Matrix N N ℂ} (h : IsPVM P) :
    IsPVM fun c => ∑ b, P (b, c) :=
  h.toIn.marg_right.toIsPVM

/-- The other order. -/
theorem IsPVM.marg_mul_marg' {P : B × C → Matrix N N ℂ} (h : IsPVM P) (b : B) (c : C) :
    (∑ c', P (b, c')) * (∑ b', P (b', c)) = P (b, c) :=
  h.toIn.marg_mul_marg' b c

end Marginals

/-! ## The analysis

Stated for abstract families in one algebra --- the two parties enter only through the
hypotheses `hcomm`, `hcomm'` (the factors commute) and `hmul`, `hmul'` (Bob's two marginals
multiply to the joint element). That keeps the algebra in a single type, and `commutation_analysis`
below is the instance where the families are `aOp` and `bOp` of a POVM and a projective
measurement, through `BipartiteModel.commutation_analysis` in the tensor-product model. -/

section Analysis

variable {N : Type*} [Fintype N] [DecidableEq N] {B C : Type*} [Fintype B] [Fintype C]
  {v : N → ℂ} {δ : ℝ}

/-- Putting a family in front, with the front index in the first component of the pair. -/
theorem sum_prod_snorm_sq_mul_le_fst (v : N → ℂ)
    (F : B → Matrix N N ℂ) (hF : ∑ b, (F b)ᴴ * F b ≤ (1 : Matrix N N ℂ))
    (M : C → Matrix N N ℂ) :
    ∑ p : B × C, snorm v (F p.1 * M p.2) ^ 2 ≤ ∑ c, snorm v (M c) ^ 2 :=
  (StateModel.mat v).sum_prod_snorm_sq_mul_le_fst F ((StateModel.mat v).isColContraction_of_le hF)
    M

/-- Putting a family in front, with the front index in the second component. -/
theorem sum_prod_snorm_sq_mul_le_snd (v : N → ℂ)
    (F : C → Matrix N N ℂ) (hF : ∑ c, (F c)ᴴ * F c ≤ (1 : Matrix N N ℂ))
    (M : B → Matrix N N ℂ) :
    ∑ p : B × C, snorm v (F p.2 * M p.1) ^ 2 ≤ ∑ b, snorm v (M b) ^ 2 :=
  (StateModel.mat v).sum_prod_snorm_sq_mul_le_snd F ((StateModel.mat v).isColContraction_of_le hF)
    M

/-- **The commutation analysis, in one algebra**: `StateModel.commutation_analysis_abstract` in
the matrix model. -/
theorem commutation_analysis_abstract (v : N → ℂ)
    (alpha : B → Matrix N N ℂ) (gamma : C → Matrix N N ℂ)
    (betaB : B → Matrix N N ℂ) (betaC : C → Matrix N N ℂ)
    (betaBC : B × C → Matrix N N ℂ)
    (halpha : ∑ b, (alpha b)ᴴ * alpha b ≤ (1 : Matrix N N ℂ))
    (hgamma : ∑ c, (gamma c)ᴴ * gamma c ≤ (1 : Matrix N N ℂ))
    (hbetaB : ∑ b, (betaB b)ᴴ * betaB b ≤ (1 : Matrix N N ℂ))
    (hbetaC : ∑ c, (betaC c)ᴴ * betaC c ≤ (1 : Matrix N N ℂ))
    (hcomm : ∀ b c, alpha b * betaC c = betaC c * alpha b)
    (hcomm' : ∀ b c, gamma c * betaB b = betaB b * gamma c)
    (hmul : ∀ b c, betaC c * betaB b = betaBC (b, c))
    (hmul' : ∀ b c, betaB b * betaC c = betaBC (b, c))
    (hA : ∑ b, snorm v (alpha b - betaB b) ^ 2 ≤ δ)
    (hC : ∑ c, snorm v (gamma c - betaC c) ^ 2 ≤ δ) :
    ∑ p : B × C, snorm v (alpha p.1 * gamma p.2 - gamma p.2 * alpha p.1) ^ 2 ≤ 16 * δ :=
  (StateModel.mat v).commutation_analysis_abstract alpha gamma betaB betaC betaBC
    ((StateModel.mat v).isColContraction_of_le halpha)
    ((StateModel.mat v).isColContraction_of_le hgamma)
    ((StateModel.mat v).isColContraction_of_le hbetaB)
    ((StateModel.mat v).isColContraction_of_le hbetaC) hcomm hcomm' hmul hmul' hA hC

end Analysis

/-! ## The instance: a POVM pair on Alice against a projective measurement on Bob -/

section Instance

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {B C : Type*} [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

/-- **The commutation analysis** (`lem:commutation-analysis`). Two POVMs on Alice's factor, each
cross-party close to the corresponding marginal of one **projective** measurement on Bob's,
commute on the state at `16 delta`. -/
theorem commutation_analysis {ψ : dA × dB → ℂ} {A : POVM B dA} {Cm : POVM C dA}
    {P : B × C → Matrix dB dB ℂ} (hP : IsPVM P) {δ : ℝ}
    (hA : ∑ b, snorm ψ ((aOp ((A.mats b).val) : Matrix (dA × dB) (dA × dB) ℂ)
        - bOp (∑ c, P (b, c))) ^ 2 ≤ δ)
    (hC : ∑ c, snorm ψ ((aOp ((Cm.mats c).val) : Matrix (dA × dB) (dA × dB) ℂ)
        - bOp (∑ b, P (b, c))) ^ 2 ≤ δ) :
    ∑ p : B × C, snorm ψ ((aOp ((A.mats p.1).val) : Matrix (dA × dB) (dA × dB) ℂ)
          * aOp ((Cm.mats p.2).val)
        - (aOp ((Cm.mats p.2).val) : Matrix (dA × dB) (dA × dB) ℂ)
          * aOp ((A.mats p.1).val)) ^ 2 ≤ 16 * δ := by
  have h := (BipartiteModel.tensor ψ).commutation_analysis (A := A.toIn) (Cm := Cm.toIn)
    hP.toIn hA hC
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_)) h
  show _ = snorm ψ (aOp ((A.mats p.1).val * (Cm.mats p.2).val
    - (Cm.mats p.2).val * (A.mats p.1).val) : Matrix (dA × dB) (dA × dB) ℂ) ^ 2
  rw [aOp_sub, aOp_mul, aOp_mul]

/-- The commutator form, with the difference inside a single `aOp`. -/
theorem commutation_analysis_aOp {ψ : dA × dB → ℂ} {A : POVM B dA} {Cm : POVM C dA}
    {P : B × C → Matrix dB dB ℂ} (hP : IsPVM P) {δ : ℝ}
    (hA : ∑ b, snorm ψ ((aOp ((A.mats b).val) : Matrix (dA × dB) (dA × dB) ℂ)
        - bOp (∑ c, P (b, c))) ^ 2 ≤ δ)
    (hC : ∑ c, snorm ψ ((aOp ((Cm.mats c).val) : Matrix (dA × dB) (dA × dB) ℂ)
        - bOp (∑ b, P (b, c))) ^ 2 ≤ δ) :
    ∑ p : B × C, snorm ψ (aOp ((A.mats p.1).val * (Cm.mats p.2).val
        - (Cm.mats p.2).val * (A.mats p.1).val) : Matrix (dA × dB) (dA × dB) ℂ) ^ 2
      ≤ 16 * δ := by
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_)) (commutation_analysis hP hA hC)
  rw [aOp_sub, aOp_mul, aOp_mul]

/-! ### From the POVM elements to the observables

The last step of the paper's commuting case: expanding a two-outcome observable as `Id - 2 M_1`,
the commutator of two such observables is **exactly** four times the commutator of the two
`M_1`'s, because the identity commutes with everything. So the transfer costs a factor `16` in the
squared norm and no approximation at all. -/

theorem obs2_commutator_eq {d : Type*} [Fintype d] [DecidableEq d]
    (A : POVM (ZMod 2) d) (Cm : POVM (ZMod 2) d) :
    obs2 A * obs2 Cm - obs2 Cm * obs2 A
      = (4 : ℂ) • (((A.mats 1).val) * ((Cm.mats 1).val)
        - ((Cm.mats 1).val) * ((A.mats 1).val)) := by
  have hA : ((A.mats 0).val) = 1 - ((A.mats 1).val) := by
    have h := POVM.sum_val A
    rw [show (univ : Finset (ZMod 2)) = {0, 1} from by decide, Finset.sum_insert (by decide),
      Finset.sum_singleton] at h
    linear_combination (norm := module) h
  have hC : ((Cm.mats 0).val) = 1 - ((Cm.mats 1).val) := by
    have h := POVM.sum_val Cm
    rw [show (univ : Finset (ZMod 2)) = {0, 1} from by decide, Finset.sum_insert (by decide),
      Finset.sum_singleton] at h
    linear_combination (norm := module) h
  rw [obs2, obs2, hA, hC]
  noncomm_ring
  module

end Instance

end MIPRE

end

end
