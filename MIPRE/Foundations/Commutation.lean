/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.CrossConsistency
import MIPRE.Foundations.PVM

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
-/

noncomputable section

namespace MIPRE

open Finset Matrix
open scoped ComplexOrder MatrixOrder

-- Every statement here mentions both factors of the joint space, and the two `DecidableEq`s are
-- needed for matrix multiplication on it; omitting them declaration by declaration would be a
-- dozen `omit` lines with no consumer.
set_option linter.unusedSectionVars false

/-! ## The quadratic form is monotone -/

section Qform

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem qform_nonneg_of_nonneg (v : N → ℂ) {Z : Matrix N N ℂ}
    (hZ : (0 : Matrix N N ℂ) ≤ Z) : 0 ≤ qform v Z := by
  have h := (Matrix.nonneg_iff_posSemidef.mp hZ).dotProduct_mulVec_nonneg v
  exact (Complex.nonneg_iff.mp h).1

theorem qform_le_of_le (v : N → ℂ) {X Y : Matrix N N ℂ} (h : X ≤ Y) :
    qform v X ≤ qform v Y := by
  have h0 : 0 ≤ qform v (Y - X) := qform_nonneg_of_nonneg v (sub_nonneg.mpr h)
  rw [qform_sub] at h0
  linarith

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
    ∑ i, snorm v (F i * M) ^ 2 ≤ snorm v M ^ 2 := by
  have key : ∀ i : ι, snorm v (F i * M) ^ 2 = qform v (Mᴴ * ((F i)ᴴ * F i) * M) := by
    intro i
    rw [snorm_sq_eq_qform, Matrix.conjTranspose_mul]
    congr 1
    noncomm_ring
  rw [Finset.sum_congr rfl fun i _ => key i, ← qform_sum]
  have hsum : ∑ i : ι, Mᴴ * ((F i)ᴴ * F i) * M = Mᴴ * (∑ i, (F i)ᴴ * F i) * M := by
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [hsum, snorm_sq_eq_qform]
  refine qform_le_of_le v ?_
  have hpsd : (0 : Matrix N N ℂ) ≤ Mᴴ * ((1 : Matrix N N ℂ) - ∑ i, (F i)ᴴ * F i) * M :=
    Matrix.nonneg_iff_posSemidef.mpr
      ((Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hF)).conjTranspose_mul_mul_same M)
  have hsplit : Mᴴ * ((1 : Matrix N N ℂ) - ∑ i, (F i)ᴴ * F i) * M
      = Mᴴ * M - Mᴴ * (∑ i, (F i)ᴴ * F i) * M := by noncomm_ring
  rw [hsplit] at hpsd
  exact sub_nonneg.mp hpsd

/-- **A contraction in front costs nothing.** The one-operator case of `sum_snorm_sq_mul_le`. -/
theorem snorm_sq_mul_le_of_contraction (v : N → ℂ) {P : Matrix N N ℂ}
    (hP : Pᴴ * P ≤ (1 : Matrix N N ℂ)) (M : Matrix N N ℂ) :
    snorm v (P * M) ^ 2 ≤ snorm v M ^ 2 := by
  rw [snorm_sq_eq_qform, snorm_sq_eq_qform, Matrix.conjTranspose_mul,
    show Mᴴ * Pᴴ * (P * M) = Mᴴ * (Pᴴ * P) * M from by noncomm_ring]
  refine qform_le_of_le v ?_
  have hpsd : (0 : Matrix N N ℂ) ≤ Mᴴ * ((1 : Matrix N N ℂ) - Pᴴ * P) * M :=
    Matrix.nonneg_iff_posSemidef.mpr
      ((Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hP)).conjTranspose_mul_mul_same M)
  rw [show Mᴴ * ((1 : Matrix N N ℂ) - Pᴴ * P) * M = Mᴴ * M - Mᴴ * (Pᴴ * P) * M from by
    noncomm_ring] at hpsd
  exact sub_nonneg.mp hpsd

/-- **A sum of mutually orthogonal projections times arbitrary operators has orthogonal terms.**
The cross terms carry `P i * P j = 0`, so the squared state norm is additive --- exactly, and with
no appeal to the size of the index set. -/
theorem snorm_sq_sum_proj_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (v : N → ℂ)
    {P : ι → Matrix N N ℂ} (hPsa : ∀ i, (P i)ᴴ = P i)
    (horth : ∀ i j, i ≠ j → P i * P j = 0) (W : ι → Matrix N N ℂ) (s : Finset ι) :
    snorm v (∑ i ∈ s, P i * W i) ^ 2 = ∑ i ∈ s, snorm v (P i * W i) ^ 2 := by
  classical
  rw [snorm_sq_eq_qform, Matrix.conjTranspose_sum, Finset.sum_mul, qform_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Matrix.mul_sum, qform_sum, Finset.sum_eq_single_of_mem i hi fun j _ hji => ?_,
    snorm_sq_eq_qform]
  rw [Matrix.conjTranspose_mul, hPsa,
    show (W i)ᴴ * P i * (P j * W j) = (W i)ᴴ * (P i * P j) * W j from by noncomm_ring,
    horth i j (Ne.symm hji), Matrix.mul_zero, Matrix.zero_mul]
  show qform v 0 = 0
  rw [qform, Matrix.zero_mulVec]
  simp

/-- **`lem:cool-closeness-fact`, in its partition form.** A projective measurement `A` that is
`delta`-close to a family `B` stays `delta`-close to it after multiplying each element by `A`'s own
element and summing over the fibres of an outcome map --- *simultaneously* over all the fibres,
which is what the consumers need: the single-subset form applied to the `q` fibres of an outcome
map one at a time would cost a factor `q`.

The two facts are that projectivity kills the cross terms inside a fibre, and that each `A i` is a
contraction. The fibres being disjoint is what lets the outer sum be absorbed. -/
theorem sum_snorm_sq_cool {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (v : N → ℂ) {A : ι → Matrix N N ℂ} (hA : IsPVM A) (B : ι → Matrix N N ℂ) (f : ι → κ) :
    ∑ k : κ, snorm v (∑ i ∈ univ.filter fun i => f i = k, (A i - A i * B i)) ^ 2
      ≤ ∑ i, snorm v (A i - B i) ^ 2 := by
  classical
  have hterm : ∀ i, A i - A i * B i = A i * (A i - B i) := fun i => by
    rw [Matrix.mul_sub, hA.idem]
  have horth : ∀ i j : ι, i ≠ j →
      (A i * (A i - B i))ᴴ * (A j * (A j - B j)) = 0 := by
    intro i j hij
    rw [Matrix.conjTranspose_mul, hA.isSelfAdjoint,
      show (A i - B i)ᴴ * A i * (A j * (A j - B j))
          = (A i - B i)ᴴ * (A i * A j) * (A j - B j) from by noncomm_ring,
      hA.orthogonal hij, Matrix.mul_zero, Matrix.zero_mul]
  have hfib : ∀ k : κ, snorm v (∑ i ∈ univ.filter fun i => f i = k, (A i - A i * B i)) ^ 2
      = ∑ i ∈ univ.filter fun i => f i = k, snorm v (A i * (A i - B i)) ^ 2 := by
    intro k
    rw [Finset.sum_congr rfl fun i (_ : i ∈ univ.filter fun i => f i = k) => hterm i,
      snorm_sq_eq_qform, Matrix.conjTranspose_sum, Finset.sum_mul, qform_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Matrix.mul_sum, qform_sum, Finset.sum_eq_single_of_mem i hi fun j _ hji => ?_,
      snorm_sq_eq_qform]
    rw [horth i j (Ne.symm hji)]
    show qform v 0 = 0
    rw [qform, Matrix.zero_mulVec]
    simp
  rw [Finset.sum_congr rfl fun k (_ : k ∈ univ) => hfib k]
  refine le_trans (le_of_eq (Finset.sum_fiberwise (univ : Finset ι) f
    fun i => snorm v (A i * (A i - B i)) ^ 2)) (Finset.sum_le_sum fun i _ => ?_)
  refine snorm_sq_mul_le_of_contraction v ?_ _
  rw [hA.isSelfAdjoint, hA.idem]
  exact le_trans (Finset.single_le_sum (fun j _ => hA.nonneg j) (mem_univ i))
    (le_of_eq hA.sum_eq_one)

/-- The triangle inequality for a family of deviations, at the usual cost of a factor two. -/
theorem sum_snorm_sq_triangle' {ι : Type*} [Fintype ι] (v : N → ℂ)
    (P Q R : ι → Matrix N N ℂ) :
    ∑ i, snorm v (P i - R i) ^ 2
      ≤ 2 * ∑ i, snorm v (P i - Q i) ^ 2 + 2 * ∑ i, snorm v (Q i - R i) ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hsplit : P i - R i = (P i - Q i) + (Q i - R i) := by abel
  have htri : snorm v (P i - R i) ≤ snorm v (P i - Q i) + snorm v (Q i - R i) := by
    rw [hsplit]; exact snorm_add_le v _ _
  nlinarith [snorm_nonneg v (P i - Q i), snorm_nonneg v (Q i - R i),
    snorm_nonneg v (P i - R i), sq_nonneg (snorm v (P i - Q i) - snorm v (Q i - R i))]

/-- The three-term triangle inequality for a family of deviations. -/
theorem sum_snorm_sq_triangle3 {κ : Type*} [Fintype κ] (v : N → ℂ)
    (P Q R T : κ → Matrix N N ℂ) :
    ∑ o, snorm v (P o - T o) ^ 2
      ≤ 3 * ∑ o, snorm v (P o - Q o) ^ 2 + 3 * ∑ o, snorm v (Q o - R o) ^ 2
        + 3 * ∑ o, snorm v (R o - T o) ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun o _ => ?_
  have hsplit : P o - T o = (P o - Q o) + ((Q o - R o) + (R o - T o)) := by abel
  have htri : snorm v (P o - T o)
      ≤ snorm v (P o - Q o) + (snorm v (Q o - R o) + snorm v (R o - T o)) := by
    rw [hsplit]
    exact le_trans (snorm_add_le v _ _) (by
      have := snorm_add_le v (Q o - R o) (R o - T o)
      linarith)
  nlinarith [snorm_nonneg v (P o - Q o), snorm_nonneg v (Q o - R o), snorm_nonneg v (R o - T o),
    snorm_nonneg v (P o - T o), sq_nonneg (snorm v (P o - Q o) - snorm v (Q o - R o)),
    sq_nonneg (snorm v (P o - Q o) - snorm v (R o - T o)),
    sq_nonneg (snorm v (Q o - R o) - snorm v (R o - T o))]

/-- The weighted form, over a set of questions: the shape every item of `lem:qld-win` is stated
in. -/
theorem sum_weighted_snorm_sq_triangle3 {ι κ : Type*} [Fintype κ] (v : N → ℂ)
    {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (S : Finset ι) (P Q R T : ι → κ → Matrix N N ℂ) :
    ∑ i ∈ S, w i * ∑ o, snorm v (P i o - T i o) ^ 2
      ≤ 3 * ∑ i ∈ S, w i * ∑ o, snorm v (P i o - Q i o) ^ 2
        + 3 * ∑ i ∈ S, w i * ∑ o, snorm v (Q i o - R i o) ^ 2
        + 3 * ∑ i ∈ S, w i * ∑ o, snorm v (R i o - T i o) ^ 2 := by
  have hstep : ∀ i ∈ S, w i * ∑ o, snorm v (P i o - T i o) ^ 2
      ≤ 3 * (w i * ∑ o, snorm v (P i o - Q i o) ^ 2)
        + 3 * (w i * ∑ o, snorm v (Q i o - R i o) ^ 2)
        + 3 * (w i * ∑ o, snorm v (R i o - T i o) ^ 2) := by
    intro i _
    have h := sum_snorm_sq_triangle3 v (P i) (Q i) (R i) (T i)
    nlinarith [hw i]
  refine le_trans (Finset.sum_le_sum hstep) (le_of_eq ?_)
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]

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
  have hkey := sum_snorm_sq_triangle' ψ
    (fun o => (aOp (Q o) : Matrix (dA × dB) (dA × dB) ℂ))
    (fun o => (aOp (Q' o) : Matrix (dA × dB) (dA × dB) ℂ))
    (fun o => (bOp (R o) : Matrix (dA × dB) (dA × dB) ℂ))
  have e1 : ∑ o, xSqNorm ψ (Q o) (R o)
      = ∑ o, snorm ψ ((aOp (Q o) : Matrix (dA × dB) (dA × dB) ℂ) - bOp (R o)) ^ 2 :=
    Finset.sum_congr rfl fun o _ => xSqNorm_eq_snorm_sq ψ (Q o) (R o)
  have e2 : ∑ o, snorm ψ ((aOp (Q o) : Matrix (dA × dB) (dA × dB) ℂ) - aOp (Q' o)) ^ 2
      = ∑ o, stateSqNorm ψ (Q o - Q' o) :=
    Finset.sum_congr rfl fun o _ => by
      rw [← aOp_sub, stateSqNorm, stateNorm, norm_stateVec_eq_snorm]
  have e3 : ∑ o, snorm ψ ((aOp (Q' o) : Matrix (dA × dB) (dA × dB) ℂ) - bOp (R o)) ^ 2
      = ∑ o, xSqNorm ψ (Q' o) (R o) :=
    (Finset.sum_congr rfl fun o _ => xSqNorm_eq_snorm_sq ψ (Q' o) (R o)).symm
  rw [e1]
  rw [e2, e3] at hkey
  linarith

end TwoStep

/-! ## Marginals of a coarse-grained POVM -/

section MapMarginal

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- **The marginal of a jointly coarse-grained POVM is the coarse-graining of one component.**
`sum_c (M.map (f, g))_{b,c} = (M.map f)_b`: the fibres of `(f, g)` over `{b} x C` partition the
fibre of `f` over `b`. -/
theorem POVM.sum_mats_map_prod {ι B C : Type*} [Fintype ι] [DecidableEq ι] [Fintype B]
    [DecidableEq B] [Fintype C] [DecidableEq C] (M : POVM ι d) (f : ι → B) (g : ι → C) (b : B) :
    ∑ c, (((M.map fun a => (f a, g a)).mats (b, c)).val) = (((M.map f).mats b).val) := by
  classical
  have hL : ∀ c : C, (((M.map fun a => (f a, g a)).mats (b, c)).val)
      = ∑ a, if (f a, g a) = (b, c) then ((M.mats a).val) else 0 := by
    intro c
    show ((∑ a ∈ univ.filter fun a => (f a, g a) = (b, c), M.mats a : selfAdjoint _)).val = _
    rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_filter]
  rw [Finset.sum_congr rfl fun c (_ : c ∈ univ) => hL c, Finset.sum_comm]
  have hR : (((M.map f).mats b).val) = ∑ a, if f a = b then ((M.mats a).val) else 0 := by
    show ((∑ a ∈ univ.filter fun a => f a = b, M.mats a : selfAdjoint _)).val = _
    rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_filter]
  rw [hR]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : f a = b
  · rw [if_pos h, Finset.sum_eq_single (g a) (fun c _ hc => if_neg fun he => hc (by
      rw [← (Prod.mk.injEq .. ▸ he : f a = b ∧ g a = c).2]))
      fun hmem => absurd (Finset.mem_univ (g a)) hmem, if_pos (by rw [h])]
  · rw [if_neg h]
    exact Finset.sum_eq_zero fun c _ => if_neg fun he => h (Prod.mk.injEq .. ▸ he).1

/-- The other marginal. -/
theorem POVM.sum_mats_map_prod' {ι B C : Type*} [Fintype ι] [DecidableEq ι] [Fintype B]
    [DecidableEq B] [Fintype C] [DecidableEq C] (M : POVM ι d) (f : ι → B) (g : ι → C) (c : C) :
    ∑ b, (((M.map fun a => (f a, g a)).mats (b, c)).val) = (((M.map g).mats c).val) := by
  classical
  have hL : ∀ b : B, (((M.map fun a => (f a, g a)).mats (b, c)).val)
      = ∑ a, if (f a, g a) = (b, c) then ((M.mats a).val) else 0 := by
    intro b
    show ((∑ a ∈ univ.filter fun a => (f a, g a) = (b, c), M.mats a : selfAdjoint _)).val = _
    rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_filter]
  rw [Finset.sum_congr rfl fun b (_ : b ∈ univ) => hL b, Finset.sum_comm]
  have hR : (((M.map g).mats c).val) = ∑ a, if g a = c then ((M.mats a).val) else 0 := by
    show ((∑ a ∈ univ.filter fun a => g a = c, M.mats a : selfAdjoint _)).val = _
    rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_filter]
  rw [hR]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : g a = c
  · rw [if_pos h, Finset.sum_eq_single (f a) (fun b _ hb => if_neg fun he => hb (by
      rw [← (Prod.mk.injEq .. ▸ he : f a = b ∧ g a = c).1]))
      fun hmem => absurd (Finset.mem_univ (f a)) hmem, if_pos (by rw [h])]
  · rw [if_neg h]
    exact Finset.sum_eq_zero fun b _ => if_neg fun he => h (Prod.mk.injEq .. ▸ he).2

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
    (∑ b', P (b', c)) * (∑ c', P (b, c')) = P (b, c) := by
  classical
  rw [Finset.sum_mul]
  rw [Finset.sum_eq_single b (fun b' _ hb' => ?_) fun hmem => absurd (Finset.mem_univ b) hmem]
  · rw [Finset.mul_sum,
      Finset.sum_eq_single c (fun c' _ hc' => ?_) fun hmem => absurd (Finset.mem_univ c) hmem]
    · exact h.idem (b, c)
    · exact h.orthogonal fun he => hc' (Prod.mk.injEq .. ▸ he).2.symm
  · rw [Finset.mul_sum]
    refine Finset.sum_eq_zero fun c' _ => ?_
    exact h.orthogonal fun he => hb' (Prod.mk.injEq .. ▸ he).1

/-- The marginal over `C`, as the coarse-graining of `P` that forgets the second outcome. -/
theorem IsPVM.sum_marg_left {P : B × C → Matrix N N ℂ} (h : IsPVM P) :
    ∑ b, (∑ c, P (b, c)) = 1 := by
  rw [← Fintype.sum_prod_type]
  exact h.sum_eq_one

theorem IsPVM.sum_marg_right {P : B × C → Matrix N N ℂ} (h : IsPVM P) :
    ∑ c, (∑ b, P (b, c)) = 1 := by
  rw [Finset.sum_comm, ← Fintype.sum_prod_type]
  exact h.sum_eq_one

/-- The marginal of a projective measurement with a product outcome set is projective. -/
theorem IsPVM.marg_left {P : B × C → Matrix N N ℂ} (h : IsPVM P) :
    IsPVM fun b => ∑ c, P (b, c) where
  isSelfAdjoint b := by
    rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun c _ => h.isSelfAdjoint (b, c)
  idem b := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum, Finset.sum_eq_single c (fun c' _ hc' => ?_)
      fun hmem => absurd (Finset.mem_univ c) hmem]
    · exact h.idem (b, c)
    · exact h.orthogonal fun he => hc' (Prod.mk.injEq .. ▸ he).2.symm
  sum_eq_one := h.sum_marg_left

theorem IsPVM.marg_right {P : B × C → Matrix N N ℂ} (h : IsPVM P) :
    IsPVM fun c => ∑ b, P (b, c) where
  isSelfAdjoint c := by
    rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun b _ => h.isSelfAdjoint (b, c)
  idem c := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum, Finset.sum_eq_single b (fun b' _ hb' => ?_)
      fun hmem => absurd (Finset.mem_univ b) hmem]
    · exact h.idem (b, c)
    · exact h.orthogonal fun he => hb' (Prod.mk.injEq .. ▸ he).1.symm
  sum_eq_one := h.sum_marg_right

/-- The other order. -/
theorem IsPVM.marg_mul_marg' {P : B × C → Matrix N N ℂ} (h : IsPVM P) (b : B) (c : C) :
    (∑ c', P (b, c')) * (∑ b', P (b', c)) = P (b, c) := by
  classical
  rw [Finset.sum_mul]
  rw [Finset.sum_eq_single c (fun c' _ hc' => ?_) fun hmem => absurd (Finset.mem_univ c) hmem]
  · rw [Finset.mul_sum,
      Finset.sum_eq_single b (fun b' _ hb' => ?_) fun hmem => absurd (Finset.mem_univ b) hmem]
    · exact h.idem (b, c)
    · exact h.orthogonal fun he => hb' (Prod.mk.injEq .. ▸ he).1.symm
  · rw [Finset.mul_sum]
    refine Finset.sum_eq_zero fun b' _ => ?_
    exact h.orthogonal fun he => hc' (Prod.mk.injEq .. ▸ he).2

end Marginals

/-! ## The analysis

Stated for abstract families in one matrix algebra --- the two parties enter only through the
hypotheses `hcomm`, `hcomm'` (the factors commute) and `hmul`, `hmul'` (Bob's two marginals
multiply to the joint element). That keeps the algebra in a single type, and `commutation_analysis`
below is the instance where the families are `aOp` and `bOp` of a POVM and a projective
measurement. -/

section Analysis

variable {N : Type*} [Fintype N] [DecidableEq N] {B C : Type*} [Fintype B] [Fintype C]
  {v : N → ℂ} {δ : ℝ}

/-- Putting a family in front, with the front index in the first component of the pair. -/
theorem sum_prod_snorm_sq_mul_le_fst (v : N → ℂ)
    (F : B → Matrix N N ℂ) (hF : ∑ b, (F b)ᴴ * F b ≤ (1 : Matrix N N ℂ))
    (M : C → Matrix N N ℂ) :
    ∑ p : B × C, snorm v (F p.1 * M p.2) ^ 2 ≤ ∑ c, snorm v (M c) ^ 2 := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  exact Finset.sum_le_sum fun c _ => sum_snorm_sq_mul_le v F hF (M c)

/-- Putting a family in front, with the front index in the second component. -/
theorem sum_prod_snorm_sq_mul_le_snd (v : N → ℂ)
    (F : C → Matrix N N ℂ) (hF : ∑ c, (F c)ᴴ * F c ≤ (1 : Matrix N N ℂ))
    (M : B → Matrix N N ℂ) :
    ∑ p : B × C, snorm v (F p.2 * M p.1) ^ 2 ≤ ∑ b, snorm v (M b) ^ 2 := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_le_sum fun b _ => sum_snorm_sq_mul_le v F hF (M b)

/-- **The commutation analysis, in one algebra.** `alpha` and `gamma` are the two families that
are to commute; `betaB`, `betaC` are what they are respectively close to, and `betaBC` is the
joint operator both products reach. -/
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
    ∑ p : B × C, snorm v (alpha p.1 * gamma p.2 - gamma p.2 * alpha p.1) ^ 2 ≤ 16 * δ := by
  classical
  -- `alpha_b gamma_c` reaches `betaBC` in two steps
  have s1 : ∑ p : B × C, snorm v (alpha p.1 * gamma p.2 - alpha p.1 * betaC p.2) ^ 2 ≤ δ := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_))
      (le_trans (sum_prod_snorm_sq_mul_le_fst v alpha halpha
        (fun c => gamma c - betaC c)) hC)
    rw [Matrix.mul_sub]
  have s2 : ∑ p : B × C, snorm v (alpha p.1 * betaC p.2 - betaBC p) ^ 2 ≤ δ := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_))
      (le_trans (sum_prod_snorm_sq_mul_le_snd v betaC hbetaC
        (fun b => alpha b - betaB b)) hA)
    rw [Matrix.mul_sub, ← hcomm p.1 p.2, hmul p.1 p.2]
  have h1 : ∑ p : B × C, snorm v (alpha p.1 * gamma p.2 - betaBC p) ^ 2 ≤ 4 * δ := by
    refine le_trans (sum_snorm_sq_triangle' v _ (fun p => alpha p.1 * betaC p.2) _) ?_
    linarith
  -- `gamma_c alpha_b` reaches the same operator
  have s3 : ∑ p : B × C, snorm v (gamma p.2 * alpha p.1 - gamma p.2 * betaB p.1) ^ 2 ≤ δ := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_))
      (le_trans (sum_prod_snorm_sq_mul_le_snd v gamma hgamma
        (fun b => alpha b - betaB b)) hA)
    rw [Matrix.mul_sub]
  have s4 : ∑ p : B × C, snorm v (gamma p.2 * betaB p.1 - betaBC p) ^ 2 ≤ δ := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_))
      (le_trans (sum_prod_snorm_sq_mul_le_fst v betaB hbetaB
        (fun c => gamma c - betaC c)) hC)
    rw [Matrix.mul_sub, ← hcomm' p.1 p.2, hmul' p.1 p.2]
  have h2 : ∑ p : B × C, snorm v (gamma p.2 * alpha p.1 - betaBC p) ^ 2 ≤ 4 * δ := by
    refine le_trans (sum_snorm_sq_triangle' v _ (fun p => gamma p.2 * betaB p.1) _) ?_
    linarith
  have h2' : ∑ p : B × C, snorm v (betaBC p - gamma p.2 * alpha p.1) ^ 2 ≤ 4 * δ := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_)) h2
    rw [snorm_sub_comm]
  refine le_trans (sum_snorm_sq_triangle' v _ betaBC _) ?_
  linarith

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
          * aOp ((A.mats p.1).val)) ^ 2 ≤ 16 * δ :=
  commutation_analysis_abstract ψ
    (fun b => (aOp ((A.mats b).val) : Matrix (dA × dB) (dA × dB) ℂ))
    (fun c => (aOp ((Cm.mats c).val) : Matrix (dA × dB) (dA × dB) ℂ))
    (fun b => (bOp (∑ c, P (b, c)) : Matrix (dA × dB) (dA × dB) ℂ))
    (fun c => (bOp (∑ b, P (b, c)) : Matrix (dA × dB) (dA × dB) ℂ))
    (fun p => (bOp (P p) : Matrix (dA × dB) (dA × dB) ℂ))
    (sum_aOp_conjTranspose_mul_self_le_one A) (sum_aOp_conjTranspose_mul_self_le_one Cm)
    (le_of_eq (sum_bOp_conjTranspose_mul_self_of_isPVM hP.marg_left))
    (le_of_eq (sum_bOp_conjTranspose_mul_self_of_isPVM hP.marg_right))
    (fun b c => aOp_mul_bOp _ _) (fun b c => aOp_mul_bOp _ _)
    (fun b c => by rw [← bOp_mul, hP.marg_mul_marg b c])
    (fun b c => by rw [← bOp_mul, hP.marg_mul_marg' b c])
    hA hC

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
