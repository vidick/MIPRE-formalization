/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Commutation
import MIPRE.Foundations.CrossConsistency
import MIPRE.Foundations.Dilation
import MIPRE.Foundations.Linearity

/-!
# The sandwich of two approximately commuting projective measurements

Two projective measurements `{X_a}` and `{Z_b}` on one party that *approximately commute* on a
state cannot in general be measured jointly. The **sandwich**

`R_{a,b} = Z_b X_a Z_b`

always can: it is a POVM --- exactly, by projectivity of `Z` alone --- so its Naimark dilation is
a genuine *projective* joint measurement, and the dilation's compression identity carries every
Born-rule estimate about `R` to the dilated measurement unchanged.

What has to be proved is that the sandwich is approximately self-consistent across the two
parties, and that is the content of `one_sub_sum_bornProb_sand_le`: a five-link chain from

`sum_{a,b} <psi| R_{a,b} (x) R'_{a,b} |psi>`  to  `1`,

whose links are, in order, the two parties' commutators (each paid for by one Cauchy--Schwarz
against a family of squared norms summing to at most one), the two parties' `X`-consistency
collapsed by `sum_a X'_a = Id`, and the `Z`-consistency. The one thing the chain must *not* do is
bound the `q^2` outcome pairs one at a time: that would cost a factor `q` and the conclusion has
to be `q`-independent. Every link here is therefore an estimate on a single operator product ---
either a sum that telescopes exactly, or one Cauchy--Schwarz over the whole outcome set.

The statement carries an index `iota` with weights, because that is how it is used: the two
measurements come from a question and the bound is an average over questions, and averaging a
square root would otherwise need a second Jensen step.
-/

noncomputable section

namespace MIPRE

open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker

set_option linter.unusedSectionVars false

/-! ## Weighted Cauchy--Schwarz -/

/-- **Cauchy--Schwarz against a weight.** The one inequality the chain's square roots come from,
and also the Jensen step that moves an average inside a square root (take `v = 1`). -/
theorem sum_weighted_mul_le_sqrt {ι : Type*} [Fintype ι] (w u v : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∑ i, w i * (u i * v i)
      ≤ Real.sqrt (∑ i, w i * u i ^ 2) * Real.sqrt (∑ i, w i * v i ^ 2) := by
  classical
  set f : ι → ℝ := fun i => Real.sqrt (w i) * u i with hf
  set g : ι → ℝ := fun i => Real.sqrt (w i) * v i with hg
  have hfg : ∀ i, f i * g i = w i * (u i * v i) := by
    intro i
    rw [hf, hg]
    show Real.sqrt (w i) * u i * (Real.sqrt (w i) * v i) = w i * (u i * v i)
    rw [show Real.sqrt (w i) * u i * (Real.sqrt (w i) * v i)
        = (Real.sqrt (w i) * Real.sqrt (w i)) * (u i * v i) from by ring,
      Real.mul_self_sqrt (hw i)]
  have hf2 : ∀ i, f i ^ 2 = w i * u i ^ 2 := by
    intro i
    rw [hf]
    show (Real.sqrt (w i) * u i) ^ 2 = w i * u i ^ 2
    rw [mul_pow, Real.sq_sqrt (hw i)]
  have hg2 : ∀ i, g i ^ 2 = w i * v i ^ 2 := by
    intro i
    rw [hg]
    show (Real.sqrt (w i) * v i) ^ 2 = w i * v i ^ 2
    rw [mul_pow, Real.sq_sqrt (hw i)]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset ι) f g
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => hf2 i,
    Finset.sum_congr rfl fun i (_ : i ∈ univ) => hg2 i] at hCS
  have hnn : 0 ≤ ∑ i, w i * u i ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)
  calc ∑ i, w i * (u i * v i) = ∑ i, f i * g i :=
        (Finset.sum_congr rfl fun i _ => hfg i).symm
    _ ≤ |∑ i, f i * g i| := le_abs_self _
    _ = Real.sqrt ((∑ i, f i * g i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((∑ i, w i * u i ^ 2) * ∑ i, w i * v i ^ 2) := Real.sqrt_le_sqrt hCS
    _ = Real.sqrt (∑ i, w i * u i ^ 2) * Real.sqrt (∑ i, w i * v i ^ 2) := Real.sqrt_mul hnn _

/-- An unweighted Cauchy--Schwarz, in the same shape. -/
theorem sum_mul_le_sqrt {ι : Type*} [Fintype ι] (u v : ι → ℝ) :
    ∑ i, u i * v i ≤ Real.sqrt (∑ i, u i ^ 2) * Real.sqrt (∑ i, v i ^ 2) := by
  have h := sum_weighted_mul_le_sqrt (fun _ : ι => (1 : ℝ)) u v fun _ => zero_le_one
  simpa using h

/-- **Moving an average inside a square root.** Cauchy--Schwarz against the constant one. -/
theorem sum_weighted_sqrt_le {ι : Type*} [Fintype ι] (w f : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (hf : ∀ i, 0 ≤ f i) :
    ∑ i, w i * Real.sqrt (f i) ≤ Real.sqrt (∑ i, w i * f i) := by
  have h := sum_weighted_mul_le_sqrt w (fun i => Real.sqrt (f i)) (fun _ => (1 : ℝ)) hw0
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => show
      w i * (Real.sqrt (f i) * 1) = w i * Real.sqrt (f i) from by rw [mul_one],
    Finset.sum_congr rfl fun i (_ : i ∈ univ) => show
      w i * Real.sqrt (f i) ^ 2 = w i * f i from by rw [Real.sq_sqrt (hf i)],
    Finset.sum_congr rfl fun i (_ : i ∈ univ) => show w i * (1 : ℝ) ^ 2 = w i from by ring,
    hw1, Real.sqrt_one, mul_one] at h
  exact h

/-! ## Sums over a product of the outcome set -/

theorem sum_prod_id {M : Type*} [AddCommMonoid M] {α : Type*} [Fintype α] (f : α × α → M) :
    ∑ p : α × α, f p = ∑ a : α, ∑ b : α, f (a, b) := by
  rw [← Finset.univ_product_univ, Finset.sum_product]

theorem sum_prod_swap {M : Type*} [AddCommMonoid M] {α : Type*} [Fintype α] (f : α × α → M) :
    ∑ p : α × α, f p = ∑ b : α, ∑ a : α, f (a, b) := by
  rw [sum_prod_id]
  exact Finset.sum_comm

/-! ## Quadratic forms: Cauchy--Schwarz and the order -/

section QForm

variable {N : Type*} [Fintype N]

theorem inner_evec (u w : N → ℂ) : (inner ℂ (evec u) (evec w) : ℂ) = star u ⬝ᵥ w := by
  rw [evec, evec, EuclideanSpace.inner_toLp_toLp, dotProduct]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- **Cauchy--Schwarz for a quadratic form.** The one estimate the chain uses, in the shape the
chain needs: the form of a product, split onto the two vectors. -/
theorem abs_qform_conjTranspose_mul_le (v : N → ℂ) (M P : Matrix N N ℂ) :
    |qform v (Mᴴ * P)| ≤ snorm v M * snorm v P := by
  have h : qform v (Mᴴ * P) = (inner ℂ (evec (M *ᵥ v)) (evec (P *ᵥ v)) : ℂ).re := by
    rw [qform, ← star_mulVec_dotProduct, inner_evec]
  rw [h]
  exact le_trans (Complex.abs_re_le_norm _) (norm_inner_le_norm _ _)

variable [DecidableEq N]

/-- **A projection is bounded by the identity.** -/
theorem proj_le_one {P : Matrix N N ℂ} (hsa : Pᴴ = P) (hidem : P * P = P) :
    P ≤ (1 : Matrix N N ℂ) := by
  refine sub_nonneg.mp (Matrix.nonneg_iff_posSemidef.mpr ?_)
  have h : (1 : Matrix N N ℂ) - P = ((1 : Matrix N N ℂ) - P)ᴴ * ((1 : Matrix N N ℂ) - P) := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hsa, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hidem]
    abel
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- **A projection is a contraction on a unit vector.** -/
theorem snorm_le_one_of_proj {v : N → ℂ} (hv : ‖evec v‖ = 1) {P : Matrix N N ℂ}
    (hsa : Pᴴ = P) (hidem : P * P = P) : snorm v P ≤ 1 := by
  have hsq : snorm v P ^ 2 ≤ 1 := by
    rw [snorm_sq_eq_qform, hsa, hidem]
    refine le_trans (qform_le_of_le v (proj_le_one hsa hidem)) ?_
    rw [qform_one v hv]
  nlinarith [snorm_nonneg v P, hsq]

end QForm

/-! ## The two factors -/

section Bipartite

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

theorem aOp_mul_bOp_eq (U : Matrix dA dA ℂ) (V : Matrix dB dB ℂ) :
    (aOp U : Matrix (dA × dB) _ ℂ) * bOp V = U ⊗ₖ V := by
  rw [aOp, bOp, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

theorem bornProb_eq_qform (ψ : dA × dB → ℂ) (U : Matrix dA dA ℂ) (V : Matrix dB dB ℂ) :
    bornProb ψ U V = qform ψ ((aOp U : Matrix (dA × dB) _ ℂ) * bOp V) := by
  rw [aOp_mul_bOp_eq, bornProb, qform]

/-- Cauchy--Schwarz for a mixed product, with the deviation on **Alice's** side. -/
theorem abs_qform_aOp_mul_bOp_le (ψ : dA × dB → ℂ) (U : Matrix dA dA ℂ) (V : Matrix dB dB ℂ) :
    |qform ψ ((aOp U : Matrix (dA × dB) _ ℂ) * bOp V)|
      ≤ ‖stateVecB ψ (Vᴴ)‖ * stateNorm ψ U := by
  have h : (aOp U : Matrix (dA × dB) _ ℂ) * bOp V = (bOp (Vᴴ) : Matrix (dA × dB) _ ℂ)ᴴ * aOp U := by
    rw [bOp_conjTranspose, Matrix.conjTranspose_conjTranspose, aOp_mul_bOp]
  rw [h, stateNorm]
  refine le_trans (abs_qform_conjTranspose_mul_le ψ _ _) (le_of_eq ?_)
  rw [← norm_stateVecB_eq_snorm, ← norm_stateVec_eq_snorm]

/-- Cauchy--Schwarz for a mixed product, with the deviation on **Bob's** side. -/
theorem abs_qform_aOp_mul_bOp_le' (ψ : dA × dB → ℂ) (U : Matrix dA dA ℂ) (V : Matrix dB dB ℂ) :
    |qform ψ ((aOp U : Matrix (dA × dB) _ ℂ) * bOp V)|
      ≤ stateNorm ψ (Uᴴ) * ‖stateVecB ψ V‖ := by
  have h : (aOp U : Matrix (dA × dB) _ ℂ) * bOp V = (aOp (Uᴴ) : Matrix (dA × dB) _ ℂ)ᴴ * bOp V := by
    rw [aOp_conjTranspose, Matrix.conjTranspose_conjTranspose]
  rw [h, stateNorm]
  refine le_trans (abs_qform_conjTranspose_mul_le ψ _ _) (le_of_eq ?_)
  rw [← norm_stateVecB_eq_snorm, ← norm_stateVec_eq_snorm]

/-- **A contraction in front costs nothing**, on Alice's side. -/
theorem stateNorm_mul_le (ψ : dA × dB → ℂ) {P : Matrix dA dA ℂ}
    (hP : Pᴴ * P ≤ (1 : Matrix dA dA ℂ)) (N : Matrix dA dA ℂ) :
    stateNorm ψ (P * N) ≤ stateNorm ψ N := by
  rw [stateNorm, stateNorm, norm_stateVec_eq_snorm, norm_stateVec_eq_snorm, aOp_mul]
  have h := snorm_mul_le ψ (bnd_aOp (HB := dB) hP) (aOp N : Matrix (dA × dB) _ ℂ)
  rwa [one_mul] at h

/-- **A contraction in front costs nothing**, on Bob's side. -/
theorem norm_stateVecB_mul_le (ψ : dA × dB → ℂ) {P : Matrix dB dB ℂ}
    (hP : Pᴴ * P ≤ (1 : Matrix dB dB ℂ)) (N : Matrix dB dB ℂ) :
    ‖stateVecB ψ (P * N)‖ ≤ ‖stateVecB ψ N‖ := by
  rw [norm_stateVecB_eq_snorm, norm_stateVecB_eq_snorm, bOp_mul]
  have h := snorm_mul_le ψ (bnd_bOp (HA := dA) hP) (bOp N : Matrix (dA × dB) _ ℂ)
  rwa [one_mul] at h

end Bipartite

/-! ## Sums of mutually orthogonal projections -/

section Proj

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- **A sum of mutually orthogonal projections is a projection.** -/
theorem conjTranspose_sum_of_orth {ι : Type*} [Fintype ι] {P : ι → Matrix N N ℂ}
    (hsa : ∀ i, (P i)ᴴ = P i) : (∑ i, P i)ᴴ = ∑ i, P i := by
  rw [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl fun i _ => hsa i

theorem mul_self_sum_of_orth {ι : Type*} [Fintype ι] [DecidableEq ι] {P : ι → Matrix N N ℂ}
    (hidem : ∀ i, P i * P i = P i) (horth : ∀ i j, i ≠ j → P i * P j = 0) :
    (∑ i, P i) * (∑ i, P i) = ∑ i, P i := by
  classical
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.sum_eq_single_of_mem i (mem_univ i)
    fun j _ hj => horth i j (Ne.symm hj)]
  exact hidem i

end Proj

/-! ## Products of the two factors -/

section Bipartite2

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

theorem aOp_bOp_mul_aOp_bOp (U U' : Matrix dA dA ℂ) (V V' : Matrix dB dB ℂ) :
    ((aOp U : Matrix (dA × dB) _ ℂ) * bOp V) * ((aOp U' : Matrix (dA × dB) _ ℂ) * bOp V')
      = (aOp (U * U') : Matrix (dA × dB) _ ℂ) * bOp (V * V') := by
  rw [aOp_mul_bOp_eq, aOp_mul_bOp_eq, aOp_mul_bOp_eq, ← Matrix.mul_kronecker_mul]

theorem aOp_bOp_conjTranspose (U : Matrix dA dA ℂ) (V : Matrix dB dB ℂ) :
    ((aOp U : Matrix (dA × dB) _ ℂ) * bOp V)ᴴ
      = (aOp (Uᴴ) : Matrix (dA × dB) _ ℂ) * bOp (Vᴴ) := by
  rw [aOp_mul_bOp_eq, aOp_mul_bOp_eq, Matrix.conjTranspose_kronecker]

theorem stateSqNorm_eq_qform (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) :
    stateSqNorm ψ M = qform ψ ((aOp (Mᴴ * M) : Matrix (dA × dB) _ ℂ)) := by
  rw [stateSqNorm, stateNorm, norm_stateVec_eq_snorm, snorm_sq_eq_qform, aOp_conjTranspose,
    ← aOp_mul]

theorem normSq_stateVecB_eq_qform (ψ : dA × dB → ℂ) (M : Matrix dB dB ℂ) :
    ‖stateVecB ψ M‖ ^ 2 = qform ψ ((bOp (Mᴴ * M) : Matrix (dA × dB) _ ℂ)) := by
  rw [norm_stateVecB_eq_snorm, snorm_sq_eq_qform, bOp_conjTranspose, ← bOp_mul]

/-- **Expanding a cross-party deviation.** -/
theorem xSqNorm_eq_expand (ψ : dA × dB → ℂ) {A : Matrix dA dA ℂ} (hA : Aᴴ = A)
    (B : Matrix dB dB ℂ) :
    xSqNorm ψ A B = stateSqNorm ψ A + ‖stateVecB ψ B‖ ^ 2 - 2 * bornProb ψ A B := by
  rw [xSqNorm, norm_sub_sq (𝕜 := ℂ), inner_stateVec_stateVecB ψ hA, stateSqNorm, stateNorm,
    bornProb]
  simp only [RCLike.re_to_complex]
  ring

/-- **The consistency of two projective measurements, as a defect from one.** With both families
projective the two diagonal sums are exactly one, so the agreement probability and the summed
cross-party deviation determine each other. -/
theorem one_sub_sum_bornProb_eq {A : Type*} [Fintype A] [DecidableEq A] {ψ : dA × dB → ℂ}
    (hψ : ‖evec ψ‖ = 1) {X : A → Matrix dA dA ℂ} {X' : A → Matrix dB dB ℂ}
    (hX : IsPVM X) (hX' : IsPVM X') :
    1 - ∑ a, bornProb ψ (X a) (X' a) = (∑ a, xSqNorm ψ (X a) (X' a)) / 2 := by
  classical
  have hA : ∑ a, stateSqNorm ψ (X a) = 1 := by
    rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => by
      rw [stateSqNorm_eq_qform (dB := dB) ψ (X a), hX.isSelfAdjoint a, hX.idem a],
      ← qform_sum, ← aOp_sum, hX.sum_eq_one, aOp_one, qform_one _ hψ]
  have hB : ∑ a, ‖stateVecB ψ (X' a)‖ ^ 2 = 1 := by
    rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => by
      rw [normSq_stateVecB_eq_qform (dA := dA) ψ (X' a), hX'.isSelfAdjoint a, hX'.idem a],
      ← qform_sum, ← bOp_sum, hX'.sum_eq_one, bOp_one, qform_one _ hψ]
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
    xSqNorm_eq_expand ψ (hX.isSelfAdjoint a) (X' a), Finset.sum_sub_distrib,
    Finset.sum_add_distrib, hA, hB, ← Finset.mul_sum]
  ring

end Bipartite2

/-! ## The sandwich -/

section Sand

variable {A : Type*} [Fintype A] [DecidableEq A]
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-- **The sandwich** `R_{a,b} = Z_b X_a Z_b` of two projective measurements. -/
def sand {d : Type*} [Fintype d] [DecidableEq d] (X Z : A → Matrix d d ℂ) (p : A × A) :
    Matrix d d ℂ :=
  Z p.2 * X p.1 * Z p.2

variable {d : Type*} [Fintype d] [DecidableEq d] {X Z : A → Matrix d d ℂ}

/-- The sandwich is the Gram operator of the ordered product, which is where its positivity and
its normalization both come from. -/
theorem sand_eq_gram (hX : IsPVM X) (hZ : IsPVM Z) (p : A × A) :
    sand X Z p = (X p.1 * Z p.2)ᴴ * (X p.1 * Z p.2) := by
  rw [Matrix.conjTranspose_mul, hX.isSelfAdjoint, hZ.isSelfAdjoint, sand]
  calc Z p.2 * X p.1 * Z p.2 = Z p.2 * (X p.1 * X p.1) * Z p.2 := by rw [hX.idem]
    _ = Z p.2 * X p.1 * (X p.1 * Z p.2) := by noncomm_ring

theorem sand_conjTranspose (hX : IsPVM X) (hZ : IsPVM Z) (p : A × A) :
    (sand X Z p)ᴴ = sand X Z p := by
  rw [sand_eq_gram hX hZ, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

theorem sand_posSemidef (hX : IsPVM X) (hZ : IsPVM Z) (p : A × A) : (sand X Z p).PosSemidef := by
  rw [sand_eq_gram hX hZ]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- **The sandwich is a POVM**, exactly: only projectivity of `Z` and completeness of `X` are
used, and no approximate commutation whatsoever. -/
theorem sum_sand (hX : IsPVM X) (hZ : IsPVM Z) : ∑ p : A × A, sand X Z p = 1 := by
  classical
  rw [sum_prod_swap]
  rw [Finset.sum_congr rfl fun b (_ : b ∈ univ) => show
      (∑ a : A, sand X Z (a, b)) = Z b from by
    rw [show (∑ a : A, sand X Z (a, b)) = Z b * (∑ a : A, X a) * Z b from by
        rw [Matrix.mul_sum, Finset.sum_mul]
        rfl,
      hX.sum_eq_one, Matrix.mul_one, hZ.idem]]
  exact hZ.sum_eq_one

/-- The sandwich, as a bundled POVM. -/
def sandPOVM (hX : IsPVM X) (hZ : IsPVM Z) : POVM (A × A) d where
  mats p := ⟨sand X Z p, selfAdjoint.mem_iff.mpr (by
    rw [Matrix.star_eq_conjTranspose]
    exact sand_conjTranspose hX hZ p)⟩
  nonneg p := Subtype.coe_le_coe.mp (Matrix.nonneg_iff_posSemidef.mpr (sand_posSemidef hX hZ p))
  normalized := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact sum_sand hX hZ

@[simp] theorem sandPOVM_mats (hX : IsPVM X) (hZ : IsPVM Z) (p : A × A) :
    (((sandPOVM hX hZ).mats p).val) = sand X Z p := rfl

end Sand

/-! ## The chain

Five links from the agreement of the two parties' sandwiches to one. The two middle links are the
parties' commutators, each paid for by one Cauchy--Schwarz against a family of squared norms
summing to at most one; the third collapses the `X`-outcome sum by completeness; the last is the
`Z`-consistency. -/

section Chain

variable {A : Type*} [Fintype A] [DecidableEq A]
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {X Z : A → Matrix dA dA ℂ} {X' Z' : A → Matrix dB dB ℂ}

/-- A projective measurement's elements are contractions. -/
theorem IsPVM.conjTranspose_mul_self_le_one {N : Type*} [Fintype N] [DecidableEq N]
    {P : A → Matrix N N ℂ} (h : IsPVM P) (a : A) : (P a)ᴴ * P a ≤ (1 : Matrix N N ℂ) := by
  rw [h.isSelfAdjoint a, h.idem a]
  exact proj_le_one (h.isSelfAdjoint a) (h.idem a)

/-- The ordered products' squared norms sum to exactly one. -/
theorem sum_stateSqNorm_ord (hψ : ‖evec ψ‖ = 1) (hX : IsPVM X) (hZ : IsPVM Z) :
    ∑ p : A × A, stateSqNorm ψ (X p.1 * Z p.2) = (1 : ℝ) := by
  classical
  have hterm : ∀ p : A × A, stateSqNorm ψ (X p.1 * Z p.2)
      = qform ψ ((aOp (sand X Z p) : Matrix (dA × dB) _ ℂ)) := by
    intro p
    rw [stateSqNorm_eq_qform (dB := dB) ψ, ← sand_eq_gram hX hZ]
  rw [Finset.sum_congr rfl fun p (_ : p ∈ univ) => hterm p, ← qform_sum, ← aOp_sum,
    sum_sand hX hZ, aOp_one, qform_one _ hψ]

/-- **Link 1**: replacing each sandwich by the ordered product costs Alice's commutator. -/
theorem abs_link1_le (hZ : IsPVM Z) {S' : A × A → Matrix dB dB ℂ}
    (hS' : ∀ p, (S' p)ᴴ = S' p) :
    |(∑ p : A × A, qform ψ ((aOp (sand X Z p) : Matrix (dA × dB) _ ℂ) * bOp (S' p)))
        - ∑ p : A × A, qform ψ ((aOp (Z p.2 * X p.1) : Matrix (dA × dB) _ ℂ) * bOp (S' p))|
      ≤ Real.sqrt (∑ p : A × A, stateSqNorm ψ (X p.1 * Z p.2 - Z p.2 * X p.1))
        * Real.sqrt (∑ p : A × A, ‖stateVecB ψ (S' p)‖ ^ 2) := by
  classical
  have hdiff : ∀ p : A × A, sand X Z p - Z p.2 * X p.1
      = Z p.2 * (X p.1 * Z p.2 - Z p.2 * X p.1) := by
    intro p
    calc sand X Z p - Z p.2 * X p.1
        = Z p.2 * X p.1 * Z p.2 - Z p.2 * Z p.2 * X p.1 := by rw [hZ.idem]; rfl
      _ = Z p.2 * (X p.1 * Z p.2 - Z p.2 * X p.1) := by noncomm_ring
  have hstep : (∑ p : A × A, qform ψ ((aOp (sand X Z p) : Matrix (dA × dB) _ ℂ) * bOp (S' p)))
        - ∑ p : A × A, qform ψ ((aOp (Z p.2 * X p.1) : Matrix (dA × dB) _ ℂ) * bOp (S' p))
      = ∑ p : A × A, qform ψ ((aOp (Z p.2 * (X p.1 * Z p.2 - Z p.2 * X p.1))
          : Matrix (dA × dB) _ ℂ) * bOp (S' p)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← hdiff p, aOp_sub, Matrix.sub_mul, qform_sub]
  rw [hstep]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun p (_ : p ∈ univ) => ?_)
    (sum_mul_le_sqrt (fun p : A × A => stateNorm ψ (X p.1 * Z p.2 - Z p.2 * X p.1))
      (fun p : A × A => ‖stateVecB ψ (S' p)‖))
  refine le_trans (abs_qform_aOp_mul_bOp_le ψ _ _) (le_of_le_of_eq ?_ (mul_comm _ _))
  rw [hS' p]
  exact mul_le_mul_of_nonneg_left
    (stateNorm_mul_le (dB := dB) ψ (hZ.conjTranspose_mul_self_le_one p.2) _) (norm_nonneg _)

/-- **Link 2**: replacing Bob's sandwich by his ordered product costs Bob's commutator. -/
theorem abs_link2_le (hX : IsPVM X) (hZ : IsPVM Z) (hZ' : IsPVM Z') :
    |(∑ p : A × A, qform ψ
          ((aOp (Z p.2 * X p.1) : Matrix (dA × dB) _ ℂ) * bOp (sand X' Z' p)))
        - ∑ p : A × A, qform ψ
          ((aOp (Z p.2 * X p.1) : Matrix (dA × dB) _ ℂ) * bOp (Z' p.2 * X' p.1))|
      ≤ Real.sqrt (∑ p : A × A, stateSqNorm ψ (X p.1 * Z p.2))
        * Real.sqrt (∑ p : A × A, ‖stateVecB ψ (X' p.1 * Z' p.2 - Z' p.2 * X' p.1)‖ ^ 2) := by
  classical
  have hdiff : ∀ p : A × A, sand X' Z' p - Z' p.2 * X' p.1
      = Z' p.2 * (X' p.1 * Z' p.2 - Z' p.2 * X' p.1) := by
    intro p
    calc sand X' Z' p - Z' p.2 * X' p.1
        = Z' p.2 * X' p.1 * Z' p.2 - Z' p.2 * Z' p.2 * X' p.1 := by rw [hZ'.idem]; rfl
      _ = Z' p.2 * (X' p.1 * Z' p.2 - Z' p.2 * X' p.1) := by noncomm_ring
  have hstep : (∑ p : A × A, qform ψ
          ((aOp (Z p.2 * X p.1) : Matrix (dA × dB) _ ℂ) * bOp (sand X' Z' p)))
        - ∑ p : A × A, qform ψ
          ((aOp (Z p.2 * X p.1) : Matrix (dA × dB) _ ℂ) * bOp (Z' p.2 * X' p.1))
      = ∑ p : A × A, qform ψ ((aOp (Z p.2 * X p.1) : Matrix (dA × dB) _ ℂ)
          * bOp (Z' p.2 * (X' p.1 * Z' p.2 - Z' p.2 * X' p.1))) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← hdiff p, bOp_sub, Matrix.mul_sub, qform_sub]
  rw [hstep]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun p (_ : p ∈ univ) => ?_)
    (sum_mul_le_sqrt (fun p : A × A => stateNorm ψ (X p.1 * Z p.2))
      (fun p : A × A => ‖stateVecB ψ (X' p.1 * Z' p.2 - Z' p.2 * X' p.1)‖))
  refine le_trans (abs_qform_aOp_mul_bOp_le' ψ _ _) ?_
  rw [Matrix.conjTranspose_mul, hX.isSelfAdjoint, hZ.isSelfAdjoint]
  exact mul_le_mul_of_nonneg_left
    (norm_stateVecB_mul_le (dA := dA) ψ (hZ'.conjTranspose_mul_self_le_one p.2) _)
    (stateNorm_nonneg _ _)

/-- The diagonal `Z`-agreement operator, and the `X`-disagreement operator: both projections,
because their summands are mutually orthogonal projections. -/
theorem isProj_diag (hZ : IsPVM Z) (hZ' : IsPVM Z') :
    ((∑ b : A, (aOp (Z b) : Matrix (dA × dB) _ ℂ) * bOp (Z' b))ᴴ
        = ∑ b : A, (aOp (Z b) : Matrix (dA × dB) _ ℂ) * bOp (Z' b))
      ∧ (∑ b : A, (aOp (Z b) : Matrix (dA × dB) _ ℂ) * bOp (Z' b))
          * (∑ b : A, (aOp (Z b) : Matrix (dA × dB) _ ℂ) * bOp (Z' b))
        = ∑ b : A, (aOp (Z b) : Matrix (dA × dB) _ ℂ) * bOp (Z' b) := by
  refine ⟨conjTranspose_sum_of_orth fun b => ?_, mul_self_sum_of_orth (fun b => ?_) fun b b' hb => ?_⟩
  · rw [aOp_bOp_conjTranspose, hZ.isSelfAdjoint, hZ'.isSelfAdjoint]
  · rw [aOp_bOp_mul_aOp_bOp, hZ.idem, hZ'.idem]
  · rw [aOp_bOp_mul_aOp_bOp, hZ'.orthogonal hb, bOp, Matrix.kronecker_zero, Matrix.mul_zero]

theorem isProj_disag (hX : IsPVM X) (hX' : IsPVM X') :
    ((∑ a : A, (aOp (1 - X a) : Matrix (dA × dB) _ ℂ) * bOp (X' a))ᴴ
        = ∑ a : A, (aOp (1 - X a) : Matrix (dA × dB) _ ℂ) * bOp (X' a))
      ∧ (∑ a : A, (aOp (1 - X a) : Matrix (dA × dB) _ ℂ) * bOp (X' a))
          * (∑ a : A, (aOp (1 - X a) : Matrix (dA × dB) _ ℂ) * bOp (X' a))
        = ∑ a : A, (aOp (1 - X a) : Matrix (dA × dB) _ ℂ) * bOp (X' a) := by
  have hsa : ∀ a : A, ((1 : Matrix dA dA ℂ) - X a)ᴴ = 1 - X a := fun a => by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hX.isSelfAdjoint]
  have hid : ∀ a : A, ((1 : Matrix dA dA ℂ) - X a) * (1 - X a) = 1 - X a := fun a => by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, hX.idem]
    abel
  refine ⟨conjTranspose_sum_of_orth fun a => ?_, mul_self_sum_of_orth (fun a => ?_) fun a a' ha => ?_⟩
  · rw [aOp_bOp_conjTranspose, hsa, hX'.isSelfAdjoint]
  · rw [aOp_bOp_mul_aOp_bOp, hid, hX'.idem]
  · rw [aOp_bOp_mul_aOp_bOp, hX'.orthogonal ha, bOp, Matrix.kronecker_zero, Matrix.mul_zero]

/-- The `X`-disagreement operator's expectation is the `X`-consistency defect. -/
theorem qform_disag (hψ : ‖evec ψ‖ = 1) (hX : IsPVM X) (hX' : IsPVM X') :
    qform ψ (∑ a : A, (aOp (1 - X a) : Matrix (dA × dB) _ ℂ) * bOp (X' a))
      = (∑ a : A, xSqNorm ψ (X a) (X' a)) / 2 := by
  classical
  have hterm : ∀ a : A, (aOp (1 - X a) : Matrix (dA × dB) _ ℂ) * bOp (X' a)
      = (bOp (X' a) : Matrix (dA × dB) _ ℂ) - (aOp (X a) : Matrix (dA × dB) _ ℂ) * bOp (X' a) := by
    intro a
    rw [aOp_sub, aOp_one, Matrix.sub_mul, Matrix.one_mul]
  have hone : ∑ a : A, qform ψ (bOp (X' a) : Matrix (dA × dB) _ ℂ) = 1 := by
    rw [← qform_sum, ← bOp_sum, hX'.sum_eq_one, bOp_one, qform_one _ hψ]
  rw [qform_sum, Finset.sum_congr rfl fun a (_ : a ∈ univ) => by
      rw [hterm a, qform_sub, ← bornProb_eq_qform], Finset.sum_sub_distrib, hone,
    ← one_sub_sum_bornProb_eq hψ hX hX']

/-- **Link 3**: dropping Alice's `X`-outcome costs her `X`-consistency with Bob, and nothing that
depends on the number of outcomes: the whole outcome sum is one operator product. -/
theorem abs_link3_le (hψ : ‖evec ψ‖ = 1) (hX : IsPVM X) (hZ : IsPVM Z)
    (hX' : IsPVM X') (hZ' : IsPVM Z') :
    |(∑ p : A × A, qform ψ
          ((aOp (Z p.2 * X p.1) : Matrix (dA × dB) _ ℂ) * bOp (Z' p.2 * X' p.1)))
        - ∑ p : A × A, qform ψ
          ((aOp (Z p.2) : Matrix (dA × dB) _ ℂ) * bOp (Z' p.2 * X' p.1))|
      ≤ Real.sqrt ((∑ a : A, xSqNorm ψ (X a) (X' a)) / 2) := by
  classical
  set Pd : Matrix (dA × dB) (dA × dB) ℂ :=
    ∑ b : A, (aOp (Z b) : Matrix (dA × dB) _ ℂ) * bOp (Z' b) with hPd
  set Dd : Matrix (dA × dB) (dA × dB) ℂ :=
    ∑ a : A, (aOp (1 - X a) : Matrix (dA × dB) _ ℂ) * bOp (X' a) with hDd
  have hprod : Pd * Dd = ∑ p : A × A, (aOp (Z p.2 * (1 - X p.1)) : Matrix (dA × dB) _ ℂ)
      * bOp (Z' p.2 * X' p.1) := by
    rw [sum_prod_swap (fun p : A × A => (aOp (Z p.2 * (1 - X p.1)) : Matrix (dA × dB) _ ℂ)
      * bOp (Z' p.2 * X' p.1)), hPd, hDd, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => aOp_bOp_mul_aOp_bOp _ _ _ _
  rw [abs_sub_comm]
  have hstep : (∑ p : A × A, qform ψ
          ((aOp (Z p.2) : Matrix (dA × dB) _ ℂ) * bOp (Z' p.2 * X' p.1)))
        - ∑ p : A × A, qform ψ
          ((aOp (Z p.2 * X p.1) : Matrix (dA × dB) _ ℂ) * bOp (Z' p.2 * X' p.1))
      = qform ψ (Pd * Dd) := by
    rw [hprod, qform_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← qform_sub]
    congr 1
    rw [Matrix.mul_sub, Matrix.mul_one, aOp_sub, Matrix.sub_mul]
  rw [hstep]
  have hPsa := (isProj_diag (dB := dB) hZ hZ').1
  have hPid := (isProj_diag (dB := dB) hZ hZ').2
  have hDsa := (isProj_disag (dB := dB) hX hX').1
  have hDid := (isProj_disag (dB := dB) hX hX').2
  have hcs : |qform ψ (Pd * Dd)| ≤ snorm ψ Pd * snorm ψ Dd := by
    have h := abs_qform_conjTranspose_mul_le ψ Pd Dd
    rwa [hPsa] at h
  have hP1 : snorm ψ Pd ≤ 1 := snorm_le_one_of_proj hψ hPsa hPid
  have hDeq : snorm ψ Dd = Real.sqrt ((∑ a : A, xSqNorm ψ (X a) (X' a)) / 2) := by
    rw [← qform_disag hψ hX hX', ← hDd,
      show qform ψ Dd = snorm ψ Dd ^ 2 from by rw [snorm_sq_eq_qform, hDsa, hDid],
      Real.sqrt_sq (snorm_nonneg ψ Dd)]
  rw [← hDeq]
  calc |qform ψ (Pd * Dd)| ≤ snorm ψ Pd * snorm ψ Dd := hcs
    _ ≤ 1 * snorm ψ Dd := mul_le_mul_of_nonneg_right hP1 (snorm_nonneg ψ Dd)
    _ = snorm ψ Dd := one_mul _

/-- **Link 4**: Bob's `X`-outcome sums away, exactly. -/
theorem link4_eq (hX' : IsPVM X') :
    ∑ p : A × A, qform ψ ((aOp (Z p.2) : Matrix (dA × dB) _ ℂ) * bOp (Z' p.2 * X' p.1))
      = ∑ b : A, qform ψ ((aOp (Z b) : Matrix (dA × dB) _ ℂ) * bOp (Z' b)) := by
  classical
  rw [sum_prod_swap (fun p : A × A => qform ψ
    ((aOp (Z p.2) : Matrix (dA × dB) _ ℂ) * bOp (Z' p.2 * X' p.1)))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← qform_sum]
  congr 1
  show (∑ a : A, (aOp (Z b) : Matrix (dA × dB) _ ℂ) * bOp (Z' b * X' a))
    = (aOp (Z b) : Matrix (dA × dB) _ ℂ) * bOp (Z' b)
  rw [← Matrix.mul_sum, ← bOp_sum, ← Matrix.mul_sum, hX'.sum_eq_one, Matrix.mul_one]

/-- **Link 5**: the `Z`-agreement is one minus half the `Z`-consistency defect. -/
theorem link5_eq (hψ : ‖evec ψ‖ = 1) (hZ : IsPVM Z) (hZ' : IsPVM Z') :
    ∑ b : A, qform ψ ((aOp (Z b) : Matrix (dA × dB) _ ℂ) * bOp (Z' b))
      = 1 - (∑ b : A, xSqNorm ψ (Z b) (Z' b)) / 2 := by
  rw [Finset.sum_congr rfl fun b (_ : b ∈ univ) => (bornProb_eq_qform ψ (Z b) (Z' b)).symm,
    ← one_sub_sum_bornProb_eq hψ hZ hZ']
  ring

end Chain

/-! ## The chain, assembled -/

section Assemble

variable {A : Type*} [Fintype A] [DecidableEq A]
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

theorem norm_evec_eq_one_of_unit {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) : ‖evec ψ‖ = 1 := by
  have h : ‖evec ψ‖ ^ 2 = 1 := by rw [norm_evec_sq, hψ, Complex.one_re]
  nlinarith [norm_nonneg (evec ψ), h]

/-- **The sandwich of two approximately commuting projective measurements is approximately
self-consistent across the two parties.** The five links of the chain, added up. Every error term
is `q`-independent: the two commutators enter under a square root through one Cauchy--Schwarz
each, the `X`-consistency through a third, and the `Z`-consistency linearly. -/
theorem one_sub_sum_bornProb_sand_le {ι : Type*} [Fintype ι] {w : ι → ℝ}
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    {X Z : ι → A → Matrix dA dA ℂ} {X' Z' : ι → A → Matrix dB dB ℂ}
    (hX : ∀ i, IsPVM (X i)) (hZ : ∀ i, IsPVM (Z i))
    (hX' : ∀ i, IsPVM (X' i)) (hZ' : ∀ i, IsPVM (Z' i))
    {cA cB α β : ℝ}
    (hcA : ∑ i, w i * ∑ p : A × A,
        stateSqNorm ψ (X i p.1 * Z i p.2 - Z i p.2 * X i p.1) ≤ cA)
    (hcB : ∑ i, w i * ∑ p : A × A,
        ‖stateVecB ψ (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1)‖ ^ 2 ≤ cB)
    (hα : ∑ i, w i * ∑ a : A, xSqNorm ψ (X i a) (X' i a) ≤ α)
    (hβ : ∑ i, w i * ∑ b : A, xSqNorm ψ (Z i b) (Z' i b) ≤ β) :
    1 - ∑ i, w i * ∑ p : A × A,
          bornProb ψ (sand (X i) (Z i) p) (sand (X' i) (Z' i) p)
      ≤ Real.sqrt cA + Real.sqrt cB + Real.sqrt (α / 2) + β / 2 := by
  classical
  have hψ' : ‖evec ψ‖ = 1 := norm_evec_eq_one_of_unit hψ
  set cAi : ι → ℝ := fun i => ∑ p : A × A,
    stateSqNorm ψ (X i p.1 * Z i p.2 - Z i p.2 * X i p.1) with hcAi
  set cBi : ι → ℝ := fun i => ∑ p : A × A,
    ‖stateVecB ψ (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1)‖ ^ 2 with hcBi
  set αi : ι → ℝ := fun i => ∑ a : A, xSqNorm ψ (X i a) (X' i a) with hαi
  set βi : ι → ℝ := fun i => ∑ b : A, xSqNorm ψ (Z i b) (Z' i b) with hβi
  have hcAi0 : ∀ i, 0 ≤ cAi i := fun i =>
    Finset.sum_nonneg fun p _ => stateSqNorm_nonneg _ _
  have hcBi0 : ∀ i, 0 ≤ cBi i := fun i => Finset.sum_nonneg fun p _ => sq_nonneg _
  have hαi0 : ∀ i, 0 ≤ αi i := fun i => Finset.sum_nonneg fun a _ => xSqNorm_nonneg _ _ _
  -- the pointwise chain
  have hpt : ∀ i, 1 - ∑ p : A × A,
        bornProb ψ (sand (X i) (Z i) p) (sand (X' i) (Z' i) p)
      ≤ Real.sqrt (cAi i) + Real.sqrt (cBi i) + Real.sqrt (αi i / 2) + βi i / 2 := by
    intro i
    have hborn : ∀ p : A × A,
        bornProb ψ (sand (X i) (Z i) p) (sand (X' i) (Z' i) p)
          = qform ψ ((aOp (sand (X i) (Z i) p) : Matrix (dA × dB) _ ℂ)
              * bOp (sand (X' i) (Z' i) p)) := fun p => bornProb_eq_qform ψ _ _
    rw [Finset.sum_congr rfl fun p (_ : p ∈ univ) => hborn p]
    -- the four links
    have h1 := abs_link1_le (ψ := ψ) (X := X i) (hZ i) (S' := sand (X' i) (Z' i))
      fun p => sand_conjTranspose (hX' i) (hZ' i) p
    have h2 := abs_link2_le (X := X i) (Z := Z i) (X' := X' i) (Z' := Z' i)
      (ψ := ψ) (hX i) (hZ i) (hZ' i)
    have h3 := abs_link3_le (ψ := ψ) hψ' (hX i) (hZ i) (hX' i) (hZ' i)
    have h4 := link4_eq (ψ := ψ) (Z := Z i) (Z' := Z' i) (hX' i)
    have h5 := link5_eq (ψ := ψ) hψ' (hZ i) (hZ' i)
    -- the two normalizations
    have hB1 : ∑ p : A × A, ‖stateVecB ψ (sand (X' i) (Z' i) p)‖ ^ 2 ≤ 1 := by
      have h := sum_stateSqNormB_le_one (dA := dA) (B := A × A) hψ (sandPOVM (hX' i) (hZ' i))
      simpa using h
    have hA1 : ∑ p : A × A, stateSqNorm ψ (X i p.1 * Z i p.2) = 1 :=
      sum_stateSqNorm_ord (dB := dB) hψ' (hX i) (hZ i)
    -- link 1's second factor and link 2's first factor are at most one
    have hs1 : Real.sqrt (∑ p : A × A, ‖stateVecB ψ (sand (X' i) (Z' i) p)‖ ^ 2) ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
      exact Real.sqrt_le_sqrt hB1
    have hs2 : Real.sqrt (∑ p : A × A, stateSqNorm ψ (X i p.1 * Z i p.2)) = 1 := by
      rw [hA1, Real.sqrt_one]
    have hsA0 : 0 ≤ Real.sqrt (cAi i) := Real.sqrt_nonneg _
    have hsB0 : 0 ≤ Real.sqrt (cBi i) := Real.sqrt_nonneg _
    have h1' : |(∑ p : A × A, qform ψ ((aOp (sand (X i) (Z i) p) : Matrix (dA × dB) _ ℂ)
          * bOp (sand (X' i) (Z' i) p)))
        - ∑ p : A × A, qform ψ ((aOp (Z i p.2 * X i p.1) : Matrix (dA × dB) _ ℂ)
          * bOp (sand (X' i) (Z' i) p))| ≤ Real.sqrt (cAi i) := by
      refine le_trans h1 ?_
      calc Real.sqrt (cAi i)
            * Real.sqrt (∑ p : A × A, ‖stateVecB ψ (sand (X' i) (Z' i) p)‖ ^ 2)
          ≤ Real.sqrt (cAi i) * 1 := mul_le_mul_of_nonneg_left hs1 hsA0
        _ = Real.sqrt (cAi i) := mul_one _
    have h2' : |(∑ p : A × A, qform ψ ((aOp (Z i p.2 * X i p.1) : Matrix (dA × dB) _ ℂ)
          * bOp (sand (X' i) (Z' i) p)))
        - ∑ p : A × A, qform ψ ((aOp (Z i p.2 * X i p.1) : Matrix (dA × dB) _ ℂ)
          * bOp (Z' i p.2 * X' i p.1))| ≤ Real.sqrt (cBi i) := by
      refine le_trans h2 ?_
      rw [hs2, one_mul]
    have habs1 := abs_le.mp h1'
    have habs2 := abs_le.mp h2'
    have habs3 := abs_le.mp h3
    rw [h4, h5] at habs3
    linarith [habs1.1, habs1.2, habs2.1, habs2.2, habs3.1, habs3.2]
  -- average
  have hsum : 1 - ∑ i, w i * ∑ p : A × A,
        bornProb ψ (sand (X i) (Z i) p) (sand (X' i) (Z' i) p)
      = ∑ i, w i * (1 - ∑ p : A × A,
          bornProb ψ (sand (X i) (Z i) p) (sand (X' i) (Z' i) p)) := by
    rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => mul_sub (w i) 1 _, Finset.sum_sub_distrib,
      Finset.sum_congr rfl fun i (_ : i ∈ univ) => mul_one (w i), hw1]
  rw [hsum]
  refine le_trans (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hpt i) (hw0 i)) ?_
  have hsplit : ∑ i, w i * (Real.sqrt (cAi i) + Real.sqrt (cBi i)
        + Real.sqrt (αi i / 2) + βi i / 2)
      = (∑ i, w i * Real.sqrt (cAi i)) + (∑ i, w i * Real.sqrt (cBi i))
        + (∑ i, w i * Real.sqrt (αi i / 2)) + ∑ i, w i * (βi i / 2) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit]
  have jA : ∑ i, w i * Real.sqrt (cAi i) ≤ Real.sqrt cA :=
    le_trans (sum_weighted_sqrt_le w cAi hw0 hw1 hcAi0) (Real.sqrt_le_sqrt hcA)
  have jB : ∑ i, w i * Real.sqrt (cBi i) ≤ Real.sqrt cB :=
    le_trans (sum_weighted_sqrt_le w cBi hw0 hw1 hcBi0) (Real.sqrt_le_sqrt hcB)
  have jα : ∑ i, w i * Real.sqrt (αi i / 2) ≤ Real.sqrt (α / 2) := by
    refine le_trans (sum_weighted_sqrt_le w (fun i => αi i / 2) hw0 hw1
      fun i => by linarith [hαi0 i]) (Real.sqrt_le_sqrt ?_)
    rw [show (∑ i, w i * (αi i / 2)) = (∑ i, w i * αi i) / 2 from by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring]
    linarith
  have jβ : ∑ i, w i * (βi i / 2) ≤ β / 2 := by
    rw [show (∑ i, w i * (βi i / 2)) = (∑ i, w i * βi i) / 2 from by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring]
    linarith
  linarith

end Assemble

/-! ## The two-sided extension, and the dilated joint measurement -/

section Ext2

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

theorem stateVecB_add' (ψ : dA × dB → ℂ) (M N : Matrix dB dB ℂ) :
    stateVecB ψ (M + N) = stateVecB ψ M + stateVecB ψ N := by
  show WithLp.toLp 2 _ = WithLp.toLp 2 _ + WithLp.toLp 2 _
  rw [Matrix.kronecker_add, Matrix.add_mulVec]
  rfl

theorem stateVecB_sub' (ψ : dA × dB → ℂ) (M N : Matrix dB dB ℂ) :
    stateVecB ψ (M - N) = stateVecB ψ M - stateVecB ψ N := by
  have h : M - N = M + (-1 : ℂ) • N := by module
  rw [h, stateVecB_add', stateVecB_smul]
  module

/-- **Replacing Bob's operator inside a cross-party deviation.** -/
theorem xNorm_le_add_stateVecB (ψ : dA × dB → ℂ) (Aop : Matrix dA dA ℂ) (B₁ B₂ : Matrix dB dB ℂ) :
    xNorm ψ Aop B₂ ≤ xNorm ψ Aop B₁ + ‖stateVecB ψ (B₁ - B₂)‖ := by
  rw [xNorm, xNorm, stateVecB_sub',
    show stateVec ψ Aop - stateVecB ψ B₂
      = (stateVec ψ Aop - stateVecB ψ B₁) + (stateVecB ψ B₁ - stateVecB ψ B₂) from by abel]
  exact norm_add_le _ _

variable {Anc Bnc : Type*} [Fintype Anc] [DecidableEq Anc] [Fintype Bnc] [DecidableEq Bnc]

/-- **The two-sided extension of a state**: one ancilla register in the fixed state `|a0>`
adjoined to *each* party. This is `def:expanded-state`'s shape with an inert ancilla, and it is
what a *pair* of Naimark dilations --- one per party --- is compressed back by. -/
def extVec2 (ψ : dA × dB → ℂ) (a₀ : Anc) (b₀ : Bnc) : (dA × Anc) × (dB × Bnc) → ℂ :=
  ((ancillaEmbed dA a₀) ⊗ₖ (ancillaEmbed dB b₀)) *ᵥ ψ

theorem ancillaEmbed_kron_isometry2 (a₀ : Anc) (b₀ : Bnc) :
    (((ancillaEmbed dA a₀) ⊗ₖ (ancillaEmbed dB b₀))ᴴ
        * ((ancillaEmbed dA a₀) ⊗ₖ (ancillaEmbed dB b₀)))
      = (1 : Matrix (dA × dB) (dA × dB) ℂ) := by
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ancillaEmbed_isometry,
    ancillaEmbed_isometry, Matrix.one_kronecker_one]

theorem extVec2_unit {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (a₀ : Anc) (b₀ : Bnc) :
    star (extVec2 ψ a₀ b₀) ⬝ᵥ extVec2 ψ a₀ b₀ = 1 := by
  rw [extVec2, star_mulVec_dotProduct, ancillaEmbed_kron_isometry2, Matrix.one_mulVec, hψ]

/-- **The Born rule on the twice-extended state is the Born rule of the two compressions.** -/
theorem bornProb_extVec2 (ψ : dA × dB → ℂ) (a₀ : Anc) (b₀ : Bnc)
    (EA : Matrix (dA × Anc) (dA × Anc) ℂ) (EB : Matrix (dB × Bnc) (dB × Bnc) ℂ) :
    bornProb (extVec2 ψ a₀ b₀) EA EB
      = bornProb ψ ((ancillaEmbed dA a₀)ᴴ * (EA * ancillaEmbed dA a₀))
          ((ancillaEmbed dB b₀)ᴴ * (EB * ancillaEmbed dB b₀)) := by
  rw [bornProb, bornProb, extVec2, dotProduct_mulVec_conj]
  congr 2
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]

theorem qform_aOp_extVec2 (ψ : dA × dB → ℂ) (a₀ : Anc) (b₀ : Bnc)
    (EA : Matrix (dA × Anc) (dA × Anc) ℂ) :
    qform (extVec2 ψ a₀ b₀) (aOp EA)
      = qform ψ ((aOp ((ancillaEmbed dA a₀)ᴴ * (EA * ancillaEmbed dA a₀))
          : Matrix (dA × dB) _ ℂ)) := by
  rw [show qform (extVec2 ψ a₀ b₀) (aOp EA)
      = bornProb (extVec2 ψ a₀ b₀) EA (1 : Matrix (dB × Bnc) (dB × Bnc) ℂ) from by
    rw [bornProb_eq_qform, bOp_one, Matrix.mul_one], bornProb_extVec2, Matrix.one_mul,
    ancillaEmbed_isometry, bornProb_eq_qform, bOp_one, Matrix.mul_one]

theorem qform_bOp_extVec2 (ψ : dA × dB → ℂ) (a₀ : Anc) (b₀ : Bnc)
    (EB : Matrix (dB × Bnc) (dB × Bnc) ℂ) :
    qform (extVec2 ψ a₀ b₀) (bOp EB)
      = qform ψ ((bOp ((ancillaEmbed dB b₀)ᴴ * (EB * ancillaEmbed dB b₀))
          : Matrix (dA × dB) _ ℂ)) := by
  rw [show qform (extVec2 ψ a₀ b₀) (bOp EB)
      = bornProb (extVec2 ψ a₀ b₀) (1 : Matrix (dA × Anc) (dA × Anc) ℂ) EB from by
    rw [bornProb_eq_qform, aOp_one, Matrix.one_mul], bornProb_extVec2, Matrix.one_mul,
    ancillaEmbed_isometry, bornProb_eq_qform, aOp_one, Matrix.one_mul]

/-- An operator with an inert ancilla compresses to itself. -/
theorem compress_aOp (b₀ : Bnc) (N : Matrix dB dB ℂ) :
    (ancillaEmbed dB b₀)ᴴ * ((aOp N : Matrix (dB × Bnc) _ ℂ) * ancillaEmbed dB b₀) = N := by
  rw [aOp, kron_one_mul_ancillaEmbed,
    ← Matrix.mul_assoc ((ancillaEmbed dB b₀)ᴴ) (ancillaEmbed dB b₀) N, ancillaEmbed_isometry,
    Matrix.one_mul]

/-- Bob's inert-ancilla operator has the same state norm on the extended state. -/
theorem normSq_stateVecB_extVec2_aOp (ψ : dA × dB → ℂ) (a₀ : Anc) (b₀ : Bnc)
    (N : Matrix dB dB ℂ) :
    ‖stateVecB (extVec2 ψ a₀ b₀) (aOp N : Matrix (dB × Bnc) _ ℂ)‖ ^ 2
      = ‖stateVecB ψ N‖ ^ 2 := by
  rw [normSq_stateVecB_eq_qform, aOp_conjTranspose, ← aOp_mul, qform_bOp_extVec2, compress_aOp,
    ← normSq_stateVecB_eq_qform]

end Ext2

/-! ## The dilated joint measurement -/

section Joint

variable {A : Type*} [Fintype A] [DecidableEq A]
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

theorem norm_stateVecB_extVec2_aOp {Anc Bnc : Type*} [Fintype Anc] [DecidableEq Anc]
    [Fintype Bnc] [DecidableEq Bnc] (ψ : dA × dB → ℂ) (a₀ : Anc) (b₀ : Bnc)
    (N : Matrix dB dB ℂ) :
    ‖stateVecB (extVec2 ψ a₀ b₀) (aOp N : Matrix (dB × Bnc) _ ℂ)‖ = ‖stateVecB ψ N‖ := by
  have h := normSq_stateVecB_extVec2_aOp ψ a₀ b₀ N
  nlinarith [norm_nonneg (stateVecB (extVec2 ψ a₀ b₀) (aOp N : Matrix (dB × Bnc) _ ℂ)),
    norm_nonneg (stateVecB ψ N), h]

/-- **Replacing Bob's operator inside a squared cross-party deviation**, at the usual factor
two. -/
theorem xSqNorm_le_of_stateVecB (ψ : dA × dB → ℂ) (Aop : Matrix dA dA ℂ)
    (B₁ B₂ : Matrix dB dB ℂ) :
    xSqNorm ψ Aop B₂ ≤ 2 * xSqNorm ψ Aop B₁ + 2 * ‖stateVecB ψ (B₁ - B₂)‖ ^ 2 := by
  have h := xNorm_le_add_stateVecB ψ Aop B₁ B₂
  rw [xSqNorm_eq_sq, xSqNorm_eq_sq]
  nlinarith [xNorm_nonneg ψ Aop B₂, xNorm_nonneg ψ Aop B₁,
    norm_nonneg (stateVecB ψ (B₁ - B₂)),
    sq_nonneg (xNorm ψ Aop B₁ - ‖stateVecB ψ (B₁ - B₂)‖)]

variable {ψ : dA × dB → ℂ}
  {Q : (A × A) → Matrix (dA × (A × A)) (dA × (A × A)) ℂ}
  {Q' : (A × A) → Matrix (dB × (A × A)) (dB × (A × A)) ℂ}
  {R : (A × A) → Matrix dA dA ℂ} {R' : (A × A) → Matrix dB dB ℂ}

/-- **The dilated pair's self-consistency is the sandwiches' agreement defect**, exactly: the
compression identity transports the whole Born-rule expansion. -/
theorem sum_xSqNorm_dilated_eq (hψ : star ψ ⬝ᵥ ψ = 1) (a₀ : A × A)
    (hQ : IsPVM Q) (hQ' : IsPVM Q')
    (hkA : ∀ p, (ancillaEmbed dA a₀)ᴴ * (Q p * ancillaEmbed dA a₀) = R p)
    (hkB : ∀ p, (ancillaEmbed dB a₀)ᴴ * (Q' p * ancillaEmbed dB a₀) = R' p)
    (hR : ∑ p : A × A, R p = 1) (hR' : ∑ p : A × A, R' p = 1) :
    ∑ p : A × A, xSqNorm (extVec2 ψ a₀ a₀) (Q p) (Q' p)
      = 2 * (1 - ∑ p : A × A, bornProb ψ (R p) (R' p)) := by
  classical
  have hψ' : ‖evec ψ‖ = 1 := norm_evec_eq_one_of_unit hψ
  have hterm : ∀ p : A × A, xSqNorm (extVec2 ψ a₀ a₀) (Q p) (Q' p)
      = qform ψ ((aOp (R p) : Matrix (dA × dB) _ ℂ)) + qform ψ ((bOp (R' p) : Matrix (dA × dB) _ ℂ))
        - 2 * bornProb ψ (R p) (R' p) := by
    intro p
    have e1 : stateSqNorm (extVec2 ψ a₀ a₀) (Q p)
        = qform ψ ((aOp (R p) : Matrix (dA × dB) _ ℂ)) := by
      rw [stateSqNorm_eq_qform, hQ.isSelfAdjoint p, hQ.idem p, qform_aOp_extVec2, hkA]
    have e2 : ‖stateVecB (extVec2 ψ a₀ a₀) (Q' p)‖ ^ 2
        = qform ψ ((bOp (R' p) : Matrix (dA × dB) _ ℂ)) := by
      rw [normSq_stateVecB_eq_qform, hQ'.isSelfAdjoint p, hQ'.idem p, qform_bOp_extVec2, hkB]
    have e3 : bornProb (extVec2 ψ a₀ a₀) (Q p) (Q' p) = bornProb ψ (R p) (R' p) := by
      rw [bornProb_extVec2, hkA, hkB]
    rw [xSqNorm_eq_expand _ (hQ.isSelfAdjoint p), e1, e2, e3]
  rw [Finset.sum_congr rfl fun p (_ : p ∈ univ) => hterm p, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← qform_sum, ← qform_sum, ← aOp_sum, ← bOp_sum, hR, hR',
    aOp_one, bOp_one, qform_one _ hψ', ← Finset.mul_sum]
  ring

/-- The same bound against the **undilated** sandwich on Bob's side, extended by identity on his
ancilla. -/
theorem sum_xSqNorm_dilated_aOp_le (hψ : star ψ ⬝ᵥ ψ = 1) (a₀ : A × A)
    (hQ : IsPVM Q)
    (hkA : ∀ p, (ancillaEmbed dA a₀)ᴴ * (Q p * ancillaEmbed dA a₀) = R p)
    (hR : ∑ p : A × A, R p = 1) (hR'B : ∑ p : A × A, ‖stateVecB ψ (R' p)‖ ^ 2 ≤ 1) :
    ∑ p : A × A, xSqNorm (extVec2 ψ a₀ a₀) (Q p) (aOp (R' p))
      ≤ 2 * (1 - ∑ p : A × A, bornProb ψ (R p) (R' p)) := by
  classical
  have hψ' : ‖evec ψ‖ = 1 := norm_evec_eq_one_of_unit hψ
  have hterm : ∀ p : A × A, xSqNorm (extVec2 ψ a₀ a₀) (Q p) (aOp (R' p))
      = qform ψ ((aOp (R p) : Matrix (dA × dB) _ ℂ)) + ‖stateVecB ψ (R' p)‖ ^ 2
        - 2 * bornProb ψ (R p) (R' p) := by
    intro p
    have e1 : stateSqNorm (extVec2 ψ a₀ a₀) (Q p)
        = qform ψ ((aOp (R p) : Matrix (dA × dB) _ ℂ)) := by
      rw [stateSqNorm_eq_qform, hQ.isSelfAdjoint p, hQ.idem p, qform_aOp_extVec2, hkA]
    have e3 : bornProb (extVec2 ψ a₀ a₀) (Q p) (aOp (R' p)) = bornProb ψ (R p) (R' p) := by
      rw [bornProb_extVec2, hkA, compress_aOp]
    rw [xSqNorm_eq_expand _ (hQ.isSelfAdjoint p), e1, e3, normSq_stateVecB_extVec2_aOp]
  rw [Finset.sum_congr rfl fun p (_ : p ∈ univ) => hterm p, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← qform_sum, ← aOp_sum, hR, aOp_one, qform_one _ hψ',
    ← Finset.mul_sum]
  linarith

end Joint

/-! ## The theorem -/

section Main

variable {A : Type*} [Fintype A] [DecidableEq A]
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-- **Two approximately commuting projective measurements on each party admit a joint projective
measurement**, on each party's space enlarged by one ancilla register, which is self-consistent
across the parties and consistent with *both* ordered products of the originals --- all at errors
independent of the number of outcomes.

The construction is the Naimark dilation of the sandwich `Z_b X_a Z_b`; `hkA` and `hkB` record
that the dilations compress back to it, which is what carries every estimate. -/
theorem exists_projective_joint {ι : Type*} [Fintype ι] {w : ι → ℝ}
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (a₀ : A × A)
    {X Z : ι → A → Matrix dA dA ℂ} {X' Z' : ι → A → Matrix dB dB ℂ}
    (hX : ∀ i, IsPVM (X i)) (hZ : ∀ i, IsPVM (Z i))
    (hX' : ∀ i, IsPVM (X' i)) (hZ' : ∀ i, IsPVM (Z' i))
    {cA cB α β : ℝ}
    (hcA : ∑ i, w i * ∑ p : A × A,
        stateSqNorm ψ (X i p.1 * Z i p.2 - Z i p.2 * X i p.1) ≤ cA)
    (hcB : ∑ i, w i * ∑ p : A × A,
        ‖stateVecB ψ (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1)‖ ^ 2 ≤ cB)
    (hα : ∑ i, w i * ∑ a : A, xSqNorm ψ (X i a) (X' i a) ≤ α)
    (hβ : ∑ i, w i * ∑ b : A, xSqNorm ψ (Z i b) (Z' i b) ≤ β) :
    ∃ (QA : ι → (A × A) → Matrix (dA × (A × A)) (dA × (A × A)) ℂ)
      (QB : ι → (A × A) → Matrix (dB × (A × A)) (dB × (A × A)) ℂ),
      (∀ i, IsPVM (QA i)) ∧ (∀ i, IsPVM (QB i))
      ∧ (∀ i p, (ancillaEmbed dA a₀)ᴴ * (QA i p * ancillaEmbed dA a₀) = sand (X i) (Z i) p)
      ∧ (∀ i p, (ancillaEmbed dB a₀)ᴴ * (QB i p * ancillaEmbed dB a₀) = sand (X' i) (Z' i) p)
      ∧ (∑ i, w i * ∑ p : A × A, xSqNorm (extVec2 ψ a₀ a₀) (QA i p) (QB i p)
          ≤ 2 * (Real.sqrt cA + Real.sqrt cB + Real.sqrt (α / 2) + β / 2))
      ∧ (∑ i, w i * ∑ p : A × A,
            xSqNorm (extVec2 ψ a₀ a₀) (QA i p) (aOp (Z' i p.2 * X' i p.1))
          ≤ 4 * (Real.sqrt cA + Real.sqrt cB + Real.sqrt (α / 2) + β / 2) + 2 * cB)
      ∧ (∑ i, w i * ∑ p : A × A,
            xSqNorm (extVec2 ψ a₀ a₀) (QA i p) (aOp (X' i p.1 * Z' i p.2))
          ≤ 4 * (Real.sqrt cA + Real.sqrt cB + Real.sqrt (α / 2) + β / 2) + 8 * cB) := by
  classical
  -- the two dilations
  obtain ⟨PA, hAsa, hAid, hAsum, hAk⟩ :=
    exists_projective_dilation (d := dA) (A := A × A) (X := ι) a₀
      (E := fun i p => sand (X i) (Z i) p)
      (fun i p => sand_posSemidef (hX i) (hZ i) p) fun i => sum_sand (hX i) (hZ i)
  obtain ⟨PB, hBsa, hBid, hBsum, hBk⟩ :=
    exists_projective_dilation (d := dB) (A := A × A) (X := ι) a₀
      (E := fun i p => sand (X' i) (Z' i) p)
      (fun i p => sand_posSemidef (hX' i) (hZ' i) p) fun i => sum_sand (hX' i) (hZ' i)
  have hPA : ∀ i, IsPVM (PA i) := fun i =>
    { isSelfAdjoint := fun p => by rw [← Matrix.star_eq_conjTranspose, hAsa i p]
      idem := hAid i
      sum_eq_one := hAsum i }
  have hPB : ∀ i, IsPVM (PB i) := fun i =>
    { isSelfAdjoint := fun p => by rw [← Matrix.star_eq_conjTranspose, hBsa i p]
      idem := hBid i
      sum_eq_one := hBsum i }
  -- the chain
  have hchain := one_sub_sum_bornProb_sand_le hw0 hw1 hψ hX hZ hX' hZ' hcA hcB hα hβ
  set Γ : ℝ := Real.sqrt cA + Real.sqrt cB + Real.sqrt (α / 2) + β / 2 with hΓ
  set γ : ι → ℝ := fun i => 1 - ∑ p : A × A,
    bornProb ψ (sand (X i) (Z i) p) (sand (X' i) (Z' i) p) with hγ
  have hγsum : ∑ i, w i * γ i ≤ Γ := by
    rw [hγ, hΓ]
    rw [show (∑ i, w i * (1 - ∑ p : A × A,
          bornProb ψ (sand (X i) (Z i) p) (sand (X' i) (Z' i) p)))
        = 1 - ∑ i, w i * ∑ p : A × A,
          bornProb ψ (sand (X i) (Z i) p) (sand (X' i) (Z' i) p) from by
      rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => mul_sub (w i) 1 _,
        Finset.sum_sub_distrib, Finset.sum_congr rfl fun i (_ : i ∈ univ) => mul_one (w i), hw1]]
    exact hchain
  have hB1 : ∀ i, ∑ p : A × A, ‖stateVecB ψ (sand (X' i) (Z' i) p)‖ ^ 2 ≤ 1 := fun i => by
    have h := sum_stateSqNormB_le_one (dA := dA) (B := A × A) hψ (sandPOVM (hX' i) (hZ' i))
    simpa using h
  -- item 1: self-consistency
  have hitem1 : ∀ i, ∑ p : A × A, xSqNorm (extVec2 ψ a₀ a₀) (PA i p) (PB i p) = 2 * γ i :=
    fun i => sum_xSqNorm_dilated_eq hψ a₀ (hPA i) (hPB i) (hAk i) (hBk i)
      (sum_sand (hX i) (hZ i)) (sum_sand (hX' i) (hZ' i))
  -- item 1': against the undilated sandwich
  have hitem1' : ∀ i, ∑ p : A × A,
      xSqNorm (extVec2 ψ a₀ a₀) (PA i p) (aOp (sand (X' i) (Z' i) p)) ≤ 2 * γ i := fun i =>
    sum_xSqNorm_dilated_aOp_le hψ a₀ (hPA i) (hAk i) (sum_sand (hX i) (hZ i)) (hB1 i)
  -- the sandwich is close to each ordered product, on Bob's side
  have hord1 : ∀ (i : ι) (p : A × A),
      ‖stateVecB ψ (sand (X' i) (Z' i) p - Z' i p.2 * X' i p.1)‖
        ≤ ‖stateVecB ψ (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1)‖ := by
    intro i p
    rw [show sand (X' i) (Z' i) p - Z' i p.2 * X' i p.1
        = Z' i p.2 * (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1) from by
      calc sand (X' i) (Z' i) p - Z' i p.2 * X' i p.1
          = Z' i p.2 * X' i p.1 * Z' i p.2 - Z' i p.2 * Z' i p.2 * X' i p.1 := by
            rw [(hZ' i).idem]; rfl
        _ = Z' i p.2 * (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1) := by noncomm_ring]
    exact norm_stateVecB_mul_le (dA := dA) ψ ((hZ' i).conjTranspose_mul_self_le_one p.2) _
  have hord2 : ∀ (i : ι) (p : A × A),
      ‖stateVecB ψ (sand (X' i) (Z' i) p - X' i p.1 * Z' i p.2)‖
        ≤ 2 * ‖stateVecB ψ (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1)‖ := by
    intro i p
    have hsplit : sand (X' i) (Z' i) p - X' i p.1 * Z' i p.2
        = (sand (X' i) (Z' i) p - Z' i p.2 * X' i p.1)
          - (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1) := by abel
    rw [hsplit, stateVecB_sub']
    refine le_trans (norm_sub_le _ _) ?_
    have h1 := hord1 i p
    linarith
  -- items 2 and 3
  have hitem2 : ∀ i, ∑ p : A × A,
        xSqNorm (extVec2 ψ a₀ a₀) (PA i p) (aOp (Z' i p.2 * X' i p.1))
      ≤ 4 * γ i + 2 * ∑ p : A × A,
        ‖stateVecB ψ (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1)‖ ^ 2 := by
    intro i
    have hstep : ∀ p : A × A,
        xSqNorm (extVec2 ψ a₀ a₀) (PA i p) (aOp (Z' i p.2 * X' i p.1))
          ≤ 2 * xSqNorm (extVec2 ψ a₀ a₀) (PA i p) (aOp (sand (X' i) (Z' i) p))
            + 2 * ‖stateVecB ψ (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1)‖ ^ 2 := by
      intro p
      refine le_trans (xSqNorm_le_of_stateVecB _ _ (aOp (sand (X' i) (Z' i) p)) _) ?_
      have hred : ‖stateVecB (extVec2 ψ a₀ a₀)
            ((aOp (sand (X' i) (Z' i) p) : Matrix (dB × (A × A)) _ ℂ)
              - aOp (Z' i p.2 * X' i p.1))‖
          ≤ ‖stateVecB ψ (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1)‖ := by
        rw [← aOp_sub, norm_stateVecB_extVec2_aOp]
        exact hord1 i p
      have h0 := norm_nonneg (stateVecB (extVec2 ψ a₀ a₀)
        ((aOp (sand (X' i) (Z' i) p) : Matrix (dB × (A × A)) _ ℂ)
          - aOp (Z' i p.2 * X' i p.1)))
      nlinarith [norm_nonneg (stateVecB ψ (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1))]
    refine le_trans (Finset.sum_le_sum fun p _ => hstep p) ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h := hitem1' i
    linarith
  have hitem3 : ∀ i, ∑ p : A × A,
        xSqNorm (extVec2 ψ a₀ a₀) (PA i p) (aOp (X' i p.1 * Z' i p.2))
      ≤ 4 * γ i + 8 * ∑ p : A × A,
        ‖stateVecB ψ (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1)‖ ^ 2 := by
    intro i
    have hstep : ∀ p : A × A,
        xSqNorm (extVec2 ψ a₀ a₀) (PA i p) (aOp (X' i p.1 * Z' i p.2))
          ≤ 2 * xSqNorm (extVec2 ψ a₀ a₀) (PA i p) (aOp (sand (X' i) (Z' i) p))
            + 8 * ‖stateVecB ψ (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1)‖ ^ 2 := by
      intro p
      refine le_trans (xSqNorm_le_of_stateVecB _ _ (aOp (sand (X' i) (Z' i) p)) _) ?_
      have hred : ‖stateVecB (extVec2 ψ a₀ a₀)
            ((aOp (sand (X' i) (Z' i) p) : Matrix (dB × (A × A)) _ ℂ)
              - aOp (X' i p.1 * Z' i p.2))‖
          ≤ 2 * ‖stateVecB ψ (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1)‖ := by
        rw [← aOp_sub, norm_stateVecB_extVec2_aOp]
        exact hord2 i p
      have h0 := norm_nonneg (stateVecB (extVec2 ψ a₀ a₀)
        ((aOp (sand (X' i) (Z' i) p) : Matrix (dB × (A × A)) _ ℂ)
          - aOp (X' i p.1 * Z' i p.2)))
      nlinarith [norm_nonneg (stateVecB ψ (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1))]
    refine le_trans (Finset.sum_le_sum fun p _ => hstep p) ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h := hitem1' i
    linarith
  refine ⟨PA, PB, hPA, hPB, hAk, hBk, ?_, ?_, ?_⟩
  · rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => by rw [hitem1 i]]
    rw [show (∑ i, w i * (2 * γ i)) = 2 * ∑ i, w i * γ i from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring]
    linarith
  · refine le_trans (Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hitem2 i) (hw0 i)) ?_
    rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => mul_add (w i) (4 * γ i) _,
      Finset.sum_add_distrib,
      show (∑ i, w i * (4 * γ i)) = 4 * ∑ i, w i * γ i from by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring,
      show (∑ i, w i * (2 * ∑ p : A × A,
            ‖stateVecB ψ (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1)‖ ^ 2))
          = 2 * ∑ i, w i * ∑ p : A × A,
            ‖stateVecB ψ (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1)‖ ^ 2 from by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring]
    linarith
  · refine le_trans (Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hitem3 i) (hw0 i)) ?_
    rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => mul_add (w i) (4 * γ i) _,
      Finset.sum_add_distrib,
      show (∑ i, w i * (4 * γ i)) = 4 * ∑ i, w i * γ i from by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring,
      show (∑ i, w i * (8 * ∑ p : A × A,
            ‖stateVecB ψ (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1)‖ ^ 2))
          = 8 * ∑ i, w i * ∑ p : A × A,
            ‖stateVecB ψ (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1)‖ ^ 2 from by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring]
    linarith

end Main

end MIPRE

end
