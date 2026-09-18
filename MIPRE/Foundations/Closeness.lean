/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Distances

/-!
# The Hilbert--Schmidt closeness calculus

Every soundness argument in the pipeline compares two families of operators in the
*state-dependent* distance `∑_a ‖(M_a - N_a)|ψ⟩‖²` and then passes from closeness of the
families to closeness of the values, losing a square root. For a *synchronous* strategy the
state is the normalized trace itself, so that distance is the normalized Hilbert--Schmidt
distance of `MIPRE/Foundations/Distances.lean`, and the whole calculus follows from
Cauchy--Schwarz for `MIPRE.hsInner`.

This file is that calculus, and nothing about games.

* `MIPRE.ntr` — the real part of the normalized trace `Tr(M)/d`, with the identities the
  arguments use: additive, tracial (`ntr_mul_comm`), `ntr 1 = 1`;
* `hsNormSq_add`, `hsNormSq_sub` — the parallelogram expansion, which is where the cross term
  `2⟨A, B⟩` that Cauchy--Schwarz then bounds comes from;
* `re_hsInner_le`, `abs_re_hsInner_le` — **Cauchy--Schwarz** for the normalized
  Hilbert--Schmidt inner product;
* `sum_abs_re_hsInner_le` — Cauchy--Schwarz once more, over a finite index set: the form the
  arguments actually use, with the two sums of squared norms on the right;
* `sum_mul_sqrt_le` — the averaging step `𝔼 √f ≤ √(𝔼 f)`, again Cauchy--Schwarz.

## Implementation notes

`hsInner A B = τ(Aᴴ B)` is the inner product of a genuine inner product space (Mathlib's
`Matrix.toMatrixInnerProductSpace` at the identity), but that structure is a
`noncomputable def` rather than an instance, so using it would mean carrying `letI` through
every statement. Cauchy--Schwarz is instead proved here from the entrywise formula and
`Real.sum_sqrt_mul_sqrt_le`, which is the same proof and costs one lemma.
-/

namespace MIPRE

open Finset ComplexOrder Matrix

variable {n : Type*} [Fintype n]

/-! ## The normalized trace as a real number -/

/-- The real part of the dimension-normalized trace, `τ(M) = Tr(M)/d`. Outcome probabilities
of a synchronous strategy are values of this, and so is every quantity the closeness calculus
manipulates. -/
noncomputable def ntr (M : Matrix n n ℂ) : ℝ := M.trace.re / (Fintype.card n : ℝ)

@[simp] theorem ntr_zero : ntr (0 : Matrix n n ℂ) = 0 := by simp [ntr]

theorem ntr_fin (d : ℕ) (M : Matrix (Fin d) (Fin d) ℂ) : ntr M = M.trace.re / (d : ℝ) := by
  rw [ntr, Fintype.card_fin]

theorem ntr_add (A B : Matrix n n ℂ) : ntr (A + B) = ntr A + ntr B := by
  simp [ntr, Matrix.trace_add, add_div]

theorem ntr_sub (A B : Matrix n n ℂ) : ntr (A - B) = ntr A - ntr B := by
  simp [ntr, Matrix.trace_sub, sub_div]

theorem ntr_neg (A : Matrix n n ℂ) : ntr (-A) = -ntr A := by
  simp [ntr, Matrix.trace_neg, neg_div]

theorem ntr_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix n n ℂ) :
    ntr (∑ i ∈ s, f i) = ∑ i ∈ s, ntr (f i) := by
  simp [ntr, Matrix.trace_sum, Complex.re_sum, Finset.sum_div]

theorem ntr_mul_comm (A B : Matrix n n ℂ) : ntr (A * B) = ntr (B * A) := by
  rw [ntr, ntr, Matrix.trace_mul_comm]

theorem ntr_conjTranspose (A : Matrix n n ℂ) : ntr Aᴴ = ntr A := by
  rw [ntr, ntr, Matrix.trace_conjTranspose]
  simp

theorem ntr_one [DecidableEq n] [Nonempty n] : ntr (1 : Matrix n n ℂ) = 1 := by
  have h : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  rw [ntr, Matrix.trace_one]
  simp

/-! ## The Hilbert--Schmidt inner product, in terms of `ntr` -/

theorem re_hsInner_eq (A B : Matrix n n ℂ) : (hsInner A B).re = ntr (Aᴴ * B) := by
  rw [hsInner, ntr, ← Complex.ofReal_natCast, Complex.div_ofReal_re]

theorem hsNormSq_eq (A : Matrix n n ℂ) : hsNormSq A = ntr (Aᴴ * A) := by
  rw [hsNormSq, re_hsInner_eq]

theorem re_hsInner_comm (A B : Matrix n n ℂ) : (hsInner B A).re = (hsInner A B).re := by
  rw [re_hsInner_eq, re_hsInner_eq, ← ntr_conjTranspose (Bᴴ * A), Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]

theorem hsNormSq_neg (A : Matrix n n ℂ) : hsNormSq (-A) = hsNormSq A := by
  rw [hsNormSq_eq, hsNormSq_eq, Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg,
    neg_neg]

theorem re_hsInner_neg_right (A B : Matrix n n ℂ) :
    (hsInner A (-B)).re = -(hsInner A B).re := by
  rw [re_hsInner_eq, re_hsInner_eq, Matrix.mul_neg, ntr_neg]

theorem re_hsInner_neg_left (A B : Matrix n n ℂ) :
    (hsInner (-A) B).re = -(hsInner A B).re := by
  rw [← re_hsInner_comm (-A) B, re_hsInner_neg_right B A, re_hsInner_comm A B]

/-- The parallelogram expansion: the cross term is what Cauchy--Schwarz then bounds. -/
theorem hsNormSq_add (A B : Matrix n n ℂ) :
    hsNormSq (A + B) = hsNormSq A + 2 * (hsInner A B).re + hsNormSq B := by
  rw [hsNormSq_eq, hsNormSq_eq, hsNormSq_eq, re_hsInner_eq, Matrix.conjTranspose_add,
    Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, ntr_add, ntr_add, ntr_add]
  have h : ntr (Bᴴ * A) = ntr (Aᴴ * B) := by
    rw [← re_hsInner_eq, ← re_hsInner_eq, re_hsInner_comm]
  rw [h]
  ring

theorem hsNormSq_sub (A B : Matrix n n ℂ) :
    hsNormSq (A - B) = hsNormSq A - 2 * (hsInner A B).re + hsNormSq B := by
  rw [sub_eq_add_neg, hsNormSq_add, hsNormSq_neg, re_hsInner_neg_right]
  ring

/-! ## Cauchy--Schwarz -/

/-- The trace of `Aᴴ B`, entrywise. -/
private theorem trace_conjTranspose_mul_eq (A B : Matrix n n ℂ) :
    (Aᴴ * B).trace = ∑ p : n × n, star (A p.1 p.2) * B p.1 p.2 := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Fintype.sum_prod_type_right]

private theorem re_trace_self_eq (A : Matrix n n ℂ) :
    (Aᴴ * A).trace.re = ∑ p : n × n, ‖A p.1 p.2‖ ^ 2 := by
  rw [trace_conjTranspose_mul_eq, Complex.re_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.norm_eq_sqrt_sq_add_sq, Real.sq_sqrt (by positivity)]
  ring

private theorem re_trace_self_nonneg (A : Matrix n n ℂ) : 0 ≤ (Aᴴ * A).trace.re := by
  rw [re_trace_self_eq]
  positivity

private theorem re_trace_mul_le (A B : Matrix n n ℂ) :
    (Aᴴ * B).trace.re ≤ √((Aᴴ * A).trace.re) * √((Bᴴ * B).trace.re) := by
  calc (Aᴴ * B).trace.re
      ≤ ∑ p : n × n, ‖A p.1 p.2‖ * ‖B p.1 p.2‖ := by
        rw [trace_conjTranspose_mul_eq, Complex.re_sum]
        refine Finset.sum_le_sum fun p _ => ?_
        calc (star (A p.1 p.2) * B p.1 p.2).re
            ≤ ‖star (A p.1 p.2) * B p.1 p.2‖ := Complex.re_le_norm _
          _ = ‖A p.1 p.2‖ * ‖B p.1 p.2‖ := by rw [norm_mul, norm_star]
    _ = ∑ p : n × n, √(‖A p.1 p.2‖ ^ 2) * √(‖B p.1 p.2‖ ^ 2) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    _ ≤ √(∑ p : n × n, ‖A p.1 p.2‖ ^ 2) * √(∑ p : n × n, ‖B p.1 p.2‖ ^ 2) :=
        Real.sum_sqrt_mul_sqrt_le _ (fun _ => by positivity) (fun _ => by positivity)
    _ = √((Aᴴ * A).trace.re) * √((Bᴴ * B).trace.re) := by
        rw [re_trace_self_eq, re_trace_self_eq]

/-- **Cauchy--Schwarz** for the normalized Hilbert--Schmidt inner product. -/
theorem re_hsInner_le (A B : Matrix n n ℂ) :
    (hsInner A B).re ≤ √(hsNormSq A) * √(hsNormSq B) := by
  rcases Nat.eq_zero_or_pos (Fintype.card n) with hc | hc
  · have hn : IsEmpty n := Fintype.card_eq_zero_iff.mp hc
    simp [hsInner, hsNormSq]
  · have hd : (0 : ℝ) < (Fintype.card n : ℝ) := by exact_mod_cast hc
    have e1 : (hsInner A B).re = (Aᴴ * B).trace.re / (Fintype.card n : ℝ) := by
      rw [re_hsInner_eq, ntr]
    have e2 : √(hsNormSq A) * √(hsNormSq B)
        = √((Aᴴ * A).trace.re) * √((Bᴴ * B).trace.re) / (Fintype.card n : ℝ) := by
      rw [hsNormSq_eq, hsNormSq_eq, ntr, ntr, Real.sqrt_div (re_trace_self_nonneg A),
        Real.sqrt_div (re_trace_self_nonneg B), div_mul_div_comm, Real.mul_self_sqrt hd.le]
    rw [e1, e2]
    gcongr
    exact re_trace_mul_le A B

/-- Cauchy--Schwarz, both signs. -/
theorem abs_re_hsInner_le (A B : Matrix n n ℂ) :
    |(hsInner A B).re| ≤ √(hsNormSq A) * √(hsNormSq B) := by
  refine abs_le.mpr ⟨?_, re_hsInner_le A B⟩
  have h := re_hsInner_le (-A) B
  rw [hsNormSq_neg, re_hsInner_neg_left] at h
  linarith

/-- **Cauchy--Schwarz over a finite index set**, the form the soundness arguments use. -/
theorem sum_abs_re_hsInner_le {ι : Type*} (s : Finset ι) (M N : ι → Matrix n n ℂ) :
    |∑ i ∈ s, (hsInner (M i) (N i)).re|
      ≤ √(∑ i ∈ s, hsNormSq (M i)) * √(∑ i ∈ s, hsNormSq (N i)) := by
  calc |∑ i ∈ s, (hsInner (M i) (N i)).re|
      ≤ ∑ i ∈ s, |(hsInner (M i) (N i)).re| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, √(hsNormSq (M i)) * √(hsNormSq (N i)) :=
        Finset.sum_le_sum fun i _ => abs_re_hsInner_le _ _
    _ ≤ √(∑ i ∈ s, hsNormSq (M i)) * √(∑ i ∈ s, hsNormSq (N i)) :=
        Real.sum_sqrt_mul_sqrt_le _ (fun i => hsNormSq_nonneg (M i))
          (fun i => hsNormSq_nonneg (N i))

/-! ## Projections

A *projection* here is what a projective measurement's operators are: self-adjoint and
idempotent. Under the normalized trace the squared Hilbert--Schmidt norm of a projection, and
of a product of two projections, collapses to a normalized trace, which is what turns the
closeness calculus into statements about outcome probabilities. -/

/-- A projection's squared Hilbert--Schmidt norm is its normalized trace. -/
theorem hsNormSq_of_proj {P : Matrix n n ℂ} (hsa : star P = P) (hid : P * P = P) :
    hsNormSq P = ntr P := by
  rw [hsNormSq_eq, ← Matrix.star_eq_conjTranspose, hsa, hid]

/-- The squared Hilbert--Schmidt norm of a product of two projections is the normalized trace
of the product -- the very quantity a synchronous strategy's value is built from. -/
theorem hsNormSq_mul_of_proj {P Q : Matrix n n ℂ} (hP : star P = P) (hPid : P * P = P)
    (hQ : star Q = Q) (hQid : Q * Q = Q) : hsNormSq (P * Q) = ntr (P * Q) := by
  rw [hsNormSq_eq, ← Matrix.star_eq_conjTranspose, star_mul, hP, hQ,
    show Q * P * (P * Q) = Q * (P * P) * Q from by noncomm_ring, hPid, ntr_mul_comm,
    show Q * (Q * P) = Q * Q * P from by noncomm_ring, hQid]
  exact ntr_mul_comm Q P

/-- `⟨P E, Q E⟩ = τ(E P Q)` when `E` is a projection: how the arguments move a projection from
one side of the inner product to the other. -/
theorem re_hsInner_mul_mul_of_proj {E P Q : Matrix n n ℂ} (hE : star E = E) (hEid : E * E = E)
    (hP : star P = P) : (hsInner (P * E) (Q * E)).re = ntr (E * P * Q) := by
  rw [re_hsInner_eq, ← Matrix.star_eq_conjTranspose, star_mul, hE, hP,
    show E * P * (Q * E) = E * P * Q * E from by noncomm_ring, ntr_mul_comm,
    show E * (E * P * Q) = E * E * P * Q from by noncomm_ring, hEid]

/-- `⟨E, P E⟩ = τ(E P)` when `E` is a projection. -/
theorem re_hsInner_self_mul_of_proj {E P : Matrix n n ℂ} (hE : star E = E) (hEid : E * E = E) :
    (hsInner E (P * E)).re = ntr (E * P) := by
  rw [re_hsInner_eq, ← Matrix.star_eq_conjTranspose, hE,
    show E * (P * E) = E * P * E from by noncomm_ring, ntr_mul_comm,
    show E * (E * P) = E * E * P from by noncomm_ring, hEid]

/-- `⟨P E, E⟩ = τ(E P)` when `E` and `P` are projections. -/
theorem re_hsInner_mul_self_of_proj {E P : Matrix n n ℂ} (hE : star E = E) (hEid : E * E = E)
    (hP : star P = P) : (hsInner (P * E) E).re = ntr (E * P) := by
  rw [re_hsInner_eq, ← Matrix.star_eq_conjTranspose, star_mul, hE, hP,
    show E * P * E = E * P * E from rfl, ntr_mul_comm,
    show E * (E * P) = E * E * P from by noncomm_ring, hEid]

/-! ## The averaging step -/

/-- `𝔼_μ √f ≤ √(𝔼_μ 1) · √(𝔼_μ f)`, which for a probability distribution is Jensen's
inequality for the square root. It is Cauchy--Schwarz applied to `√μ` and `√(μ f)`. -/
theorem sum_mul_sqrt_le {ι : Type*} (s : Finset ι) (μ f : ι → ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (hf : ∀ i, 0 ≤ f i) :
    ∑ i ∈ s, μ i * √(f i) ≤ √(∑ i ∈ s, μ i) * √(∑ i ∈ s, μ i * f i) := by
  have key : ∀ i, μ i * √(f i) = √(μ i) * √(μ i * f i) := by
    intro i
    rw [Real.sqrt_mul (hμ i), ← mul_assoc, Real.mul_self_sqrt (hμ i)]
  rw [Finset.sum_congr rfl fun i _ => key i]
  exact Real.sum_sqrt_mul_sqrt_le _ hμ (fun i => mul_nonneg (hμ i) (hf i))

end MIPRE
