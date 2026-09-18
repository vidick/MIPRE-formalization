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

theorem re_hsInner_add_left (A B C : Matrix n n ℂ) :
    (hsInner (A + B) C).re = (hsInner A C).re + (hsInner B C).re := by
  rw [re_hsInner_eq, re_hsInner_eq, re_hsInner_eq, Matrix.conjTranspose_add, Matrix.add_mul,
    ntr_add]

theorem re_hsInner_add_right (A B C : Matrix n n ℂ) :
    (hsInner A (B + C)).re = (hsInner A B).re + (hsInner A C).re := by
  rw [re_hsInner_eq, re_hsInner_eq, re_hsInner_eq, Matrix.mul_add, ntr_add]

theorem re_hsInner_sub_left (A B C : Matrix n n ℂ) :
    (hsInner (A - B) C).re = (hsInner A C).re - (hsInner B C).re := by
  rw [re_hsInner_eq, re_hsInner_eq, re_hsInner_eq, Matrix.conjTranspose_sub, Matrix.sub_mul,
    ntr_sub]

theorem re_hsInner_sub_right (A B C : Matrix n n ℂ) :
    (hsInner A (B - C)).re = (hsInner A B).re - (hsInner A C).re := by
  rw [re_hsInner_eq, re_hsInner_eq, re_hsInner_eq, Matrix.mul_sub, ntr_sub]

theorem hsNormSq_eq_re_hsInner_self (A : Matrix n n ℂ) : hsNormSq A = (hsInner A A).re := rfl

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

/-- `⟨P Q, E⟩ = τ(E Q P)` for self-adjoint `P` and `Q`. -/
theorem re_hsInner_mul_of_proj {P Q E : Matrix n n ℂ} (hP : star P = P) (hQ : star Q = Q) :
    (hsInner (P * Q) E).re = ntr (E * Q * P) := by
  rw [re_hsInner_eq, ← Matrix.star_eq_conjTranspose, star_mul, hP, hQ, ntr_mul_comm,
    show E * (Q * P) = E * Q * P from by noncomm_ring]

section OneSub

variable [DecidableEq n]

theorem star_one_sub {P : Matrix n n ℂ} (hP : star P = P) : star (1 - P) = 1 - P := by
  rw [star_sub, star_one, hP]

theorem one_sub_mul_one_sub {P : Matrix n n ℂ} (hPid : P * P = P) :
    (1 - P) * (1 - P) = 1 - P := by
  rw [show (1 - P) * (1 - P) = 1 - P - P + P * P from by noncomm_ring, hPid]
  abel

end OneSub

/-! ## The closeness estimate

The one inequality the soundness argument needs, and the only place a Cauchy--Schwarz is
spent before the value comparison. Three families of projections: `O` a measurement, and `C`,
`D` such that the products `C D` are a measurement too. Then the squared distance between
`C_i D_i` and `O_i` is bounded by three times the two *disagreements* `τ(O_i(1 - D_i))` and
`τ(O_i(1 - C_i))` --- linearly, with no square root. Writing `C_i O_i = O_i - X_i` and
`D_i O_i = O_i - Y_i`, the two disagreements are exactly `∑ ‖X_i‖²` and `∑ ‖Y_i‖²`, and the
only term that is not one of them is `∑ ⟨Y_i, X_i⟩`, which Cauchy--Schwarz and the
arithmetic-geometric mean inequality bound by half their sum. -/

section Estimate

variable [DecidableEq n]

theorem sum_hsNormSq_sub_le {ι : Type*} [Fintype ι] (O C D : ι → Matrix n n ℂ)
    (hO : ∀ i, star (O i) = O i) (hOid : ∀ i, O i * O i = O i)
    (hC : ∀ i, star (C i) = C i) (hCid : ∀ i, C i * C i = C i)
    (hD : ∀ i, star (D i) = D i) (hDid : ∀ i, D i * D i = D i)
    (hOsum : ∑ i, ntr (O i) = 1) (hCDsum : ∑ i, ntr (C i * D i) = 1) :
    ∑ i, hsNormSq (C i * D i - O i)
      ≤ 3 * ((∑ i, ntr (O i * (1 - D i))) + ∑ i, ntr (O i * (1 - C i))) := by
  -- the two error families, and their squared norms
  have hX : ∀ i, hsNormSq ((1 - C i) * O i) = ntr (O i * (1 - C i)) := fun i => by
    rw [hsNormSq_mul_of_proj (star_one_sub (hC i)) (one_sub_mul_one_sub (hCid i)) (hO i) (hOid i),
      ntr_mul_comm]
  have hY : ∀ i, hsNormSq ((1 - D i) * O i) = ntr (O i * (1 - D i)) := fun i => by
    rw [hsNormSq_mul_of_proj (star_one_sub (hD i)) (one_sub_mul_one_sub (hDid i)) (hO i) (hOid i),
      ntr_mul_comm]
  have hαnn : 0 ≤ ∑ i, ntr (O i * (1 - D i)) := by
    rw [Finset.sum_congr rfl fun i _ => (hY i).symm]
    exact Finset.sum_nonneg fun i _ => hsNormSq_nonneg _
  have hβnn : 0 ≤ ∑ i, ntr (O i * (1 - C i)) := by
    rw [Finset.sum_congr rfl fun i _ => (hX i).symm]
    exact Finset.sum_nonneg fun i _ => hsNormSq_nonneg _
  -- the left-hand side, term by term
  have hlhs : ∑ i, hsNormSq (C i * D i - O i)
      = 2 - 2 * ∑ i, ntr (O i * D i * C i) := by
    have hterm : ∀ i, hsNormSq (C i * D i - O i)
        = ntr (C i * D i) - 2 * ntr (O i * D i * C i) + ntr (O i) := fun i => by
      rw [hsNormSq_sub, hsNormSq_mul_of_proj (hC i) (hCid i) (hD i) (hDid i),
        re_hsInner_mul_of_proj (hC i) (hD i), hsNormSq_of_proj (hO i) (hOid i)]
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    rw [show (∑ i, (ntr (C i * D i) - 2 * ntr (O i * D i * C i) + ntr (O i)))
        = ((∑ i, ntr (C i * D i)) - ∑ i, 2 * ntr (O i * D i * C i)) + ∑ i, ntr (O i) from by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib], hOsum, hCDsum,
      ← Finset.mul_sum]
    ring
  -- the triple trace, expanded through the two error families
  have hmid : ∑ i, ntr (O i * D i * C i)
      = 1 - (∑ i, ntr (O i * (1 - C i))) - (∑ i, ntr (O i * (1 - D i)))
        + ∑ i, (hsInner ((1 - D i) * O i) ((1 - C i) * O i)).re := by
    have hsplit : ∀ i, ntr (O i * D i * C i)
        = ntr (O i) - ntr (O i * (1 - C i)) - ntr (O i * (1 - D i))
          + (hsInner ((1 - D i) * O i) ((1 - C i) * O i)).re := fun i => by
      rw [← re_hsInner_mul_mul_of_proj (hO i) (hOid i) (hD i),
        show D i * O i = O i - (1 - D i) * O i from by noncomm_ring,
        show C i * O i = O i - (1 - C i) * O i from by noncomm_ring,
        re_hsInner_sub_left, re_hsInner_sub_right, re_hsInner_sub_right,
        ← hsNormSq_eq_re_hsInner_self, hsNormSq_of_proj (hO i) (hOid i),
        re_hsInner_self_mul_of_proj (hO i) (hOid i),
        re_hsInner_mul_self_of_proj (hO i) (hOid i) (star_one_sub (hD i))]
      ring
    rw [Finset.sum_congr rfl fun i _ => hsplit i]
    rw [show (∑ i, (ntr (O i) - ntr (O i * (1 - C i)) - ntr (O i * (1 - D i))
          + (hsInner ((1 - D i) * O i) ((1 - C i) * O i)).re))
        = (((∑ i, ntr (O i)) - ∑ i, ntr (O i * (1 - C i))) - ∑ i, ntr (O i * (1 - D i)))
          + ∑ i, (hsInner ((1 - D i) * O i) ((1 - C i) * O i)).re from by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib], hOsum]
  -- Cauchy--Schwarz on the one remaining term
  have hcs : |∑ i, (hsInner ((1 - D i) * O i) ((1 - C i) * O i)).re|
      ≤ √(∑ i, ntr (O i * (1 - D i))) * √(∑ i, ntr (O i * (1 - C i))) := by
    refine (sum_abs_re_hsInner_le univ (fun i => (1 - D i) * O i)
      (fun i => (1 - C i) * O i)).trans (le_of_eq ?_)
    rw [Finset.sum_congr rfl fun i _ => hY i, Finset.sum_congr rfl fun i _ => hX i]
  -- and the arithmetic-geometric mean inequality
  have hamgm : √(∑ i, ntr (O i * (1 - D i))) * √(∑ i, ntr (O i * (1 - C i)))
      ≤ ((∑ i, ntr (O i * (1 - D i))) + ∑ i, ntr (O i * (1 - C i))) / 2 := by
    rw [← Real.sqrt_mul hαnn]
    calc √((∑ i, ntr (O i * (1 - D i))) * ∑ i, ntr (O i * (1 - C i)))
        ≤ √((((∑ i, ntr (O i * (1 - D i))) + ∑ i, ntr (O i * (1 - C i))) / 2) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ((∑ i, ntr (O i * (1 - D i)))
            - ∑ i, ntr (O i * (1 - C i)))])
      _ = ((∑ i, ntr (O i * (1 - D i))) + ∑ i, ntr (O i * (1 - C i))) / 2 :=
          Real.sqrt_sq (by positivity)
  rw [hlhs, hmid]
  have := abs_le.mp hcs
  linarith [this.1, this.2]


omit [DecidableEq n] in
/-- **Close measurements have close values**: the measurement-level statement of
`fact:approx-implies-close-value` (from [NW19, Fact 4.31]), in the one direction the soundness
argument needs and in the synchronous setting, where the products `C_i D_i` are automatically a
measurement. **The square root is spent here, and only here.** -/
theorem sum_ntr_mul_ge {ι : Type*} [Fintype ι] (O C D : ι → Matrix n n ℂ) (acc : Finset ι)
    (hO : ∀ i, star (O i) = O i) (hOid : ∀ i, O i * O i = O i)
    (hC : ∀ i, star (C i) = C i) (hCid : ∀ i, C i * C i = C i)
    (hD : ∀ i, star (D i) = D i) (hDid : ∀ i, D i * D i = D i)
    (hOsum : ∑ i, ntr (O i) = 1) :
    (∑ i ∈ acc, ntr (O i)) - 2 * √(∑ i, hsNormSq (C i * D i - O i))
      ≤ ∑ i ∈ acc, ntr (C i * D i) := by
  have hOnn : ∀ i, 0 ≤ ntr (O i) := fun i => by
    rw [← hsNormSq_of_proj (hO i) (hOid i)]
    exact hsNormSq_nonneg _
  have hterm : ∀ i, ntr (C i * D i)
      = ntr (O i) + 2 * (hsInner (O i) (C i * D i - O i)).re
        + hsNormSq (C i * D i - O i) := fun i => by
    have h1 : hsNormSq (O i + (C i * D i - O i))
        = hsNormSq (O i) + 2 * (hsInner (O i) (C i * D i - O i)).re
          + hsNormSq (C i * D i - O i) := hsNormSq_add _ _
    rw [show O i + (C i * D i - O i) = C i * D i from by abel] at h1
    rw [← hsNormSq_mul_of_proj (hC i) (hCid i) (hD i) (hDid i), h1,
      hsNormSq_of_proj (hO i) (hOid i)]
  have hsum : ∑ i ∈ acc, ntr (C i * D i)
      = (∑ i ∈ acc, ntr (O i)) + 2 * (∑ i ∈ acc, (hsInner (O i) (C i * D i - O i)).re)
        + ∑ i ∈ acc, hsNormSq (C i * D i - O i) := by
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum]
  have hEnn : 0 ≤ ∑ i ∈ acc, hsNormSq (C i * D i - O i) :=
    Finset.sum_nonneg fun i _ => hsNormSq_nonneg _
  have hcs : |∑ i ∈ acc, (hsInner (O i) (C i * D i - O i)).re|
      ≤ √(∑ i ∈ acc, hsNormSq (O i)) * √(∑ i ∈ acc, hsNormSq (C i * D i - O i)) :=
    sum_abs_re_hsInner_le acc _ _
  have h3 : √(∑ i ∈ acc, hsNormSq (O i)) ≤ 1 := by
    rw [Finset.sum_congr rfl fun i _ => hsNormSq_of_proj (hO i) (hOid i), ← Real.sqrt_one]
    refine Real.sqrt_le_sqrt ?_
    rw [← hOsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => hOnn i
  have h4 : √(∑ i ∈ acc, hsNormSq (C i * D i - O i))
      ≤ √(∑ i, hsNormSq (C i * D i - O i)) :=
    Real.sqrt_le_sqrt (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun i _ _ => hsNormSq_nonneg _)
  have hmul : √(∑ i ∈ acc, hsNormSq (O i)) * √(∑ i ∈ acc, hsNormSq (C i * D i - O i))
      ≤ 1 * √(∑ i, hsNormSq (C i * D i - O i)) :=
    mul_le_mul h3 h4 (Real.sqrt_nonneg _) zero_le_one
  rw [hsum]
  have hb := abs_le.mp hcs
  rw [one_mul] at hmul
  linarith [hb.1, hb.2]

end Estimate

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
