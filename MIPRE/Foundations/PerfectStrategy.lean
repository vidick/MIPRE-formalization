/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Games

/-!
# Perfect strategies reject nothing on the support

Every completeness argument in the pipeline needs the same step: a strategy of value `1` does
not merely win on average, it assigns probability zero to each rejected answer pair at each
question pair the verifier actually asks. That step was used implicitly inside
`MIPRE.tracialValue_le_one` and nowhere available as a lemma; this file states it.

* `sum_re_tracial` — at a fixed question pair the outcome probabilities sum to one. This was a
  `have` inside `tracialValue_le_one`; it is the reason the value is at most one, and it is
  wanted on its own.
* `re_eq_zero_of_tracialValue_eq_one` — the characterization: if the value is `1` then
  `τ(M^x_a M^y_b) = 0` whenever `μ(x, y) > 0` and `(a, b)` is rejected.

Both are at the generic tracial level, so they serve synchronous and commuting strategies
alike; `SyncStrategy.re_eq_zero_of_value_eq_one` is the synchronous spelling, with the
normalized trace written out as `Tr(M^x_a M^y_b)/d`.
-/

namespace MIPRE

open Finset
open scoped ComplexOrder

variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]

omit [Fintype X] [DecidableEq A] in
/-- At a fixed question pair the outcome probabilities sum to one: `∑_{a,b} τ(M^x_a M^y_b) =
τ(1) = 1`. -/
theorem sum_re_tracial (τ : TracialState 𝒜) (P : ProjectiveMeasurement X A 𝒜) (x y : X) :
    ∑ a, ∑ b, (τ (P.M x a * P.M y b)).re = 1 := by
  have hsum : ∑ a, ∑ b, τ (P.M x a * P.M y b) = 1 := by
    have h1 : ∀ a, ∑ b, τ (P.M x a * P.M y b) = τ (P.M x a) := fun a => by
      rw [← map_sum, ← Finset.mul_sum, P.normalized, mul_one]
    simp_rw [h1]
    rw [← map_sum, P.normalized, τ.map_one]
  have := congrArg Complex.re hsum
  simpa [Complex.re_sum] using this

omit [Fintype X] [DecidableEq A] in
/-- The outcome probabilities are nonnegative. -/
theorem re_nonneg_tracial (τ : TracialState 𝒜) (P : ProjectiveMeasurement X A 𝒜)
    (x y : X) (a b : A) : 0 ≤ (τ (P.M x a * P.M y b)).re :=
  τ.re_nonneg_mul (P.selfAdjoint x a) (P.projective x a) (P.selfAdjoint y b) (P.projective y b)

omit [DecidableEq A] in
/-- Flattening the fourfold sum of a value into one sum over a product type. -/
private theorem sum_flat (F : X → X → A → A → ℝ) :
    ∑ x, ∑ y, ∑ a, ∑ b, F x y a b
      = ∑ p : X × X × A × A, F p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  simp [Fintype.sum_prod_type]

/-- **A perfect strategy rejects nothing on the support.** If the value is `1` then every
rejected answer pair has probability zero at every question pair of positive weight. -/
theorem re_eq_zero_of_tracialValue_eq_one (G : SynchronousGame X A) (τ : TracialState 𝒜)
    (P : ProjectiveMeasurement X A 𝒜) (h : tracialValue G τ P = 1)
    {x y : X} (hxy : 0 < G.μ x y) {a b : A} (hD : G.D x y a b = false) :
    (τ (P.M x a * P.M y b)).re = 0 := by
  classical
  have hle : ∀ p ∈ (univ : Finset (X × X × A × A)),
      G.μ p.1 p.2.1 * (if G.D p.1 p.2.1 p.2.2.1 p.2.2.2 then 1 else 0) *
          (τ (P.M p.1 p.2.2.1 * P.M p.2.1 p.2.2.2)).re
        ≤ G.μ p.1 p.2.1 * (τ (P.M p.1 p.2.2.1 * P.M p.2.1 p.2.2.2)).re := by
    intro p _
    cases hDp : G.D p.1 p.2.1 p.2.2.1 p.2.2.2 with
    | false => simpa using mul_nonneg (G.μ_nonneg _ _) (re_nonneg_tracial τ P _ _ _ _)
    | true => simp
  have hsumf : ∑ p : X × X × A × A,
      G.μ p.1 p.2.1 * (if G.D p.1 p.2.1 p.2.2.1 p.2.2.2 then 1 else 0) *
        (τ (P.M p.1 p.2.2.1 * P.M p.2.1 p.2.2.2)).re = 1 := by
    rw [← sum_flat (fun x y a b => G.μ x y * (if G.D x y a b then 1 else 0) *
      (τ (P.M x a * P.M y b)).re)]
    exact h
  have hsumg : ∑ p : X × X × A × A,
      G.μ p.1 p.2.1 * (τ (P.M p.1 p.2.2.1 * P.M p.2.1 p.2.2.2)).re = 1 := by
    rw [← sum_flat (fun x y a b => G.μ x y * (τ (P.M x a * P.M y b)).re)]
    refine (Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_).trans G.μ_sum_one
    simp_rw [← Finset.mul_sum]
    rw [sum_re_tracial τ P x y, mul_one]
  have hp := (Finset.sum_eq_sum_iff_of_le hle).mp (by rw [hsumf, hsumg]) (x, y, a, b)
    (mem_univ _)
  rw [hD] at hp
  simp only [Bool.false_eq_true, if_false, mul_zero, zero_mul] at hp
  exact (mul_eq_zero.mp hp.symm).resolve_left hxy.ne'

/-- The converse: if every rejected answer pair has probability zero at every question pair
of positive weight, the value is `1`. Completeness arguments go this way -- one builds a
strategy, checks it never produces a rejected outcome, and concludes. -/
theorem tracialValue_eq_one_of_re_eq_zero (G : SynchronousGame X A) (τ : TracialState 𝒜)
    (P : ProjectiveMeasurement X A 𝒜)
    (h : ∀ x y, 0 < G.μ x y → ∀ a b, G.D x y a b = false →
      (τ (P.M x a * P.M y b)).re = 0) :
    tracialValue G τ P = 1 := by
  classical
  have hterm : ∀ p : X × X × A × A,
      G.μ p.1 p.2.1 * (if G.D p.1 p.2.1 p.2.2.1 p.2.2.2 then 1 else 0) *
          (τ (P.M p.1 p.2.2.1 * P.M p.2.1 p.2.2.2)).re
        = G.μ p.1 p.2.1 * (τ (P.M p.1 p.2.2.1 * P.M p.2.1 p.2.2.2)).re := by
    intro p
    cases hD : G.D p.1 p.2.1 p.2.2.1 p.2.2.2 with
    | true => simp
    | false =>
        rcases (G.μ_nonneg p.1 p.2.1).lt_or_eq with hμ | hμ
        · rw [h _ _ hμ _ _ hD]; simp
        · rw [← hμ]; simp
  calc tracialValue G τ P
      = ∑ p : X × X × A × A, G.μ p.1 p.2.1 *
          (if G.D p.1 p.2.1 p.2.2.1 p.2.2.2 then 1 else 0) *
          (τ (P.M p.1 p.2.2.1 * P.M p.2.1 p.2.2.2)).re := by
        rw [← sum_flat (fun x y a b => G.μ x y * (if G.D x y a b then 1 else 0) *
          (τ (P.M x a * P.M y b)).re)]
        rfl
    _ = ∑ p : X × X × A × A, G.μ p.1 p.2.1 *
          (τ (P.M p.1 p.2.2.1 * P.M p.2.1 p.2.2.2)).re :=
        Finset.sum_congr rfl fun p _ => hterm p
    _ = 1 := by
        rw [← sum_flat (fun x y a b => G.μ x y * (τ (P.M x a * P.M y b)).re)]
        refine (Finset.sum_congr rfl fun x _ =>
          Finset.sum_congr rfl fun y _ => ?_).trans G.μ_sum_one
        simp_rw [← Finset.mul_sum]
        rw [sum_re_tracial τ P x y, mul_one]

namespace SyncStrategy

variable {G : SynchronousGame X A}

/-- `SyncStrategy.value` is the generic tracial value at the normalized trace, by definition.
Named so that the application below need not ask the unifier to see through `value`, which is
a `whnf` timeout when it does. -/
theorem value_eq_tracialValue (S : SyncStrategy G) :
    S.value = tracialValue G
      (normalizedTrace (Fin S.d) (hn := Fin.pos_iff_nonempty.mp S.d_pos)) S.P := rfl

open scoped Matrix in
/-- The real part of the normalized trace, written out. Stated once because both the value-one
characterization and the faithfulness lemmas below need it. -/
theorem normalizedTrace_re (S : SyncStrategy G) (M : Matrix (Fin S.d) (Fin S.d) ℂ) :
    ((normalizedTrace (Fin S.d) (hn := Fin.pos_iff_nonempty.mp S.d_pos)) M).re
      = M.trace.re / (S.d : ℝ) := by
  show ((Fintype.card (Fin S.d) : ℂ)⁻¹ * M.trace).re = _
  rw [Fintype.card_fin, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
    Complex.re_ofReal_mul, inv_mul_eq_div]

/-- The synchronous spelling: a value-`1` synchronous strategy has `Tr(M^x_a M^y_b) = 0` for
every rejected answer pair at every question pair of positive weight. -/
theorem re_eq_zero_of_value_eq_one (S : SyncStrategy G) (h : S.value = 1)
    {x y : X} (hxy : 0 < G.μ x y) {a b : A} (hD : G.D x y a b = false) :
    (S.P.M x a * S.P.M y b).trace.re / (S.d : ℝ) = 0 := by
  have h' : tracialValue G
      (normalizedTrace (Fin S.d) (hn := Fin.pos_iff_nonempty.mp S.d_pos)) S.P = 1 := by
    rw [← value_eq_tracialValue]; exact h
  rw [← normalizedTrace_re]
  exact re_eq_zero_of_tracialValue_eq_one G _ S.P h' hxy hD

/-! ## Faithfulness, and orthogonality of a projective measurement

The normalized trace on matrices is *faithful*, which the generic tracial level cannot see.
Two consequences that completeness arguments need at the operator level rather than the state
level, and which the paper uses without comment: a rejected outcome of a value-one strategy is
not merely improbable but the zero operator, and distinct outcomes at one question are exactly
orthogonal. -/

open scoped Matrix in
/-- A self-adjoint idempotent whose normalized trace vanishes is the zero operator. -/
theorem eq_zero_of_trace_re_eq_zero (S : SyncStrategy G) {M : Matrix (Fin S.d) (Fin S.d) ℂ}
    (hsa : star M = M) (hidem : M * M = M) (h : M.trace.re / (S.d : ℝ) = 0) : M = 0 := by
  have hd : (S.d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr S.d_pos.ne'
  have hre : M.trace.re = 0 := (div_eq_zero_iff.mp h).resolve_right hd
  have him : M.trace.im = 0 := by
    refine Complex.conj_eq_iff_im.mp ?_
    rw [starRingEnd_apply, ← Matrix.trace_conjTranspose, ← Matrix.star_eq_conjTranspose, hsa]
  have htr : M.trace = 0 := Complex.ext hre him
  have hH : Mᴴ * M = M := by rw [← Matrix.star_eq_conjTranspose, hsa, hidem]
  exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp (by rw [hH, htr])

open scoped Matrix in
/-- **Distinct outcomes of a projective measurement are orthogonal.** The tracial statement
`ProjectiveMeasurement.consistency` says the *probability* is zero; on matrices, faithfulness
of the trace upgrades that to the operator identity, which is what a commutation obligation at
a repeated question needs. -/
theorem orthogonal (S : SyncStrategy G) (x : X) {a b : A} (hab : a ≠ b) :
    S.P.M x a * S.P.M x b = 0 := by
  have hd : ((Fintype.card (Fin S.d) : ℂ))⁻¹ ≠ 0 := by
    simp [Fintype.card_fin, S.d_pos.ne']
  have hτ := ProjectiveMeasurement.consistency S.P
    (normalizedTrace (Fin S.d) (hn := Fin.pos_iff_nonempty.mp S.d_pos)) x hab
  rw [normalizedTrace_apply] at hτ
  have htr : (S.P.M x a * S.P.M x b).trace = 0 := (mul_eq_zero.mp hτ).resolve_left hd
  -- `(M^x_b M^x_a)ᴴ (M^x_b M^x_a) = M^x_a M^x_b M^x_a`, whose trace is that of `M^x_a M^x_b`
  have hzero : S.P.M x b * S.P.M x a = 0 := by
    refine Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp ?_
    have hH : (S.P.M x b * S.P.M x a)ᴴ * (S.P.M x b * S.P.M x a)
        = S.P.M x a * S.P.M x b * S.P.M x a := by
      rw [Matrix.conjTranspose_mul, ← Matrix.star_eq_conjTranspose,
        ← Matrix.star_eq_conjTranspose, S.P.selfAdjoint, S.P.selfAdjoint]
      calc S.P.M x a * S.P.M x b * (S.P.M x b * S.P.M x a)
          = S.P.M x a * (S.P.M x b * S.P.M x b) * S.P.M x a := by noncomm_ring
        _ = S.P.M x a * S.P.M x b * S.P.M x a := by rw [S.P.projective]
    rw [hH]
    have e1 : S.P.M x a * S.P.M x b * S.P.M x a
        = S.P.M x a * (S.P.M x b * S.P.M x a) := by noncomm_ring
    have e2 : S.P.M x b * S.P.M x a * S.P.M x a = S.P.M x b * S.P.M x a := by
      rw [Matrix.mul_assoc, S.P.projective]
    rw [e1, Matrix.trace_mul_comm, e2, Matrix.trace_mul_comm, htr]
  have hconj : S.P.M x a * S.P.M x b = (S.P.M x b * S.P.M x a)ᴴ := by
    rw [Matrix.conjTranspose_mul, ← Matrix.star_eq_conjTranspose,
      ← Matrix.star_eq_conjTranspose, S.P.selfAdjoint, S.P.selfAdjoint]
  rw [hconj, hzero, Matrix.conjTranspose_zero]

end SyncStrategy

end MIPRE
