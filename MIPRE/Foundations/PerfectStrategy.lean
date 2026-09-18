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

namespace SyncStrategy

variable {G : SynchronousGame X A}

/-- `SyncStrategy.value` is the generic tracial value at the normalized trace, by definition.
Named so that the application below need not ask the unifier to see through `value`, which is
a `whnf` timeout when it does. -/
theorem value_eq_tracialValue (S : SyncStrategy G) :
    S.value = tracialValue G
      (normalizedTrace (Fin S.d) (hn := Fin.pos_iff_nonempty.mp S.d_pos)) S.P := rfl

/-- The synchronous spelling: a value-`1` synchronous strategy has `Tr(M^x_a M^y_b) = 0` for
every rejected answer pair at every question pair of positive weight. -/
theorem re_eq_zero_of_value_eq_one (S : SyncStrategy G) (h : S.value = 1)
    {x y : X} (hxy : 0 < G.μ x y) {a b : A} (hD : G.D x y a b = false) :
    (S.P.M x a * S.P.M y b).trace.re / (S.d : ℝ) = 0 := by
  have h' : tracialValue G
      (normalizedTrace (Fin S.d) (hn := Fin.pos_iff_nonempty.mp S.d_pos)) S.P = 1 := by
    rw [← value_eq_tracialValue]; exact h
  have hz := re_eq_zero_of_tracialValue_eq_one G _ S.P h' hxy hD
  have : ((normalizedTrace (Fin S.d) (hn := Fin.pos_iff_nonempty.mp S.d_pos))
      (S.P.M x a * S.P.M y b)).re = (S.P.M x a * S.P.M y b).trace.re / (S.d : ℝ) := by
    show ((Fintype.card (Fin S.d) : ℂ)⁻¹ * (S.P.M x a * S.P.M y b).trace).re = _
    rw [Fintype.card_fin, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
      Complex.re_ofReal_mul, inv_mul_eq_div]
  rw [← this]
  exact hz

end SyncStrategy

end MIPRE
