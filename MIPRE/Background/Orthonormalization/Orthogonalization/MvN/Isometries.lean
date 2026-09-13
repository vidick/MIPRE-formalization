/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/MvN/Isometries.lean
-/
/-
# Tier T3, type III: partial isometries and the isometries of the halving

Proof-side toolkit for the type III case of tier T3 (`PLAN.md` §9, step III):
the elementary Murray–von Neumann manipulations Section 5 of the paper uses
without comment, phrased relative to a central projection `z` (the type III
summand), with the vocabulary of `Orthogonalization/MvN/Defs.lean`.

* `exists_partial_isometry_of_le_of_equiv`: comparison from an inclusion into
  an equivalent projection — if `P ≤ P'` and `P' ∼ Q` then `P` is equivalent
  to a subprojection of `Q`, realized by the partial isometry `v P`;
* `exists_isometries_of_halving`: under a nonzero central projection `z` with
  the halving property (field H4 of the interface), for every `n ≥ 1` there are
  `u_1, …, u_n ∈ M` with `u_i* u_i = z`, `u_i* u_j = 0` (`i ≠ j`) and
  `∑ u_i u_i* = z` — the isometries behind "`1_n ⊗ 1 ∼ e_{11} ⊗ 1` in `M_n(M)`"
  in the type III case (Takesaki V.1.36, `z` properly infinite), obtained by
  iterating one halving `z = e + (z − e)`, `e ∼ z − e ∼ z`.

No statement of the paper. Proof-side only.
-/
import Mathlib
import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.TypeIIINet

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace Orthogonalization.MvN

open scoped BigOperators ComplexOrder
open Blocks

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Small facts about partial isometries and projections -/

/-- Adjoint form of `mul_star_mul_self_eq_self`: if `v* v` is a projection then
`v* (v v*) = v*`. -/
theorem star_mul_self_mul_star {v : H →L[ℂ] H} (h : IsStarProjection (star v * v)) :
    star v * (v * star v) = star v := by
  calc star v * (v * star v) = star v * v * star v := by rw [mul_assoc]
    _ = star (v * (star v * v)) := by rw [star_mul, star_mul, star_star]
    _ = star v := by rw [mul_star_mul_self_eq_self h]

/-- If `v* v = p` is a projection then `v p = v`. -/
theorem mul_eq_self_of_star_mul_self_eq {v p : H →L[ℂ] H} (hp : IsStarProjection p)
    (h : star v * v = p) : v * p = v := by
  rw [← h]
  exact mul_star_mul_self_eq_self (h.symm ▸ hp)

/-- If `v* v = p` is a projection then `p v* = v*`. -/
theorem proj_mul_star_eq_self_of_star_mul_self_eq {v p : H →L[ℂ] H} (hp : IsStarProjection p)
    (h : star v * v = p) : p * star v = star v := by
  have := congrArg star (mul_eq_self_of_star_mul_self_eq hp h)
  rwa [star_mul, hp.isSelfAdjoint.star_eq] at this

/-- `z − e` is a projection when `e ≤ z` are projections. -/
theorem isStarProjection_sub_of_le {e z : H →L[ℂ] H} (hz : IsStarProjection z)
    (he : IsStarProjection e) (hez : e * z = e) (hze : z * e = e) :
    IsStarProjection (z - e) := by
  refine ⟨?_, ?_⟩
  · show (z - e) * (z - e) = z - e
    rw [sub_mul, mul_sub, mul_sub, hz.isIdempotentElem.eq, hze, hez, he.isIdempotentElem.eq]
    abel
  · rw [IsSelfAdjoint, star_sub, hz.isSelfAdjoint.star_eq, he.isSelfAdjoint.star_eq]

/-- A projection `e ≤ z` is orthogonal to `z − e`. -/
theorem proj_mul_sub_eq_zero {e z : H →L[ℂ] H} (he : IsStarProjection e) (hez : e * z = e) :
    e * (z - e) = 0 := by
  rw [mul_sub, hez, he.isIdempotentElem.eq, sub_self]

/-- An element `u ∈ M` with `u* u = z`, `z` a central projection, satisfies `z u = u`
(from `u z = u` and centrality). -/
theorem central_mul_eq_self_of_star_mul_self_eq {M : VonNeumannAlgebra H}
    {z u : H →L[ℂ] H} (hz : IsCentralProj M z) (huM : u ∈ M) (h : star u * u = z) :
    z * u = u := by
  rw [(hz.commute u huM).eq]
  exact mul_eq_self_of_star_mul_self_eq hz.isStarProjection h

/-! ### Comparison from an inclusion into an equivalent projection -/

/-- If `P ≤ P'` and `P' ∼ Q` then `P` is equivalent to a subprojection of `Q`:
`w := v P` for the partial isometry `v` of `P' ∼ Q` satisfies `w* w = P`, `w w* ≤ Q`.
(`P'` need not be assumed to be a projection: it is `v* v`.) -/
theorem exists_partial_isometry_of_le_of_equiv (M : VonNeumannAlgebra H) {P P' Q : H →L[ℂ] H}
    (hP : IsStarProjection P) (hPM : P ∈ M) (hPP' : P * P' = P) (h : MvNEquiv M P' Q) :
    ∃ w ∈ M, star w * w = P ∧ IsStarProjection (w * star w) ∧ (w * star w) * Q = w * star w := by
  obtain ⟨v, hvM, hv1, hv2⟩ := h
  -- `w* w = P (v* v) P = P P' P = P`
  have hw1 : star (v * P) * (v * P) = P := by
    rw [star_mul, hP.isSelfAdjoint.star_eq]
    calc P * star v * (v * P) = P * (star v * v) * P := by noncomm_ring
      _ = P := by rw [hv1, hPP', hP.isIdempotentElem.eq]
  -- `w w* = v P v*`
  have hww : v * P * star (v * P) = v * P * star v := by
    rw [star_mul, hP.isSelfAdjoint.star_eq]
    calc v * P * (P * star v) = v * (P * P) * star v := by noncomm_ring
      _ = v * P * star v := by rw [hP.isIdempotentElem.eq]
  have hwP : IsStarProjection (star (v * P) * (v * P)) := by rw [hw1]; exact hP
  refine ⟨v * P, mul_mem hvM hPM, hw1, isStarProjection_mul_star_of hwP, ?_⟩
  -- `(v P v*) (v v*) = v P (v* v) v* = v P P' v* = v P v*`
  rw [hww, ← hv2]
  calc v * P * star v * (v * star v) = v * (P * (star v * v)) * star v := by noncomm_ring
    _ = v * P * star v := by rw [hv1, hPP']

/-! ### Isometries with orthogonal ranges summing to `z`, from halving -/

/-- Under a nonzero central projection `z` with the halving property (field H4 of the
interface at `z`), for every `n ≥ 1` there are `u_1, …, u_n ∈ M` with `u_i* u_i = z`,
`u_i* u_j = 0` for `i ≠ j`, and `∑ u_i u_i* = z`. Proof: halve `z = e + (z − e)` with
`e ∼ z − e ∼ z`, take partial isometries `v_e : z → e`, `v_f : z → z − e`, and
iterate: `u := (v_e, v_f u'_1, …, v_f u'_n)` for `u'` a family of length `n`. -/
theorem exists_isometries_of_halving (M : VonNeumannAlgebra H) {z : H →L[ℂ] H}
    (hz : IsCentralProj M z) (hz0 : z ≠ 0)
    (hH4 : ∀ q, IsStarProjection q → q ∈ M → q * z = q → q ≠ 0 →
      ∃ e, IsStarProjection e ∧ e ∈ M ∧ e * q = e ∧ MvNEquiv M e (q - e) ∧ MvNEquiv M e q)
    (n : ℕ) (hn : 0 < n) :
    ∃ u : Fin n → H →L[ℂ] H, (∀ i, u i ∈ M) ∧ (∀ i, star (u i) * u i = z) ∧
      (∀ i j, i ≠ j → star (u i) * u j = 0) ∧ ∑ i, u i * star (u i) = z := by
  have hzP := hz.isStarProjection
  have hzM := hz.mem
  have hzz : star z * z = z := by rw [hzP.isSelfAdjoint.star_eq, hzP.isIdempotentElem.eq]
  have hzz' : z * star z = z := by rw [hzP.isSelfAdjoint.star_eq, hzP.isIdempotentElem.eq]
  -- one halving of `z`: `e ≤ z` with `e ∼ z − e ∼ z`
  obtain ⟨e, heP, heM, hez, hef, heq⟩ := hH4 z hzP hzM hzP.isIdempotentElem.eq hz0
  have hze : z * e = e := proj_mul_left_of_mul_right heP hzP hez
  have hfP : IsStarProjection (z - e) := isStarProjection_sub_of_le hzP heP hez hze
  have hfz : MvNEquiv M (z - e) z := hef.symm.trans hfP heq
  -- the partial isometries `v_e : z → e` and `v_f : z → z − e`
  obtain ⟨v_e, hveM, hvez, hvee⟩ := heq.symm
  obtain ⟨v_f, hvfM, hvfz, hvff⟩ := hfz.symm
  have hveP : IsStarProjection (star v_e * v_e) := by rw [hvez]; exact hzP
  have hvfP : IsStarProjection (star v_f * v_f) := by rw [hvfz]; exact hzP
  have hvfz' : v_f * z = v_f := mul_eq_self_of_star_mul_self_eq hzP hvfz
  have hef0 : e * (z - e) = 0 := proj_mul_sub_eq_zero heP hez
  -- orthogonality of the ranges: `v_e* v_f = v_e* (v_e v_e*) (v_f v_f*) v_f = v_e* e (z − e) v_f = 0`
  have hvevf : star v_e * v_f = 0 := by
    have h1 : star v_e * (v_e * star v_e) = star v_e := star_mul_self_mul_star hveP
    have h2 : v_f * star v_f * v_f = v_f := by
      rw [mul_assoc]; exact mul_star_mul_self_eq_self hvfP
    calc star v_e * v_f = (star v_e * (v_e * star v_e)) * (v_f * star v_f * v_f) := by
          rw [h1, h2]
      _ = star v_e * (e * (z - e)) * v_f := by rw [hvee, hvff]; noncomm_ring
      _ = 0 := by rw [hef0, mul_zero, zero_mul]
  have hvfve : star v_f * v_e = 0 := by
    have := congrArg star hvevf
    rwa [star_mul, star_star, star_zero] at this
  -- induction on `n ≥ 1`
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  clear hn
  induction n with
  | zero =>
    refine ⟨fun _ => z, fun _ => hzM, fun _ => hzz,
      fun i j hij => absurd ((Fin.fin_one_eq_zero i).trans (Fin.fin_one_eq_zero j).symm) hij, ?_⟩
    rw [Fin.sum_univ_one]
    exact hzz'
  | succ n ih =>
    obtain ⟨u', hu'M, hu'z, hu'orth, hu'sum⟩ := ih
    have hzu : ∀ i, z * u' i = u' i := fun i =>
      central_mul_eq_self_of_star_mul_self_eq hz (hu'M i) (hu'z i)
    refine ⟨Fin.cons v_e (fun i => v_f * u' i), ?_, ?_, ?_, ?_⟩
    · -- membership
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · rw [Fin.cons_zero]; exact hveM
      · rw [Fin.cons_succ]; exact mul_mem hvfM (hu'M i)
    · -- isometries: `(v_f u'_i)* (v_f u'_i) = u'_i* z u'_i = u'_i* u'_i = z`
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · rw [Fin.cons_zero]; exact hvez
      · rw [Fin.cons_succ, star_mul]
        calc star (u' i) * star v_f * (v_f * u' i)
            = star (u' i) * (star v_f * v_f) * u' i := by noncomm_ring
          _ = star (u' i) * u' i := by rw [hvfz, mul_assoc, hzu i]
          _ = z := hu'z i
    · -- orthogonality
      intro i j
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j
        · intro hij; exact absurd rfl hij
        · intro _
          rw [Fin.cons_zero, Fin.cons_succ, ← mul_assoc, hvevf, zero_mul]
      · refine Fin.cases ?_ (fun j => ?_) j
        · intro _
          rw [Fin.cons_succ, Fin.cons_zero, star_mul, mul_assoc, hvfve, mul_zero]
        · intro hij
          have hij' : i ≠ j := fun h => hij (congrArg Fin.succ h)
          rw [Fin.cons_succ, Fin.cons_succ, star_mul]
          calc star (u' i) * star v_f * (v_f * u' j)
              = star (u' i) * (star v_f * v_f) * u' j := by noncomm_ring
            _ = star (u' i) * u' j := by rw [hvfz, mul_assoc, hzu j]
            _ = 0 := hu'orth i j hij'
    · -- the sum: `v_e v_e* + v_f (∑ u'_i u'_i*) v_f* = e + v_f z v_f* = e + (z − e) = z`
      have hterm : ∀ i : Fin (n + 1),
          v_f * u' i * star (v_f * u' i) = v_f * (u' i * star (u' i)) * star v_f := by
        intro i
        rw [star_mul]
        noncomm_ring
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, hterm]
      rw [← Finset.sum_mul, ← Finset.mul_sum, hu'sum, hvfz', hvff, hvee]
      abel

end Orthogonalization.MvN
