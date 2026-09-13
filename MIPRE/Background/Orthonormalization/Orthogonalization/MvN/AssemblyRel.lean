/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/MvN/AssemblyRel.lean
-/
/-
# The three-term estimate relative to a projection (step **F3** in a corner)

The last step of the proof of Theorem 1.2 in the finite case (M. de la Salle,
*Orthogonalization of Positive Operator Valued Measures*, arXiv:2103.14126v2,
Section 3, end of the proof; `PLAN.md` §1, step **F3**) is proved in
`Orthogonalization/Assembly.lean` for a POVM summing to `1` and a functional
positive on all of `B(H)`. The general case (tier T3) runs the same argument in
a corner `p M p` of a von Neumann algebra `M`: the POVM `(a_i)` sums to a
projection `p ∈ M`, the assembled PVM `(p'_i)` sums to `p`, and the functional
`φ` is only known to be positive on `M` and normalized by `φ p = 1`.

This file proves that relative version, `assembled_bound_rel`: with
`s` an abstract square root of `y = ∑ j, q_j a_j` supported in `p`
(`0 ≤ s ≤ 1`, `s p = s`, `s² = y`, `s p'_i s = q_i a_i`),

`φ (∑ i, |a_i − p'_i|²) < 9 ε` whenever `φ (∑ a_i²) > 1 − ε` and
`φ (∑ q_i a_i) ≥ 1 − ε`.

The proof is the decomposition `a_i − p'_i = b_i + d_i + c_i` of the absolute
proof (`b_i = (1 − q_i) a_i`, `d_i = p'_i s − p'_i`, `c_i = q_i a_i − p'_i s`)
with `1` replaced by `p` in the three operator bounds, monotonicity of `φ`
on `M` (`Blocks/StateOnM.lean`) in place of monotonicity on `B(H)`, and the
weighted triangle inequality for functionals positive on `M`
(`MvN/Local.lean`) in place of the Cauchy–Schwarz-based one, which is how the
constant `9 = (3/2)·(2 + 2) + 3` arises here.

Nothing in this file is a statement of the paper; it is proof-side machinery
for `Orthogonalization/Basic.lean`.
-/
import Mathlib
import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.Local
import MIPRE.Background.Orthonormalization.Orthogonalization.Assembly
import MIPRE.Background.Orthonormalization.Orthogonalization.Blocks.StateOnM

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace Orthogonalization.MvN

open scoped ComplexOrder BigOperators
open Blocks

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Operator bounds relative to `p` -/

section Terms

variable {p s : H →L[ℂ] H}

omit [CompleteSpace H] in
/-- `(1 - s) p (1 - s) = p - s - s + s²` when `s` is supported in `p`
(`s p = s = p s`). -/
theorem one_sub_mul_proj_mul_one_sub (hsp : s * p = s) (hps : p * s = s) :
    (1 - s) * p * (1 - s) = p - s - s + s * s := by
  have e : (1 - s) * p * (1 - s) = p - p * s - s * p + s * (p * s) := by noncomm_ring
  rw [e, hps, hsp]

/-- `p - s - s + s² ≤ p - s²` for `0 ≤ s ≤ 1`: the difference is `2 (s - s²) ≥ 0`. -/
theorem proj_sub_two_mul_add_sq_le (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    p - s - s + s * s ≤ p - s * s := by
  have h : 0 ≤ s - s * s := sub_nonneg.mpr (sq_le_self_of_le_one hs0 hs1)
  refine le_of_nonneg_sub ?_
  have key : p - s * s - (p - s - s + s * s) = (s - s * s) + (s - s * s) := by noncomm_ring
  rw [key]
  exact add_nonneg h h

end Terms

/-! ### The three-term estimate in the corner -/

/-- **Step F3 relative to a projection.** The three-term estimate of the paper in
the corner `p M p`: the POVM `(a_i)` of `M` sums to the projection `p ∈ M`, the
projections `(p'_i)` of `M` sum to `p`, the functional `φ` is positive on `M` with
`φ p = 1`, and `s ∈ M` is an abstract square root of `∑ j, q_j a_j` supported in `p`.
Then `φ (∑ i, |a_i - p'_i|²) < 9 ε` whenever `φ (∑ i, a_i²) > 1 - ε` and
`φ (∑ i, q_i a_i) ≥ 1 - ε`.

The proof decomposes `a_i - p'_i = b_i + d_i + c_i` with `b_i = (1 - q_i) a_i`,
`d_i = p'_i s - p'_i`, `c_i = q_i a_i - p'_i s`, bounds
`∑ b_i* b_i ≤ p - ∑ q_j a_j`, `∑ d_i* d_i ≤ p - ∑ q_j a_j`, `∑ c_i* c_i ≤ p - ∑ a_i²`
in `M`, evaluates `φ`, and assembles with the weighted triangle inequality
(`‖b + d‖² ≤ 2 ‖b‖² + 2 ‖d‖²`, then `‖(b + d) + c‖² ≤ (3/2) ‖b + d‖² + 3 ‖c‖²`). -/
theorem assembled_bound_rel (M : VonNeumannAlgebra H) (φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ)
    (hφ : ∀ x ∈ M, 0 ≤ φ (star x * x)) {p : H →L[ℂ] H} (hp : IsStarProjection p) (hpM : p ∈ M)
    (hφp : φ p = 1) {ι : Type*} [Fintype ι] (a q p' : ι → H →L[ℂ] H) (s : H →L[ℂ] H)
    (haM : ∀ i, a i ∈ M) (ha0 : ∀ i, 0 ≤ a i) (hap : ∑ i, a i = p)
    (hq : ∀ i, IsStarProjection (q i)) (hqM : ∀ i, q i ∈ M) (hqa : ∀ i, Commute (q i) (a i))
    (hp' : ∀ i, IsStarProjection (p' i)) (hp'M : ∀ i, p' i ∈ M) (hp'sum : ∑ i, p' i = p)
    (hsM : s ∈ M) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hsp : s * p = s) (hss : s * s = ∑ j, q j * a j)
    (hsp' : ∀ i, s * p' i * s = q i * a i)
    (ε : ℝ) (hε : 1 - ε < (φ (∑ i, a i * a i)).re)
    (hlarge : 1 - ε ≤ (φ (∑ i, q i * a i)).re) :
    (φ (∑ i, star (a i - p' i) * (a i - p' i))).re < 9 * ε := by
  -- Elementary consequences of the hypotheses.
  have hone : (φ p).re = 1 := by rw [hφp]; simp
  have hsa : star s = s := IsSelfAdjoint.of_nonneg hs0
  have hps : p * s = s := by
    have h := congrArg star hsp
    rwa [star_mul, hsa, hp.isSelfAdjoint.star_eq] at h
  have hp1 : p ≤ 1 := sub_nonneg.mp hp.one_sub.nonneg
  have ha_le_p : ∀ i, a i ≤ p := by
    intro i
    rw [← hap]
    exact Finset.single_le_sum (f := a) (fun j _ => ha0 j) (Finset.mem_univ i)
  have ha_le_one : ∀ i, a i ≤ 1 := fun i => (ha_le_p i).trans hp1
  have haa : ∀ i, a i * a i ≤ a i := fun i => sq_le_self_of_le_one (ha0 i) (ha_le_one i)
  have hsum_aa_le : ∑ i, a i * a i ≤ p := by
    rw [← hap]; exact Finset.sum_le_sum fun i _ => haa i
  -- Memberships in `M`.
  have haaM : ∑ i, a i * a i ∈ M := sum_mem fun i _ => mul_mem (haM i) (haM i)
  have hqaM : ∑ i, q i * a i ∈ M := sum_mem fun i _ => mul_mem (hqM i) (haM i)
  have hbM : ∀ i, (1 - q i) * a i ∈ M := fun i =>
    mul_mem (sub_mem (one_mem M) (hqM i)) (haM i)
  have hdM : ∀ i, p' i * s - p' i ∈ M := fun i => sub_mem (mul_mem (hp'M i) hsM) (hp'M i)
  have hcM : ∀ i, q i * a i - p' i * s ∈ M := fun i =>
    sub_mem (mul_mem (hqM i) (haM i)) (mul_mem (hp'M i) hsM)
  have hbound_aa : (φ (∑ i, a i * a i)).re ≤ 1 := by
    have h := re_map_le_of_mem hφ haaM hpM hsum_aa_le
    rwa [hone] at h
  have hε0 : 0 < ε := by linarith
  -- Values of `φ` on the two operators that appear as bounds.
  have hval_y : (φ (p - ∑ i, q i * a i)).re = 1 - (φ (∑ i, q i * a i)).re := by
    rw [map_sub, Complex.sub_re, hone]
  have hval_aa : (φ (p - ∑ i, a i * a i)).re = 1 - (φ (∑ i, a i * a i)).re := by
    rw [map_sub, Complex.sub_re, hone]
  -- The first term `b_i = (1 - q_i) a_i`.
  have hb_op : ∀ i, star ((1 - q i) * a i) * ((1 - q i) * a i) ≤ (1 - q i) * a i := by
    intro i
    have hr : IsStarProjection (1 - q i) := (hq i).one_sub
    have hcr : Commute (1 - q i) (a i) := (Commute.one_left (a i)).sub_left (hqa i)
    rw [star_mul_self_proj_mul hr (IsSelfAdjoint.of_nonneg (ha0 i)) hcr]
    exact Orthogonalization.IsStarProjection.mul_le_mul_of_commute hr (haa i)
      (hcr.sub_right (hcr.mul_right hcr))
  have hb_sum : ∑ i, (1 - q i) * a i = p - ∑ i, q i * a i := by
    simp only [sub_mul, one_mul]
    rw [Finset.sum_sub_distrib, hap]
  have hb : (φ (∑ i, star ((1 - q i) * a i) * ((1 - q i) * a i))).re ≤ ε := by
    have hstep : ∑ i, star ((1 - q i) * a i) * ((1 - q i) * a i) ≤ p - ∑ i, q i * a i := by
      rw [← hb_sum]
      exact Finset.sum_le_sum fun i _ => hb_op i
    have h := re_map_le_of_mem hφ (sum_mem fun i _ => mul_mem (star_mem (hbM i)) (hbM i))
      (sub_mem hpM hqaM) hstep
    rw [hval_y] at h
    linarith
  -- The third term `d_i = p'_i s - p'_i`.
  have hd : (φ (∑ i, star (p' i * s - p' i) * (p' i * s - p' i))).re ≤ ε := by
    have hsum : ∑ i, (1 - s) * p' i * (1 - s) = (1 - s) * p * (1 - s) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, hp'sum]
    have hstep : ∑ i, star (p' i * s - p' i) * (p' i * s - p' i) ≤ p - ∑ j, q j * a j := by
      calc ∑ i, star (p' i * s - p' i) * (p' i * s - p' i)
          = ∑ i, (1 - s) * p' i * (1 - s) :=
            Finset.sum_congr rfl fun i _ => star_mul_self_proj_mul_sub_self (hp' i) hsa
        _ = (1 - s) * p * (1 - s) := hsum
        _ = p - s - s + s * s := one_sub_mul_proj_mul_one_sub hsp hps
        _ ≤ p - s * s := proj_sub_two_mul_add_sq_le hs0 hs1
        _ = p - ∑ j, q j * a j := by rw [hss]
    have h := re_map_le_of_mem hφ (sum_mem fun i _ => mul_mem (star_mem (hdM i)) (hdM i))
      (sub_mem hpM hqaM) hstep
    rw [hval_y] at h
    linarith
  -- The second term `c_i = q_i a_i - p'_i s`.
  have hc : (φ (∑ i, star (q i * a i - p' i * s) * (q i * a i - p' i * s))).re < ε := by
    have hc_op : ∀ i,
        star (q i * a i - p' i * s) * (q i * a i - p' i * s) ≤ a i - a i * a i := by
      intro i
      have hci : q i * a i - p' i * s = (s - 1) * (p' i * s) := by
        rw [← hsp' i]; noncomm_ring
      have hstar_ps : star (p' i * s) = s * p' i := by
        rw [star_mul, hsa, (hp' i).isSelfAdjoint.star_eq]
      have h1 : star (q i * a i - p' i * s) * (q i * a i - p' i * s)
          = star (p' i * s) * ((1 - s) * (1 - s)) * (p' i * s) := by
        rw [hci, star_mul_self_sub_one_mul hsa]
      have h2 : star (p' i * s) * ((1 - s) * (1 - s)) * (p' i * s)
          ≤ star (p' i * s) * (1 - s * s) * (p' i * s) :=
        conj_le_conj (one_sub_sq_le_one_sub_sq' hs0 hs1) (p' i * s)
      have h3 : star (p' i * s) * (1 - s * s) * (p' i * s)
          = q i * a i - q i * a i * (q i * a i) := by
        rw [hstar_ps]
        exact conj_one_sub_sq_eq (hp' i).isIdempotentElem.eq (hsp' i)
      have h4 : q i * a i - q i * a i * (q i * a i) = q i * (a i - a i * a i) :=
        proj_mul_sub_sq (hq i) (hqa i)
      have h5 : q i * (a i - a i * a i) ≤ a i - a i * a i :=
        Orthogonalization.IsStarProjection.mul_le_of_commute (hq i) (sub_nonneg.mpr (haa i))
          ((hqa i).sub_right ((hqa i).mul_right (hqa i)))
      calc star (q i * a i - p' i * s) * (q i * a i - p' i * s)
          = star (p' i * s) * ((1 - s) * (1 - s)) * (p' i * s) := h1
        _ ≤ star (p' i * s) * (1 - s * s) * (p' i * s) := h2
        _ = q i * a i - q i * a i * (q i * a i) := h3
        _ = q i * (a i - a i * a i) := h4
        _ ≤ a i - a i * a i := h5
    have hc_sum : ∑ i, (a i - a i * a i) = p - ∑ i, a i * a i := by
      rw [Finset.sum_sub_distrib, hap]
    have hstep : ∑ i, star (q i * a i - p' i * s) * (q i * a i - p' i * s)
        ≤ p - ∑ i, a i * a i := by
      rw [← hc_sum]
      exact Finset.sum_le_sum fun i _ => hc_op i
    have h := re_map_le_of_mem hφ (sum_mem fun i _ => mul_mem (star_mem (hcM i)) (hcM i))
      (sub_mem hpM haaM) hstep
    rw [hval_aa] at h
    linarith
  -- Assemble: `a_i - p'_i = (b_i + d_i) + c_i` and the weighted triangle inequality.
  have hbd : (φ (∑ i, star ((1 - q i) * a i + (p' i * s - p' i))
      * ((1 - q i) * a i + (p' i * s - p' i)))).re ≤ 4 * ε := by
    have h : (φ (∑ i, star ((1 - q i) * a i + (p' i * s - p' i))
        * ((1 - q i) * a i + (p' i * s - p' i)))).re
        ≤ (1 + (1 : ℝ)) * (φ (∑ i, star ((1 - q i) * a i) * ((1 - q i) * a i))).re
          + (1 + (1 : ℝ)⁻¹) * (φ (∑ i, star (p' i * s - p' i) * (p' i * s - p' i))).re :=
      sum_re_map_star_add_mul_add_le hφ hbM hdM one_pos
    rw [inv_one] at h
    linarith
  have hbdM : ∀ i, (1 - q i) * a i + (p' i * s - p' i) ∈ M := fun i => add_mem (hbM i) (hdM i)
  have hfinal : (φ (∑ i, star (((1 - q i) * a i + (p' i * s - p' i)) + (q i * a i - p' i * s))
      * (((1 - q i) * a i + (p' i * s - p' i)) + (q i * a i - p' i * s)))).re
      ≤ (1 + (2⁻¹ : ℝ)) * (φ (∑ i, star ((1 - q i) * a i + (p' i * s - p' i))
          * ((1 - q i) * a i + (p' i * s - p' i)))).re
        + (1 + (2⁻¹ : ℝ)⁻¹)
          * (φ (∑ i, star (q i * a i - p' i * s) * (q i * a i - p' i * s))).re :=
    sum_re_map_star_add_mul_add_le hφ hbdM hcM (by norm_num)
  rw [inv_inv] at hfinal
  have hfun : ∀ i, a i - p' i
      = ((1 - q i) * a i + (p' i * s - p' i)) + (q i * a i - p' i * s) := by
    intro i; noncomm_ring
  have hsum_eq : ∑ i, star (a i - p' i) * (a i - p' i)
      = ∑ i, star (((1 - q i) * a i + (p' i * s - p' i)) + (q i * a i - p' i * s))
          * (((1 - q i) * a i + (p' i * s - p' i)) + (q i * a i - p' i * s)) :=
    Finset.sum_congr rfl fun i _ => by rw [hfun i]
  rw [hsum_eq]
  linarith

end Orthogonalization.MvN
