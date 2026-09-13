/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/Assembly.lean
-/
/-
# Assembly of the orthogonalized PVM (step **F3**)

This file carries out the last step of the proof of Theorem 1.2 in the finite
case (M. de la Salle, *Orthogonalization of Positive Operator Valued Measures*,
arXiv:2103.14126v2, Section 3, lines 247–271 of `manuscript/arXiv2103.14126v2.tex`;
`PLAN.md` §1, step **F3**).

The input is the isometry data of `Orthogonalization/IsometryData.lean`: reading
the partial isometry `u ∈ M_n(M)` of Lemma 3.2 block by block gives operators
`w_i = (e_{1i} ⊗ 1) u` on `H` satisfying

* (W1) `∑ i, w_i* w_i = 1`,
* (W2) `w_i w_j* = δ_{ij} q_i`,
* (W3) `w_i √y = q_i √a_i` where `y = ∑ j, q_j a_j`.

The paper's PVM is `p_i = u* t_i u` with `t_i = e_{ii} ⊗ q_i`, which in this
block notation is exactly `p_i = w_i* w_i` (`assembledPVM`). We prove:

* `IsometryData.q_mul_w`: `q_i w_i = w_i`;
* `assembledPVM_isStarProjection`, `sum_assembledPVM`: `(p_i)` is a PVM;
* `sqrt_mul_assembledPVM_mul_sqrt`: the paper's `|x| p_i |x| = q_i a_i`;
* `assembled_bound`: the three-term estimate
  `φ (∑ i, |a_i − p_i|²) < 9 ε`, from `φ (∑ a_i²) > 1 − ε` and
  `φ (∑ q_i a_i) ≥ 1 − ε`.

The estimate is proved through `assembled_bound_core`, which abstracts the
square root `|x|` into a plain operator `s` subject to the three properties the
argument actually uses (`0 ≤ s ≤ 1`, `s² = y`, `s p_i s = q_i a_i`); this keeps
the (long) inequality bookkeeping free of `CFC.sqrt`.

Nothing in this file is a statement of the paper; it is proof-side machinery for
`Orthogonalization/Basic.lean`.
-/
import Mathlib
import MIPRE.Background.Orthonormalization.Orthogonalization.Positivity
import MIPRE.Background.Orthonormalization.Orthogonalization.PhiNorm
import MIPRE.Background.Orthonormalization.Orthogonalization.IsometryData

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace Orthogonalization

open scoped ComplexOrder BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### The assembled projections -/

/-- The PVM assembled from the isometry data: `p_i = w_i* w_i`, which is the
paper's `p_i = u* t_i u` for `t_i = e_{ii} ⊗ q_i` read block by block. -/
noncomputable def assembledPVM {ι : Type*} (w : ι → H →L[ℂ] H) (i : ι) : H →L[ℂ] H :=
  star (w i) * w i

section Assembled

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {a q w : ι → H →L[ℂ] H}

/-- From (W1) and (W2): `q_i w_i = w_i`. Indeed
`q_i w_i = ∑ j, (w_i w_j*) w_j = w_i ∑ j, w_j* w_j = w_i`. -/
theorem IsometryData.q_mul_w (hw : IsometryData a q w) (i : ι) : q i * w i = w i := by
  have h1 : ∑ j, w i * star (w j) * w j = w i := by
    have hassoc : ∀ j : ι, w i * star (w j) * w j = w i * (star (w j) * w j) :=
      fun j => mul_assoc _ _ _
    simp_rw [hassoc, ← Finset.mul_sum, hw.sum_star_mul, mul_one]
  have h2 : ∑ j, w i * star (w j) * w j = q i * w i := by
    have hterm : ∀ j : ι, w i * star (w j) * w j = if i = j then q i * w i else 0 := by
      intro j
      rw [hw.mul_star i j]
      by_cases h : i = j
      · subst h; simp
      · simp [h]
    simp_rw [hterm]
    simp
  rw [← h2, h1]

/-- Each `p_i = w_i* w_i` is a star projection: self-adjointness is
`star_mul`/`star_star`, and idempotence follows from (W2) and
`IsometryData.q_mul_w`, since
`(w_i* w_i)(w_i* w_i) = w_i* (w_i w_i*) w_i = w_i* q_i w_i = w_i* w_i`. -/
theorem assembledPVM_isStarProjection (hw : IsometryData a q w) (i : ι) :
    IsStarProjection (assembledPVM w i) := by
  have hii : w i * star (w i) = q i := by simpa using hw.mul_star i i
  have hidem : assembledPVM w i * assembledPVM w i = assembledPVM w i := by
    show star (w i) * w i * (star (w i) * w i) = star (w i) * w i
    calc star (w i) * w i * (star (w i) * w i)
        = star (w i) * (w i * star (w i) * w i) := by noncomm_ring
      _ = star (w i) * (q i * w i) := by rw [hii]
      _ = star (w i) * w i := by rw [hw.q_mul_w i]
  have hsa : star (assembledPVM w i) = assembledPVM w i := by
    show star (star (w i) * w i) = star (w i) * w i
    rw [star_mul, star_star]
  exact ⟨hidem, hsa⟩

/-- The assembled projections sum to `1`: this is (W1). -/
theorem sum_assembledPVM (hw : IsometryData a q w) : ∑ i, assembledPVM w i = 1 :=
  hw.sum_star_mul

/-- The paper's identity `|x| p_i |x| = q_i a_i` (with `|x| = √(∑ j, q_j a_j)`):
`s p_i s = (w_i s)* (w_i s) = (q_i √a_i)* (q_i √a_i) = √a_i q_i √a_i = q_i a_i`,
using (W3), self-adjointness of `s` and of `√a_i`, idempotence of `q_i`, and the
fact that `q_i` commutes with `√a_i`. -/
theorem sqrt_mul_assembledPVM_mul_sqrt (hw : IsometryData a q w)
    (hq : ∀ i, IsStarProjection (q i)) (hqa : ∀ i, Commute (q i) (a i))
    (ha0 : ∀ i, 0 ≤ a i) (i : ι) :
    CFC.sqrt (∑ j, q j * a j) * assembledPVM w i * CFC.sqrt (∑ j, q j * a j) = q i * a i := by
  have hsa : star (CFC.sqrt (∑ j, q j * a j)) = CFC.sqrt (∑ j, q j * a j) :=
    IsSelfAdjoint.of_nonneg (sqrt_nonneg _)
  have hra : star (CFC.sqrt (a i)) = CFC.sqrt (a i) := IsSelfAdjoint.of_nonneg (sqrt_nonneg _)
  have hcomm : Commute (q i) (CFC.sqrt (a i)) := Orthogonalization.Commute.sqrt (hqa i)
  have hcomm' : CFC.sqrt (a i) * q i = q i * CFC.sqrt (a i) := hcomm.eq.symm
  have key : CFC.sqrt (∑ j, q j * a j) * assembledPVM w i * CFC.sqrt (∑ j, q j * a j)
      = star (w i * CFC.sqrt (∑ j, q j * a j)) * (w i * CFC.sqrt (∑ j, q j * a j)) := by
    rw [star_mul, hsa]
    show _ = CFC.sqrt (∑ j, q j * a j) * star (w i) * (w i * CFC.sqrt (∑ j, q j * a j))
    show CFC.sqrt (∑ j, q j * a j) * (star (w i) * w i) * CFC.sqrt (∑ j, q j * a j) = _
    noncomm_ring
  rw [key, hw.mul_sqrt i, star_mul, hra, (hq i).isSelfAdjoint.star_eq]
  calc CFC.sqrt (a i) * q i * (q i * CFC.sqrt (a i))
      = CFC.sqrt (a i) * (q i * q i) * CFC.sqrt (a i) := by noncomm_ring
    _ = CFC.sqrt (a i) * q i * CFC.sqrt (a i) := by rw [(hq i).isIdempotentElem.eq]
    _ = q i * (CFC.sqrt (a i) * CFC.sqrt (a i)) := by rw [hcomm']; noncomm_ring
    _ = q i * a i := by rw [sqrt_mul_sqrt_self (ha0 i)]

end Assembled

/-! ### Operator identities and inequalities for the three terms -/

section Terms

variable {r x s z : H →L[ℂ] H}

/-- Monotonicity of the compression by a projection commuting with the
difference: if `u ≤ v`, `r` is a projection and `r` commutes with `v - u`, then
`r u ≤ r v`, because `r (v - u)` is a product of commuting positive operators. -/
theorem IsStarProjection.mul_le_mul_of_commute (hr : IsStarProjection r) {u v : H →L[ℂ] H}
    (huv : u ≤ v) (h : Commute r (v - u)) : r * u ≤ r * v := by
  have h0 : 0 ≤ r * (v - u) :=
    Orthogonalization.mul_nonneg_of_commute hr.nonneg (sub_nonneg.mpr huv) h
  have he : r * (v - u) = r * v - r * u := by noncomm_ring
  rw [he] at h0
  exact sub_nonneg.mp h0

/-- `(r x)* (r x) = r x²` for a projection `r` commuting with a self-adjoint `x`.
This is the first term of the paper's decomposition, with `r = 1 - q_i`. -/
theorem star_mul_self_proj_mul (hr : IsStarProjection r) (hx : IsSelfAdjoint x)
    (h : Commute r x) : star (r * x) * (r * x) = r * (x * x) := by
  have h1 : star (r * x) = x * r := by
    rw [star_mul, hr.isSelfAdjoint.star_eq, hx.star_eq]
  rw [h1]
  calc x * r * (r * x) = x * (r * r) * x := by noncomm_ring
    _ = x * r * x := by rw [hr.isIdempotentElem.eq]
    _ = r * x * x := by rw [← h.eq]
    _ = r * (x * x) := mul_assoc _ _ _

/-- `(p (s - 1))* (p (s - 1)) = (1 - s) p (1 - s)` for a projection `p` and a
self-adjoint `s`. This is the third term of the paper's decomposition. -/
theorem star_mul_self_proj_mul_sub_self {p : H →L[ℂ] H} (hp : IsStarProjection p)
    (hs : star s = s) : star (p * s - p) * (p * s - p) = (1 - s) * p * (1 - s) := by
  have h1 : p * s - p = p * (s - 1) := by noncomm_ring
  rw [h1, star_mul, star_sub, hs, star_one, hp.isSelfAdjoint.star_eq]
  calc (s - 1) * p * (p * (s - 1)) = (s - 1) * (p * p) * (s - 1) := by noncomm_ring
    _ = (s - 1) * p * (s - 1) := by rw [hp.isIdempotentElem.eq]
    _ = (1 - s) * p * (1 - s) := by noncomm_ring

/-- `((s - 1) x)* ((s - 1) x) = x* (1 - s)² x` for a self-adjoint `s`; the
conjugating element of the second term of the paper's decomposition. -/
theorem star_mul_self_sub_one_mul (hs : star s = s) (x : H →L[ℂ] H) :
    star ((s - 1) * x) * ((s - 1) * x) = star x * ((1 - s) * (1 - s)) * x := by
  rw [star_mul, star_sub, hs, star_one]
  noncomm_ring

omit [CompleteSpace H] in
/-- With `s p s = z` and `p` idempotent: `s p (1 - s²) p s = z - z²`. This is
the paper's `|x| p_i (1 - |x|²) p_i |x| = |x| p_i |x| - (|x| p_i |x|)²`. -/
theorem conj_one_sub_sq_eq {p : H →L[ℂ] H} (hp : p * p = p) (hps : s * p * s = z) :
    s * p * (1 - s * s) * (p * s) = z - z * z := by
  have expand : s * p * (1 - s * s) * (p * s)
      = s * (p * p) * s - s * p * s * (s * p * s) := by noncomm_ring
  rw [expand, hp, hps]

/-- `q x - (q x)² = q (x - x²)` for a projection `q` commuting with `x`. -/
theorem proj_mul_sub_sq {qq : H →L[ℂ] H} (hq : IsStarProjection qq) (h : Commute qq x) :
    qq * x - qq * x * (qq * x) = qq * (x - x * x) := by
  have h1 : qq * x * (qq * x) = qq * (x * x) := by
    calc qq * x * (qq * x) = qq * (x * qq) * x := by noncomm_ring
      _ = qq * (qq * x) * x := by rw [h.eq]
      _ = qq * qq * (x * x) := by noncomm_ring
      _ = qq * (x * x) := by rw [hq.isIdempotentElem.eq]
  rw [h1]
  noncomm_ring

end Terms

/-! ### The `φ`-step -/

/-- If the operator `∑ i, b_i* b_i` is dominated by `x`, then the squared
seminorm `‖(b_i)‖_φ²` is dominated by `φ x` (real parts): the real part of a
positive functional is monotone. -/
theorem phiNormSq_le_re_map_of_le {φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ}
    (hφ : ∀ z : H →L[ℂ] H, 0 ≤ φ (star z * z)) {ι : Type*} [Fintype ι]
    {b : ι → H →L[ℂ] H} {x : H →L[ℂ] H} (h : ∑ i, star (b i) * b i ≤ x) :
    phiNormSq φ b ≤ (φ x).re := by
  rw [phiNormSq_eq_re_map_sum]
  exact re_le_re_of_le hφ h

/-! ### The three-term estimate -/

section Bound

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **The core of step F3.** The paper's estimate, with the square root
`|x| = √(∑ j, q_j a_j)` abstracted into an operator `s` subject only to the
properties the argument uses: `0 ≤ s ≤ 1`, `s² = ∑ j, q_j a_j` and
`s p_i s = q_i a_i`.

The proof decomposes `a_i - p_i = b_i + d_i + c_i` with
`b_i = (1 - q_i) a_i`, `d_i = p_i s - p_i`, `c_i = q_i a_i - p_i s`
and bounds `‖b‖_φ² ≤ ε`, `‖d‖_φ² ≤ ε`, `‖c‖_φ² < ε`; three applications of the
triangle inequality (`phiNormSq_add_add_lt`) then give the constant `9`. -/
theorem assembled_bound_core (φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ)
    (hφ : ∀ x : H →L[ℂ] H, 0 ≤ φ (star x * x)) (hφ1 : φ 1 = 1)
    (a q p : ι → H →L[ℂ] H) (s : H →L[ℂ] H)
    (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∑ i, a i = 1)
    (hq : ∀ i, IsStarProjection (q i)) (hqa : ∀ i, Commute (q i) (a i))
    (hp : ∀ i, IsStarProjection (p i)) (hpsum : ∑ i, p i = 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hss : s * s = ∑ j, q j * a j)
    (hsp : ∀ i, s * p i * s = q i * a i)
    (ε : ℝ) (hε : 1 - ε < (φ (∑ i, a i * a i)).re)
    (hlarge : 1 - ε ≤ (φ (∑ i, q i * a i)).re) :
    (φ (∑ i, star (a i - p i) * (a i - p i))).re < 9 * ε := by
  -- Elementary consequences of the hypotheses.
  have hone : (φ (1 : H →L[ℂ] H)).re = 1 := by rw [hφ1]; simp
  have hsa : star s = s := IsSelfAdjoint.of_nonneg hs0
  have ha_le_one : ∀ i, a i ≤ 1 := by
    intro i
    rw [← ha1]
    exact Finset.single_le_sum (f := a) (fun j _ => ha0 j) (Finset.mem_univ i)
  have haa : ∀ i, a i * a i ≤ a i := fun i => sq_le_self_of_le_one (ha0 i) (ha_le_one i)
  have hsum_aa_le : ∑ i, a i * a i ≤ 1 := by
    rw [← ha1]; exact Finset.sum_le_sum fun i _ => haa i
  have hbound_aa : (φ (∑ i, a i * a i)).re ≤ 1 := by
    have h := re_le_re_of_le hφ hsum_aa_le
    rwa [hone] at h
  have hε0 : 0 < ε := by linarith
  -- Values of `φ` on the two operators that appear as bounds.
  have hval_y : (φ (1 - ∑ i, q i * a i)).re = 1 - (φ (∑ i, q i * a i)).re := by
    rw [map_sub, Complex.sub_re, hone]
  have hval_aa : (φ (1 - ∑ i, a i * a i)).re = 1 - (φ (∑ i, a i * a i)).re := by
    rw [map_sub, Complex.sub_re, hone]
  -- The first term `b_i = (1 - q_i) a_i`.
  have hb_op : ∀ i, star ((1 - q i) * a i) * ((1 - q i) * a i) ≤ (1 - q i) * a i := by
    intro i
    have hr : IsStarProjection (1 - q i) := (hq i).one_sub
    have hcr : Commute (1 - q i) (a i) := (Commute.one_left (a i)).sub_left (hqa i)
    rw [star_mul_self_proj_mul hr (IsSelfAdjoint.of_nonneg (ha0 i)) hcr]
    exact Orthogonalization.IsStarProjection.mul_le_mul_of_commute hr (haa i)
      (hcr.sub_right (hcr.mul_right hcr))
  have hb_sum : ∑ i, (1 - q i) * a i = 1 - ∑ i, q i * a i := by
    simp only [sub_mul, one_mul]
    rw [Finset.sum_sub_distrib, ha1]
  have hb : phiNormSq φ (fun i => (1 - q i) * a i) ≤ ε := by
    have hstep : ∑ i, star ((1 - q i) * a i) * ((1 - q i) * a i) ≤ 1 - ∑ i, q i * a i := by
      rw [← hb_sum]
      exact Finset.sum_le_sum fun i _ => hb_op i
    have h := phiNormSq_le_re_map_of_le (φ := φ) hφ (b := fun i => (1 - q i) * a i) hstep
    rw [hval_y] at h
    linarith
  -- The third term `d_i = p_i s - p_i`.
  have hd : phiNormSq φ (fun i => p i * s - p i) ≤ ε := by
    have hsum : ∑ i, (1 - s) * p i * (1 - s) = (1 - s) * (1 - s) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, hpsum, mul_one]
    have hle : (1 - s) * (1 - s) ≤ 1 - ∑ j, q j * a j := by
      have h := one_sub_sq_le_one_sub_sq' hs0 hs1
      rwa [hss] at h
    have hstep : ∑ i, star (p i * s - p i) * (p i * s - p i) ≤ 1 - ∑ j, q j * a j := by
      calc ∑ i, star (p i * s - p i) * (p i * s - p i)
          = ∑ i, (1 - s) * p i * (1 - s) :=
            Finset.sum_congr rfl fun i _ => star_mul_self_proj_mul_sub_self (hp i) hsa
        _ = (1 - s) * (1 - s) := hsum
        _ ≤ 1 - ∑ j, q j * a j := hle
    have h := phiNormSq_le_re_map_of_le (φ := φ) hφ (b := fun i => p i * s - p i) hstep
    rw [hval_y] at h
    linarith
  -- The second term `c_i = q_i a_i - p_i s`.
  have hc : phiNormSq φ (fun i => q i * a i - p i * s) < ε := by
    have hc_op : ∀ i, star (q i * a i - p i * s) * (q i * a i - p i * s) ≤ a i - a i * a i := by
      intro i
      have hci : q i * a i - p i * s = (s - 1) * (p i * s) := by
        rw [← hsp i]; noncomm_ring
      have hstar_ps : star (p i * s) = s * p i := by
        rw [star_mul, hsa, (hp i).isSelfAdjoint.star_eq]
      have h1 : star (q i * a i - p i * s) * (q i * a i - p i * s)
          = star (p i * s) * ((1 - s) * (1 - s)) * (p i * s) := by
        rw [hci, star_mul_self_sub_one_mul hsa]
      have h2 : star (p i * s) * ((1 - s) * (1 - s)) * (p i * s)
          ≤ star (p i * s) * (1 - s * s) * (p i * s) :=
        conj_le_conj (one_sub_sq_le_one_sub_sq' hs0 hs1) (p i * s)
      have h3 : star (p i * s) * (1 - s * s) * (p i * s) = q i * a i - q i * a i * (q i * a i) := by
        rw [hstar_ps]
        exact conj_one_sub_sq_eq (hp i).isIdempotentElem.eq (hsp i)
      have h4 : q i * a i - q i * a i * (q i * a i) = q i * (a i - a i * a i) :=
        proj_mul_sub_sq (hq i) (hqa i)
      have h5 : q i * (a i - a i * a i) ≤ a i - a i * a i :=
        Orthogonalization.IsStarProjection.mul_le_of_commute (hq i) (sub_nonneg.mpr (haa i))
          ((hqa i).sub_right ((hqa i).mul_right (hqa i)))
      calc star (q i * a i - p i * s) * (q i * a i - p i * s)
          = star (p i * s) * ((1 - s) * (1 - s)) * (p i * s) := h1
        _ ≤ star (p i * s) * (1 - s * s) * (p i * s) := h2
        _ = q i * a i - q i * a i * (q i * a i) := h3
        _ = q i * (a i - a i * a i) := h4
        _ ≤ a i - a i * a i := h5
    have hc_sum : ∑ i, (a i - a i * a i) = 1 - ∑ i, a i * a i := by
      rw [Finset.sum_sub_distrib, ha1]
    have hstep : ∑ i, star (q i * a i - p i * s) * (q i * a i - p i * s) ≤ 1 - ∑ i, a i * a i := by
      rw [← hc_sum]
      exact Finset.sum_le_sum fun i _ => hc_op i
    have h := phiNormSq_le_re_map_of_le (φ := φ) hφ (b := fun i => q i * a i - p i * s) hstep
    rw [hval_aa] at h
    linarith
  -- Assemble: `a_i - p_i = b_i + d_i + c_i` and apply the triangle inequality.
  have hgoal : (φ (∑ i, star (a i - p i) * (a i - p i))).re
      = phiNormSq φ (fun i => a i - p i) := (phiNormSq_eq_re_map_sum _).symm
  rw [hgoal]
  have hfun : (fun i => a i - p i)
      = (fun i => (1 - q i) * a i) + (fun i => p i * s - p i)
        + (fun i => q i * a i - p i * s) := by
    funext i
    simp only [Pi.add_apply]
    noncomm_ring
  rw [hfun]
  exact phiNormSq_add_add_lt hφ hε0 hb hd hc

/-- **Step F3 of the proof of Theorem 1.2 in the finite case.** Given the
isometry data `(w_i)` of Lemma 3.2 for a POVM `(a_i)` and the commuting
projections `(q_i)` of Lemma 3.1, the assembled PVM `p_i = w_i* w_i` satisfies
`φ (∑ i, |a_i - p_i|²) < 9 ε` whenever `φ (∑ i, a_i²) > 1 - ε` and
`φ (∑ i, q_i a_i) ≥ 1 - ε`. -/
theorem assembled_bound (φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ)
    (hφ : ∀ x : H →L[ℂ] H, 0 ≤ φ (star x * x)) (hφ1 : φ 1 = 1)
    (a q w : ι → H →L[ℂ] H) (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∑ i, a i = 1)
    (hq : ∀ i, IsStarProjection (q i)) (hqa : ∀ i, Commute (q i) (a i))
    (hw : IsometryData a q w) (ε : ℝ) (hε : 1 - ε < (φ (∑ i, a i * a i)).re)
    (hlarge : 1 - ε ≤ (φ (∑ i, q i * a i)).re) :
    (φ (∑ i, star (a i - assembledPVM w i) * (a i - assembledPVM w i))).re < 9 * ε := by
  have hy0 : (0 : H →L[ℂ] H) ≤ ∑ j, q j * a j :=
    Finset.sum_nonneg fun j _ =>
      Orthogonalization.IsStarProjection.mul_nonneg_of_commute (hq j) (ha0 j) (hqa j)
  have hy1 : ∑ j, q j * a j ≤ 1 := by
    rw [← ha1]
    exact Finset.sum_le_sum fun j _ =>
      Orthogonalization.IsStarProjection.mul_le_of_commute (hq j) (ha0 j) (hqa j)
  exact assembled_bound_core φ hφ hφ1 a q (assembledPVM w) (CFC.sqrt (∑ j, q j * a j))
    ha0 ha1 hq hqa (assembledPVM_isStarProjection hw) (sum_assembledPVM hw)
    (sqrt_nonneg _) (sqrt_le_one_of_le_one hy1) (sqrt_mul_sqrt_self hy0)
    (sqrt_mul_assembledPVM_mul_sqrt hw hq hqa ha0) ε hε hlarge

end Bound

end Orthogonalization
