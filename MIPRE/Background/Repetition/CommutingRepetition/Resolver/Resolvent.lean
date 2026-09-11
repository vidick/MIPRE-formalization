/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Resolver/Resolvent.lean
-/
/-
# Resolvents of positive contractions and the pointwise resolver bound
(nodes 1.2.6.1, 1.2.6.2)

Layer A1/A2 of `PLAN-resolver-entropic.md`. In a unital C*-algebra with its
Loewner order: for a positive element `F` and `u > 0`, the resolvent
`R_F(u) = (F + u)⁻¹` and the resolver fiber `f_F(u) = F (F + u)⁻¹`
(04_resolver_corner.tex, eqs resolver-fiber, resolvent-notation), both as
`cfc` outputs; the fiber difference identity (eq resolver-fiber-difference,
node 1.2.6.1) from the second resolvent identity of `Prelim/Entropy.lean`;
the bound `R_F(u)² ≼ u⁻¹ R_F(u)`; and the **pointwise expectation bound**
(eq pointwise-resolver-entropy, node 1.2.6.2): for weights `wₖ ≥ 0` with
`∑ wₖ Fₖ = W F̄`,

  `∑ wₖ (f_{Fₖ}(u) − f_{F̄}(u))² ≼ u (∑ wₖ R_{Fₖ}(u) − W R_{F̄}(u))`.

Nothing here is a manuscript statement (proof layer of node 1.2.6).
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Prelim.Entropy

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace Resolver

open scoped BigOperators

set_option linter.unusedSectionVars false

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-! ### Scalar-multiplication monotonicity in the Loewner order -/

theorem smul_nonneg_of_nonneg {w : ℝ} (hw : 0 ≤ w) {a : A} (ha : 0 ≤ a) : 0 ≤ w • a := by
  have hsq : a = CFC.sqrt a * CFC.sqrt a := (CFC.sqrt_mul_sqrt_self a ha).symm
  have hsa : IsSelfAdjoint (CFC.sqrt a) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)
  have : w • a = star (Real.sqrt w • CFC.sqrt a) * (Real.sqrt w • CFC.sqrt a) := by
    rw [star_smul, hsa.star_eq, star_trivial, smul_mul_assoc, mul_smul_comm, smul_smul,
      Real.mul_self_sqrt hw, ← hsq]
  rw [this]
  exact star_mul_self_nonneg _

theorem smul_le_smul_left {w : ℝ} (hw : 0 ≤ w) {a b : A} (hab : a ≤ b) : w • a ≤ w • b := by
  have := smul_nonneg_of_nonneg hw (sub_nonneg.mpr hab)
  rw [smul_sub] at this
  exact sub_nonneg.mp this

/-! ### Spectra of positive contractions -/

theorem spectrum_nonneg {F : A} (hF0 : 0 ≤ F) {x : ℝ} (hx : x ∈ spectrum ℝ F) : 0 ≤ x :=
  spectrum_nonneg_of_nonneg hF0 hx

theorem spectrum_le_one {F : A} (hF1 : F ≤ 1) {x : ℝ} (hx : x ∈ spectrum ℝ F) : x ≤ 1 := by
  have hmem : (1 : ℝ) - x ∈ spectrum ℝ (algebraMap ℝ A 1 - F) := by
    rw [← spectrum.singleton_sub_eq]
    exact ⟨1, Set.mem_singleton 1, x, hx, rfl⟩
  rw [map_one] at hmem
  have := spectrum_nonneg_of_nonneg (sub_nonneg.mpr hF1) hmem
  linarith

/-! ### The resolvent and the resolver fiber -/

/-- The resolvent `R_F(u) = (F + u)⁻¹` (eq resolvent-notation). -/
noncomputable def res (F : A) (u : ℝ) : A := cfc (fun t : ℝ => (t + u)⁻¹) F

/-- The resolver fiber `f_F(u) = F (F + u)⁻¹` (eq resolver-fiber). -/
noncomputable def fib (F : A) (u : ℝ) : A := cfc (fun t : ℝ => t / (t + u)) F

variable {F : A} {u : ℝ}

theorem continuousOn_res (hF0 : 0 ≤ F) (hu : 0 < u) :
    ContinuousOn (fun t : ℝ => (t + u)⁻¹) (spectrum ℝ F) :=
  (continuousOn_id.add continuousOn_const).inv₀ fun _ hx =>
    ne_of_gt (add_pos_of_nonneg_of_pos (spectrum_nonneg hF0 hx) hu)

theorem continuousOn_fib (hF0 : 0 ≤ F) (hu : 0 < u) :
    ContinuousOn (fun t : ℝ => t / (t + u)) (spectrum ℝ F) :=
  continuousOn_id.div (continuousOn_id.add continuousOn_const) fun _ hx =>
    ne_of_gt (add_pos_of_nonneg_of_pos (spectrum_nonneg hF0 hx) hu)

theorem continuousOn_add_const (s : Set ℝ) : ContinuousOn (fun t : ℝ => t + u) s := by
  fun_prop

theorem res_isSelfAdjoint : IsSelfAdjoint (res F u) := cfc_predicate _ F

theorem fib_isSelfAdjoint : IsSelfAdjoint (fib F u) := cfc_predicate _ F

theorem res_nonneg (hF0 : 0 ≤ F) (hu : 0 < u) : 0 ≤ res F u :=
  cfc_nonneg fun _ hx => inv_nonneg.mpr (add_pos_of_nonneg_of_pos (spectrum_nonneg hF0 hx) hu).le

theorem fib_nonneg (hF0 : 0 ≤ F) (hu : 0 < u) : 0 ≤ fib F u :=
  cfc_nonneg fun _ hx => div_nonneg (spectrum_nonneg hF0 hx)
    (add_pos_of_nonneg_of_pos (spectrum_nonneg hF0 hx) hu).le

/-- `cfc (t + u) F = F + u`. -/
theorem cfc_add_const_eq (hF0 : 0 ≤ F) :
    cfc (fun t : ℝ => t + u) F = F + algebraMap ℝ A u := by
  have hsa : IsSelfAdjoint F := IsSelfAdjoint.of_nonneg hF0
  rw [cfc_add_const u (fun t : ℝ => t) F continuousOn_id hsa, cfc_id' ℝ F hsa]

theorem res_mul_add (hF0 : 0 ≤ F) (hu : 0 < u) :
    res F u * (F + algebraMap ℝ A u) = 1 := by
  have hsa : IsSelfAdjoint F := IsSelfAdjoint.of_nonneg hF0
  rw [← cfc_add_const_eq hF0, res, ← cfc_mul _ _ F (continuousOn_res hF0 hu)
    (continuousOn_add_const _)]
  rw [← cfc_one ℝ F hsa]
  refine cfc_congr fun x hx => ?_
  have : x + u ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos (spectrum_nonneg hF0 hx) hu)
  simp [inv_mul_cancel₀ this]

theorem add_mul_res (hF0 : 0 ≤ F) (hu : 0 < u) :
    (F + algebraMap ℝ A u) * res F u = 1 := by
  have hsa : IsSelfAdjoint F := IsSelfAdjoint.of_nonneg hF0
  rw [← cfc_add_const_eq hF0, res, ← cfc_mul _ _ F (continuousOn_add_const _)
    (continuousOn_res hF0 hu)]
  rw [← cfc_one ℝ F hsa]
  refine cfc_congr fun x hx => ?_
  have : x + u ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos (spectrum_nonneg hF0 hx) hu)
  simp [mul_inv_cancel₀ this]

/-- `f_F(u) = F R_F(u)`. -/
theorem fib_eq_mul_res (hF0 : 0 ≤ F) (hu : 0 < u) : fib F u = F * res F u := by
  have hsa : IsSelfAdjoint F := IsSelfAdjoint.of_nonneg hF0
  rw [res, fib]
  conv_rhs => enter [1]; rw [← cfc_id' ℝ F hsa]
  rw [← cfc_mul (fun t : ℝ => t) (fun t : ℝ => (t + u)⁻¹) F continuousOn_id
    (continuousOn_res hF0 hu)]
  exact cfc_congr fun x _ => div_eq_mul_inv x (x + u)

/-- `f_F(u) = R_F(u) F`. -/
theorem fib_eq_res_mul (hF0 : 0 ≤ F) (hu : 0 < u) : fib F u = res F u * F := by
  have hsa : IsSelfAdjoint F := IsSelfAdjoint.of_nonneg hF0
  rw [res, fib]
  conv_rhs => enter [2]; rw [← cfc_id' ℝ F hsa]
  rw [← cfc_mul (fun t : ℝ => (t + u)⁻¹) (fun t : ℝ => t) F (continuousOn_res hF0 hu)
    continuousOn_id]
  exact cfc_congr fun x _ => by rw [div_eq_mul_inv, mul_comm]

/-- `f_F(u) = 1 − u R_F(u)`. -/
theorem fib_eq_one_sub (hF0 : 0 ≤ F) (hu : 0 < u) : fib F u = 1 - u • res F u := by
  have hsa : IsSelfAdjoint F := IsSelfAdjoint.of_nonneg hF0
  rw [res, fib, ← cfc_smul u (fun t : ℝ => (t + u)⁻¹) F (continuousOn_res hF0 hu),
    ← cfc_one ℝ F hsa,
    ← cfc_sub (f := (1 : ℝ → ℝ)) (g := fun x : ℝ => u • (x + u)⁻¹) (hf := continuousOn_const)
      (hg := (continuousOn_res hF0 hu).const_smul u)]
  refine cfc_congr fun x hx => ?_
  have : x + u ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos (spectrum_nonneg hF0 hx) hu)
  simp only [Pi.one_apply, smul_eq_mul]
  field_simp
  ring

theorem fib_le_one (hF0 : 0 ≤ F) (hu : 0 < u) : fib F u ≤ 1 := by
  have hsa : IsSelfAdjoint F := IsSelfAdjoint.of_nonneg hF0
  rw [fib, ← cfc_one ℝ F hsa]
  refine cfc_mono (fun x hx => ?_) (continuousOn_fib hF0 hu) continuousOn_const
  have hx0 := spectrum_nonneg hF0 hx
  simp only [Pi.one_apply]
  rw [div_le_one (add_pos_of_nonneg_of_pos hx0 hu)]
  linarith

theorem norm_res_le (hF0 : 0 ≤ F) (hu : 0 < u) : ‖res F u‖ ≤ u⁻¹ := by
  refine norm_cfc_le (inv_pos.mpr hu).le fun x hx => ?_
  have hx0 := spectrum_nonneg hF0 hx
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_pos.mpr (add_pos_of_nonneg_of_pos hx0 hu)).le]
  exact inv_anti₀ hu (by linarith)

theorem norm_fib_le_one (hF0 : 0 ≤ F) (hu : 0 < u) : ‖fib F u‖ ≤ 1 := by
  refine norm_cfc_le zero_le_one fun x hx => ?_
  have hx0 := spectrum_nonneg hF0 hx
  have hpos := add_pos_of_nonneg_of_pos hx0 hu
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hx0 hpos.le), div_le_one hpos]
  linarith

theorem norm_fib_le (hF0 : 0 ≤ F) (hu : 0 < u) : ‖fib F u‖ ≤ ‖F‖ / u := by
  rw [fib_eq_mul_res hF0 hu, div_eq_mul_inv]
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_res_le hF0 hu) (norm_nonneg F))

/-- `R_F(u)² ≼ u⁻¹ R_F(u)` (the resolvent is bounded by `u⁻¹`). -/
theorem res_mul_res_le (hF0 : 0 ≤ F) (hu : 0 < u) :
    res F u * res F u ≤ u⁻¹ • res F u := by
  rw [res, ← cfc_mul _ _ F (continuousOn_res hF0 hu) (continuousOn_res hF0 hu),
    ← cfc_smul u⁻¹ _ F (continuousOn_res hF0 hu)]
  refine cfc_mono (fun x hx => ?_) ((continuousOn_res hF0 hu).mul (continuousOn_res hF0 hu))
    ((continuousOn_res hF0 hu).const_smul u⁻¹)
  have hx0 := spectrum_nonneg hF0 hx
  have hpos := add_pos_of_nonneg_of_pos hx0 hu
  simp only [smul_eq_mul]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ hu (by linarith)) (inv_pos.mpr hpos).le

/-! ### The fiber difference identity (node 1.2.6.1) -/

/-- eq resolver-fiber-difference: `f_F(u) − f_G(u) = u R_F(u) (F − G) R_G(u)`. -/
theorem fib_sub_fib {F G : A} (hF0 : 0 ≤ F) (hG0 : 0 ≤ G) (hu : 0 < u) :
    fib F u - fib G u = u • (res F u * (F - G) * res G u) := by
  have h := noncommutative_resolvent_identity F G (algebraMap ℝ A u) (res F u) (res G u)
    (res_mul_add hF0 hu) (add_mul_res hG0 hu)
  rw [fib_eq_one_sub hF0 hu, fib_eq_one_sub hG0 hu]
  rw [show (1 : A) - u • res F u - (1 - u • res G u) = u • (res G u - res F u) by
    rw [smul_sub]; abel]
  rw [show res G u - res F u = -(res F u - res G u) by abel, h]
  congr 1
  noncomm_ring

/-- Pulling scalar weights and a two-sided conjugation out of a finite sum. -/
theorem sum_smul_conj {ι : Type*} [Fintype ι] (w : ι → ℝ) (X : ι → A) (P Q : A) :
    (∑ i, w i • (P * X i * Q)) = P * (∑ i, w i • X i) * Q := by
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, smul_mul_assoc]

/-- The weighted second-order resolvent identity in the division-free mean
form `∑ wₖ Fₖ = W F̄` (eq second-resolvent-rearranged, summed). -/
theorem weighted_res_identity {ι : Type*} [Fintype ι] (w : ι → ℝ) (Fs : ι → A) (Fb : A)
    (hF0 : ∀ i, 0 ≤ Fs i) (hFb0 : 0 ≤ Fb) (hu : 0 < u)
    (hmean : (∑ i, w i • Fs i) = (∑ i, w i) • Fb) :
    (∑ i, w i • res (Fs i) u) - (∑ i, w i) • res Fb u
      = res Fb u * (∑ i, w i • ((Fs i - Fb) * res (Fs i) u * (Fs i - Fb))) * res Fb u := by
  have hterm : ∀ i, res (Fs i) u
      = res Fb u - res Fb u * (Fs i - Fb) * res Fb u
        + res Fb u * (Fs i - Fb) * res (Fs i) u * (Fs i - Fb) * res Fb u := fun i =>
    noncommutative_resolvent_second_order (Fs i) Fb (algebraMap ℝ A u) (res (Fs i) u) (res Fb u)
      (add_mul_res (hF0 i) hu) (res_mul_add (hF0 i) hu) (add_mul_res hFb0 hu)
      (res_mul_add hFb0 hu)
  have hJ : (∑ i, w i • (Fs i - Fb)) = 0 := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hmean, sub_self]
  have hsum : (∑ i, w i • res (Fs i) u)
      = ∑ i, (w i • res Fb u - w i • (res Fb u * (Fs i - Fb) * res Fb u)
        + w i • (res Fb u * ((Fs i - Fb) * res (Fs i) u * (Fs i - Fb)) * res Fb u)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_lhs => rw [hterm i]
    rw [smul_add, smul_sub]
    congr 2
    simp only [mul_assoc]
  rw [hsum, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_smul,
    sum_smul_conj, sum_smul_conj, hJ]
  simp

/-! ### The pointwise expectation bound (node 1.2.6.2) -/

/-- **eq pointwise-resolver-entropy**: for nonnegative weights with
`∑ wₖ Fₖ = W F̄`, `∑ wₖ (f_{Fₖ}(u) − f_{F̄}(u))² ≼ u (∑ wₖ R_{Fₖ}(u) − W R_{F̄}(u))`. -/
theorem pointwise_expectation_bound {ι : Type*} [Fintype ι] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (Fs : ι → A) (Fb : A) (hF0 : ∀ i, 0 ≤ Fs i) (hFb0 : 0 ≤ Fb) (hu : 0 < u)
    (hmean : (∑ i, w i • Fs i) = (∑ i, w i) • Fb) :
    (∑ i, w i • ((fib (Fs i) u - fib Fb u) * (fib (Fs i) u - fib Fb u)))
      ≤ u • ((∑ i, w i • res (Fs i) u) - (∑ i, w i) • res Fb u) := by
  have hterm : ∀ i, (fib (Fs i) u - fib Fb u) * (fib (Fs i) u - fib Fb u)
      ≤ u • (res Fb u * ((Fs i - Fb) * res (Fs i) u * (Fs i - Fb)) * res Fb u) := by
    intro i
    have hX : fib (Fs i) u - fib Fb u = u • (res (Fs i) u * (Fs i - Fb) * res Fb u) :=
      fib_sub_fib (hF0 i) hFb0 hu
    have hXsa : IsSelfAdjoint (fib (Fs i) u - fib Fb u) :=
      fib_isSelfAdjoint.sub fib_isSelfAdjoint
    have hJsa : IsSelfAdjoint (Fs i - Fb) :=
      (IsSelfAdjoint.of_nonneg (hF0 i)).sub (IsSelfAdjoint.of_nonneg hFb0)
    have hX' : fib (Fs i) u - fib Fb u = u • (res Fb u * (Fs i - Fb) * res (Fs i) u) := by
      rw [← hXsa.star_eq, hX, star_smul, star_trivial, star_mul, star_mul,
        res_isSelfAdjoint.star_eq, res_isSelfAdjoint.star_eq, hJsa.star_eq, mul_assoc]
    have hsq : (fib (Fs i) u - fib Fb u) * (fib (Fs i) u - fib Fb u)
        = (u * u) • (star ((Fs i - Fb) * res Fb u) * (res (Fs i) u * res (Fs i) u) *
            ((Fs i - Fb) * res Fb u)) := by
      conv_lhs => enter [1]; rw [hX']
      conv_lhs => enter [2]; rw [hX]
      rw [smul_mul_assoc, mul_smul_comm, smul_smul, star_mul, res_isSelfAdjoint.star_eq,
        hJsa.star_eq]
      congr 1
      noncomm_ring
    rw [hsq]
    have hle := star_left_conjugate_le_conjugate (res_mul_res_le (hF0 i) hu)
      ((Fs i - Fb) * res Fb u)
    refine (smul_le_smul_left (mul_nonneg hu.le hu.le) hle).trans (le_of_eq ?_)
    rw [star_mul, res_isSelfAdjoint.star_eq, hJsa.star_eq, mul_smul_comm, smul_mul_assoc,
      smul_smul, show u * u * u⁻¹ = u by field_simp]
    congr 1
    noncomm_ring
  calc (∑ i, w i • ((fib (Fs i) u - fib Fb u) * (fib (Fs i) u - fib Fb u)))
      ≤ ∑ i, w i • (u • (res Fb u * ((Fs i - Fb) * res (Fs i) u * (Fs i - Fb)) * res Fb u)) :=
        Finset.sum_le_sum fun i _ => smul_le_smul_left (hw i) (hterm i)
    _ = u • (res Fb u * (∑ i, w i • ((Fs i - Fb) * res (Fs i) u * (Fs i - Fb))) * res Fb u) := by
        rw [← sum_smul_conj, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_comm]
    _ = _ := by rw [weighted_res_identity w Fs Fb hF0 hFb0 hu hmean]

end Resolver

end CommutingRepetition
