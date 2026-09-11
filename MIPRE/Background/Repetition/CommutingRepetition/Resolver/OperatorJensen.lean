/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Resolver/OperatorJensen.lean
-/
/-
# Operator Jensen for the scalar entropy `H₁ = negMulLog` (proof layer of node 1.2.6)

Layer A8 of `PLAN-resolver-entropic.md` (05_prerounding.tex, eq
positive-functional-jensen): for a positive real-linear functional `ω` on a
C*-algebra with `ω(1) ≤ 1` and a positive contraction `F`,
`ω(H₁(F)) ≤ H₁(ω(F))`. Proved by the tangent line of the concave `negMulLog`
at `x̄ = ω(F)/ω(1)` (the tangent inequality is the scalar
`self_sub_one_le_mul_log` at `t/x̄`), `cfc_mono`, the scaling
`m · negMulLog(y/m) ≤ negMulLog y` for `m ≤ 1`, and tangents at `ε → 0`
when `ω(F) = 0`. Nothing here is a manuscript statement.
-/
import Mathlib

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace Resolver

set_option linter.unusedSectionVars false

/-! ### The scalar tangent inequality -/

/-- The tangent line of `negMulLog` at `x > 0` dominates it on `[0, ∞)`. -/
theorem negMulLog_le_tangent {x t : ℝ} (hx : 0 < x) (ht : 0 ≤ t) :
    Real.negMulLog t ≤ Real.negMulLog x + (-Real.log x - 1) * (t - x) := by
  rcases ht.lt_or_eq with ht' | ht'
  · have h := Real.self_sub_one_le_mul_log (div_nonneg ht hx.le)
    rw [Real.log_div ht'.ne' hx.ne'] at h
    have h2 : t - x ≤ t * (Real.log t - Real.log x) := by
      have := mul_le_mul_of_nonneg_left h hx.le
      rwa [mul_sub, mul_one, mul_div_cancel₀ _ hx.ne', ← mul_assoc, mul_div_cancel₀ _ hx.ne']
        at this
    have key : Real.negMulLog t - (Real.negMulLog x + (-Real.log x - 1) * (t - x))
        = -(t * (Real.log t - Real.log x) - (t - x)) := by
      simp only [Real.negMulLog]
      ring
    linarith
  · subst ht'
    have : Real.negMulLog x + (-Real.log x - 1) * (0 - x) = x := by
      simp only [Real.negMulLog]
      ring
    rw [this, Real.negMulLog_zero]
    exact hx.le

/-- `m · negMulLog (y / m) ≤ negMulLog y` for `0 < m ≤ 1`, `0 ≤ y`. -/
theorem smul_negMulLog_div_le {m y : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1) (hy : 0 ≤ y) :
    m * Real.negMulLog (y / m) ≤ Real.negMulLog y := by
  rcases hy.lt_or_eq with hy' | hy'
  · simp only [Real.negMulLog, Real.log_div hy'.ne' hm0.ne']
    have hlogm : Real.log m ≤ 0 := Real.log_nonpos hm0.le hm1
    have : m * (-(y / m) * (Real.log y - Real.log m)) = -y * Real.log y + y * Real.log m := by
      field_simp
      ring
    rw [this]
    nlinarith
  · subst hy'
    simp [Real.negMulLog]

/-! ### The operator version -/

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem continuousOn_negMulLog (s : Set ℝ) : ContinuousOn Real.negMulLog s :=
  Real.continuous_negMulLog.continuousOn

/-- The affine tangent bound as an operator inequality: for `0 ≤ F ≤ 1` and
`x > 0`, `H₁(F) ≼ (H₁(x) − s x)·1 + s F` with `s = −log x − 1`. -/
theorem cfc_negMulLog_le_affine {F : A} (hF0 : 0 ≤ F) {x : ℝ} (hx : 0 < x) :
    cfc Real.negMulLog F
      ≤ algebraMap ℝ A (Real.negMulLog x - (-Real.log x - 1) * x) + (-Real.log x - 1) • F := by
  have hsa : IsSelfAdjoint F := IsSelfAdjoint.of_nonneg hF0
  have hrhs : algebraMap ℝ A (Real.negMulLog x - (-Real.log x - 1) * x) + (-Real.log x - 1) • F
      = cfc (fun t : ℝ => (Real.negMulLog x - (-Real.log x - 1) * x) + (-Real.log x - 1) * t) F := by
    rw [cfc_const_add _ _ F (by fun_prop) hsa, cfc_const_mul_id _ F hsa]
  rw [hrhs]
  refine cfc_mono (fun t ht => ?_) (continuousOn_negMulLog _) (by fun_prop)
  have ht0 : 0 ≤ t := spectrum_nonneg_of_nonneg hF0 ht
  have := negMulLog_le_tangent hx ht0
  linarith

theorem cfc_negMulLog_nonneg {F : A} (hF0 : 0 ≤ F) (hF1 : F ≤ 1) :
    0 ≤ cfc Real.negMulLog F := by
  refine cfc_nonneg fun t ht => Real.negMulLog_nonneg (spectrum_nonneg_of_nonneg hF0 ht) ?_
  have hmem : (1 : ℝ) - t ∈ spectrum ℝ (algebraMap ℝ A 1 - F) := by
    rw [← spectrum.singleton_sub_eq]
    exact ⟨1, Set.mem_singleton 1, t, ht, rfl⟩
  rw [map_one] at hmem
  linarith [spectrum_nonneg_of_nonneg (sub_nonneg.mpr hF1) hmem]

/-- **Operator Jensen** (eq positive-functional-jensen): for a positive
real-linear functional `ω` with `ω(1) ≤ 1` and a positive contraction `F`,
`ω(H₁(F)) ≤ H₁(ω(F))`. -/
theorem jensen_negMulLog (ω : A →ₗ[ℝ] ℝ) (hmono : ∀ {a b : A}, a ≤ b → ω a ≤ ω b)
    (hm1 : ω 1 ≤ 1) {F : A} (hF0 : 0 ≤ F) (hF1 : F ≤ 1) :
    ω (cfc Real.negMulLog F) ≤ Real.negMulLog (ω F) := by
  have hone : (0 : A) ≤ 1 := zero_le_one
  have hm0 : 0 ≤ ω 1 := by simpa using hmono hone
  have hy0 : 0 ≤ ω F := by simpa using hmono hF0
  have hym : ω F ≤ ω 1 := hmono hF1
  -- the affine bound evaluated by `ω`
  have haff : ∀ x : ℝ, 0 < x → ω (cfc Real.negMulLog F)
      ≤ (Real.negMulLog x - (-Real.log x - 1) * x) * ω 1 + (-Real.log x - 1) * ω F := by
    intro x hx
    have h := hmono (cfc_negMulLog_le_affine hF0 hx)
    rwa [map_add, map_smul, Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul,
      smul_eq_mul] at h
  rcases hm0.lt_or_eq with hm | hm
  · rcases hy0.lt_or_eq with hy | hy
    · -- x̄ = ω F / ω 1
      have hx : 0 < ω F / ω 1 := div_pos hy hm
      have h := haff _ hx
      have hxm : ω F / ω 1 * ω 1 = ω F := div_mul_cancel₀ _ hm.ne'
      calc ω (cfc Real.negMulLog F)
          ≤ (Real.negMulLog (ω F / ω 1) - (-Real.log (ω F / ω 1) - 1) * (ω F / ω 1)) * ω 1
            + (-Real.log (ω F / ω 1) - 1) * ω F := h
        _ = ω 1 * Real.negMulLog (ω F / ω 1) := by
            rw [sub_mul, mul_assoc, hxm]
            ring
        _ ≤ Real.negMulLog (ω F) := smul_negMulLog_div_le hm hm1 hy0
    · -- ω F = 0: tangents at ε → 0
      rw [← hy, Real.negMulLog_zero]
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have hε' : 0 < ε / ω 1 := div_pos hε hm
      have h := haff _ hε'
      rw [← hy, mul_zero, add_zero] at h
      have : (Real.negMulLog (ε / ω 1) - (-Real.log (ε / ω 1) - 1) * (ε / ω 1)) * ω 1 = ε := by
        simp only [Real.negMulLog]
        field_simp
        ring
      rw [this] at h
      linarith
  · -- ω 1 = 0 forces ω = 0 on `[0, 1]`
    have hle : cfc Real.negMulLog F ≤ (1 : A) := by
      have hsa : IsSelfAdjoint F := IsSelfAdjoint.of_nonneg hF0
      rw [← cfc_one ℝ F hsa]
      refine cfc_mono (fun t ht => ?_) (continuousOn_negMulLog _) continuousOn_const
      have ht0 := spectrum_nonneg_of_nonneg hF0 ht
      simp only [Pi.one_apply]
      linarith [Real.negMulLog_le_one_sub_self ht0]
    have h1 := hmono hle
    have h2 := hmono (cfc_negMulLog_nonneg hF0 hF1)
    rw [map_zero] at h2
    have hy : ω F = 0 := le_antisymm (hym.trans hm.symm.le) hy0
    rw [hy, Real.negMulLog_zero]
    linarith

end Resolver

end CommutingRepetition
