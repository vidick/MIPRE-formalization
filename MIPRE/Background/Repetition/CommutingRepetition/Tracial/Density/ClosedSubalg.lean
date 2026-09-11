/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Tracial/Density/ClosedSubalg.lean
-/
/-
# Closed `*`-subalgebras of `B(H)` as C*-algebras (stage E7.3a)

`Tracial/Density/RadonNikodym.lean` consumes a C*-algebra `𝒞` with a *compatible*
`PartialOrder` and `StarOrderedRing` structure, together with positive linear
functionals on it. This file supplies that layer for `𝒞 = ↥s`, `s` a norm-closed
`*`-subalgebra of `B(H)`:

* the order is the *restricted Loewner order* (`Subtype.partialOrder`), so
  `0 ≤ a` in `↥s` is literally `0 ≤ (a : B(H))` (`coe_nonneg_iff`, `Iff.rfl`);
* `StarOrderedRing ↥s` holds because the continuous-functional-calculus square
  root of a positive element of `s` stays in `s` (`cfc_mem_of_isClosed`, from
  `StarAlgebra.elemental.le_iff_mem`);
* `subVecState` and `subBobState` are the two families of positive functionals E7
  needs: the vector state `c·⟪ξ, · ξ⟫` and Bob's `⟪ξ, (·) (B ξ)⟫` for a positive
  `B` commuting with `s`.

Proof-side; nothing here is specific to the crossed product.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.Generated

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace Density

open scoped InnerProductSpace ComplexOrder

set_option linter.unusedSectionVars false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## The square root inside a closed `*`-subalgebra -/

section Sqrt

variable (s : StarSubalgebra ℂ (H →L[ℂ] H)) (hcl : IsClosed (s : Set (H →L[ℂ] H)))

include hcl in
/-- The continuous functional calculus of a self-adjoint element of a norm-closed
`*`-subalgebra stays inside it. -/
theorem cfc_mem_of_isClosed {A : H →L[ℂ] H} (hsa : IsSelfAdjoint A) (hA : A ∈ s)
    (f : ℝ → ℝ) : cfc f A ∈ s := by
  rw [cfc_real_eq_complex f hsa]
  exact (StarAlgebra.elemental.le_iff_mem hcl).mpr hA (cfc_mem_elemental _ _)

include hcl in
/-- A positive element of a norm-closed `*`-subalgebra has a self-adjoint square root
inside it. -/
theorem exists_sqrt_mem_of_isClosed {A : H →L[ℂ] H} (h0 : 0 ≤ A) (hA : A ∈ s) :
    ∃ r ∈ s, IsSelfAdjoint r ∧ r * r = A := by
  have hsa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg h0
  refine ⟨cfc Real.sqrt A, cfc_mem_of_isClosed s hcl hsa hA _, cfc_predicate _ _, ?_⟩
  rw [← cfc_mul Real.sqrt Real.sqrt A Real.continuous_sqrt.continuousOn
    Real.continuous_sqrt.continuousOn]
  calc cfc (fun t : ℝ => Real.sqrt t * Real.sqrt t) A = cfc (fun t : ℝ => t) A :=
        cfc_congr fun t ht => Real.mul_self_sqrt (spectrum_nonneg_of_nonneg h0 ht)
    _ = A := cfc_id' ℝ A hsa

end Sqrt

/-! ## The restricted Loewner order -/

section Order

variable (s : StarSubalgebra ℂ (H →L[ℂ] H)) [hcl : IsClosed (s : Set (H →L[ℂ] H))]

theorem coe_le_iff (a b : ↥s) : a ≤ b ↔ (a : H →L[ℂ] H) ≤ (b : H →L[ℂ] H) := Iff.rfl

theorem coe_nonneg_iff (a : ↥s) : 0 ≤ a ↔ (0 : H →L[ℂ] H) ≤ (a : H →L[ℂ] H) := Iff.rfl

/-- **A norm-closed `*`-subalgebra of `B(H)` is a `StarOrderedRing`** for the restricted
Loewner order. -/
instance instStarOrderedRing : StarOrderedRing ↥s := by
  refine StarOrderedRing.of_le_iff fun x y => ⟨fun h => ?_, fun ⟨t, ht⟩ => ?_⟩
  · have h0 : (0 : H →L[ℂ] H) ≤ (y : H →L[ℂ] H) - x := sub_nonneg.mpr h
    obtain ⟨r, hrmem, hrsa, hrr⟩ :=
      exists_sqrt_mem_of_isClosed s hcl h0 (sub_mem y.2 x.2)
    refine ⟨⟨r, hrmem⟩, Subtype.ext ?_⟩
    show (y : H →L[ℂ] H) = (x : H →L[ℂ] H) + star r * r
    rw [hrsa.star_eq, hrr, add_sub_cancel]
  · show (x : H →L[ℂ] H) ≤ (y : H →L[ℂ] H)
    rw [show ((y : H →L[ℂ] H)) = ((x + star t * t : ↥s) : H →L[ℂ] H) by rw [← ht]]
    show (x : H →L[ℂ] H) ≤ (x : H →L[ℂ] H) + star (t : H →L[ℂ] H) * t
    exact le_add_of_nonneg_right (star_mul_self_nonneg _)

end Order

/-! ## Positive functionals from vectors -/

section States

theorem inner_nonneg_of_nonneg {T : H →L[ℂ] H} (h0 : 0 ≤ T) (ξ : H) : 0 ≤ ⟪ξ, T ξ⟫_ℂ := by
  have hp := (ContinuousLinearMap.nonneg_iff_isPositive T).mp h0
  have := hp.inner_nonneg_right ξ
  exact this

variable (s : StarSubalgebra ℂ (H →L[ℂ] H)) [hcl : IsClosed (s : Set (H →L[ℂ] H))]

/-- The scaled vector functional `a ↦ c·⟪ξ, a ξ⟫` on a closed `*`-subalgebra. -/
noncomputable def subVecState {c : ℝ} (hc : 0 ≤ c) (ξ : H) : ↥s →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀
    { toFun := fun a => (c : ℂ) * ⟪ξ, (a : H →L[ℂ] H) ξ⟫_ℂ
      map_add' := fun a b => by
        show (c : ℂ) * ⟪ξ, ((a : H →L[ℂ] H) + b) ξ⟫_ℂ = _
        rw [ContinuousLinearMap.add_apply, inner_add_right, mul_add]
      map_smul' := fun r a => by
        show (c : ℂ) * ⟪ξ, ((r • a : ↥s) : H →L[ℂ] H) ξ⟫_ℂ = r • ((c : ℂ) * _)
        rw [show (((r • a : ↥s) : H →L[ℂ] H)) = r • (a : H →L[ℂ] H) from rfl,
          ContinuousLinearMap.smul_apply, inner_smul_right, smul_eq_mul]
        ring }
    fun a ha => by
      show 0 ≤ (c : ℂ) * ⟪ξ, (a : H →L[ℂ] H) ξ⟫_ℂ
      exact mul_nonneg (Complex.zero_le_real.mpr hc)
        (inner_nonneg_of_nonneg ((coe_nonneg_iff s a).mp ha) ξ)

theorem subVecState_apply {c : ℝ} (hc : 0 ≤ c) (ξ : H) (a : ↥s) :
    subVecState s hc ξ a = (c : ℂ) * ⟪ξ, (a : H →L[ℂ] H) ξ⟫_ℂ := rfl

/-- Bob's functional `a ↦ ⟪ξ, a (B ξ)⟫` for a positive `B` commuting with `s`. -/
noncomputable def subBobState (ξ : H) {B : H →L[ℂ] H} (hB : 0 ≤ B)
    (hcom : ∀ a ∈ s, Commute a B) : ↥s →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀
    { toFun := fun a => ⟪ξ, (a : H →L[ℂ] H) (B ξ)⟫_ℂ
      map_add' := fun a b => by
        show ⟪ξ, ((a : H →L[ℂ] H) + b) (B ξ)⟫_ℂ = _
        rw [ContinuousLinearMap.add_apply, inner_add_right]
      map_smul' := fun r a => by
        show ⟪ξ, ((r • a : ↥s) : H →L[ℂ] H) (B ξ)⟫_ℂ = r • _
        rw [show (((r • a : ↥s) : H →L[ℂ] H)) = r • (a : H →L[ℂ] H) from rfl,
          ContinuousLinearMap.smul_apply, inner_smul_right, smul_eq_mul] }
    fun a ha => by
      show 0 ≤ ⟪ξ, (a : H →L[ℂ] H) (B ξ)⟫_ℂ
      obtain ⟨r, hrmem, hrsa, hrr⟩ :=
        exists_sqrt_mem_of_isClosed s hcl ((coe_nonneg_iff s a).mp ha) a.2
      have hcr : Commute r B := hcom r hrmem
      have key : (a : H →L[ℂ] H) (B ξ) = r (B (r ξ)) := by
        have : (a : H →L[ℂ] H) * B = r * (B * r) := by
          rw [← hrr, mul_assoc, ← hcr.eq, ← mul_assoc]
        have h2 := congrArg (fun T : H →L[ℂ] H => T ξ) this
        simpa only [ContinuousLinearMap.mul_apply] using h2
      have hadj : ContinuousLinearMap.adjoint r = r := by
        rw [← ContinuousLinearMap.star_eq_adjoint]; exact hrsa.star_eq
      rw [key, ← ContinuousLinearMap.adjoint_inner_left, hadj]
      exact inner_nonneg_of_nonneg hB (r ξ)

theorem subBobState_apply (ξ : H) {B : H →L[ℂ] H} (hB : 0 ≤ B)
    (hcom : ∀ a ∈ s, Commute a B) (a : ↥s) :
    subBobState s ξ hB hcom a = ⟪ξ, (a : H →L[ℂ] H) (B ξ)⟫_ℂ := rfl

end States

end Density

end CommutingRepetition
