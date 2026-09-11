/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/Modular/Centralizer.lean
-/
/-
# The centralizer is tracial (density stage E4.4)

For `x ∈ M` commuting with `R` (equivalently with every bounded Borel function of
`R`, in particular fixed by the modular group `σ_t`), the vector state
`ψ = ⟪Ω, · Ω⟫` satisfies `ψ(x y) = ψ(y x)` for every `y ∈ M` (HJX (M2)).

The proof uses only the bounded identity `T J (xΩ) = (2 − R)(x*Ω)` of RvD
Lemma 4.5: for `x, y ∈ M`,
`⟪(2−R) xΩ, (2−R) y*Ω⟫ = ⟪T J x*Ω, T J yΩ⟫ = ⟪T² yΩ, x*Ω⟫ = ⟪R(2−R) yΩ, x*Ω⟫`,
and when `x` commutes with `R` both sides collapse (`(2−R)Ω = Ω`, `R(2−R)Ω = Ω`)
to `⟪xΩ, y*Ω⟫ = ⟪yΩ, x*Ω⟫`.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.Modular.Tomita

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace VN

namespace Modular

open scoped InnerProductSpace ComplexConjugate
open BorelCalc

set_option linter.unusedSectionVars false

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (M : VonNeumannAlgebra K) (Ω : K)

theorem two_apply_eq (ξ : K) : (2 : K →L[ℂ] K) ξ = ξ + ξ := by
  rw [show (2 : K →L[ℂ] K) = 1 + 1 from one_add_one_eq_two.symm, _root_.add_apply,
    one_apply_eq_self]

theorem two_sub_R_Ω : (2 - R M Ω) Ω = Ω := by
  rw [_root_.sub_apply, R_Ω, two_apply_eq]; abel

theorem R_mul_two_sub_R_Ω : (R M Ω * (2 - R M Ω)) Ω = Ω := by
  rw [mul_apply_eq_comp, two_sub_R_Ω, R_Ω]

theorem R_mul_two_sub_R_isSelfAdjoint : IsSelfAdjoint (R M Ω * (2 - R M Ω)) := by
  rw [← Tm_mul_Tm]
  show star (Tm M Ω * Tm M Ω) = Tm M Ω * Tm M Ω
  rw [star_mul, (Tm_isSelfAdjoint M Ω).star_eq]

/-- An operator commuting with `R` commutes with `2 − R`. -/
theorem commute_two_sub_R_of_commute_R {x : K →L[ℂ] K} (h : Commute x (R M Ω)) :
    Commute x (2 - R M Ω) :=
  Commute.sub_right (Commute.ofNat_right x 2) h

variable (hs : IsSeparating (M : Set (K →L[ℂ] K)) Ω) (hc : IsCyclic (M : Set (K →L[ℂ] K)) Ω)

include hs hc in
/-- The bounded KMS-type identity: `⟪(2−R) xΩ, (2−R) y*Ω⟫ = ⟪R(2−R) yΩ, x*Ω⟫` for `x, y ∈ M`. -/
theorem inner_two_sub_R_apply {x y : K →L[ℂ] K} (hx : x ∈ M) (hy : y ∈ M) :
    ⟪(2 - R M Ω) (x Ω), (2 - R M Ω) (star y Ω)⟫_ℂ =
      ⟪(R M Ω * (2 - R M Ω)) (y Ω), star x Ω⟫_ℂ := by
  have h1 : (2 - R M Ω) (x Ω) = Tm M Ω (Jm M Ω (star x Ω)) := by
    rw [Tm_Jm_apply_mem M Ω hs hc (star_mem hx), star_star]
  have h2 : (2 - R M Ω) (star y Ω) = Tm M Ω (Jm M Ω (y Ω)) :=
    (Tm_Jm_apply_mem M Ω hs hc hy).symm
  rw [h1, h2, ← inner_sa (Tm_isSelfAdjoint M Ω), ← Jm_Tm_comm M Ω hs hc,
    ← Jm_Tm_comm M Ω hs hc, inner_Jm_left M Ω hs hc, Jm_Jm M Ω hs hc, ← mul_apply_eq_comp,
    Tm_mul_Tm]

include hs hc in
/-- **(M2)**: an element of `M` commuting with `R` is `ψ`-central: `ψ(x y) = ψ(y x)`. -/
theorem inner_Ω_mul_comm {x y : K →L[ℂ] K} (hx : x ∈ M) (hxR : Commute x (R M Ω)) (hy : y ∈ M) :
    ⟪Ω, (x * y) Ω⟫_ℂ = ⟪Ω, (y * x) Ω⟫_ℂ := by
  have hxR' : Commute (star x) (R M Ω) := by
    have := hxR.star_star
    rwa [(R_isSelfAdjoint M Ω).star_eq] at this
  have hx2 : Commute (star x) (2 - R M Ω) := commute_two_sub_R_of_commute_R M Ω hxR'
  have hxRR : Commute x (R M Ω * (2 - R M Ω)) :=
    hxR.mul_right (commute_two_sub_R_of_commute_R M Ω hxR)
  have key := inner_two_sub_R_apply M Ω hs hc (star_mem hx) (star_mem hy)
  rw [star_star, star_star] at key
  have hL : (2 - R M Ω) (star x Ω) = star x Ω := by
    rw [← mul_apply_eq_comp, ← hx2.eq, mul_apply_eq_comp, two_sub_R_Ω]
  have hR : (R M Ω * (2 - R M Ω)) (x Ω) = x Ω := by
    rw [← mul_apply_eq_comp, ← hxRR.eq, mul_apply_eq_comp, R_mul_two_sub_R_Ω]
  rw [inner_sa (two_sub_R_isSelfAdjoint M Ω), hL, hL,
    ← inner_sa (R_mul_two_sub_R_isSelfAdjoint M Ω), hR] at key
  rw [mul_apply_eq_comp, mul_apply_eq_comp, ← ContinuousLinearMap.adjoint_inner_left x (y Ω) Ω,
    ← ContinuousLinearMap.adjoint_inner_left y (x Ω) Ω, ← ContinuousLinearMap.star_eq_adjoint,
    ← ContinuousLinearMap.star_eq_adjoint]
  exact key

/-! ## The centralizer -/

/-- The centralizer of `ψ`: elements of `M` commuting with `R` (hence with every bounded Borel
function of `R`; in particular fixed by the modular group). -/
def IsCentral (x : K →L[ℂ] K) : Prop := x ∈ M ∧ Commute x (R M Ω)

namespace IsCentral

variable {M Ω}

theorem mem {x : K →L[ℂ] K} (h : IsCentral M Ω x) : x ∈ M := h.1

theorem commute_R {x : K →L[ℂ] K} (h : IsCentral M Ω x) : Commute x (R M Ω) := h.2

theorem σ_eq {x : K →L[ℂ] K} (h : IsCentral M Ω x) (t : ℝ) : σ M Ω t x = x :=
  σ_eq_self_of_commute_R M Ω h.2 t

theorem one : IsCentral M Ω (1 : K →L[ℂ] K) := ⟨one_mem _, Commute.one_left _⟩

theorem star {x : K →L[ℂ] K} (h : IsCentral M Ω x) : IsCentral M Ω (star x) := by
  refine ⟨star_mem h.1, ?_⟩
  have := h.2.star_star
  rwa [(R_isSelfAdjoint M Ω).star_eq] at this

theorem mul {x y : K →L[ℂ] K} (hx : IsCentral M Ω x) (hy : IsCentral M Ω y) :
    IsCentral M Ω (x * y) := ⟨mul_mem hx.1 hy.1, hx.2.mul_left hy.2⟩

theorem add {x y : K →L[ℂ] K} (hx : IsCentral M Ω x) (hy : IsCentral M Ω y) :
    IsCentral M Ω (x + y) := ⟨add_mem hx.1 hy.1, hx.2.add_left hy.2⟩

theorem smul (c : ℂ) {x : K →L[ℂ] K} (hx : IsCentral M Ω x) : IsCentral M Ω (c • x) :=
  ⟨VN.smul_mem_vn M c hx.1, hx.2.smul_left c⟩

/-- Real continuous functions of a central element are central. -/
theorem cfc_real {x : K →L[ℂ] K} (hx : IsCentral M Ω x) (f : ℝ → ℝ) :
    IsCentral M Ω (cfc f x) :=
  ⟨VN.cfc_real_mem M hx.1 f, hx.2.cfc_real f⟩

/-- **(M2)**: `ψ(x y) = ψ(y x)` for central `x` and all `y ∈ M`. -/
theorem tracial (hs : IsSeparating (M : Set (K →L[ℂ] K)) Ω)
    (hc : IsCyclic (M : Set (K →L[ℂ] K)) Ω) {x y : K →L[ℂ] K} (hx : IsCentral M Ω x)
    (hy : y ∈ M) : ⟪Ω, (x * y) Ω⟫_ℂ = ⟪Ω, (y * x) Ω⟫_ℂ :=
  inner_Ω_mul_comm M Ω hs hc hx.1 hx.2 hy

end IsCentral

end Modular

end VN

end CommutingRepetition
