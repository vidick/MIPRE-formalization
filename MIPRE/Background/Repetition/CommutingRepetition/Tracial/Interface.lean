/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Tracial/Interface.lean
-/
/-
# The tracial standard-form interface (Stage B contract, core layer)

Needs-driven interface per the formalization plan: exactly the facts the
manuscript consumes from "finite von Neumann algebra with faithful normal
normalized trace in standard form", bundled as data. Deliberately NOT
required to be a C*- or von Neumann algebra: the amplifications and tensor
powers of Section 6 must stay inside the interface (plan item 16), and only
the `CStarLayer` mixin (separate file) demands functional calculus.

Anchors: 02_preliminaries.tex "Finite tracial standard form"; audit defs
`tracial_standard_form`, `tracially_embeddable`; consumption inventory
items 1, 10-11, 16 of the plan.
-/
import Mathlib

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped BigOperators InnerProductSpace

universe u

/-- Algebraic positivity: `a` is a finite sum of hermitian squares
`∑ᵢ cᵢ* cᵢ` — the algebraic positive cone of a ∗-ring. In a C*-algebra
this coincides with the usual positive cone (a positive element is a
single square, and a sum of squares is positive); the interface uses the
sums-of-squares cone so that positivity of effects can be *stated* — and
is closed under the POVM coarse-graining of node 1.1.3 — without any
C*-structure. [DIFFERENCES.md D13] -/
def IsPosElem {A : Type*} [AddCommMonoid A] [Mul A] [Star A] (a : A) : Prop :=
  ∃ (k : ℕ) (c : Fin k → A), a = ∑ i, star (c i) * c i

section PosElem

variable {A : Type*} [AddCommMonoid A] [Mul A] [Star A]

/-- A single hermitian square is algebraically positive. -/
theorem isPosElem_star_mul_self (c : A) : IsPosElem (star c * c) :=
  ⟨1, fun _ => c, by simp⟩

theorem isPosElem_zero : IsPosElem (0 : A) :=
  ⟨0, fun i => i.elim0, by simp⟩

/-- The algebraic positive cone is closed under addition. -/
theorem IsPosElem.add {a b : A} (ha : IsPosElem a) (hb : IsPosElem b) :
    IsPosElem (a + b) := by
  obtain ⟨k, c, rfl⟩ := ha
  obtain ⟨l, d, rfl⟩ := hb
  refine ⟨k + l, Fin.append c d, ?_⟩
  rw [Fin.sum_univ_add]
  simp

/-- The algebraic positive cone is closed under finite sums — the fact
POVM coarse-graining needs (node 1.1.3). -/
theorem isPosElem_sum {ι : Type*} (s : Finset ι) (f : ι → A)
    (h : ∀ i ∈ s, IsPosElem (f i)) : IsPosElem (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isPosElem_zero
  | insert j t hj ih =>
    rw [Finset.sum_insert hj]
    exact (h j (Finset.mem_insert_self j t)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end PosElem

/-- The algebraic positive cone is closed under nonnegative real scaling:
`r • (∑ cᵢ* cᵢ) = ∑ (√r cᵢ)* (√r cᵢ)` — the fact convex combinations of
effects need (05_prerounding.tex, eq effective-HK: "finite convex
combinations of positive contractions in `M`"). -/
theorem IsPosElem.smul_ofReal {A : Type*} [AddCommMonoid A] [Mul A]
    [Star A] [Module ℂ A] [SMulCommClass ℂ A A] [IsScalarTower ℂ A A]
    [StarModule ℂ A] {x : A} (hx : IsPosElem x) {r : ℝ} (hr : 0 ≤ r) :
    IsPosElem ((r : ℂ) • x) := by
  obtain ⟨k, c, rfl⟩ := hx
  refine ⟨k, fun i => ((Real.sqrt r : ℂ)) • c i, ?_⟩
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Real.mul_self_sqrt hr]

/-- Standard form of a tracial ∗-algebra: carrier `A` with a normalized
trace `τ`, the GNS Hilbert space `H = L²(A, τ)` with dense embedding `ι`,
commuting left and right actions `L`, `R`, and the evaluation identities.
[02_preliminaries.tex, "Finite tracial standard form"] -/
structure StdTracialAlgebra : Type (u + 1) where
  A : Type u
  [ringA : Ring A]
  [starRingA : StarRing A]
  [algebraA : Algebra ℂ A]
  [starModuleA : StarModule ℂ A]
  τ : A →ₗ[ℂ] ℂ
  τ_one : τ 1 = 1
  τ_mul_comm : ∀ a b : A, τ (a * b) = τ (b * a)
  τ_star : ∀ a : A, τ (star a) = star (τ a)
  H : Type u
  [nacgH : NormedAddCommGroup H]
  [ipsH : InnerProductSpace ℂ H]
  [completeH : CompleteSpace H]
  ι : A →ₗ[ℂ] H
  ι_dense : DenseRange ι
  ι_inner : ∀ a b : A, ⟪ι a, ι b⟫_ℂ = τ (star a * b)
  L : A →⋆ₐ[ℂ] (H →L[ℂ] H)
  R : Aᵐᵒᵖ →⋆ₐ[ℂ] (H →L[ℂ] H)
  L_apply : ∀ a b : A, L a (ι b) = ι (a * b)
  R_apply : ∀ a b : A, R (MulOpposite.op a) (ι b) = ι (b * a)
  LR_commute : ∀ a b : A, Commute (L a) (R (MulOpposite.op b))

namespace StdTracialAlgebra

variable (M : StdTracialAlgebra.{u})

attribute [instance] ringA starRingA algebraA starModuleA nacgH ipsH completeH

/-- The trace vector `Ω_τ = ι 1`. -/
noncomputable def traceVector : M.H := M.ι 1

/-- Right action on an element written without the opposite wrapper. -/
noncomputable def Rop (a : M.A) : M.H →L[ℂ] M.H := M.R (MulOpposite.op a)

/-- The evaluation identity behind everything in Sections 3–7:
`⟪ι σ', L(x) R(y) ι σ⟫ = τ((σ')* x σ y)`.
Specializes to the correlation formula
`⟪σ, L(E) R(F) σ⟫ = τ(σ* E σ F)` (03_tracial_reduction.tex, eq
tracial-correlation-formula; audit node 1.1.4). -/
theorem inner_L_R (σ' x σ y : M.A) :
    ⟪M.ι σ', M.L x (M.Rop y (M.ι σ))⟫_ℂ = M.τ (star σ' * (x * σ * y)) := by
  rw [Rop, M.R_apply, M.L_apply, M.ι_inner]
  simp [mul_assoc]

/-- τ is positive: `τ(a* a) = ‖ι a‖²` is a nonnegative real. -/
theorem τ_star_self_nonneg (a : M.A) :
    0 ≤ (M.τ (star a * a)).re ∧ (M.τ (star a * a)).im = 0 := by
  rw [← M.ι_inner a a]
  constructor
  · exact inner_self_nonneg (𝕜 := ℂ) (x := M.ι a)
  · exact inner_self_im (𝕜 := ℂ) (M.ι a)

/-- The left action of an algebraically positive element is a positive
operator: `L(∑ cᵢ* cᵢ) = ∑ L(cᵢ)† ∘ L(cᵢ)`. -/
theorem L_isPositive {a : M.A} (ha : IsPosElem a) :
    (M.L a).IsPositive := by
  obtain ⟨k, c, rfl⟩ := ha
  rw [map_sum]
  refine Finset.sum_induction _ ContinuousLinearMap.IsPositive
    (fun _ _ ha hb => ha.add hb) ContinuousLinearMap.isPositive_zero
    fun i _ => ?_
  have h : M.L (star (c i) * c i) =
      (ContinuousLinearMap.adjoint (M.L (c i))).comp (M.L (c i)) := by
    rw [map_mul, map_star, ContinuousLinearMap.star_eq_adjoint]
    rfl
  rw [h]
  exact ContinuousLinearMap.isPositive_adjoint_comp_self (M.L (c i))

/-- The right action of an algebraically positive element is a positive
operator: `R(op(∑ cᵢ* cᵢ)) = ∑ R(op cᵢ) ∘ R(op cᵢ)†`. -/
theorem Rop_isPositive {a : M.A} (ha : IsPosElem a) :
    (M.Rop a).IsPositive := by
  obtain ⟨k, c, rfl⟩ := ha
  have hsum : M.Rop (∑ i, star (c i) * c i)
      = ∑ i, M.Rop (star (c i) * c i) := by
    unfold Rop
    rw [Finset.op_sum, map_sum]
  rw [hsum]
  refine Finset.sum_induction _ ContinuousLinearMap.IsPositive
    (fun _ _ ha hb => ha.add hb) ContinuousLinearMap.isPositive_zero
    fun i _ => ?_
  have h : M.Rop (star (c i) * c i) = (M.R (MulOpposite.op (c i))).comp
      (ContinuousLinearMap.adjoint (M.R (MulOpposite.op (c i)))) := by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star,
      ← MulOpposite.op_star]
    calc M.Rop (star (c i) * c i)
        = M.R (MulOpposite.op (c i) * MulOpposite.op (star (c i))) := by
          rw [Rop, MulOpposite.op_mul]
      _ = M.R (MulOpposite.op (c i)) * M.R (MulOpposite.op (star (c i))) :=
          map_mul _ _ _
      _ = (M.R (MulOpposite.op (c i))).comp
            (M.R (MulOpposite.op (star (c i)))) :=
          rfl
  rw [h]
  exact ContinuousLinearMap.isPositive_self_comp_adjoint
    (M.R (MulOpposite.op (c i)))

/-- Positivity of the two-sided pairing: for algebraically positive
`u, w` and any `σ`, `τ(σ* u σ w) = ⟪ι σ, L(u) R(w) ι σ⟫ ≥ 0` — the
commuting product of the positive operators `L(u)` and `R(w)` applied to
the state `ι σ` (the Born-rule nonnegativity behind eq
tracial-correlation-formula and the detagging inequality of node
1.1.3). -/
theorem pairing_nonneg (σ : M.A) {u w : M.A}
    (hu : IsPosElem u) (hw : IsPosElem w) :
    0 ≤ (M.τ (star σ * (u * σ * w))).re := by
  have hL : (0 : M.H →L[ℂ] M.H) ≤ M.L u := by
    rw [ContinuousLinearMap.le_def]
    simpa using M.L_isPositive hu
  have hR : (0 : M.H →L[ℂ] M.H) ≤ M.Rop w := by
    rw [ContinuousLinearMap.le_def]
    simpa using M.Rop_isPositive hw
  have hmul := Commute.mul_nonneg hL hR (M.LR_commute u w)
  rw [ContinuousLinearMap.le_def] at hmul
  simp only [sub_zero] at hmul
  have h := hmul.2 (M.ι σ)
  rw [← M.inner_L_R σ u σ w, ← RCLike.re_to_complex, inner_re_symm]
  exact h

end StdTracialAlgebra

end CommutingRepetition
