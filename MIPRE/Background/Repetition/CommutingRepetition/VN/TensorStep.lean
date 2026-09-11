/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/TensorStep.lean
-/
/-
# Binary tensor product of standard tracial algebras (Stage B, WP-B3b)

For standard tracial algebras `M₁, M₂`, the algebraic tensor product
`M₁.A ⊗[ℂ] M₂.A` with the product trace `τ(a ⊗ b) = τ₁(a) τ₂(b)` is
again a standard tracial algebra: its GNS space is the completion of
the inner-product tensor product `M₁.H ⊗[ℂ] M₂.H` (Mathlib's
`TensorProduct.instInnerProductSpace`, with
`⟪x ⊗ y, x' ⊗ y'⟫ = ⟪x, x'⟫ ⟪y, y'⟫`), the embedding is
`ι₁ ⊗ ι₂` followed by the coercion into the completion, and the left
and right representations act factorwise through `TensorProduct.mapL`
extended to the completion.

Infrastructure for the tensor-power interface of Section 6
(`TensorPowerData`, OTQCS/Compile.lean, eq amplified-resource): the
`R`-fold power is the iterated binary step, with the factor
∗-embeddings built from `includeLeft`/`includeRight`.

No manuscript anchor of its own (like VN/Amplify.lean).
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Tracial.Interface

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace StdTracialAlgebra

open scoped TensorProduct InnerProductSpace

universe u

variable (M₁ M₂ : StdTracialAlgebra.{u})

/-! ### The product trace -/

/-- The product trace `τ(a ⊗ b) = τ₁(a) τ₂(b)` on the algebraic tensor
product. -/
noncomputable def stepτ : (M₁.A ⊗[ℂ] M₂.A) →ₗ[ℂ] ℂ :=
  (TensorProduct.lid ℂ ℂ).toLinearMap ∘ₗ TensorProduct.map M₁.τ M₂.τ

@[simp] theorem stepτ_tmul (a : M₁.A) (b : M₂.A) :
    stepτ M₁ M₂ (a ⊗ₜ b) = M₁.τ a * M₂.τ b := by
  simp [stepτ, TensorProduct.lid_tmul, smul_eq_mul]

theorem stepτ_one : stepτ M₁ M₂ 1 = 1 := by
  rw [Algebra.TensorProduct.one_def, stepτ_tmul, M₁.τ_one, M₂.τ_one,
    one_mul]

theorem stepτ_mul_comm (x y : M₁.A ⊗[ℂ] M₂.A) :
    stepτ M₁ M₂ (x * y) = stepτ M₁ M₂ (y * x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul c d =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, stepτ_tmul]
      rw [M₁.τ_mul_comm a c, M₂.τ_mul_comm b d]
    | add y₁ y₂ h₁ h₂ =>
      rw [mul_add, add_mul, map_add, map_add, h₁, h₂]
  | add x₁ x₂ h₁ h₂ =>
    rw [add_mul, mul_add, map_add, map_add, h₁, h₂]

theorem stepτ_star (x : M₁.A ⊗[ℂ] M₂.A) :
    stepτ M₁ M₂ (star x) = star (stepτ M₁ M₂ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [TensorProduct.star_tmul, stepτ_tmul, stepτ_tmul, M₁.τ_star,
      M₂.τ_star, star_mul']
  | add x₁ x₂ h₁ h₂ => rw [star_add, map_add, map_add, h₁, h₂, star_add]

/-! ### The GNS space -/

/-- The GNS space of the product trace: the completion of the
inner-product tensor product of the two GNS spaces. -/
abbrev StepH := UniformSpace.Completion (M₁.H ⊗[ℂ] M₂.H)

/-- The GNS embedding: `ι₁ ⊗ ι₂` into the completion. -/
noncomputable def stepι : (M₁.A ⊗[ℂ] M₂.A) →ₗ[ℂ] StepH M₁ M₂ :=
  (UniformSpace.Completion.toComplₗᵢ (E := M₁.H ⊗[ℂ] M₂.H)).toLinearMap
    ∘ₗ TensorProduct.map M₁.ι M₂.ι

@[simp] theorem stepι_tmul (a : M₁.A) (b : M₂.A) :
    stepι M₁ M₂ (a ⊗ₜ b) = ((M₁.ι a ⊗ₜ M₂.ι b : M₁.H ⊗[ℂ] M₂.H) :
      StepH M₁ M₂) := rfl

theorem stepι_inner (x y : M₁.A ⊗[ℂ] M₂.A) :
    ⟪stepι M₁ M₂ x, stepι M₁ M₂ y⟫_ℂ = stepτ M₁ M₂ (star x * y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul c d =>
      rw [stepι_tmul, stepι_tmul, UniformSpace.Completion.inner_coe,
        TensorProduct.inner_tmul, M₁.ι_inner, M₂.ι_inner,
        TensorProduct.star_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        stepτ_tmul]
    | add y₁ y₂ h₁ h₂ =>
      rw [map_add, inner_add_right, h₁, h₂, mul_add, map_add]
  | add x₁ x₂ h₁ h₂ =>
    rw [map_add, inner_add_left, h₁, h₂, star_add, add_mul, map_add]

/-- Density of the algebraic image inside the tensor product (before
completion): the range of `ι₁ ⊗ ι₂` is dense in `H₁ ⊗ H₂`. Two-slot
closed-preimage argument: for fixed `a`, the set of `y` with
`ι₁ a ⊗ y` in the closure is closed and contains the dense range of
`ι₂`; then the set of `x` with `x ⊗ y` in the closure is closed and
contains the dense range of `ι₁`; conclude on pure tensors and extend
by the submodule structure of the closure. -/
theorem denseRange_map_ι :
    DenseRange (TensorProduct.map M₁.ι M₂.ι) := by
  set K : Set (M₁.H ⊗[ℂ] M₂.H) :=
    closure (Set.range (TensorProduct.map M₁.ι M₂.ι)) with hK
  have hKclosed : IsClosed K := isClosed_closure
  -- Step 1: `ι₁ a ⊗ y ∈ K` for every `a` and every `y`.
  have step1 : ∀ (a : M₁.A) (y : M₂.H),
      ((M₁.ι a) ⊗ₜ[ℂ] y : M₁.H ⊗[ℂ] M₂.H) ∈ K := by
    intro a y
    have hcont : Continuous fun w : M₂.H =>
        ((M₁.ι a) ⊗ₜ[ℂ] w : M₁.H ⊗[ℂ] M₂.H) :=
      (TensorProduct.mkL ℂ M₁.H M₂.H (M₁.ι a)).continuous
    have hclosed : IsClosed {w : M₂.H |
        ((M₁.ι a) ⊗ₜ[ℂ] w : M₁.H ⊗[ℂ] M₂.H) ∈ K} :=
      hKclosed.preimage hcont
    have hsub : Set.range M₂.ι ⊆ {w : M₂.H |
        ((M₁.ι a) ⊗ₜ[ℂ] w : M₁.H ⊗[ℂ] M₂.H) ∈ K} := by
      rintro _ ⟨b, rfl⟩
      exact subset_closure ⟨a ⊗ₜ b, by simp⟩
    have : (Set.univ : Set M₂.H) ⊆ {w : M₂.H |
        ((M₁.ι a) ⊗ₜ[ℂ] w : M₁.H ⊗[ℂ] M₂.H) ∈ K} := by
      rw [← M₂.ι_dense.closure_range]
      calc closure (Set.range M₂.ι) ⊆ closure {w : M₂.H |
            ((M₁.ι a) ⊗ₜ[ℂ] w : M₁.H ⊗[ℂ] M₂.H) ∈ K} :=
          closure_mono hsub
        _ = _ := hclosed.closure_eq
    exact this (Set.mem_univ y)
  -- Step 2: `x ⊗ y ∈ K` for every `x` and `y`.
  have step2 : ∀ (x : M₁.H) (y : M₂.H),
      (x ⊗ₜ[ℂ] y : M₁.H ⊗[ℂ] M₂.H) ∈ K := by
    intro x y
    have hcont : Continuous fun w : M₁.H =>
        (w ⊗ₜ[ℂ] y : M₁.H ⊗[ℂ] M₂.H) :=
      ((TensorProduct.mkL ℂ M₁.H M₂.H).flip y).continuous
    have hclosed : IsClosed {w : M₁.H |
        (w ⊗ₜ[ℂ] y : M₁.H ⊗[ℂ] M₂.H) ∈ K} := hKclosed.preimage hcont
    have hsub : Set.range M₁.ι ⊆ {w : M₁.H |
        (w ⊗ₜ[ℂ] y : M₁.H ⊗[ℂ] M₂.H) ∈ K} := by
      rintro _ ⟨a, rfl⟩
      exact step1 a y
    have : (Set.univ : Set M₁.H) ⊆ {w : M₁.H |
        (w ⊗ₜ[ℂ] y : M₁.H ⊗[ℂ] M₂.H) ∈ K} := by
      rw [← M₁.ι_dense.closure_range]
      calc closure (Set.range M₁.ι) ⊆ closure {w : M₁.H |
            (w ⊗ₜ[ℂ] y : M₁.H ⊗[ℂ] M₂.H) ∈ K} := closure_mono hsub
        _ = _ := hclosed.closure_eq
    exact this (Set.mem_univ x)
  -- Conclude: the closure of the range submodule is everything.
  have htop : (LinearMap.range
      (TensorProduct.map M₁.ι M₂.ι)).topologicalClosure = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | tmul x y =>
      have hmem : (x ⊗ₜ[ℂ] y : M₁.H ⊗[ℂ] M₂.H) ∈
          ((LinearMap.range
            (TensorProduct.map M₁.ι M₂.ι)).topologicalClosure :
              Set (M₁.H ⊗[ℂ] M₂.H)) := by
        rw [Submodule.topologicalClosure_coe, LinearMap.coe_range]
        exact step2 x y
      exact hmem
    | add z₁ z₂ h₁ h₂ => exact add_mem h₁ h₂
  have hdense := Submodule.dense_iff_topologicalClosure_eq_top.mpr htop
  rw [LinearMap.coe_range] at hdense
  exact hdense

/-- The GNS embedding has dense range (density in the algebraic tensor
product composed with density of the completion coercion). -/
theorem stepι_dense : DenseRange (stepι M₁ M₂) := by
  have h1 : DenseRange ((↑) : (M₁.H ⊗[ℂ] M₂.H) → StepH M₁ M₂) :=
    UniformSpace.Completion.denseRange_coe
  have h2 := denseRange_map_ι M₁ M₂
  exact h1.comp h2 (UniformSpace.Completion.continuous_coe _)

/-! ### Extending operators to the completion -/

/-- The completion coercion as a continuous linear map. -/
noncomputable def toStepH : (M₁.H ⊗[ℂ] M₂.H) →L[ℂ] StepH M₁ M₂ :=
  (UniformSpace.Completion.toComplₗᵢ
    (E := M₁.H ⊗[ℂ] M₂.H)).toContinuousLinearMap

@[simp] theorem toStepH_apply (w : M₁.H ⊗[ℂ] M₂.H) :
    toStepH M₁ M₂ w = (w : StepH M₁ M₂) := rfl

theorem denseRange_toStepH : DenseRange (toStepH M₁ M₂) :=
  UniformSpace.Completion.denseRange_coe

theorem isUniformInducing_toStepH : IsUniformInducing (toStepH M₁ M₂) :=
  (UniformSpace.Completion.toComplₗᵢ
    (E := M₁.H ⊗[ℂ] M₂.H)).isometry.isUniformInducing

/-- The unique bounded extension of an operator on the algebraic
tensor product to the completed GNS space. -/
noncomputable def extendStep
    (T : (M₁.H ⊗[ℂ] M₂.H) →L[ℂ] (M₁.H ⊗[ℂ] M₂.H)) :
    StepH M₁ M₂ →L[ℂ] StepH M₁ M₂ :=
  ((toStepH M₁ M₂).comp T).extend (toStepH M₁ M₂)

theorem extendStep_coe (T : (M₁.H ⊗[ℂ] M₂.H) →L[ℂ] (M₁.H ⊗[ℂ] M₂.H))
    (w : M₁.H ⊗[ℂ] M₂.H) :
    extendStep M₁ M₂ T (w : StepH M₁ M₂) = ((T w : M₁.H ⊗[ℂ] M₂.H) :
      StepH M₁ M₂) := by
  have h := ContinuousLinearMap.extend_eq ((toStepH M₁ M₂).comp T)
    (denseRange_toStepH M₁ M₂) (isUniformInducing_toStepH M₁ M₂) w
  unfold extendStep
  simpa using h

/-- Two operators on the completion agreeing on coercions are equal. -/
theorem ext_of_coe {P Q : StepH M₁ M₂ →L[ℂ] StepH M₁ M₂}
    (h : ∀ w : M₁.H ⊗[ℂ] M₂.H,
      P (w : StepH M₁ M₂) = Q (w : StepH M₁ M₂)) : P = Q := by
  apply ContinuousLinearMap.coeFn_injective
  exact (denseRange_toStepH M₁ M₂).equalizer P.continuous Q.continuous
    (funext h)

theorem extendStep_id :
    extendStep M₁ M₂ (ContinuousLinearMap.id ℂ (M₁.H ⊗[ℂ] M₂.H)) =
      ContinuousLinearMap.id ℂ (StepH M₁ M₂) :=
  ext_of_coe M₁ M₂ fun w => by
    rw [extendStep_coe]; rfl

theorem extendStep_comp
    (S T : (M₁.H ⊗[ℂ] M₂.H) →L[ℂ] (M₁.H ⊗[ℂ] M₂.H)) :
    extendStep M₁ M₂ (S.comp T) =
      (extendStep M₁ M₂ S).comp (extendStep M₁ M₂ T) :=
  ext_of_coe M₁ M₂ fun w => by
    rw [ContinuousLinearMap.comp_apply, extendStep_coe, extendStep_coe,
      extendStep_coe, ContinuousLinearMap.comp_apply]

theorem extendStep_add
    (S T : (M₁.H ⊗[ℂ] M₂.H) →L[ℂ] (M₁.H ⊗[ℂ] M₂.H)) :
    extendStep M₁ M₂ (S + T) = extendStep M₁ M₂ S + extendStep M₁ M₂ T :=
  ext_of_coe M₁ M₂ fun w => by
    simp only [extendStep_coe, ContinuousLinearMap.add_apply]
    exact UniformSpace.Completion.coe_add _ _

theorem extendStep_smul (c : ℂ)
    (T : (M₁.H ⊗[ℂ] M₂.H) →L[ℂ] (M₁.H ⊗[ℂ] M₂.H)) :
    extendStep M₁ M₂ (c • T) = c • extendStep M₁ M₂ T :=
  ext_of_coe M₁ M₂ fun w => by
    simp only [extendStep_coe, ContinuousLinearMap.smul_apply]
    exact UniformSpace.Completion.coe_smul _ _

theorem extendStep_zero :
    extendStep M₁ M₂ 0 = 0 :=
  ext_of_coe M₁ M₂ fun w => by
    simp only [extendStep_coe, ContinuousLinearMap.zero_apply]
    exact UniformSpace.Completion.coe_zero

/-- Adjoint duality for factorwise operators on the algebraic tensor
product: `⟪(S* ⊗ T*) w, w'⟫ = ⟪w, (S ⊗ T) w'⟫`. -/
theorem inner_mapL_star (S : M₁.H →L[ℂ] M₁.H) (T : M₂.H →L[ℂ] M₂.H)
    (w w' : M₁.H ⊗[ℂ] M₂.H) :
    ⟪TensorProduct.mapL (star S) (star T) w, w'⟫_ℂ =
      ⟪w, TensorProduct.mapL S T w'⟫_ℂ := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    induction w' using TensorProduct.induction_on with
    | zero => simp
    | tmul x' y' =>
      rw [TensorProduct.mapL_tmul, TensorProduct.mapL_tmul,
        TensorProduct.inner_tmul, TensorProduct.inner_tmul,
        ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.adjoint_inner_left]
    | add z₁ z₂ h₁ h₂ =>
      rw [map_add, inner_add_right, inner_add_right, h₁, h₂]
  | add z₁ z₂ h₁ h₂ =>
    rw [map_add, inner_add_left, inner_add_left, h₁, h₂]

/-- Adjoint compatibility of the extension, from inner-product duality
of the unextended operators: if `⟪P w, w'⟫ = ⟪w, Q w'⟫` on the
algebraic tensor product then the extension of `P` is the adjoint of
the extension of `Q`. -/
theorem extendStep_star_of_inner
    {P Q : (M₁.H ⊗[ℂ] M₂.H) →L[ℂ] (M₁.H ⊗[ℂ] M₂.H)}
    (hPQ : ∀ w w' : M₁.H ⊗[ℂ] M₂.H, ⟪P w, w'⟫_ℂ = ⟪w, Q w'⟫_ℂ) :
    extendStep M₁ M₂ P = star (extendStep M₁ M₂ Q) := by
  conv_rhs => rw [ContinuousLinearMap.star_eq_adjoint]
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro v w
  -- two-slot density: check on coercions, extend by continuity
  have hcore : ∀ (u u' : M₁.H ⊗[ℂ] M₂.H),
      ⟪extendStep M₁ M₂ P
          (u : StepH M₁ M₂), (u' : StepH M₁ M₂)⟫_ℂ =
        ⟪(u : StepH M₁ M₂),
          extendStep M₁ M₂ Q
            (u' : StepH M₁ M₂)⟫_ℂ := by
    intro u u'
    rw [extendStep_coe, extendStep_coe,
      UniformSpace.Completion.inner_coe,
      UniformSpace.Completion.inner_coe]
    exact hPQ u u'
  have hstep1 : ∀ (u' : M₁.H ⊗[ℂ] M₂.H) (v : StepH M₁ M₂),
      ⟪extendStep M₁ M₂ P v,
          (u' : StepH M₁ M₂)⟫_ℂ =
        ⟪v, extendStep M₁ M₂ Q
          (u' : StepH M₁ M₂)⟫_ℂ := by
    intro u' v
    have hclosed : IsClosed {v : StepH M₁ M₂ |
        ⟪extendStep M₁ M₂ P v,
            (u' : StepH M₁ M₂)⟫_ℂ =
          ⟪v, extendStep M₁ M₂ Q
            (u' : StepH M₁ M₂)⟫_ℂ} := by
      apply isClosed_eq
      · exact Continuous.inner ((extendStep M₁ M₂ P).continuous)
          continuous_const
      · exact Continuous.inner continuous_id continuous_const
    have hsub : Set.range ((↑) : (M₁.H ⊗[ℂ] M₂.H) → StepH M₁ M₂) ⊆
        {v : StepH M₁ M₂ |
          ⟪extendStep M₁ M₂ P v,
              (u' : StepH M₁ M₂)⟫_ℂ =
            ⟪v, extendStep M₁ M₂ Q
              (u' : StepH M₁ M₂)⟫_ℂ} := by
      rintro _ ⟨u, rfl⟩
      exact hcore u u'
    have hv : v ∈ closure
        (Set.range ((↑) : (M₁.H ⊗[ℂ] M₂.H) → StepH M₁ M₂)) := by
      rw [(UniformSpace.Completion.denseRange_coe
        (α := M₁.H ⊗[ℂ] M₂.H)).closure_range]
      trivial
    exact closure_minimal hsub hclosed hv
  have hclosed2 : IsClosed {w : StepH M₁ M₂ |
      ⟪extendStep M₁ M₂ P v,
          w⟫_ℂ =
        ⟪v, extendStep M₁ M₂ Q w⟫_ℂ} := by
    apply isClosed_eq
    · exact Continuous.inner continuous_const continuous_id
    · exact Continuous.inner continuous_const
        ((extendStep M₁ M₂ Q).continuous)
  have hsub2 : Set.range ((↑) : (M₁.H ⊗[ℂ] M₂.H) → StepH M₁ M₂) ⊆
      {w : StepH M₁ M₂ |
        ⟪extendStep M₁ M₂ P v,
            w⟫_ℂ =
          ⟪v, extendStep M₁ M₂ Q w⟫_ℂ} := by
    rintro _ ⟨u', rfl⟩
    exact hstep1 u' v
  have hw : w ∈ closure
      (Set.range ((↑) : (M₁.H ⊗[ℂ] M₂.H) → StepH M₁ M₂)) := by
    rw [(UniformSpace.Completion.denseRange_coe
      (α := M₁.H ⊗[ℂ] M₂.H)).closure_range]
    trivial
  exact closure_minimal hsub2 hclosed2 hw


/-! ### The factorwise representation -/

theorem extendStep_one :
    extendStep M₁ M₂ 1 = 1 :=
  extendStep_id M₁ M₂

section TensorRep

variable {A₁ : Type*} [Ring A₁] [StarRing A₁] [Algebra ℂ A₁]
  [StarModule ℂ A₁]
variable {A₂ : Type*} [Ring A₂] [StarRing A₂] [Algebra ℂ A₂]
  [StarModule ℂ A₂]
variable (φ₁ : A₁ →⋆ₐ[ℂ] (M₁.H →L[ℂ] M₁.H))
variable (φ₂ : A₂ →⋆ₐ[ℂ] (M₂.H →L[ℂ] M₂.H))

/-- The factorwise action on the algebraic tensor product:
`a ⊗ b ↦ φ₁(a) ⊗ φ₂(b)` as a bounded operator. -/
noncomputable def tensorRep0 : (A₁ ⊗[ℂ] A₂) →ₗ[ℂ]
    ((M₁.H ⊗[ℂ] M₂.H) →L[ℂ] (M₁.H ⊗[ℂ] M₂.H)) :=
  TensorProduct.lift (LinearMap.mk₂ ℂ
    (fun a b => TensorProduct.mapL (φ₁ a) (φ₂ b))
    (fun a a' b => by rw [map_add, TensorProduct.mapL_add_left])
    (fun c a b => by rw [map_smul, TensorProduct.mapL_smul_left])
    (fun a b b' => by rw [map_add, TensorProduct.mapL_add_right])
    (fun c a b => by rw [map_smul, TensorProduct.mapL_smul_right]))

@[simp] theorem tensorRep0_tmul (a : A₁) (b : A₂) :
    tensorRep0 M₁ M₂ φ₁ φ₂ (a ⊗ₜ b) =
      TensorProduct.mapL (φ₁ a) (φ₂ b) := by
  simp [tensorRep0]

theorem tensorRep0_one : tensorRep0 M₁ M₂ φ₁ φ₂ 1 = 1 := by
  rw [Algebra.TensorProduct.one_def, tensorRep0_tmul, map_one, map_one]
  show TensorProduct.mapL (ContinuousLinearMap.id ℂ M₁.H)
    (ContinuousLinearMap.id ℂ M₂.H) = ContinuousLinearMap.id ℂ _
  exact TensorProduct.mapL_id_id

theorem tensorRep0_mul (x y : A₁ ⊗[ℂ] A₂) :
    tensorRep0 M₁ M₂ φ₁ φ₂ (x * y) =
      tensorRep0 M₁ M₂ φ₁ φ₂ x * tensorRep0 M₁ M₂ φ₁ φ₂ y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul c d =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, tensorRep0_tmul,
        tensorRep0_tmul, tensorRep0_tmul, map_mul, map_mul,
        TensorProduct.mapL_mul]
    | add y₁ y₂ h₁ h₂ =>
      rw [mul_add, map_add, h₁, h₂, map_add, mul_add]
  | add x₁ x₂ h₁ h₂ =>
    rw [add_mul, map_add, h₁, h₂, map_add, add_mul]

theorem tensorRep0_inner_star (x : A₁ ⊗[ℂ] A₂)
    (w w' : M₁.H ⊗[ℂ] M₂.H) :
    ⟪tensorRep0 M₁ M₂ φ₁ φ₂ (star x) w, w'⟫_ℂ =
      ⟪w, tensorRep0 M₁ M₂ φ₁ φ₂ x w'⟫_ℂ := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [TensorProduct.star_tmul, tensorRep0_tmul, tensorRep0_tmul,
      map_star, map_star]
    exact inner_mapL_star M₁ M₂ (φ₁ a) (φ₂ b) w w'
  | add x₁ x₂ h₁ h₂ =>
    rw [star_add, map_add, map_add, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.add_apply, inner_add_left, inner_add_right,
      h₁, h₂]

/-- **The factorwise representation on the completed GNS space**, as a
∗-algebra homomorphism: `a ⊗ b` acts by the extension of
`φ₁(a) ⊗ φ₂(b)`. -/
noncomputable def tensorRep : (A₁ ⊗[ℂ] A₂) →⋆ₐ[ℂ]
    (StepH M₁ M₂ →L[ℂ] StepH M₁ M₂) where
  toFun x := extendStep M₁ M₂ (tensorRep0 M₁ M₂ φ₁ φ₂ x)
  map_one' := by rw [tensorRep0_one]; exact extendStep_one M₁ M₂
  map_mul' x y := by
    rw [tensorRep0_mul]
    exact extendStep_comp M₁ M₂ _ _
  map_zero' := by rw [map_zero]; exact extendStep_zero M₁ M₂
  map_add' x y := by rw [map_add]; exact extendStep_add M₁ M₂ _ _
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, tensorRep0_one,
      extendStep_smul, extendStep_one]
    rw [Algebra.algebraMap_eq_smul_one]
  map_star' x :=
    extendStep_star_of_inner M₁ M₂
      (tensorRep0_inner_star M₁ M₂ φ₁ φ₂ x)

theorem tensorRep_apply (x : A₁ ⊗[ℂ] A₂) :
    tensorRep M₁ M₂ φ₁ φ₂ x =
      extendStep M₁ M₂ (tensorRep0 M₁ M₂ φ₁ φ₂ x) := rfl

theorem tensorRep_coe (x : A₁ ⊗[ℂ] A₂) (w : M₁.H ⊗[ℂ] M₂.H) :
    tensorRep M₁ M₂ φ₁ φ₂ x (w : StepH M₁ M₂) =
      ((tensorRep0 M₁ M₂ φ₁ φ₂ x w : M₁.H ⊗[ℂ] M₂.H) : StepH M₁ M₂) :=
  extendStep_coe M₁ M₂ _ w

end TensorRep


/-! ### The left and right representations and the assembly -/

/-- The opposite-algebra distribution
`(A₁ ⊗ A₂)ᵐᵒᵖ → A₁ᵐᵒᵖ ⊗ A₂ᵐᵒᵖ` as a ∗-algebra homomorphism. -/
noncomputable def opDistrib : ((M₁.A ⊗[ℂ] M₂.A)ᵐᵒᵖ) →⋆ₐ[ℂ]
    (M₁.Aᵐᵒᵖ ⊗[ℂ] M₂.Aᵐᵒᵖ) :=
  { (Algebra.TensorProduct.opAlgEquiv ℂ ℂ M₁.A M₂.A).symm.toAlgHom with
    map_star' := by
      intro x
      show (Algebra.TensorProduct.opAlgEquiv ℂ ℂ M₁.A M₂.A).symm
          (star x) =
        star ((Algebra.TensorProduct.opAlgEquiv ℂ ℂ M₁.A M₂.A).symm x)
      rw [← MulOpposite.op_unop x]
      generalize MulOpposite.unop x = y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        rw [← MulOpposite.op_star, TensorProduct.star_tmul,
          Algebra.TensorProduct.opAlgEquiv_symm_tmul,
          Algebra.TensorProduct.opAlgEquiv_symm_tmul,
          TensorProduct.star_tmul, MulOpposite.op_star,
          MulOpposite.op_star]
      | add y₁ y₂ h₁ h₂ =>
        rw [← MulOpposite.op_star, star_add, MulOpposite.op_add,
          map_add, MulOpposite.op_add, map_add, star_add,
          MulOpposite.op_star, MulOpposite.op_star, h₁, h₂] }

@[simp] theorem opDistrib_op_tmul (a : M₁.A) (b : M₂.A) :
    opDistrib M₁ M₂ (MulOpposite.op (a ⊗ₜ b)) =
      MulOpposite.op a ⊗ₜ MulOpposite.op b := by
  show (Algebra.TensorProduct.opAlgEquiv ℂ ℂ M₁.A M₂.A).symm
      (MulOpposite.op (a ⊗ₜ b)) = _
  rw [Algebra.TensorProduct.opAlgEquiv_symm_tmul]

/-- The left representation of the tensor step. -/
noncomputable def stepL : (M₁.A ⊗[ℂ] M₂.A) →⋆ₐ[ℂ]
    (StepH M₁ M₂ →L[ℂ] StepH M₁ M₂) :=
  tensorRep M₁ M₂ M₁.L M₂.L

/-- The right representation of the tensor step. -/
noncomputable def stepR : ((M₁.A ⊗[ℂ] M₂.A)ᵐᵒᵖ) →⋆ₐ[ℂ]
    (StepH M₁ M₂ →L[ℂ] StepH M₁ M₂) :=
  (tensorRep M₁ M₂ M₁.R M₂.R).comp (opDistrib M₁ M₂)

/-- The left evaluation identity on the algebraic image. -/
theorem tensorRep0_L_map_ι (x y : M₁.A ⊗[ℂ] M₂.A) :
    tensorRep0 M₁ M₂ M₁.L M₂.L x (TensorProduct.map M₁.ι M₂.ι y) =
      TensorProduct.map M₁.ι M₂.ι (x * y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul c d =>
      rw [TensorProduct.map_tmul, tensorRep0_tmul,
        TensorProduct.mapL_tmul, M₁.L_apply, M₂.L_apply,
        Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.map_tmul]
    | add y₁ y₂ h₁ h₂ =>
      rw [map_add, map_add, h₁, h₂, mul_add, map_add]
  | add x₁ x₂ h₁ h₂ =>
    rw [map_add, ContinuousLinearMap.add_apply, h₁, h₂, add_mul,
      map_add]

theorem stepL_apply (x y : M₁.A ⊗[ℂ] M₂.A) :
    stepL M₁ M₂ x (stepι M₁ M₂ y) = stepι M₁ M₂ (x * y) := by
  show tensorRep M₁ M₂ M₁.L M₂.L x
      ((TensorProduct.map M₁.ι M₂.ι y : M₁.H ⊗[ℂ] M₂.H) :
        StepH M₁ M₂) = _
  rw [tensorRep_coe, tensorRep0_L_map_ι]
  rfl

/-- The right evaluation identity on the algebraic image. -/
theorem tensorRep0_R_map_ι (x y : M₁.A ⊗[ℂ] M₂.A) :
    tensorRep0 M₁ M₂ M₁.R M₂.R
        (opDistrib M₁ M₂ (MulOpposite.op x))
        (TensorProduct.map M₁.ι M₂.ι y) =
      TensorProduct.map M₁.ι M₂.ι (y * x) := by
  induction x using TensorProduct.induction_on with
  | zero =>
    rw [MulOpposite.op_zero, map_zero, map_zero, mul_zero, map_zero]
    rfl
  | tmul a b =>
    rw [opDistrib_op_tmul, tensorRep0_tmul]
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul c d =>
      rw [TensorProduct.map_tmul, TensorProduct.mapL_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.map_tmul]
      show (M₁.Rop a) (M₁.ι c) ⊗ₜ[ℂ] (M₂.Rop b) (M₂.ι d) = _
      rw [Rop, M₁.R_apply, Rop, M₂.R_apply]
    | add y₁ y₂ h₁ h₂ =>
      rw [map_add, map_add, h₁, h₂, add_mul, map_add]
  | add x₁ x₂ h₁ h₂ =>
    rw [MulOpposite.op_add, map_add, map_add,
      ContinuousLinearMap.add_apply, h₁, h₂, mul_add, map_add]

theorem stepR_apply (x y : M₁.A ⊗[ℂ] M₂.A) :
    stepR M₁ M₂ (MulOpposite.op x) (stepι M₁ M₂ y) =
      stepι M₁ M₂ (y * x) := by
  show tensorRep M₁ M₂ M₁.R M₂.R
      (opDistrib M₁ M₂ (MulOpposite.op x))
      ((TensorProduct.map M₁.ι M₂.ι y : M₁.H ⊗[ℂ] M₂.H) :
        StepH M₁ M₂) = _
  rw [tensorRep_coe, tensorRep0_R_map_ι]
  rfl

/-- Factorwise commutation on the algebraic tensor product, from
pointwise commutation of the factor actions. -/
theorem tensorRep0_commute {A₁ : Type*} [Ring A₁] [StarRing A₁]
    [Algebra ℂ A₁] [StarModule ℂ A₁]
    {A₂ : Type*} [Ring A₂] [StarRing A₂] [Algebra ℂ A₂]
    [StarModule ℂ A₂]
    {B₁ : Type*} [Ring B₁] [StarRing B₁] [Algebra ℂ B₁]
    [StarModule ℂ B₁]
    {B₂ : Type*} [Ring B₂] [StarRing B₂] [Algebra ℂ B₂]
    [StarModule ℂ B₂]
    (φ₁ : A₁ →⋆ₐ[ℂ] (M₁.H →L[ℂ] M₁.H))
    (φ₂ : A₂ →⋆ₐ[ℂ] (M₂.H →L[ℂ] M₂.H))
    (ψ₁ : B₁ →⋆ₐ[ℂ] (M₁.H →L[ℂ] M₁.H))
    (ψ₂ : B₂ →⋆ₐ[ℂ] (M₂.H →L[ℂ] M₂.H))
    (h₁ : ∀ a c, Commute (φ₁ a) (ψ₁ c))
    (h₂ : ∀ b d, Commute (φ₂ b) (ψ₂ d))
    (x : A₁ ⊗[ℂ] A₂) (z : B₁ ⊗[ℂ] B₂) :
    Commute (tensorRep0 M₁ M₂ φ₁ φ₂ x) (tensorRep0 M₁ M₂ ψ₁ ψ₂ z) := by
  induction x using TensorProduct.induction_on with
  | zero => simp [Commute, SemiconjBy]
  | tmul a b =>
    induction z using TensorProduct.induction_on with
    | zero => simp [Commute, SemiconjBy]
    | tmul c d =>
      rw [tensorRep0_tmul, tensorRep0_tmul]
      show _ * _ = _ * _
      rw [← TensorProduct.mapL_mul, ← TensorProduct.mapL_mul,
        (h₁ a c).eq, (h₂ b d).eq]
    | add z₁ z₂ hz₁ hz₂ =>
      rw [map_add]
      exact hz₁.add_right hz₂
  | add x₁ x₂ hx₁ hx₂ =>
    rw [map_add]
    exact hx₁.add_left hx₂

theorem stepLR_commute (x y : M₁.A ⊗[ℂ] M₂.A) :
    Commute (stepL M₁ M₂ x) (stepR M₁ M₂ (MulOpposite.op y)) := by
  have h0 : Commute (tensorRep0 M₁ M₂ M₁.L M₂.L x)
      (tensorRep0 M₁ M₂ M₁.R M₂.R
        (opDistrib M₁ M₂ (MulOpposite.op y))) :=
    tensorRep0_commute M₁ M₂ M₁.L M₂.L M₁.R M₂.R
      (fun a c => M₁.LR_commute a (MulOpposite.unop c))
      (fun b d => M₂.LR_commute b (MulOpposite.unop d)) x _
  show (extendStep M₁ M₂ (tensorRep0 M₁ M₂ M₁.L M₂.L x)).comp
      (extendStep M₁ M₂ (tensorRep0 M₁ M₂ M₁.R M₂.R
        (opDistrib M₁ M₂ (MulOpposite.op y)))) =
    (extendStep M₁ M₂ (tensorRep0 M₁ M₂ M₁.R M₂.R
        (opDistrib M₁ M₂ (MulOpposite.op y)))).comp
      (extendStep M₁ M₂ (tensorRep0 M₁ M₂ M₁.L M₂.L x))
  rw [← extendStep_comp, ← extendStep_comp]
  show extendStep M₁ M₂ (tensorRep0 M₁ M₂ M₁.L M₂.L x *
      tensorRep0 M₁ M₂ M₁.R M₂.R
        (opDistrib M₁ M₂ (MulOpposite.op y))) = _
  rw [h0.eq]
  rfl

/-- **The binary tensor step**: the algebraic tensor product with the
product trace, in standard form on the completed inner-product tensor
of the GNS spaces (Stage B, WP-B3b). -/
noncomputable def tensorStep : StdTracialAlgebra.{u} where
  A := M₁.A ⊗[ℂ] M₂.A
  τ := stepτ M₁ M₂
  τ_one := stepτ_one M₁ M₂
  τ_mul_comm := stepτ_mul_comm M₁ M₂
  τ_star := stepτ_star M₁ M₂
  H := StepH M₁ M₂
  ι := stepι M₁ M₂
  ι_dense := stepι_dense M₁ M₂
  ι_inner := stepι_inner M₁ M₂
  L := stepL M₁ M₂
  R := stepR M₁ M₂
  L_apply := stepL_apply M₁ M₂
  R_apply := stepR_apply M₁ M₂
  LR_commute := fun x y => stepLR_commute M₁ M₂ x y

@[simp] theorem tensorStep_A : (tensorStep M₁ M₂).A = (M₁.A ⊗[ℂ] M₂.A) :=
  rfl

@[simp] theorem tensorStep_τ (x : M₁.A ⊗[ℂ] M₂.A) :
    (tensorStep M₁ M₂).τ x = stepτ M₁ M₂ x := rfl

end StdTracialAlgebra

end CommutingRepetition
