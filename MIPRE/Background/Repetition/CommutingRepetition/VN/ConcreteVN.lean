/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/ConcreteVN.lean
-/
/-
# The concrete von Neumann algebra of a standard tracial algebra

`vnAlg M` is the commutant `R(M)'` of the right action in `B(L²(M))`: a
norm-closed star subalgebra containing `L(M.A)` (so Mathlib's continuous
functional calculus keeps its outputs inside), on which the trace-vector
state `φ(T) = ⟪Ω, T Ω⟫` is tracial. Traciality is proved with the antiunitary
`J : ι a ↦ ι a*` (isometric by `τ_mul_comm`, extended by density): for
`x ∈ R(M)'`, `J x Ω = x* Ω` (from `x R(a) = R(a) x` and `R(a) Ω = ι a`), whence
`φ(xy) = ⟪x*Ω, yΩ⟫ = ⟪J(xΩ), J(y*Ω)⟫ = ⟪y*Ω, xΩ⟫ = φ(yx)`. No bicommutant
theorem and no weak topology is used.

`vnModel M` is the resulting standard tracial algebra (`VN/SubModel.lean`):
the algebra in which the entropic resolver arena (node 1.2.6) is built.
Infrastructure only; no manuscript statement.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.SubModel

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace StdTracialAlgebra

open scoped InnerProductSpace

universe u

variable (M : StdTracialAlgebra.{u})

/-! ## Density of `ι` -/

/-- Induction along the dense range of `ι`. -/
theorem ι_induction {p : M.H → Prop} (hp : IsClosed {v | p v}) (h : ∀ a, p (M.ι a)) (v : M.H) :
    p v :=
  M.ι_dense.induction_on v hp h

theorem ext_of_inner_ι {u v : M.H} (h : ∀ a, ⟪u, M.ι a⟫_ℂ = ⟪v, M.ι a⟫_ℂ) : u = v := by
  refine ext_inner_right ℂ fun w => ?_
  refine M.ι_induction (p := fun w => ⟪u, w⟫_ℂ = ⟪v, w⟫_ℂ) ?_ h w
  exact isClosed_eq (Continuous.inner continuous_const continuous_id)
    (Continuous.inner continuous_const continuous_id)

/-! ## The antiunitary `J` -/

/-- The range of `ι` as a submodule. -/
noncomputable def ιRange : Submodule ℂ M.H := LinearMap.range M.ι

noncomputable def ιRep (v : ↥M.ιRange) : M.A := (LinearMap.mem_range.mp v.2).choose

theorem ι_ιRep (v : ↥M.ιRange) : M.ι (M.ιRep v) = v :=
  (LinearMap.mem_range.mp v.2).choose_spec

theorem inner_ι_star (a b : M.A) : ⟪M.ι (star a), M.ι (star b)⟫_ℂ = ⟪M.ι b, M.ι a⟫_ℂ := by
  rw [M.ι_inner, M.ι_inner, star_star, M.τ_mul_comm]

theorem norm_ι_star (a : M.A) : ‖M.ι (star a)‖ = ‖M.ι a‖ := by
  have h := M.inner_ι_star a a
  have h1 := congrArg Complex.re h
  rw [← RCLike.re_to_complex, ← RCLike.re_to_complex, inner_self_eq_norm_sq,
    inner_self_eq_norm_sq] at h1
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1

theorem ι_star_welldef {a b : M.A} (h : M.ι a = M.ι b) : M.ι (star a) = M.ι (star b) := by
  have h1 : ‖M.ι (star (a - b))‖ = 0 := by
    rw [M.norm_ι_star, map_sub, h, sub_self, norm_zero]
  rw [star_sub, map_sub] at h1
  exact sub_eq_zero.mp (norm_eq_zero.mp h1)

/-- `J` on the range of `ι`: `ι a ↦ ι a*`, conjugate-linear. -/
noncomputable def J₀ : ↥M.ιRange →SL[starRingEnd ℂ] M.H :=
  LinearMap.mkContinuous
    { toFun := fun v => M.ι (star (M.ιRep v))
      map_add' := fun v w => by
        rw [← map_add, ← star_add]
        refine M.ι_star_welldef ?_
        rw [M.ι_ιRep, map_add, M.ι_ιRep, M.ι_ιRep]; rfl
      map_smul' := fun c v => by
        show M.ι (star (M.ιRep (c • v))) = (starRingEnd ℂ) c • M.ι (star (M.ιRep v))
        rw [← map_smul, ← Complex.star_def, ← star_smul]
        refine M.ι_star_welldef ?_
        rw [M.ι_ιRep, map_smul, M.ι_ιRep]; rfl } 1 fun v => by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
    rw [M.norm_ι_star, M.ι_ιRep]; rfl

theorem J₀_apply (v : ↥M.ιRange) : M.J₀ v = M.ι (star (M.ιRep v)) := rfl

theorem denseRange_subtypeL_ιRange : DenseRange M.ιRange.subtypeL := by
  have h : Set.range M.ιRange.subtypeL = Set.range M.ι := by
    ext v
    constructor
    · rintro ⟨w, rfl⟩
      exact LinearMap.mem_range.mp w.2
    · rintro ⟨a, rfl⟩
      exact ⟨⟨M.ι a, LinearMap.mem_range_self _ a⟩, rfl⟩
  rw [DenseRange, h]
  exact M.ι_dense

theorem isUniformInducing_subtypeL_ιRange : IsUniformInducing M.ιRange.subtypeL :=
  ((AddMonoidHomClass.isometry_iff_norm _).mpr fun _ => rfl).isUniformInducing

/-- The antiunitary `J`, the continuous extension of `ι a ↦ ι a*`. -/
noncomputable def J : M.H →SL[starRingEnd ℂ] M.H := M.J₀.extend M.ιRange.subtypeL

theorem J_ι (a : M.A) : M.J (M.ι a) = M.ι (star a) := by
  have hv : M.ι a ∈ M.ιRange := LinearMap.mem_range_self _ a
  have h := ContinuousLinearMap.extend_eq M.J₀ M.denseRange_subtypeL_ιRange
    M.isUniformInducing_subtypeL_ιRange ⟨M.ι a, hv⟩
  rw [show M.ιRange.subtypeL ⟨M.ι a, hv⟩ = M.ι a from rfl] at h
  rw [show M.J = M.J₀.extend M.ιRange.subtypeL from rfl, h, J₀_apply]
  exact M.ι_star_welldef (M.ι_ιRep _)

theorem inner_J_J (v w : M.H) : ⟪M.J v, M.J w⟫_ℂ = ⟪w, v⟫_ℂ := by
  refine M.ι_induction (p := fun v => ∀ w, ⟪M.J v, M.J w⟫_ℂ = ⟪w, v⟫_ℂ) ?_ (fun a => ?_) v w
  · rw [Set.setOf_forall]
    refine isClosed_iInter fun w => ?_
    exact isClosed_eq (Continuous.inner (M.J.continuous) continuous_const)
      (Continuous.inner continuous_const continuous_id)
  · intro w
    refine M.ι_induction (p := fun w => ⟪M.J (M.ι a), M.J w⟫_ℂ = ⟪w, M.ι a⟫_ℂ) ?_ (fun b => ?_) w
    · exact isClosed_eq (Continuous.inner continuous_const (M.J.continuous))
        (Continuous.inner continuous_id continuous_const)
    · rw [M.J_ι, M.J_ι, M.inner_ι_star]

theorem J_J (v : M.H) : M.J (M.J v) = v := by
  refine M.ι_induction (p := fun v => M.J (M.J v) = v) ?_ (fun a => ?_) v
  · exact isClosed_eq (M.J.continuous.comp M.J.continuous) continuous_id
  · rw [M.J_ι, M.J_ι, star_star]

theorem inner_J_left (v w : M.H) : ⟪M.J v, w⟫_ℂ = ⟪M.J w, v⟫_ℂ := by
  conv_lhs => rw [← M.J_J w]
  rw [M.inner_J_J]

/-! ## The commutant of the right action -/

/-- The concrete von Neumann algebra `R(M)' ⊆ B(L²(M))`. -/
noncomputable def vnAlg : StarSubalgebra ℂ (M.H →L[ℂ] M.H) :=
  StarSubalgebra.centralizer ℂ (Set.range M.Rop)

theorem star_Rop (a : M.A) : star (M.Rop a) = M.Rop (star a) := by
  unfold Rop
  rw [← map_star, MulOpposite.op_star]

theorem mem_vnAlg_iff {T : M.H →L[ℂ] M.H} :
    T ∈ M.vnAlg ↔ ∀ a : M.A, M.Rop a * T = T * M.Rop a := by
  unfold vnAlg
  rw [StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h a
    exact (h _ ⟨a, rfl⟩).1
  · rintro h _ ⟨a, rfl⟩
    exact ⟨h a, by rw [M.star_Rop]; exact h _⟩

theorem L_mem_vnAlg (a : M.A) : M.L a ∈ M.vnAlg := by
  rw [M.mem_vnAlg_iff]
  intro b
  exact (M.LR_commute a b).symm

theorem isClosed_vnAlg : IsClosed (M.vnAlg : Set (M.H →L[ℂ] M.H)) := by
  unfold vnAlg
  rw [StarSubalgebra.coe_centralizer]
  exact Set.isClosed_centralizer _

theorem Rop_traceVector (a : M.A) : M.Rop a M.traceVector = M.ι a := by
  unfold traceVector Rop
  rw [M.R_apply, one_mul]

theorem mulA (f g : M.H →L[ℂ] M.H) (ξ : M.H) : (f * g) ξ = f (g ξ) := rfl

/-- `J (T Ω) = T* Ω` for `T` in the commutant of the right action. -/
theorem J_apply_traceVector {T : M.H →L[ℂ] M.H} (hT : T ∈ M.vnAlg) :
    M.J (T M.traceVector) = star T M.traceVector := by
  rw [M.mem_vnAlg_iff] at hT
  refine M.ext_of_inner_ι fun a => ?_
  rw [M.inner_J_left, M.J_ι, ← M.Rop_traceVector (star a), ← M.star_Rop,
    ContinuousLinearMap.star_eq_adjoint (M.Rop a), ContinuousLinearMap.adjoint_inner_left,
    ← mulA, hT a, mulA, M.Rop_traceVector, ContinuousLinearMap.star_eq_adjoint T,
    ContinuousLinearMap.adjoint_inner_left]

/-- **Traciality of the trace-vector state on `R(M)'`.** -/
theorem traceState_mul_comm_vn {T U : M.H →L[ℂ] M.H} (hT : T ∈ M.vnAlg) (hU : U ∈ M.vnAlg) :
    M.traceState (T * U) = M.traceState (U * T) := by
  unfold traceState
  rw [mulA, mulA, ← ContinuousLinearMap.adjoint_inner_left T (U M.traceVector) M.traceVector,
    ← ContinuousLinearMap.adjoint_inner_left U (T M.traceVector) M.traceVector,
    ← ContinuousLinearMap.star_eq_adjoint T,
    ← ContinuousLinearMap.star_eq_adjoint U, ← M.J_apply_traceVector hT,
    ← M.J_apply_traceVector hU, M.inner_J_left]

/-- The tracial-subalgebra datum of the commutant. -/
noncomputable def vnData : TracialSub M where
  S := M.vnAlg
  isClosed := M.isClosed_vnAlg
  L_mem := M.L_mem_vnAlg
  tracial := fun hT hU => M.traceState_mul_comm_vn hT hU

/-- **The concrete von Neumann model**: `R(M)'` as a standard tracial algebra on `L²(M)`. -/
noncomputable def vnModel : StdTracialAlgebra.{u} := M.vnData.model

theorem vnModel_A : M.vnModel.A = ↥M.vnAlg := rfl

theorem vnModel_H : M.vnModel.H = M.H := rfl

theorem vnModel_τ (T : ↥M.vnAlg) : M.vnModel.τ T = M.traceState T.1 := rfl

theorem vnModel_ι (T : ↥M.vnAlg) : M.vnModel.ι T = T.1 M.traceVector := rfl

theorem vnModel_L (T : ↥M.vnAlg) : M.vnModel.L T = T.1 := rfl

theorem vnModel_τ_L (a : M.A) : M.vnModel.τ ⟨M.L a, M.L_mem_vnAlg a⟩ = M.τ a :=
  M.traceState_L a

end StdTracialAlgebra

end CommutingRepetition
