/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Tracial/CStarLayer.lean
-/
/-
# The C*-envelope of a standard tracial algebra (Stage B, WP-B4)

The norm closure `envAlg M` of the left representation's range in
`B(L²(M))` — a closed star subalgebra, hence a C*-algebra on which
Mathlib's continuous functional calculus operates, with `cfc_mem`
keeping every functional-calculus output inside the envelope. The
trace-vector state extends `M.τ` to the envelope and remains tracial
(by norm-density and continuity, no von Neumann closure needed: the
two-cutoff design of 04_resolver_corner.tex makes every construction
norm-convergent).

Infrastructure (no manuscript anchor of its own): this is the algebra
in which the resolver-corner construction (nodes 1.2.5.1–1.2.5.6) runs
— square roots, resolvents `(F + u)⁻¹`, and the entropy integrands are
`cfc` outputs of envelope elements, and the corner algebra `N` of
`resolver_arena_entropic` is assembled from matrix amplifications of
the envelope model. The key quantitative fact proved here is the trace
inequality `φ(X·Y) ≤ ‖Y‖·φ(X)` for commuting-side positives, which
bounds the right regular representation and will make the envelope a
`StdTracialAlgebra` (the second half of WP-B4).
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Tracial.Interface

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace StdTracialAlgebra

open scoped InnerProductSpace

universe u

variable (M : StdTracialAlgebra.{u})

/-- The C*-envelope: the norm closure of the left representation's
range in `B(L²(M))`. -/
noncomputable def envAlg : StarSubalgebra ℂ (M.H →L[ℂ] M.H) :=
  (StarAlgHom.range M.L).topologicalClosure

theorem isClosed_envAlg : IsClosed (M.envAlg : Set (M.H →L[ℂ] M.H)) :=
  StarSubalgebra.isClosed_topologicalClosure _

theorem L_mem_envAlg (a : M.A) : M.L a ∈ M.envAlg :=
  (StarAlgHom.range M.L).le_topologicalClosure ⟨a, rfl⟩

theorem range_subset_envAlg :
    (Set.range (M.L : M.A → M.H →L[ℂ] M.H)) ⊆ (M.envAlg : Set _) := by
  rintro _ ⟨a, rfl⟩
  exact M.L_mem_envAlg a

theorem envAlg_carrier_eq_closure :
    (M.envAlg : Set (M.H →L[ℂ] M.H))
      = closure (StarAlgHom.range M.L : Set (M.H →L[ℂ] M.H)) := rfl

/-- The trace-vector state on all of `B(L²(M))`:
`φ(T) = ⟪Ω_τ, T Ω_τ⟫`. On the envelope it extends `M.τ`. -/
noncomputable def traceState (T : M.H →L[ℂ] M.H) : ℂ :=
  ⟪M.traceVector, T M.traceVector⟫_ℂ

theorem traceState_L (a : M.A) : M.traceState (M.L a) = M.τ a := by
  unfold traceState traceVector
  rw [M.L_apply, M.ι_inner, star_one, one_mul, mul_one]

theorem norm_traceVector : ‖M.traceVector‖ = 1 := by
  have h : ⟪M.traceVector, M.traceVector⟫_ℂ = 1 := by
    unfold traceVector
    rw [M.ι_inner, star_one, one_mul, M.τ_one]
  have h3 : (‖M.traceVector‖ : ℝ) ^ 2 = 1 := by
    have h2 := congrArg Complex.re h
    rw [← RCLike.re_to_complex] at h2
    rwa [inner_self_eq_norm_sq (𝕜 := ℂ), Complex.one_re] at h2
  nlinarith [norm_nonneg M.traceVector]

theorem continuous_traceState : Continuous M.traceState := by
  unfold traceState
  fun_prop

/-- The trace-vector state is positive: `φ(T*T) = ‖T Ω‖² ≥ 0`. -/
theorem traceState_star_mul_self (T : M.H →L[ℂ] M.H) :
    M.traceState (star T * T)
      = ((‖T M.traceVector‖ : ℝ) : ℂ) ^ 2 := by
  unfold traceState
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K]
  norm_cast

/-- **Traciality on the envelope** (density + continuity): for
`T, S ∈ envAlg`, `φ(TS) = φ(ST)`. -/
theorem traceState_mul_comm {T S : M.H →L[ℂ] M.H}
    (hT : T ∈ M.envAlg) (hS : S ∈ M.envAlg) :
    M.traceState (T * S) = M.traceState (S * T) := by
  have hbase : ∀ (a b : M.A),
      M.traceState (M.L a * M.L b) = M.traceState (M.L b * M.L a) := by
    intro a b
    rw [← map_mul, ← map_mul, M.traceState_L, M.traceState_L,
      M.τ_mul_comm]
  -- Step 1: fix b in the range, extend the left slot to the closure.
  have hstep1 : ∀ (b : M.A), ∀ W ∈ M.envAlg,
      M.traceState (W * M.L b) = M.traceState (M.L b * W) := by
    intro b W hW
    have hclosed : IsClosed {W : M.H →L[ℂ] M.H |
        M.traceState (W * M.L b) = M.traceState (M.L b * W)} := by
      apply isClosed_eq
      · exact M.continuous_traceState.comp (continuous_mul_right _)
      · exact M.continuous_traceState.comp (continuous_mul_left _)
    have hsub : (StarAlgHom.range M.L : Set (M.H →L[ℂ] M.H))
        ⊆ {W | M.traceState (W * M.L b) = M.traceState (M.L b * W)} := by
      rintro _ ⟨a, rfl⟩
      show M.traceState (M.L a * M.L b) = M.traceState (M.L b * M.L a)
      exact hbase a b
    have hall : (M.envAlg : Set (M.H →L[ℂ] M.H))
        ⊆ {W | M.traceState (W * M.L b) = M.traceState (M.L b * W)} := by
      rw [M.envAlg_carrier_eq_closure]
      exact closure_minimal hsub hclosed
    exact hall hW
  -- Step 2: fix T in the closure, extend the right slot.
  have hclosed2 : IsClosed {W : M.H →L[ℂ] M.H |
      M.traceState (T * W) = M.traceState (W * T)} := by
    apply isClosed_eq
    · exact M.continuous_traceState.comp (continuous_mul_left _)
    · exact M.continuous_traceState.comp (continuous_mul_right _)
  have hsub2 : (StarAlgHom.range M.L : Set (M.H →L[ℂ] M.H))
      ⊆ {W | M.traceState (T * W) = M.traceState (W * T)} := by
    rintro _ ⟨b, rfl⟩
    show M.traceState (T * M.L b) = M.traceState (M.L b * T)
    exact hstep1 b T hT
  have hall2 : (M.envAlg : Set (M.H →L[ℂ] M.H))
      ⊆ {W | M.traceState (T * W) = M.traceState (W * T)} := by
    rw [M.envAlg_carrier_eq_closure]
    exact closure_minimal hsub2 hclosed2
  exact hall2 hS


theorem smul_one_mem_envAlg (c : ℂ) : c • (1 : M.H →L[ℂ] M.H) ∈ M.envAlg :=
  SMulMemClass.smul_mem c (one_mem M.envAlg)

theorem traceState_smul (c : ℂ) (T : M.H →L[ℂ] M.H) :
    M.traceState (c • T) = c * M.traceState T := by
  unfold traceState
  rw [ContinuousLinearMap.smul_apply, inner_smul_right]

theorem traceState_sub (T S : M.H →L[ℂ] M.H) :
    M.traceState (T - S) = M.traceState T - M.traceState S := by
  unfold traceState
  rw [ContinuousLinearMap.sub_apply, inner_sub_right]

/-- **The trace inequality** (the boundedness engine for the right
regular representation): for `U, T` in the envelope,
`‖(U T) Ω‖ ≤ ‖T‖ · ‖U Ω‖`. Traciality moves the `T`-square to the
other side (`φ(T* U*U T) = φ(U*U · TT*)`), the C*-gap
`‖TT*‖·1 − TT*` has a `CFC.sqrt` in the envelope (`cfc_mem` on the
closed star subalgebra), and positivity of the state on envelope
squares finishes. -/
theorem norm_mul_traceVector_le {U T : M.H →L[ℂ] M.H}
    (hU : U ∈ M.envAlg) (hT : T ∈ M.envAlg) :
    ‖(U * T) M.traceVector‖ ≤ ‖T‖ * ‖U M.traceVector‖ := by
  have hTstar : star T ∈ M.envAlg := star_mem hT
  have hUstar : star U ∈ M.envAlg := star_mem hU
  set Y : M.H →L[ℂ] M.H := T * star T with hYdef
  have hY : Y ∈ M.envAlg := mul_mem hT hTstar
  have hYsa : IsSelfAdjoint Y := by
    rw [IsSelfAdjoint, hYdef, star_mul, star_star]
  have hYpos : (0 : M.H →L[ℂ] M.H) ≤ Y := by
    simpa [hYdef] using star_mul_self_nonneg (star T)
  set Z : M.H →L[ℂ] M.H := ((‖Y‖ : ℝ) : ℂ) • 1 - Y with hZdef
  have halg : (algebraMap ℝ (M.H →L[ℂ] M.H)) ‖Y‖
      = ((‖Y‖ : ℝ) : ℂ) • (1 : M.H →L[ℂ] M.H) := by
    rw [Algebra.algebraMap_eq_smul_one]
    norm_num
  have hZpos : (0 : M.H →L[ℂ] M.H) ≤ Z := by
    rw [hZdef, sub_nonneg, ← halg]
    exact IsSelfAdjoint.le_algebraMap_norm_self hYsa
  have hZmem : Z ∈ M.envAlg := by
    rw [hZdef]
    exact sub_mem (M.smul_one_mem_envAlg _) hY
  set W : M.H →L[ℂ] M.H := CFC.sqrt Z with hWdef
  have hWpos : (0 : M.H →L[ℂ] M.H) ≤ W := CFC.sqrt_nonneg Z
  have hWsa : IsSelfAdjoint W := IsSelfAdjoint.of_nonneg hWpos
  have hWsq : W * W = Z := CFC.sqrt_mul_sqrt_self Z hZpos
  have hWmem : W ∈ M.envAlg := by
    rw [hWdef, CFC.sqrt_eq_real_sqrt Z hZpos,
      cfcₙ_eq_cfc (hf0 := by simp)]
    exact cfc_mem (𝕜' := ℂ) (hs := M.isClosed_envAlg) Real.sqrt hZmem
  have hpos_square : ∀ (V : M.H →L[ℂ] M.H),
      0 ≤ (M.traceState (star V * V)).re := by
    intro V
    rw [M.traceState_star_mul_self]
    norm_cast
    positivity
  -- the swap: φ(T* (U*U T)) = φ((U*U) Y)
  have hswap : M.traceState (star T * (star U * U * T))
      = M.traceState (star U * U * Y) := by
    have h1 : M.traceState (star T * (star U * U * T))
        = M.traceState ((star U * U * T) * star T) :=
      M.traceState_mul_comm hTstar (mul_mem (mul_mem hUstar hU) hT)
    rw [h1, hYdef, mul_assoc]
  -- the gap term is nonnegative: 0 ≤ re φ(U*U Z)
  have hgap : 0 ≤ (M.traceState (star U * U * Z)).re := by
    have h1 : star U * U * Z = star U * U * W * W := by
      rw [← hWsq, mul_assoc (star U * U) W W]
    have h2 : M.traceState (star U * U * W * W)
        = M.traceState (W * (star U * U * W)) :=
      M.traceState_mul_comm (mul_mem (mul_mem hUstar hU) hWmem) hWmem
    have h3 : W * (star U * U * W) = star (U * W) * (U * W) := by
      rw [star_mul, hWsa.star_eq]
      noncomm_ring
    have hEq : M.traceState (star U * U * Z)
        = M.traceState (star (U * W) * (U * W)) := by
      rw [h1, h2, h3]
    rw [hEq]
    exact hpos_square _
  -- φ(U*U Y) ≤ ‖Y‖ φ(U*U) in real parts
  have hmain : (M.traceState (star U * U * Y)).re
      ≤ ‖Y‖ * (M.traceState (star U * U)).re := by
    have hexpand : star U * U * Z
        = ((‖Y‖ : ℝ) : ℂ) • (star U * U) - star U * U * Y := by
      rw [hZdef, mul_sub, mul_smul_comm, mul_one]
    have h4 := hgap
    rw [hexpand, M.traceState_sub, M.traceState_smul, Complex.sub_re,
      Complex.re_ofReal_mul] at h4
    linarith
  -- assemble
  have hnorm2 : ((‖(U * T) M.traceVector‖ : ℝ)) ^ 2
      ≤ ‖T‖ ^ 2 * ‖U M.traceVector‖ ^ 2 := by
    have e1 : (M.traceState (star (U * T) * (U * T))).re
        = ‖(U * T) M.traceVector‖ ^ 2 := by
      rw [M.traceState_star_mul_self]
      norm_cast
    have e2 : (M.traceState (star U * U)).re = ‖U M.traceVector‖ ^ 2 := by
      have := M.traceState_star_mul_self U
      rw [this]
      norm_cast
    have e3 : star (U * T) * (U * T) = star T * (star U * U * T) := by
      rw [star_mul]
      noncomm_ring
    have e4 : ‖Y‖ = ‖T‖ ^ 2 := by
      rw [hYdef, CStarRing.norm_self_mul_star, sq]
    calc ‖(U * T) M.traceVector‖ ^ 2
        = (M.traceState (star (U * T) * (U * T))).re := e1.symm
      _ = (M.traceState (star U * U * Y)).re := by rw [e3, hswap]
      _ ≤ ‖Y‖ * (M.traceState (star U * U)).re := hmain
      _ = ‖T‖ ^ 2 * ‖U M.traceVector‖ ^ 2 := by rw [e4, e2]
  have h5 : ‖(U * T) M.traceVector‖ ≤ Real.sqrt (‖T‖ ^ 2 * ‖U M.traceVector‖ ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg ((U * T) M.traceVector))]
    exact Real.sqrt_le_sqrt hnorm2
  calc ‖(U * T) M.traceVector‖
      ≤ Real.sqrt (‖T‖ ^ 2 * ‖U M.traceVector‖ ^ 2) := h5
    _ = ‖T‖ * ‖U M.traceVector‖ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg T),
          Real.sqrt_sq (norm_nonneg _)]

/-- Evaluation at the trace vector, as a linear map on `B(L²(M))`. -/
noncomputable def evalΩ : (M.H →L[ℂ] M.H) →ₗ[ℂ] M.H where
  toFun T := T M.traceVector
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The envelope orbit of the trace vector: `{S Ω ∣ S ∈ envAlg}`, a
dense submodule of `L²(M)` (it contains the range of `M.ι`). -/
noncomputable def envOrbit : Submodule ℂ M.H :=
  (Subalgebra.toSubmodule M.envAlg.toSubalgebra).map M.evalΩ

theorem mem_envOrbit_iff {v : M.H} :
    v ∈ M.envOrbit ↔ ∃ T ∈ M.envAlg, T M.traceVector = v := by
  unfold envOrbit
  simp only [Submodule.mem_map, Subalgebra.mem_toSubmodule]
  rfl

theorem range_ι_subset_envOrbit :
    Set.range M.ι ⊆ (M.envOrbit : Set M.H) := by
  rintro _ ⟨a, rfl⟩
  refine (M.mem_envOrbit_iff).mpr ⟨M.L a, M.L_mem_envAlg a, ?_⟩
  show M.L a (M.ι 1) = M.ι a
  rw [M.L_apply, mul_one]

theorem envOrbit_dense : Dense (M.envOrbit : Set M.H) :=
  M.ι_dense.mono M.range_ι_subset_envOrbit

/-- Well-definedness of right multiplication on the orbit: if two
envelope elements agree at the trace vector, so do their right
translates (the trace inequality applied to the difference). -/
theorem rightMul_welldef {P Q T : M.H →L[ℂ] M.H}
    (hP : P ∈ M.envAlg) (hQ : Q ∈ M.envAlg) (hT : T ∈ M.envAlg)
    (hPQ : P M.traceVector = Q M.traceVector) :
    (P * T) M.traceVector = (Q * T) M.traceVector := by
  have hdiff : ((P - Q) * T) M.traceVector = 0 := by
    have hb := M.norm_mul_traceVector_le (sub_mem hP hQ) hT
    have hz : (P - Q) M.traceVector = 0 := by
      rw [ContinuousLinearMap.sub_apply, hPQ, sub_self]
    rw [hz, norm_zero, mul_zero] at hb
    exact norm_le_zero_iff.mp hb
  have h2 : (P * T) M.traceVector - (Q * T) M.traceVector = 0 := by
    rw [← ContinuousLinearMap.sub_apply, ← sub_mul]
    exact hdiff
  exact sub_eq_zero.mp h2

/-- A representative of an orbit element: an envelope operator whose
value at the trace vector is the given vector (choice; unique up to
`rightMul_welldef`). -/
noncomputable def orbitRep (v : ↥M.envOrbit) : M.H →L[ℂ] M.H :=
  (M.mem_envOrbit_iff.mp v.2).choose

theorem orbitRep_mem (v : ↥M.envOrbit) : M.orbitRep v ∈ M.envAlg :=
  (M.mem_envOrbit_iff.mp v.2).choose_spec.1

theorem orbitRep_apply (v : ↥M.envOrbit) :
    M.orbitRep v M.traceVector = v.1 :=
  (M.mem_envOrbit_iff.mp v.2).choose_spec.2

/-- Right translation on the orbit: `S Ω ↦ (S T) Ω`, well-defined by
`rightMul_welldef` and bounded by the trace inequality. -/
noncomputable def rightMulOrbit (T : ↥M.envAlg) :
    ↥M.envOrbit →L[ℂ] M.H := by
  refine LinearMap.mkContinuous
    { toFun := fun v => (M.orbitRep v * T.1) M.traceVector
      map_add' := ?_
      map_smul' := ?_ } ‖T.1‖ ?_
  · intro v w
    have h1 : (M.orbitRep (v + w) * T.1) M.traceVector
        = ((M.orbitRep v + M.orbitRep w) * T.1) M.traceVector := by
      refine M.rightMul_welldef (M.orbitRep_mem _)
        (add_mem (M.orbitRep_mem v) (M.orbitRep_mem w)) T.2 ?_
      rw [M.orbitRep_apply, ContinuousLinearMap.add_apply,
        M.orbitRep_apply, M.orbitRep_apply]
      rfl
    rw [h1, add_mul, ContinuousLinearMap.add_apply]
  · intro c v
    have h1 : (M.orbitRep (c • v) * T.1) M.traceVector
        = ((c • M.orbitRep v) * T.1) M.traceVector := by
      refine M.rightMul_welldef (M.orbitRep_mem _)
        (SMulMemClass.smul_mem c (M.orbitRep_mem v)) T.2 ?_
      rw [M.orbitRep_apply, ContinuousLinearMap.smul_apply,
        M.orbitRep_apply]
      rfl
    rw [h1, smul_mul_assoc, ContinuousLinearMap.smul_apply]
    rfl
  · intro v
    calc ‖(M.orbitRep v * T.1) M.traceVector‖
        ≤ ‖T.1‖ * ‖M.orbitRep v M.traceVector‖ :=
          M.norm_mul_traceVector_le (M.orbitRep_mem v) T.2
      _ = ‖T.1‖ * ‖v‖ := by rw [M.orbitRep_apply]; rfl

theorem denseRange_subtypeL_envOrbit :
    DenseRange (M.envOrbit.subtypeL) := by
  have h : Set.range (M.envOrbit.subtypeL) = (M.envOrbit : Set M.H) :=
    Subtype.range_coe
  rw [DenseRange, h]
  exact M.envOrbit_dense

theorem isUniformInducing_subtypeL_envOrbit :
    IsUniformInducing (M.envOrbit.subtypeL) := by
  have hiso : Isometry (M.envOrbit.subtypeL) :=
    (AddMonoidHomClass.isometry_iff_norm _).mpr (fun _ => rfl)
  exact hiso.isUniformInducing

/-- **The right regular representation of the envelope**: the unique
bounded extension of `S Ω ↦ (S T) Ω` along the dense orbit. -/
noncomputable def envRight (T : ↥M.envAlg) : M.H →L[ℂ] M.H :=
  (M.rightMulOrbit T).extend M.envOrbit.subtypeL

/-- The defining property of `envRight` on the orbit. -/
theorem envRight_apply (T : ↥M.envAlg) {P : M.H →L[ℂ] M.H}
    (hP : P ∈ M.envAlg) :
    M.envRight T (P M.traceVector) = (P * T.1) M.traceVector := by
  have hvmem : P M.traceVector ∈ M.envOrbit :=
    M.mem_envOrbit_iff.mpr ⟨P, hP, rfl⟩
  have h := ContinuousLinearMap.extend_eq (M.rightMulOrbit T)
    M.denseRange_subtypeL_envOrbit M.isUniformInducing_subtypeL_envOrbit
    ⟨P M.traceVector, hvmem⟩
  rw [show M.envOrbit.subtypeL ⟨P M.traceVector, hvmem⟩
      = P M.traceVector from rfl] at h
  rw [show M.envRight T = (M.rightMulOrbit T).extend M.envOrbit.subtypeL
      from rfl, h]
  show (M.orbitRep ⟨P M.traceVector, hvmem⟩ * T.1) M.traceVector
      = (P * T.1) M.traceVector
  exact M.rightMul_welldef (M.orbitRep_mem _) hP T.2 (M.orbitRep_apply _)

/-- Two operators agreeing on the dense orbit are equal. -/
theorem eq_of_eq_on_orbit {F G : M.H →L[ℂ] M.H}
    (h : ∀ (P : M.H →L[ℂ] M.H), P ∈ M.envAlg →
      F (P M.traceVector) = G (P M.traceVector)) : F = G := by
  refine ContinuousLinearMap.ext fun v => ?_
  have hset : (M.envOrbit : Set M.H) ⊆ {v : M.H | F v = G v} := by
    intro v hv
    obtain ⟨P, hP, rfl⟩ := M.mem_envOrbit_iff.mp hv
    exact h P hP
  have hclosed : IsClosed {v : M.H | F v = G v} :=
    isClosed_eq F.continuous G.continuous
  have hv : v ∈ closure (M.envOrbit : Set M.H) := by
    rw [M.envOrbit_dense.closure_eq]
    trivial
  exact closure_minimal hset hclosed hv

theorem inner_traceVector (A B : M.H →L[ℂ] M.H) :
    ⟪A M.traceVector, B M.traceVector⟫_ℂ = M.traceState (star A * B) := by
  unfold traceState
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

theorem traceState_add (T S : M.H →L[ℂ] M.H) :
    M.traceState (T + S) = M.traceState T + M.traceState S := by
  unfold traceState
  rw [ContinuousLinearMap.add_apply, inner_add_right]

theorem traceState_one : M.traceState 1 = 1 := by
  unfold traceState traceVector
  rw [ContinuousLinearMap.one_apply, M.ι_inner, star_one, one_mul,
    M.τ_one]

theorem traceState_star (T : M.H →L[ℂ] M.H) :
    M.traceState (star T) = star (M.traceState T) := by
  unfold traceState
  rw [ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm]
  rfl

theorem envRight_one : M.envRight 1 = 1 := by
  refine M.eq_of_eq_on_orbit fun P hP => ?_
  rw [M.envRight_apply 1 hP]
  show (P * (1 : M.H →L[ℂ] M.H)) M.traceVector = P M.traceVector
  rw [mul_one]

theorem envRight_mul (T T' : ↥M.envAlg) :
    M.envRight (T * T') = M.envRight T' ∘L M.envRight T := by
  refine M.eq_of_eq_on_orbit fun P hP => ?_
  rw [M.envRight_apply (T * T') hP]
  show (P * (T.1 * T'.1)) M.traceVector
      = M.envRight T' (M.envRight T (P M.traceVector))
  rw [M.envRight_apply T hP, M.envRight_apply T' (mul_mem hP T.2),
    mul_assoc]

theorem envRight_add (T T' : ↥M.envAlg) :
    M.envRight (T + T') = M.envRight T + M.envRight T' := by
  refine M.eq_of_eq_on_orbit fun P hP => ?_
  rw [ContinuousLinearMap.add_apply, M.envRight_apply (T + T') hP,
    M.envRight_apply T hP, M.envRight_apply T' hP]
  show (P * (T.1 + T'.1)) M.traceVector = _
  rw [mul_add, ContinuousLinearMap.add_apply]

theorem envRight_smul (c : ℂ) (T : ↥M.envAlg) :
    M.envRight (c • T) = c • M.envRight T := by
  refine M.eq_of_eq_on_orbit fun P hP => ?_
  rw [ContinuousLinearMap.smul_apply, M.envRight_apply (c • T) hP,
    M.envRight_apply T hP]
  show (P * (c • T.1)) M.traceVector = c • (P * T.1) M.traceVector
  rw [mul_smul_comm, ContinuousLinearMap.smul_apply]

theorem envRight_star (T : ↥M.envAlg) :
    M.envRight (star T) = star (M.envRight T) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro v w
  -- both sides are continuous in each slot; check on the orbit twice
  have hcore : ∀ (P : M.H →L[ℂ] M.H), P ∈ M.envAlg →
      ∀ (Q : M.H →L[ℂ] M.H), Q ∈ M.envAlg →
      ⟪M.envRight (star T) (P M.traceVector), Q M.traceVector⟫_ℂ
        = ⟪P M.traceVector, M.envRight T (Q M.traceVector)⟫_ℂ := by
    intro P hP Q hQ
    rw [M.envRight_apply (star T) hP, M.envRight_apply T hQ]
    have h1 : (star T).1 = star T.1 := rfl
    rw [h1, M.inner_traceVector, M.inner_traceVector,
      star_mul, star_star]
    have h2 : T.1 * star P * Q = T.1 * (star P * Q) := by
      rw [mul_assoc]
    have h3 : star P * (Q * T.1) = (star P * Q) * T.1 := by
      rw [mul_assoc]
    rw [h2, h3]
    exact M.traceState_mul_comm T.2 (mul_mem (star_mem hP) hQ)
  -- extend in the first slot for fixed orbit second slot
  have hstep1 : ∀ (Q : M.H →L[ℂ] M.H), Q ∈ M.envAlg → ∀ (v : M.H),
      ⟪M.envRight (star T) v, Q M.traceVector⟫_ℂ
        = ⟪v, M.envRight T (Q M.traceVector)⟫_ℂ := by
    intro Q hQ v
    have hset : (M.envOrbit : Set M.H) ⊆ {v : M.H |
        ⟪M.envRight (star T) v, Q M.traceVector⟫_ℂ
          = ⟪v, M.envRight T (Q M.traceVector)⟫_ℂ} := by
      intro v hv
      obtain ⟨P, hP, rfl⟩ := M.mem_envOrbit_iff.mp hv
      exact hcore P hP Q hQ
    have hclosed : IsClosed {v : M.H |
        ⟪M.envRight (star T) v, Q M.traceVector⟫_ℂ
          = ⟪v, M.envRight T (Q M.traceVector)⟫_ℂ} := by
      apply isClosed_eq
      · exact (Continuous.inner ((M.envRight (star T)).continuous)
          continuous_const)
      · exact (Continuous.inner continuous_id continuous_const)
    have hv : v ∈ closure (M.envOrbit : Set M.H) := by
      rw [M.envOrbit_dense.closure_eq]
      trivial
    exact closure_minimal hset hclosed hv
  -- extend in the second slot
  have hset2 : (M.envOrbit : Set M.H) ⊆ {w : M.H |
      ⟪M.envRight (star T) v, w⟫_ℂ = ⟪v, M.envRight T w⟫_ℂ} := by
    intro w hw
    obtain ⟨Q, hQ, rfl⟩ := M.mem_envOrbit_iff.mp hw
    exact hstep1 Q hQ v
  have hclosed2 : IsClosed {w : M.H |
      ⟪M.envRight (star T) v, w⟫_ℂ = ⟪v, M.envRight T w⟫_ℂ} := by
    apply isClosed_eq
    · exact Continuous.inner continuous_const continuous_id
    · exact Continuous.inner continuous_const (M.envRight T).continuous
  have hw : w ∈ closure (M.envOrbit : Set M.H) := by
    rw [M.envOrbit_dense.closure_eq]
    trivial
  exact closure_minimal hset2 hclosed2 hw

theorem left_envRight_commute (S T : ↥M.envAlg) :
    S.1 * M.envRight T = M.envRight T * S.1 := by
  refine M.eq_of_eq_on_orbit fun P hP => ?_
  show S.1 (M.envRight T (P M.traceVector))
      = M.envRight T (S.1 (P M.traceVector))
  rw [M.envRight_apply T hP,
    show S.1 (P M.traceVector) = (S.1 * P) M.traceVector from rfl,
    M.envRight_apply T (mul_mem S.2 hP),
    show S.1 ((P * T.1) M.traceVector)
      = (S.1 * (P * T.1)) M.traceVector from rfl,
    mul_assoc]

/-- **The envelope model** (Stage B, WP-B4): the C*-envelope of the
left representation as a standard tracial algebra on the same GNS
space. Its elements are norm limits of left multiplications, its trace
is the trace-vector state (tracial by density), its `ι` is evaluation
at the trace vector (dense by `M.ι_dense`), its left representation is
the subalgebra inclusion, and its right representation is the extended
right regular representation `envRight`. Continuous functional
calculus operates on its elements through `B(L²(M))` with `cfc_mem`
keeping outputs in the envelope — the algebra in which the
resolver-corner construction (nodes 1.2.5.x) runs. -/
noncomputable def envModel : StdTracialAlgebra.{u} where
  A := ↥M.envAlg
  τ :=
    { toFun := fun T => M.traceState T.1
      map_add' := fun T T' => M.traceState_add T.1 T'.1
      map_smul' := fun c T => by
        simpa using M.traceState_smul c T.1 }
  τ_one := M.traceState_one
  τ_mul_comm := fun T S => M.traceState_mul_comm T.2 S.2
  τ_star := fun T => M.traceState_star T.1
  H := M.H
  ι :=
    { toFun := fun T => T.1 M.traceVector
      map_add' := fun T T' => rfl
      map_smul' := fun c T => rfl }
  ι_dense := by
    have h : Set.range (fun T : ↥M.envAlg => T.1 M.traceVector)
        = (M.envOrbit : Set M.H) := by
      ext v
      constructor
      · rintro ⟨T, rfl⟩
        exact M.mem_envOrbit_iff.mpr ⟨T.1, T.2, rfl⟩
      · intro hv
        obtain ⟨P, hP, rfl⟩ := M.mem_envOrbit_iff.mp hv
        exact ⟨⟨P, hP⟩, rfl⟩
    show Dense (Set.range fun T : ↥M.envAlg => T.1 M.traceVector)
    rw [h]
    exact M.envOrbit_dense
  ι_inner := fun T S => M.inner_traceVector T.1 S.1
  L := M.envAlg.subtype
  R :=
    { toFun := fun P => M.envRight (MulOpposite.unop P)
      map_one' := M.envRight_one
      map_mul' := fun P Q => by
        have h : MulOpposite.unop (P * Q)
            = MulOpposite.unop Q * MulOpposite.unop P := rfl
        rw [h, M.envRight_mul]
        rfl
      map_zero' := by
        have h0 : (MulOpposite.unop (0 : (↥M.envAlg)ᵐᵒᵖ)) = 0 := rfl
        have h1 : M.envRight 0 = 0 := by
          have := M.envRight_smul 0 0
          simpa using this
        rw [h0, h1]
      map_add' := fun P Q => by
        have h : MulOpposite.unop (P + Q)
            = MulOpposite.unop P + MulOpposite.unop Q := rfl
        rw [h, M.envRight_add]
      commutes' := fun c => by
        have h : MulOpposite.unop ((algebraMap ℂ (↥M.envAlg)ᵐᵒᵖ) c)
            = algebraMap ℂ ↥M.envAlg c := rfl
        rw [h, Algebra.algebraMap_eq_smul_one, M.envRight_smul,
          M.envRight_one, Algebra.algebraMap_eq_smul_one]
      map_star' := fun P => by
        have h : MulOpposite.unop (star P)
            = star (MulOpposite.unop P) := rfl
        rw [h, M.envRight_star] }
  L_apply := fun T S => rfl
  R_apply := fun T S => by
    show M.envRight T (S.1 M.traceVector) = (S * T).1 M.traceVector
    exact M.envRight_apply T S.2
  LR_commute := fun T S => by
    show Commute (T.1 : M.H →L[ℂ] M.H) (M.envRight S)
    exact M.left_envRight_commute T S

/-- The envelope trace extends the original trace through the left
representation. -/
theorem envModel_τ_L (a : M.A) :
    M.envModel.τ ⟨M.L a, M.L_mem_envAlg a⟩ = M.τ a :=
  M.traceState_L a

end StdTracialAlgebra

end CommutingRepetition
