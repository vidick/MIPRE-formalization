/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/SubModel.lean
-/
/-
# Standard tracial models from closed tracial subalgebras of `B(L²(M))`

`Tracial/CStarLayer.lean` builds the envelope model `envModel M` from the norm
closure of the left representation. Its construction uses only three
properties of the closed star subalgebra: it contains `L(M.A)`, it is
norm-closed (for `cfc_mem`), and the trace-vector state is tracial on it.
This file abstracts those three properties into `TracialSub M` and repeats
the construction verbatim for any such subalgebra (`TracialSub.model`); the
concrete von Neumann model of `VN/ConcreteVN.lean` — the commutant of the
right action, which is what the entropic resolver arena (node 1.2.6) needs
— is an instance. Infrastructure only; no manuscript statement.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Tracial.CStarLayer

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace StdTracialAlgebra

open scoped InnerProductSpace

universe u

variable (M : StdTracialAlgebra.{u})

/-- A closed star subalgebra of `B(L²(M))` containing the left representation
on which the trace-vector state is tracial. -/
structure TracialSub : Type u where
  S : StarSubalgebra ℂ (M.H →L[ℂ] M.H)
  isClosed : IsClosed (S : Set (M.H →L[ℂ] M.H))
  L_mem : ∀ a : M.A, M.L a ∈ S
  tracial : ∀ {T U : M.H →L[ℂ] M.H}, T ∈ S → U ∈ S →
    M.traceState (T * U) = M.traceState (U * T)

namespace TracialSub

variable {M} (D : TracialSub M)

theorem smul_one_mem (c : ℂ) : c • (1 : M.H →L[ℂ] M.H) ∈ D.S :=
  SMulMemClass.smul_mem c (one_mem D.S)

/-- **The trace inequality** (the boundedness engine for the right
regular representation): for `U, T` in the envelope,
`‖(U T) Ω‖ ≤ ‖T‖ · ‖U Ω‖`. Traciality moves the `T`-square to the
other side (`φ(T* U*U T) = φ(U*U · TT*)`), the C*-gap
`‖TT*‖·1 − TT*` has a `CFC.sqrt` in the envelope (`cfc_mem` on the
closed star subalgebra), and positivity of the state on envelope
squares finishes. -/
theorem norm_mul_traceVector_le {U T : M.H →L[ℂ] M.H}
    (hU : U ∈ D.S) (hT : T ∈ D.S) :
    ‖(U * T) M.traceVector‖ ≤ ‖T‖ * ‖U M.traceVector‖ := by
  have hTstar : star T ∈ D.S := star_mem hT
  have hUstar : star U ∈ D.S := star_mem hU
  set Y : M.H →L[ℂ] M.H := T * star T with hYdef
  have hY : Y ∈ D.S := mul_mem hT hTstar
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
  have hZmem : Z ∈ D.S := by
    rw [hZdef]
    exact sub_mem (D.smul_one_mem _) hY
  set W : M.H →L[ℂ] M.H := CFC.sqrt Z with hWdef
  have hWpos : (0 : M.H →L[ℂ] M.H) ≤ W := CFC.sqrt_nonneg Z
  have hWsa : IsSelfAdjoint W := IsSelfAdjoint.of_nonneg hWpos
  have hWsq : W * W = Z := CFC.sqrt_mul_sqrt_self Z hZpos
  have hWmem : W ∈ D.S := by
    rw [hWdef, CFC.sqrt_eq_real_sqrt Z hZpos,
      cfcₙ_eq_cfc (hf0 := by simp)]
    exact cfc_mem (𝕜' := ℂ) (hs := D.isClosed) Real.sqrt hZmem
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
      D.tracial hTstar (mul_mem (mul_mem hUstar hU) hT)
    rw [h1, hYdef, mul_assoc]
  -- the gap term is nonnegative: 0 ≤ re φ(U*U Z)
  have hgap : 0 ≤ (M.traceState (star U * U * Z)).re := by
    have h1 : star U * U * Z = star U * U * W * W := by
      rw [← hWsq, mul_assoc (star U * U) W W]
    have h2 : M.traceState (star U * U * W * W)
        = M.traceState (W * (star U * U * W)) :=
      D.tracial (mul_mem (mul_mem hUstar hU) hWmem) hWmem
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
noncomputable def orbit : Submodule ℂ M.H :=
  (Subalgebra.toSubmodule D.S.toSubalgebra).map M.evalΩ

theorem mem_orbit_iff {v : M.H} :
    v ∈ D.orbit ↔ ∃ T ∈ D.S, T M.traceVector = v := by
  unfold orbit
  simp only [Submodule.mem_map, Subalgebra.mem_toSubmodule]
  rfl

theorem range_ι_subset_orbit :
    Set.range M.ι ⊆ (D.orbit : Set M.H) := by
  rintro _ ⟨a, rfl⟩
  refine (D.mem_orbit_iff).mpr ⟨M.L a, D.L_mem a, ?_⟩
  show M.L a (M.ι 1) = M.ι a
  rw [M.L_apply, mul_one]

theorem orbit_dense : Dense (D.orbit : Set M.H) :=
  M.ι_dense.mono D.range_ι_subset_orbit

/-- Well-definedness of right multiplication on the orbit: if two
envelope elements agree at the trace vector, so do their right
translates (the trace inequality applied to the difference). -/
theorem rightMul_welldef {P Q T : M.H →L[ℂ] M.H}
    (hP : P ∈ D.S) (hQ : Q ∈ D.S) (hT : T ∈ D.S)
    (hPQ : P M.traceVector = Q M.traceVector) :
    (P * T) M.traceVector = (Q * T) M.traceVector := by
  have hdiff : ((P - Q) * T) M.traceVector = 0 := by
    have hb := D.norm_mul_traceVector_le (sub_mem hP hQ) hT
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
noncomputable def orbitRep (v : ↥D.orbit) : M.H →L[ℂ] M.H :=
  (D.mem_orbit_iff.mp v.2).choose

theorem orbitRep_mem (v : ↥D.orbit) : D.orbitRep v ∈ D.S :=
  (D.mem_orbit_iff.mp v.2).choose_spec.1

theorem orbitRep_apply (v : ↥D.orbit) :
    D.orbitRep v M.traceVector = v.1 :=
  (D.mem_orbit_iff.mp v.2).choose_spec.2

/-- Right translation on the orbit: `S Ω ↦ (S T) Ω`, well-defined by
`rightMul_welldef` and bounded by the trace inequality. -/
noncomputable def rightMulOrbit (T : ↥D.S) :
    ↥D.orbit →L[ℂ] M.H := by
  refine LinearMap.mkContinuous
    { toFun := fun v => (D.orbitRep v * T.1) M.traceVector
      map_add' := ?_
      map_smul' := ?_ } ‖T.1‖ ?_
  · intro v w
    have h1 : (D.orbitRep (v + w) * T.1) M.traceVector
        = ((D.orbitRep v + D.orbitRep w) * T.1) M.traceVector := by
      refine D.rightMul_welldef (D.orbitRep_mem _)
        (add_mem (D.orbitRep_mem v) (D.orbitRep_mem w)) T.2 ?_
      rw [D.orbitRep_apply, ContinuousLinearMap.add_apply,
        D.orbitRep_apply, D.orbitRep_apply]
      rfl
    rw [h1, add_mul, ContinuousLinearMap.add_apply]
  · intro c v
    have h1 : (D.orbitRep (c • v) * T.1) M.traceVector
        = ((c • D.orbitRep v) * T.1) M.traceVector := by
      refine D.rightMul_welldef (D.orbitRep_mem _)
        (SMulMemClass.smul_mem c (D.orbitRep_mem v)) T.2 ?_
      rw [D.orbitRep_apply, ContinuousLinearMap.smul_apply,
        D.orbitRep_apply]
      rfl
    rw [h1, smul_mul_assoc, ContinuousLinearMap.smul_apply]
    rfl
  · intro v
    calc ‖(D.orbitRep v * T.1) M.traceVector‖
        ≤ ‖T.1‖ * ‖D.orbitRep v M.traceVector‖ :=
          D.norm_mul_traceVector_le (D.orbitRep_mem v) T.2
      _ = ‖T.1‖ * ‖v‖ := by rw [D.orbitRep_apply]; rfl

theorem denseRange_subtypeL_orbit :
    DenseRange (D.orbit.subtypeL) := by
  have h : Set.range (D.orbit.subtypeL) = (D.orbit : Set M.H) :=
    Subtype.range_coe
  rw [DenseRange, h]
  exact D.orbit_dense

theorem isUniformInducing_subtypeL_orbit :
    IsUniformInducing (D.orbit.subtypeL) := by
  have hiso : Isometry (D.orbit.subtypeL) :=
    (AddMonoidHomClass.isometry_iff_norm _).mpr (fun _ => rfl)
  exact hiso.isUniformInducing

/-- **The right regular representation of the envelope**: the unique
bounded extension of `S Ω ↦ (S T) Ω` along the dense orbit. -/
noncomputable def right (T : ↥D.S) : M.H →L[ℂ] M.H :=
  (D.rightMulOrbit T).extend D.orbit.subtypeL

/-- The defining property of `envRight` on the orbit. -/
theorem right_apply (T : ↥D.S) {P : M.H →L[ℂ] M.H}
    (hP : P ∈ D.S) :
    D.right T (P M.traceVector) = (P * T.1) M.traceVector := by
  have hvmem : P M.traceVector ∈ D.orbit :=
    D.mem_orbit_iff.mpr ⟨P, hP, rfl⟩
  have h := ContinuousLinearMap.extend_eq (D.rightMulOrbit T)
    D.denseRange_subtypeL_orbit D.isUniformInducing_subtypeL_orbit
    ⟨P M.traceVector, hvmem⟩
  rw [show D.orbit.subtypeL ⟨P M.traceVector, hvmem⟩
      = P M.traceVector from rfl] at h
  rw [show D.right T = (D.rightMulOrbit T).extend D.orbit.subtypeL
      from rfl, h]
  show (D.orbitRep ⟨P M.traceVector, hvmem⟩ * T.1) M.traceVector
      = (P * T.1) M.traceVector
  exact D.rightMul_welldef (D.orbitRep_mem _) hP T.2 (D.orbitRep_apply _)

/-- Two operators agreeing on the dense orbit are equal. -/
theorem eq_of_eq_on_orbit {F G : M.H →L[ℂ] M.H}
    (h : ∀ (P : M.H →L[ℂ] M.H), P ∈ D.S →
      F (P M.traceVector) = G (P M.traceVector)) : F = G := by
  refine ContinuousLinearMap.ext fun v => ?_
  have hset : (D.orbit : Set M.H) ⊆ {v : M.H | F v = G v} := by
    intro v hv
    obtain ⟨P, hP, rfl⟩ := D.mem_orbit_iff.mp hv
    exact h P hP
  have hclosed : IsClosed {v : M.H | F v = G v} :=
    isClosed_eq F.continuous G.continuous
  have hv : v ∈ closure (D.orbit : Set M.H) := by
    rw [D.orbit_dense.closure_eq]
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

theorem right_one : D.right 1 = 1 := by
  refine D.eq_of_eq_on_orbit fun P hP => ?_
  rw [D.right_apply 1 hP]
  show (P * (1 : M.H →L[ℂ] M.H)) M.traceVector = P M.traceVector
  rw [mul_one]

theorem right_mul (T T' : ↥D.S) :
    D.right (T * T') = D.right T' ∘L D.right T := by
  refine D.eq_of_eq_on_orbit fun P hP => ?_
  rw [D.right_apply (T * T') hP]
  show (P * (T.1 * T'.1)) M.traceVector
      = D.right T' (D.right T (P M.traceVector))
  rw [D.right_apply T hP, D.right_apply T' (mul_mem hP T.2),
    mul_assoc]

theorem right_add (T T' : ↥D.S) :
    D.right (T + T') = D.right T + D.right T' := by
  refine D.eq_of_eq_on_orbit fun P hP => ?_
  rw [ContinuousLinearMap.add_apply, D.right_apply (T + T') hP,
    D.right_apply T hP, D.right_apply T' hP]
  show (P * (T.1 + T'.1)) M.traceVector = _
  rw [mul_add, ContinuousLinearMap.add_apply]

theorem right_smul (c : ℂ) (T : ↥D.S) :
    D.right (c • T) = c • D.right T := by
  refine D.eq_of_eq_on_orbit fun P hP => ?_
  rw [ContinuousLinearMap.smul_apply, D.right_apply (c • T) hP,
    D.right_apply T hP]
  show (P * (c • T.1)) M.traceVector = c • (P * T.1) M.traceVector
  rw [mul_smul_comm, ContinuousLinearMap.smul_apply]

theorem right_star (T : ↥D.S) :
    D.right (star T) = star (D.right T) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro v w
  -- both sides are continuous in each slot; check on the orbit twice
  have hcore : ∀ (P : M.H →L[ℂ] M.H), P ∈ D.S →
      ∀ (Q : M.H →L[ℂ] M.H), Q ∈ D.S →
      ⟪D.right (star T) (P M.traceVector), Q M.traceVector⟫_ℂ
        = ⟪P M.traceVector, D.right T (Q M.traceVector)⟫_ℂ := by
    intro P hP Q hQ
    rw [D.right_apply (star T) hP, D.right_apply T hQ]
    have h1 : (star T).1 = star T.1 := rfl
    rw [h1, M.inner_traceVector, M.inner_traceVector,
      star_mul, star_star]
    have h2 : T.1 * star P * Q = T.1 * (star P * Q) := by
      rw [mul_assoc]
    have h3 : star P * (Q * T.1) = (star P * Q) * T.1 := by
      rw [mul_assoc]
    rw [h2, h3]
    exact D.tracial T.2 (mul_mem (star_mem hP) hQ)
  -- extend in the first slot for fixed orbit second slot
  have hstep1 : ∀ (Q : M.H →L[ℂ] M.H), Q ∈ D.S → ∀ (v : M.H),
      ⟪D.right (star T) v, Q M.traceVector⟫_ℂ
        = ⟪v, D.right T (Q M.traceVector)⟫_ℂ := by
    intro Q hQ v
    have hset : (D.orbit : Set M.H) ⊆ {v : M.H |
        ⟪D.right (star T) v, Q M.traceVector⟫_ℂ
          = ⟪v, D.right T (Q M.traceVector)⟫_ℂ} := by
      intro v hv
      obtain ⟨P, hP, rfl⟩ := D.mem_orbit_iff.mp hv
      exact hcore P hP Q hQ
    have hclosed : IsClosed {v : M.H |
        ⟪D.right (star T) v, Q M.traceVector⟫_ℂ
          = ⟪v, D.right T (Q M.traceVector)⟫_ℂ} := by
      apply isClosed_eq
      · exact (Continuous.inner ((D.right (star T)).continuous)
          continuous_const)
      · exact (Continuous.inner continuous_id continuous_const)
    have hv : v ∈ closure (D.orbit : Set M.H) := by
      rw [D.orbit_dense.closure_eq]
      trivial
    exact closure_minimal hset hclosed hv
  -- extend in the second slot
  have hset2 : (D.orbit : Set M.H) ⊆ {w : M.H |
      ⟪D.right (star T) v, w⟫_ℂ = ⟪v, D.right T w⟫_ℂ} := by
    intro w hw
    obtain ⟨Q, hQ, rfl⟩ := D.mem_orbit_iff.mp hw
    exact hstep1 Q hQ v
  have hclosed2 : IsClosed {w : M.H |
      ⟪D.right (star T) v, w⟫_ℂ = ⟪v, D.right T w⟫_ℂ} := by
    apply isClosed_eq
    · exact Continuous.inner continuous_const continuous_id
    · exact Continuous.inner continuous_const (D.right T).continuous
  have hw : w ∈ closure (D.orbit : Set M.H) := by
    rw [D.orbit_dense.closure_eq]
    trivial
  exact closure_minimal hset2 hclosed2 hw

theorem left_right_commute (S T : ↥D.S) :
    S.1 * D.right T = D.right T * S.1 := by
  refine D.eq_of_eq_on_orbit fun P hP => ?_
  show S.1 (D.right T (P M.traceVector))
      = D.right T (S.1 (P M.traceVector))
  rw [D.right_apply T hP,
    show S.1 (P M.traceVector) = (S.1 * P) M.traceVector from rfl,
    D.right_apply T (mul_mem S.2 hP),
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
noncomputable def model : StdTracialAlgebra.{u} where
  A := ↥D.S
  τ :=
    { toFun := fun T => M.traceState T.1
      map_add' := fun T T' => M.traceState_add T.1 T'.1
      map_smul' := fun c T => by
        simpa using M.traceState_smul c T.1 }
  τ_one := M.traceState_one
  τ_mul_comm := fun T S => D.tracial T.2 S.2
  τ_star := fun T => M.traceState_star T.1
  H := M.H
  ι :=
    { toFun := fun T => T.1 M.traceVector
      map_add' := fun T T' => rfl
      map_smul' := fun c T => rfl }
  ι_dense := by
    have h : Set.range (fun T : ↥D.S => T.1 M.traceVector)
        = (D.orbit : Set M.H) := by
      ext v
      constructor
      · rintro ⟨T, rfl⟩
        exact D.mem_orbit_iff.mpr ⟨T.1, T.2, rfl⟩
      · intro hv
        obtain ⟨P, hP, rfl⟩ := D.mem_orbit_iff.mp hv
        exact ⟨⟨P, hP⟩, rfl⟩
    show Dense (Set.range fun T : ↥D.S => T.1 M.traceVector)
    rw [h]
    exact D.orbit_dense
  ι_inner := fun T S => M.inner_traceVector T.1 S.1
  L := D.S.subtype
  R :=
    { toFun := fun P => D.right (MulOpposite.unop P)
      map_one' := D.right_one
      map_mul' := fun P Q => by
        have h : MulOpposite.unop (P * Q)
            = MulOpposite.unop Q * MulOpposite.unop P := rfl
        rw [h, D.right_mul]
        rfl
      map_zero' := by
        have h0 : (MulOpposite.unop (0 : (↥D.S)ᵐᵒᵖ)) = 0 := rfl
        have h1 : D.right 0 = 0 := by
          have := D.right_smul 0 0
          simpa using this
        rw [h0, h1]
      map_add' := fun P Q => by
        have h : MulOpposite.unop (P + Q)
            = MulOpposite.unop P + MulOpposite.unop Q := rfl
        rw [h, D.right_add]
      commutes' := fun c => by
        have h : MulOpposite.unop ((algebraMap ℂ (↥D.S)ᵐᵒᵖ) c)
            = algebraMap ℂ ↥D.S c := rfl
        rw [h, Algebra.algebraMap_eq_smul_one, D.right_smul,
          D.right_one, Algebra.algebraMap_eq_smul_one]
      map_star' := fun P => by
        have h : MulOpposite.unop (star P)
            = star (MulOpposite.unop P) := rfl
        rw [h, D.right_star] }
  L_apply := fun T S => rfl
  R_apply := fun T S => by
    show D.right T (S.1 M.traceVector) = (S * T).1 M.traceVector
    exact D.right_apply T S.2
  LR_commute := fun T S => by
    show Commute (T.1 : M.H →L[ℂ] M.H) (D.right S)
    exact D.left_right_commute T S


theorem model_τ (T : ↥D.S) : D.model.τ T = M.traceState T.1 := rfl

theorem model_ι (T : ↥D.S) : D.model.ι T = T.1 M.traceVector := rfl

theorem model_L (T : ↥D.S) : D.model.L T = T.1 := rfl

theorem model_A : D.model.A = ↥D.S := rfl

theorem model_H : D.model.H = M.H := rfl

/-- The model's trace extends the original trace through the left representation. -/
theorem model_τ_L (a : M.A) : D.model.τ ⟨M.L a, D.L_mem a⟩ = M.τ a :=
  M.traceState_L a

end TracialSub

end StdTracialAlgebra

end CommutingRepetition
