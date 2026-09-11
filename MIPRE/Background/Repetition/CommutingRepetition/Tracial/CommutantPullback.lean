/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Tracial/CommutantPullback.lean
-/
/-
# Commutant pullback through the antiunitary `J` (node 1.1.4, proof layer)

The consumed form of node 1.1.4 (`TraciallyEmbeddableCorrelation.exists_tracialStrategy`,
Tracial/Reduction.lean) asks for a `TracialStrategy` realizing a correlation in
commutant form `⟪ισ, L(E) G ισ⟫` with Bob's effects `G` in the commutant of the
left action. The manuscript pulls `G` back through the commutation theorem
`L(M)′ = R(M)″`. Here the pullback is elementary: the antiunitary
`J : ι a ↦ ι a*` of `VN/ConcreteVN.lean` satisfies `J L(a) J = R(a*)`, so
`F := J G J` lies in the commutant `R(M)′ = vnAlg M` of the right action, on
which the trace-vector state is tracial, and

    φ(L(σ)* L(E) L(σ) · JGJ) = ⟪ισ, L(E) G ισ⟫

by `J x Ω = x* Ω` on `R(M)′` and the antiunitarity of `J`. The tracial
strategy lives in `vnModel M` with density `L(σ)`, Alice's effects `L(E)` and
Bob's effects `J G J`. No bicommutant theorem is used. Infrastructure only;
no manuscript statement.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.ConcreteVN
import MIPRE.Background.Repetition.CommutingRepetition.Tracial.Density
import MIPRE.Background.Repetition.CommutingRepetition.Tracial.Strategy

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace StdTracialAlgebra

open scoped InnerProductSpace BigOperators

universe u

variable (M : StdTracialAlgebra.{u})

/-! ## More on `J` -/

theorem J_traceVector : M.J M.traceVector = M.traceVector := by
  unfold traceVector
  rw [M.J_ι, star_one]

theorem norm_J (v : M.H) : ‖M.J v‖ = ‖v‖ := by
  have h : ⟪M.J v, M.J v⟫_ℂ = ⟪v, v⟫_ℂ := M.inner_J_J v v
  have h1 := congrArg Complex.re h
  rw [← RCLike.re_to_complex, ← RCLike.re_to_complex, inner_self_eq_norm_sq,
    inner_self_eq_norm_sq] at h1
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1

/-- `J L(a) J = R(a*)`. -/
theorem J_L_J (a : M.A) (v : M.H) : M.J (M.L a (M.J v)) = M.Rop (star a) v := by
  refine M.ι_induction (p := fun v => M.J (M.L a (M.J v)) = M.Rop (star a) v) ?_ (fun b => ?_) v
  · exact isClosed_eq (M.J.continuous.comp ((M.L a).continuous.comp M.J.continuous))
      (M.Rop (star a)).continuous
  · rw [M.J_ι, M.L_apply, M.J_ι, star_mul, star_star]
    unfold Rop
    rw [M.R_apply]

/-- Conjugation by `J`, `G ↦ J G J`, as a (linear) bounded operator. -/
noncomputable def conjJ (G : M.H →L[ℂ] M.H) : M.H →L[ℂ] M.H :=
  LinearMap.mkContinuous
    { toFun := fun v => M.J (G (M.J v))
      map_add' := fun v w => by rw [map_add, map_add, map_add]
      map_smul' := fun c v => by
        simp only [RingHom.id_apply]
        rw [map_smulₛₗ, map_smul, map_smulₛₗ]
        show (starRingEnd ℂ) ((starRingEnd ℂ) c) • M.J (G (M.J v)) = c • M.J (G (M.J v))
        rw [Complex.conj_conj] } ‖G‖ fun v => by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [M.norm_J]
    calc ‖G (M.J v)‖ ≤ ‖G‖ * ‖M.J v‖ := G.le_opNorm _
      _ = ‖G‖ * ‖v‖ := by rw [M.norm_J]

theorem conjJ_apply (G : M.H →L[ℂ] M.H) (v : M.H) : M.conjJ G v = M.J (G (M.J v)) := rfl

theorem conjJ_one : M.conjJ 1 = 1 := by
  ext v
  rw [conjJ_apply, ContinuousLinearMap.one_apply, ContinuousLinearMap.one_apply, M.J_J]

theorem conjJ_sum {ι : Type*} (s : Finset ι) (G : ι → M.H →L[ℂ] M.H) :
    M.conjJ (∑ i ∈ s, G i) = ∑ i ∈ s, M.conjJ (G i) := by
  ext v
  rw [conjJ_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply, map_sum]
  rfl

/-- `J G J` commutes with the right action when `G` commutes with the left action. -/
theorem conjJ_mem_vnAlg {G : M.H →L[ℂ] M.H} (hG : ∀ m : M.A, Commute G (M.L m)) :
    M.conjJ G ∈ M.vnAlg := by
  rw [M.mem_vnAlg_iff]
  intro a
  ext v
  rw [mulA, mulA, conjJ_apply, conjJ_apply]
  have e1 : M.Rop a (M.J (G (M.J v))) = M.J (M.L (star a) (G (M.J v))) := by
    have := M.J_L_J (star a) (M.J (G (M.J v)))
    rw [star_star, M.J_J] at this
    exact this.symm
  have e2 : M.Rop a v = M.J (M.L (star a) (M.J v)) := by
    have := M.J_L_J (star a) v
    rw [star_star] at this
    exact this.symm
  rw [e1, e2, M.J_J]
  congr 1
  have := hG (star a)
  rw [Commute, SemiconjBy] at this
  exact (congrArg (fun T => T (M.J v)) this).symm

/-- `J G J` is positive when `G` is. -/
theorem conjJ_nonneg {G : M.H →L[ℂ] M.H} (hG : G.IsPositive) : 0 ≤ M.conjJ G := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive]
  refine ⟨fun v w => ?_, fun v => ?_⟩
  · -- symmetric
    show ⟪M.J (G (M.J v)), w⟫_ℂ = ⟪v, M.J (G (M.J w))⟫_ℂ
    have hsym : ∀ x y, ⟪G x, y⟫_ℂ = ⟪x, G y⟫_ℂ := fun x y => hG.1 x y
    rw [M.inner_J_left, ← hsym (M.J w) (M.J v)]
    have e : ⟪G (M.J w), M.J v⟫_ℂ = ⟪v, M.J (G (M.J w))⟫_ℂ := by
      rw [← M.inner_J_J (M.J (G (M.J w))) v, M.J_J]
    exact e
  · show 0 ≤ (⟪M.J (G (M.J v)), v⟫_ℂ).re
    rw [M.inner_J_left]
    exact hG.re_inner_nonneg_right (M.J v)

/-- **The pullback identity**: `φ(L(σ)* L(E) L(σ) · JGJ) = ⟪ισ, L(E) G ισ⟫` for `G` in the
commutant of the left action. -/
theorem traceState_conjJ (σ E : M.A) {G : M.H →L[ℂ] M.H} (hsa : IsSelfAdjoint G)
    (hG : ∀ m : M.A, Commute G (M.L m)) :
    M.traceState (M.L (star σ) * M.L E * M.L σ * M.conjJ G)
      = ⟪M.ι σ, M.L E (G (M.ι σ))⟫_ℂ := by
  set X : M.H →L[ℂ] M.H := M.L (star σ) * M.L E * M.L σ with hX
  have hXmem : X ∈ M.vnAlg :=
    mul_mem (mul_mem (M.L_mem_vnAlg _) (M.L_mem_vnAlg _)) (M.L_mem_vnAlg _)
  -- `X` is in the left representation, so it commutes with `G`
  have hXG : X * G = G * X := by
    have h1 := hG (star σ); have h2 := hG E; have h3 := hG σ
    rw [Commute, SemiconjBy] at h1 h2 h3
    rw [hX, mul_assoc, mul_assoc, ← h3, ← mul_assoc (M.L E), ← h2, mul_assoc, ← mul_assoc,
      ← h1, mul_assoc, mul_assoc]
  unfold traceState
  -- ⟪Ω, X (J (G Ω))⟫ = ⟪X* Ω, J (G Ω)⟫ = ⟪J (X Ω), J (G Ω)⟫ = ⟪G Ω, X Ω⟫
  rw [mulA, conjJ_apply, M.J_traceVector,
    ← ContinuousLinearMap.adjoint_inner_left X (M.J (G M.traceVector)) M.traceVector,
    ← ContinuousLinearMap.star_eq_adjoint, ← M.J_apply_traceVector hXmem, M.inner_J_J]
  -- ⟪G Ω, X Ω⟫ = ⟪Ω, G X Ω⟫ = ⟪Ω, X G Ω⟫
  have hGa : ⟪G M.traceVector, X M.traceVector⟫_ℂ
      = ⟪M.traceVector, G (X M.traceVector)⟫_ℂ := by
    conv_rhs => rw [← ContinuousLinearMap.adjoint_inner_left G (X M.traceVector) M.traceVector,
      ← ContinuousLinearMap.star_eq_adjoint, hsa.star_eq]
  have hσ : M.L σ M.traceVector = M.ι σ := by
    unfold traceVector; rw [M.L_apply, mul_one]
  have hc := hG σ
  rw [Commute, SemiconjBy] at hc
  rw [hGa, ← mulA, ← hXG, mulA, hX, mulA, mulA, map_star, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, hσ, ← mulA M (M.L σ) G, ← hc, mulA, hσ]

/-! ## Positivity in `vnAlg` -/

theorem sqrt_mem_vnAlg {P : M.H →L[ℂ] M.H} (hP0 : 0 ≤ P) (hP : P ∈ M.vnAlg) :
    CFC.sqrt P ∈ M.vnAlg := by
  rw [CFC.sqrt_eq_real_sqrt _ hP0, cfcₙ_eq_cfc (hf0 := by simp)]
  exact cfc_mem (𝕜' := ℂ) (hs := M.isClosed_vnAlg) Real.sqrt hP

/-- A positive operator in `vnAlg` is algebraically positive there (a single square). -/
theorem isPosElem_of_nonneg {T : M.H →L[ℂ] M.H} (hT0 : 0 ≤ T) (hT : T ∈ M.vnAlg) :
    IsPosElem (⟨T, hT⟩ : ↥M.vnAlg) := by
  refine ⟨1, fun _ => ⟨CFC.sqrt T, M.sqrt_mem_vnAlg hT0 hT⟩, ?_⟩
  rw [Fin.sum_univ_one]
  apply Subtype.ext
  show T = star (CFC.sqrt T) * CFC.sqrt T
  have hsa : IsSelfAdjoint (CFC.sqrt T) := by
    have h0 : 0 ≤ CFC.sqrt T := CFC.sqrt_nonneg _
    exact IsSelfAdjoint.of_nonneg h0
  rw [hsa.star_eq, CFC.sqrt_mul_sqrt_self _ hT0]

/-- `L a` as an element of `vnAlg M`. -/
noncomputable def Lv (a : M.A) : ↥M.vnAlg := ⟨M.L a, M.L_mem_vnAlg a⟩

theorem Lv_val (a : M.A) : (M.Lv a).1 = M.L a := rfl

theorem Lv_mul (a b : M.A) : M.Lv (a * b) = M.Lv a * M.Lv b := Subtype.ext (map_mul M.L a b)

theorem Lv_star (a : M.A) : M.Lv (star a) = star (M.Lv a) := Subtype.ext (map_star M.L a)

theorem Lv_one : M.Lv 1 = 1 := Subtype.ext (map_one M.L)

theorem coe_sum_vnAlg {ι : Type*} (s : Finset ι) (f : ι → ↥M.vnAlg) :
    ((∑ x ∈ s, f x : ↥M.vnAlg) : M.H →L[ℂ] M.H) = ∑ x ∈ s, (f x : M.H →L[ℂ] M.H) :=
  map_sum M.vnAlg.subtype f s

theorem Lv_sum {ι : Type*} (s : Finset ι) (f : ι → M.A) :
    M.Lv (∑ x ∈ s, f x) = ∑ x ∈ s, M.Lv (f x) := by
  apply Subtype.ext
  rw [Lv_val, map_sum, coe_sum_vnAlg]
  rfl

theorem isPosElem_Lv {a : M.A} (ha : IsPosElem a) : IsPosElem (M.Lv a) := by
  obtain ⟨k, c, rfl⟩ := ha
  refine ⟨k, fun i => M.Lv (c i), ?_⟩
  rw [Lv_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Lv_mul, Lv_star]

end StdTracialAlgebra

/-! ## The pulled-back tracial strategy -/

namespace TraciallyEmbeddableCorrelation

open StdTracialAlgebra
open scoped InnerProductSpace BigOperators

variable {Xc Ac : Type} [Fintype Xc] [Fintype Ac] (q : TraciallyEmbeddableCorrelation Xc Ac)

/-- Bob's pulled-back effect `J G J` in `vnAlg`. -/
noncomputable def Fv (y : Xc) (b : Ac) : ↥q.M.vnAlg :=
  ⟨q.M.conjJ (q.G y b), q.M.conjJ_mem_vnAlg (q.G_commutant y b)⟩

/-- **The tracial strategy realizing a commutant-form correlation** (node 1.1.4): the
model `vnModel M`, density `L(σ)`, Alice's effects `L(E)`, Bob's effects `J G J`. -/
noncomputable def pullback : TracialStrategy.{0} Xc Xc Ac Ac where
  M := q.M.vnModel
  σ := q.M.Lv q.σ
  σ_pos := q.M.isPosElem_Lv q.σ_pos
  σ_normalized := by
    show q.M.traceState (star (q.M.Lv q.σ) * q.M.Lv q.σ).1 = 1
    rw [← Lv_star, ← Lv_mul, Lv_val, q.M.traceState_L, q.σ_normalized]
  E x a := q.M.Lv (q.E x a)
  F y b := q.Fv y b
  E_pos x a := q.M.isPosElem_Lv (q.E_pos x a)
  F_pos y b := q.M.isPosElem_of_nonneg (q.M.conjJ_nonneg (q.G_pos y b)) _
  E_sum x := by
    have h : ∑ a, q.M.Lv (q.E x a) = (1 : ↥q.M.vnAlg) := by
      rw [← Lv_sum, q.E_sum, Lv_one]
    exact h
  F_sum y := by
    have h : ∑ b, q.Fv y b = (1 : ↥q.M.vnAlg) := by
      apply Subtype.ext
      rw [coe_sum_vnAlg]
      show ∑ b, q.M.conjJ (q.G y b) = 1
      rw [← conjJ_sum, q.G_sum, conjJ_one]
    exact h

/-- The pulled-back strategy reproduces the correlation. -/
theorem pullback_correlation : q.pullback.correlation = q.toCorrelation := by
  funext x y a b
  unfold TracialStrategy.correlation toCorrelation
  show (q.M.traceState (star (q.M.L q.σ) * (q.M.L (q.E x a) * q.M.L q.σ
      * q.M.conjJ (q.G y b)))).re = _
  rw [← map_star, show q.M.L (star q.σ) * (q.M.L (q.E x a) * q.M.L q.σ * q.M.conjJ (q.G y b))
      = q.M.L (star q.σ) * q.M.L (q.E x a) * q.M.L q.σ * q.M.conjJ (q.G y b) by
      simp only [mul_assoc],
    q.M.traceState_conjJ q.σ (q.E x a) (q.G_pos y b).isSelfAdjoint (q.G_commutant y b)]

end TraciallyEmbeddableCorrelation

end CommutingRepetition
