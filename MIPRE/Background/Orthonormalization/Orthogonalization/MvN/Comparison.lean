/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/MvN/Comparison.lean
-/
/-
# Comparison of projections in a factor with a faithful tracial functional

Proof-side step of tier T4a (Theorem 1.2 for II₁ factors): the comparison theorem
of Anantharaman–Popa, *An introduction to II₁ factors*, Prop. 9.1.8 — in a factor
`M` carrying a faithful tracial positive functional `τ`, two projections with the
same trace are Murray–von Neumann equivalent. Two ingredients enter as explicit
hypotheses: the factor property (`Z(M) = ℂ·1`) and the polar decomposition inside
`M` (field H6 of the interface).

* `exists_mul_mul_ne_zero_of_factor`: in a factor the corner `e M f` between two
  nonzero projections is nonzero (the closed span `K` of `M f H` is invariant under
  `M` and `M'`, so its projection is central, hence `1`; if `e M f = 0` then `e`
  vanishes on `K = H`).
* `IsPartialBetween M p q w`: `w ∈ M` is a partial isometry with initial projection
  below `p` and final projection below `q`; `IsPartialBetween.add` glues such a `w`
  with a partial isometry between the complements `p − w* w`, `q − w w*`.
* `exists_extension_of_ne`: as long as neither complement vanishes, the corner
  lemma and the polar decomposition produce a nonzero extension, of positive trace.
* `IsChain.exists_limit`: an increasing chain `w₀, w₁ = w₀ + u₀, …` of partial
  isometries converges strongly to a partial isometry whose initial projection is
  the strong limit of the initial projections (the orbits `wₙ ξ` are Cauchy because
  `‖wₘ ξ − wₙ ξ‖² = ⟪ξ, (wₘ* wₘ − wₙ* wₙ) ξ⟫`).
* `mvNEquiv_of_trace_eq`: the comparison theorem, by a greedy sequence (each step
  takes an extension of trace at least half the supremum of the available traces)
  in place of Zorn's lemma: the limit is maximal, so one of the two complements
  vanishes, and the trace identity forces the other to vanish as well.

No statement of the paper is made here.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.Generated
import MIPRE.Background.Repetition.CommutingRepetition.VN.MonotoneLimit
import MIPRE.Background.Repetition.CommutingRepetition.VN.BorelCalculus
import MIPRE.Background.Orthonormalization.Orthogonalization.Blocks.Bicommutant
import MIPRE.Background.Orthonormalization.Orthogonalization.Blocks.StateOnM
import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.Polar

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace Orthogonalization.MvN

open scoped BigOperators ComplexOrder InnerProductSpace
open Filter Topology CommutingRepetition.VN CommutingRepetition.StrongLimit Blocks

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Small facts about projections -/

/-- A projection `a` with `a b = a` lies below the projection `b` in the Loewner order. -/
theorem le_of_mul_eq {a b : H →L[ℂ] H} (ha : IsStarProjection a) (hb : IsStarProjection b)
    (h : a * b = a) : a ≤ b :=
  sub_nonneg.mp (ha.sub_of_mul_eq_left hb h).nonneg

/-- A projection is a contraction in the Loewner order. -/
theorem le_one_of_isStarProjection {a : H →L[ℂ] H} (ha : IsStarProjection a) : a ≤ 1 :=
  sub_nonneg.mp ha.one_sub.nonneg

/-- For projections `a ≤ b ≤ c`: `(c − b) (c − a) = c − b`. -/
theorem sub_mul_sub_of_le {a b c : H →L[ℂ] H} (ha : IsStarProjection a) (hb : IsStarProjection b)
    (hc : IsStarProjection c) (hab : a * b = a) (hbc : b * c = b) :
    (c - b) * (c - a) = c - b := by
  have hac : a * c = a := by rw [← hab, mul_assoc, hbc]
  have hca : c * a = a := proj_mul_left_of_mul_right ha hc hac
  have hba : b * a = a := proj_mul_left_of_mul_right ha hb hab
  rw [sub_mul, mul_sub, mul_sub, hc.isIdempotentElem.eq, hca, hbc, hba]
  abel

/-! ### Partial isometries between subprojections -/

/-- `w ∈ M` is a partial isometry with initial projection `w* w ≤ p` and final projection
`w w* ≤ q`. -/
structure IsPartialBetween (M : VonNeumannAlgebra H) (p q w : H →L[ℂ] H) : Prop where
  mem : w ∈ M
  proj : IsStarProjection (star w * w)
  init_le : star w * w * p = star w * w
  final_le : w * star w * q = w * star w

namespace IsPartialBetween

variable {M : VonNeumannAlgebra H} {p q w : H →L[ℂ] H}

theorem isStarProjection_mul_star (h : IsPartialBetween M p q w) :
    IsStarProjection (w * star w) :=
  isStarProjection_mul_star_of h.proj

theorem init_mem (h : IsPartialBetween M p q w) : star w * w ∈ M :=
  mul_mem (star_mem h.mem) h.mem

theorem final_mem (h : IsPartialBetween M p q w) : w * star w ∈ M :=
  mul_mem h.mem (star_mem h.mem)

/-- `w (w* w) = w`. -/
theorem mul_init (h : IsPartialBetween M p q w) : w * (star w * w) = w :=
  mul_star_mul_self_eq_self h.proj

/-- `w* (w w*) = w*`. -/
theorem star_mul_final (h : IsPartialBetween M p q w) : star w * (w * star w) = star w :=
  star_mul_self_mul_star h.proj

/-- `(w w*) w = w`. -/
theorem final_mul (h : IsPartialBetween M p q w) : w * star w * w = w := by
  rw [mul_assoc]; exact h.mul_init

/-- `w p = w`. -/
theorem mul_right_eq_self (h : IsPartialBetween M p q w) : w * p = w := by
  calc w * p = w * (star w * w) * p := by rw [h.mul_init]
    _ = w * (star w * w * p) := mul_assoc _ _ _
    _ = w := by rw [h.init_le, h.mul_init]

/-- Enlarging the target projections. -/
theorem mono {p' q' : H →L[ℂ] H} (h : IsPartialBetween M p' q' w) (hp : p' * p = p')
    (hq : q' * q = q') : IsPartialBetween M p q w where
  mem := h.mem
  proj := h.proj
  init_le := by
    calc star w * w * p = star w * w * p' * p := by rw [h.init_le]
      _ = star w * w * (p' * p) := mul_assoc _ _ _
      _ = star w * w := by rw [hp, h.init_le]
  final_le := by
    calc w * star w * q = w * star w * q' * q := by rw [h.final_le]
      _ = w * star w * (q' * q) := mul_assoc _ _ _
      _ = w * star w := by rw [hq, h.final_le]

/-- Partial isometries are contractions. -/
theorem norm_le_one (h : IsPartialBetween M p q w) : ‖w‖ ≤ 1 := by
  have h1 := CStarRing.norm_star_mul_self (x := w)
  have h2 := norm_le_one_of_isStarProjection h.proj
  rw [h1] at h2
  nlinarith [norm_nonneg w]

/-- `w* w ≤ p` in the Loewner order. -/
theorem init_le_loewner (h : IsPartialBetween M p q w) (hp : IsStarProjection p) :
    star w * w ≤ p :=
  le_of_mul_eq h.proj hp h.init_le

end IsPartialBetween

/-- The adjoint of a partial isometry `(≤ p) → (≤ q)` is a partial isometry `(≤ q) → (≤ p)`. -/
theorem IsPartialBetween.adjoint {M : VonNeumannAlgebra H} {p q w : H →L[ℂ] H}
    (h : IsPartialBetween M p q w) : IsPartialBetween M q p (star w) where
  mem := star_mem h.mem
  proj := by rw [star_star]; exact h.isStarProjection_mul_star
  init_le := by rw [star_star]; exact h.final_le
  final_le := by rw [star_star]; exact h.init_le

/-- `q w = w` (`q` self-adjoint). -/
theorem IsPartialBetween.mul_left_eq_self {M : VonNeumannAlgebra H} {p q w : H →L[ℂ] H}
    (h : IsPartialBetween M p q w) (hq : IsSelfAdjoint q) : q * w = w := by
  have := congrArg Star.star h.adjoint.mul_right_eq_self
  rwa [star_mul, star_star, hq.star_eq] at this

theorem zero_isPartialBetween (M : VonNeumannAlgebra H) (p q : H →L[ℂ] H) :
    IsPartialBetween M p q 0 where
  mem := zero_mem M
  proj := by rw [star_zero, mul_zero]; exact IsStarProjection.zero _
  init_le := by rw [star_zero, mul_zero, zero_mul]
  final_le := by rw [star_zero, mul_zero, zero_mul]

/-! ### Orthogonal sums of partial isometries -/

/-- The sum of a partial isometry `w : (≤ p) → (≤ q)` and a partial isometry between the
complements `p − w* w`, `q − w w*` is a partial isometry `(≤ p) → (≤ q)` whose initial and
final projections are the sums. -/
theorem IsPartialBetween.add {M : VonNeumannAlgebra H} {p q w u : H →L[ℂ] H}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hw : IsPartialBetween M p q w)
    (hu : IsPartialBetween M (p - star w * w) (q - w * star w) u) :
    IsPartialBetween M p q (w + u) ∧ star (w + u) * (w + u) = star w * w + star u * u ∧
      (w + u) * star (w + u) = w * star w + u * star u := by
  have hr := hw.proj
  have hl := hw.isStarProjection_mul_star
  have hr' := hu.proj
  have hl' := hu.isStarProjection_mul_star
  have hpr : p * (star w * w) = star w * w := proj_mul_left_of_mul_right hr hp hw.init_le
  have hql : q * (w * star w) = w * star w := proj_mul_left_of_mul_right hl hq hw.final_le
  have hprP : IsStarProjection (p - star w * w) := isStarProjection_sub_of_le hp hr hw.init_le hpr
  have hqlP : IsStarProjection (q - w * star w) := isStarProjection_sub_of_le hq hl hw.final_le hql
  -- orthogonality of the initial projections, and of the final ones
  have hrr' : star w * w * (star u * u) = 0 := by
    have h1 : (p - star w * w) * (star u * u) = star u * u :=
      proj_mul_left_of_mul_right hr' hprP hu.init_le
    have h2 : star w * w * (p - star w * w) = 0 := proj_mul_sub_eq_zero hr hw.init_le
    rw [← h1, ← mul_assoc, h2, zero_mul]
  have hll' : w * star w * (u * star u) = 0 := by
    have h1 : (q - w * star w) * (u * star u) = u * star u :=
      proj_mul_left_of_mul_right hl' hqlP hu.final_le
    have h2 : w * star w * (q - w * star w) = 0 := proj_mul_sub_eq_zero hl hw.final_le
    rw [← h1, ← mul_assoc, h2, zero_mul]
  -- the sum is a partial isometry
  obtain ⟨h1, h2⟩ := star_add_mul_add_eq_of_le (u₀ := w) (v := u)
    (Q := star w * w + star u * u) (P := w * star w + u * star u) hr hl
    (by rw [add_sub_cancel_left]; exact hr') (by rw [add_sub_cancel_left]; exact hl') rfl rfl
    (by rw [add_sub_cancel_left]) (by rw [add_sub_cancel_left])
    (by rw [mul_add, hr.isIdempotentElem.eq, hrr', add_zero])
    (by rw [mul_add, hl.isIdempotentElem.eq, hll', add_zero])
  -- the initial projection of `u` lies below `p`, its final projection below `q`
  have hr'p : star u * u * p = star u * u := by
    have h3 : (p - star w * w) * p = p - star w * w := by
      rw [sub_mul, hp.isIdempotentElem.eq, hw.init_le]
    calc star u * u * p = star u * u * (p - star w * w) * p := by rw [hu.init_le]
      _ = star u * u * ((p - star w * w) * p) := mul_assoc _ _ _
      _ = star u * u := by rw [h3, hu.init_le]
  have hl'q : u * star u * q = u * star u := by
    have h3 : (q - w * star w) * q = q - w * star w := by
      rw [sub_mul, hq.isIdempotentElem.eq, hw.final_le]
    calc u * star u * q = u * star u * (q - w * star w) * q := by rw [hu.final_le]
      _ = u * star u * ((q - w * star w) * q) := mul_assoc _ _ _
      _ = u * star u := by rw [h3, hu.final_le]
  refine ⟨⟨add_mem hw.mem hu.mem, ?_, ?_, ?_⟩, h1, h2⟩
  · rw [h1]; exact hr.add hr' hrr'
  · rw [h1, add_mul, hw.init_le, hr'p]
  · rw [h2, add_mul, hw.final_le, hl'q]

/-! ### The corner lemma -/

/- The hypotheses `he`, `hf` (and `heM`) are part of the statement's interface shape; the proof
only uses `e ≠ 0`, `f ≠ 0` and `f ∈ M`. -/
set_option linter.unusedVariables false in
/-- In a factor, the corner `e M f` between two nonzero projections is nonzero (the central
support of a nonzero projection is `1`). -/
theorem exists_mul_mul_ne_zero_of_factor (M : VonNeumannAlgebra H)
    (hfactor : ∀ z ∈ M, (∀ y ∈ M, Commute z y) → ∃ c : ℂ, z = c • (1 : H →L[ℂ] H))
    {e f : H →L[ℂ] H} (he : IsStarProjection e) (heM : e ∈ M) (he0 : e ≠ 0)
    (hf : IsStarProjection f) (hfM : f ∈ M) (hf0 : f ≠ 0) :
    ∃ y ∈ M, e * y * f ≠ 0 := by
  by_contra hcon
  have hzero : ∀ y ∈ M, e * y * f = 0 := fun y hy => not_not.mp fun h => hcon ⟨y, hy, h⟩
  /- The closed subspace `K` spanned by the vectors `y (f ξ)`, `y ∈ M`. -/
  set G : Set H := {v | ∃ y ∈ M, ∃ ξ, v = y (f ξ)} with hG
  set K₀ : Submodule ℂ H := Submodule.span ℂ G with hK₀
  set K : Submodule ℂ H := K₀.topologicalClosure with hK
  have hgen : ∀ y ∈ M, ∀ ξ, y (f ξ) ∈ K := fun y hy ξ =>
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨y, hy, ξ, rfl⟩)
  -- an operator mapping the generators into `K₀` leaves `K` invariant
  have hinv : ∀ T : H →L[ℂ] H, (∀ v ∈ G, T v ∈ K₀) → ∀ v ∈ K, T v ∈ K := by
    intro T hT v hv
    have h1 : K₀ ≤ K₀.comap (T : H →ₗ[ℂ] H) := Submodule.span_le.mpr fun v hv => hT v hv
    have h2 : v ∈ closure (K₀ : Set H) := by rwa [← Submodule.topologicalClosure_coe]
    have h3 : T v ∈ closure (K₀ : Set H) :=
      map_mem_closure T.continuous h2 fun x hx => h1 hx
    rwa [← Submodule.topologicalClosure_coe] at h3
  have hinvM : ∀ y ∈ M, ∀ v ∈ K, y v ∈ K := fun y hy => hinv y (by
    rintro _ ⟨y', hy', ξ, rfl⟩
    exact Submodule.subset_span ⟨y * y', mul_mem hy hy', ξ, by rw [mul_apply_eq_comp]⟩)
  have hinvC : ∀ y ∈ M.commutant, ∀ v ∈ K, y v ∈ K := fun y hy => hinv y (by
    rintro _ ⟨y', hy', ξ, rfl⟩
    refine Submodule.subset_span ⟨y', hy', y ξ, ?_⟩
    rw [← mul_apply_eq_comp, commutant_mul_of_mem hy' hy, mul_apply_eq_comp,
      ← mul_apply_eq_comp y f, commutant_mul_of_mem hfM hy, mul_apply_eq_comp])
  /- Its projection `c` commutes with `M` and `M'`, so it is a central projection of `M`. -/
  set c : H →L[ℂ] H := K.starProjection with hc
  have hcM' : ∀ y ∈ M, Commute y c := fun y hy =>
    starProjection_commute_of_invariant' K (hinvM y hy) (hinvM _ (star_mem hy))
  have hcC : ∀ y ∈ M.commutant, Commute y c := fun y hy =>
    starProjection_commute_of_invariant' K (hinvC y hy) (hinvC _ (star_mem hy))
  have hcM : c ∈ M := mem_of_commute_commutant M fun y hy => (hcC y hy).eq
  obtain ⟨lam, hlam⟩ := hfactor c hcM fun y hy => (hcM' y hy).symm
  /- `c = 1`: `c` fixes the nonzero vector `f ξ`. -/
  obtain ⟨ξ, hξ⟩ : ∃ ξ, f ξ ≠ 0 := by
    by_contra hall
    exact hf0 (ContinuousLinearMap.ext fun ξ => not_not.mp fun h => hall ⟨ξ, h⟩)
  have hfξ : f ξ ∈ K := by simpa using hgen 1 (one_mem M) ξ
  have hcf : c (f ξ) = f ξ := Submodule.starProjection_eq_self_iff.mpr hfξ
  have hlam1 : lam = 1 := by
    rw [hlam, smul_apply, one_apply_eq_self] at hcf
    have : (lam - 1) • f ξ = 0 := by rw [sub_smul, one_smul, hcf, sub_self]
    rcases smul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hξ
  have hc1 : c = 1 := by rw [hlam, hlam1, one_smul]
  have hK : ∀ v, v ∈ K := fun v => by
    have := K.starProjection_apply_mem v
    rwa [← hc, hc1, one_apply_eq_self] at this
  /- `e` vanishes on the generators, hence on `K = H`. -/
  have hker : K ≤ LinearMap.ker (e : H →ₗ[ℂ] H) := by
    refine Submodule.topologicalClosure_minimal _ ?_ (ContinuousLinearMap.isClosed_ker e)
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨y, hy, ξ, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ← mul_apply_eq_comp,
      ← mul_apply_eq_comp, hzero y hy, zero_apply]
  refine he0 (ContinuousLinearMap.ext fun v => ?_)
  have := LinearMap.mem_ker.mp (hker (hK v))
  rw [ContinuousLinearMap.coe_coe] at this
  rw [this, zero_apply]

/-! ### The extension step -/

/-- If neither complement `p − w* w`, `q − w w*` vanishes, the partial isometry `w` extends by
a nonzero partial isometry `u` between the complements; its initial projection has positive
trace when `τ` is faithful. -/
theorem exists_extension_of_ne (M : VonNeumannAlgebra H)
    (hfactor : ∀ z ∈ M, (∀ y ∈ M, Commute z y) → ∃ c : ℂ, z = c • (1 : H →L[ℂ] H))
    (hpolar : ∀ x ∈ M, ∃ u ∈ M, star u * u = rightSupport x ∧ u * star u = leftSupport x ∧
      x = u * CFC.sqrt (star x * x))
    (τ : (H →L[ℂ] H) →ₗ[ℂ] ℂ) (hτ0 : ∀ x ∈ M, 0 ≤ τ (star x * x))
    (hτf : ∀ x ∈ M, τ (star x * x) = 0 → x = 0)
    {p q w : H →L[ℂ] H} (hp : IsStarProjection p) (hpM : p ∈ M) (hq : IsStarProjection q)
    (hqM : q ∈ M) (hw : IsPartialBetween M p q w) (hr : star w * w ≠ p)
    (hl : w * star w ≠ q) :
    ∃ u, IsPartialBetween M (p - star w * w) (q - w * star w) u ∧ 0 < (τ (star u * u)).re := by
  have hrP := hw.proj
  have hlP := hw.isStarProjection_mul_star
  have hpr : IsStarProjection (p - star w * w) :=
    isStarProjection_sub_of_le hp hrP hw.init_le (proj_mul_left_of_mul_right hrP hp hw.init_le)
  have hql : IsStarProjection (q - w * star w) :=
    isStarProjection_sub_of_le hq hlP hw.final_le (proj_mul_left_of_mul_right hlP hq hw.final_le)
  have hprM : p - star w * w ∈ M := sub_mem hpM hw.init_mem
  have hqlM : q - w * star w ∈ M := sub_mem hqM hw.final_mem
  have hpr0 : p - star w * w ≠ 0 := sub_ne_zero.mpr hr.symm
  have hql0 : q - w * star w ≠ 0 := sub_ne_zero.mpr hl.symm
  obtain ⟨y, hyM, hx0⟩ := exists_mul_mul_ne_zero_of_factor M hfactor hql hqlM hql0 hpr hprM hpr0
  set x := (q - w * star w) * y * (p - star w * w) with hx
  have hxM : x ∈ M := mul_mem (mul_mem hqlM hyM) hprM
  obtain ⟨u, huM, hu1, hu2, hxu⟩ := hpolar x hxM
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hxu
    exact hx0 hxu
  have hxp : x * (p - star w * w) = x := by rw [hx, mul_assoc, hpr.isIdempotentElem.eq]
  have hqx : (q - w * star w) * x = x := by
    rw [hx, ← mul_assoc, ← mul_assoc, hql.isIdempotentElem.eq]
  refine ⟨u, ⟨huM, by rw [hu1]; exact isStarProjection_rightSupport x,
    by rw [hu1]; exact rightSupport_mul_eq_self_of hxp,
    by rw [hu2]; exact leftSupport_mul_eq_self_of hql hqx⟩, ?_⟩
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp (hτ0 u huM)
  rcases hre.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    refine hu0 (hτf u huM (Complex.ext ?_ ?_))
    · rw [Complex.zero_re]; exact heq.symm
    · rw [Complex.zero_im]; exact him.symm

/-! ### The greedy choice -/

/-- Among the partial isometries between the complements `p − w* w`, `q − w w*` there is one
whose initial projection has trace at least half the supremum of the available traces. -/
theorem exists_good_extension (M : VonNeumannAlgebra H) (τ : (H →L[ℂ] H) →ₗ[ℂ] ℂ)
    (hτ0 : ∀ x ∈ M, 0 ≤ τ (star x * x)) {p q w : H →L[ℂ] H} (hp : IsStarProjection p)
    (hpM : p ∈ M) (hw : IsPartialBetween M p q w) :
    ∃ u, IsPartialBetween M (p - star w * w) (q - w * star w) u ∧
      ∀ u', IsPartialBetween M (p - star w * w) (q - w * star w) u' →
        (τ (star u' * u')).re ≤ 2 * (τ (star u * u)).re := by
  set S : Set ℝ := {s | ∃ u', IsPartialBetween M (p - star w * w) (q - w * star w) u' ∧
    (τ (star u' * u')).re = s} with hS
  have hne : S.Nonempty := ⟨_, 0, zero_isPartialBetween M _ _, rfl⟩
  have hbdd : BddAbove S := by
    refine ⟨(τ p).re, ?_⟩
    rintro _ ⟨u', hu', rfl⟩
    have h3 : (p - star w * w) * p = p - star w * w := by
      rw [sub_mul, hp.isIdempotentElem.eq, hw.init_le]
    have hu'p : star u' * u' * p = star u' * u' := by
      calc star u' * u' * p = star u' * u' * (p - star w * w) * p := by rw [hu'.init_le]
        _ = star u' * u' * ((p - star w * w) * p) := mul_assoc _ _ _
        _ = star u' * u' := by rw [h3, hu'.init_le]
    exact re_map_le_of_mem hτ0 hu'.init_mem hpM (le_of_mul_eq hu'.proj hp hu'p)
  by_cases hσ : 0 < sSup S
  · obtain ⟨_, ⟨u, hu, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hne (half_lt_self hσ)
    refine ⟨u, hu, fun u' hu' => ?_⟩
    have := le_csSup hbdd ⟨u', hu', rfl⟩
    linarith
  · refine ⟨0, zero_isPartialBetween M _ _, fun u' hu' => ?_⟩
    have := le_csSup hbdd ⟨u', hu', rfl⟩
    have h0 : (τ (star (0 : H →L[ℂ] H) * 0)).re = 0 := by simp
    rw [h0]
    linarith [not_lt.mp hσ]

/-! ### Increasing chains of partial isometries and their strong limits -/

/-- An increasing chain of partial isometries `(≤ p) → (≤ q)`: `w (n+1) = w n + u n` with `u n`
a partial isometry between the complements of `w n`. -/
structure IsChain (M : VonNeumannAlgebra H) (p q : H →L[ℂ] H) (w u : ℕ → H →L[ℂ] H) : Prop where
  step : ∀ n, IsPartialBetween M p q (w n)
  extend : ∀ n, IsPartialBetween M (p - star (w n) * w n) (q - w n * star (w n)) (u n)
  succ_eq : ∀ n, w (n + 1) = w n + u n

namespace IsChain

variable {M : VonNeumannAlgebra H} {p q : H →L[ℂ] H} {w u : ℕ → H →L[ℂ] H}

/-- The adjoint chain. -/
theorem adjoint (hc : IsChain M p q w u) :
    IsChain M q p (fun n => star (w n)) (fun n => star (u n)) where
  step n := (hc.step n).adjoint
  extend n := by simpa only [star_star] using (hc.extend n).adjoint
  succ_eq n := by simp only [hc.succ_eq n, star_add]

theorem init_succ (hp : IsStarProjection p) (hq : IsStarProjection q) (hc : IsChain M p q w u)
    (n : ℕ) : star (w (n + 1)) * w (n + 1) = star (w n) * w n + star (u n) * u n := by
  rw [hc.succ_eq n]
  exact (IsPartialBetween.add hp hq (hc.step n) (hc.extend n)).2.1

theorem final_succ (hp : IsStarProjection p) (hq : IsStarProjection q) (hc : IsChain M p q w u)
    (n : ℕ) : w (n + 1) * star (w (n + 1)) = w n * star (w n) + u n * star (u n) := by
  rw [hc.succ_eq n]
  exact (IsPartialBetween.add hp hq (hc.step n) (hc.extend n)).2.2

theorem init_mono (hp : IsStarProjection p) (hq : IsStarProjection q) (hc : IsChain M p q w u) :
    Monotone fun n => star (w n) * w n :=
  monotone_nat_of_le_succ fun n => by
    show star (w n) * w n ≤ star (w (n + 1)) * w (n + 1)
    rw [hc.init_succ hp hq n]
    exact le_add_of_nonneg_right (star_mul_self_nonneg _)

theorem final_mono (hp : IsStarProjection p) (hq : IsStarProjection q) (hc : IsChain M p q w u) :
    Monotone fun n => w n * star (w n) :=
  monotone_nat_of_le_succ fun n => by
    show w n * star (w n) ≤ w (n + 1) * star (w (n + 1))
    rw [hc.final_succ hp hq n]
    exact le_add_of_nonneg_right (mul_star_self_nonneg _)

theorem init_mul_init (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hc : IsChain M p q w u) {n m : ℕ} (h : n ≤ m) :
    star (w n) * w n * (star (w m) * w m) = star (w n) * w n :=
  proj_mul_eq_self_of_le (hc.step n).proj (hc.step m).proj (hc.init_mono hp hq h)

theorem final_mul_final (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hc : IsChain M p q w u) {n m : ℕ} (h : n ≤ m) :
    w n * star (w n) * (w m * star (w m)) = w n * star (w n) :=
  proj_mul_eq_self_of_le (hc.step n).isStarProjection_mul_star
    (hc.step m).isStarProjection_mul_star (hc.final_mono hp hq h)

/-- `wₙ* uₘ = 0` for `n ≤ m`: the range of `uₘ` is orthogonal to that of `wₘ`, hence to that
of `wₙ`. -/
theorem star_mul_ext (hp : IsStarProjection p) (hq : IsStarProjection q) (hc : IsChain M p q w u)
    {n m : ℕ} (h : n ≤ m) : star (w n) * u m = 0 := by
  have hlm := (hc.step m).isStarProjection_mul_star
  have hqlm : IsStarProjection (q - w m * star (w m)) :=
    isStarProjection_sub_of_le hq hlm (hc.step m).final_le
      (proj_mul_left_of_mul_right hlm hq (hc.step m).final_le)
  have h1 : star (w n) * (w n * star (w n)) = star (w n) := (hc.step n).star_mul_final
  have h2 : (q - w m * star (w m)) * u m = u m :=
    (hc.extend m).mul_left_eq_self hqlm.isSelfAdjoint
  have h3 : w n * star (w n) * (q - w m * star (w m)) = 0 := by
    rw [mul_sub, (hc.step n).final_le, hc.final_mul_final hp hq h, sub_self]
  calc star (w n) * u m
      = star (w n) * (w n * star (w n)) * ((q - w m * star (w m)) * u m) := by rw [h1, h2]
    _ = star (w n) * (w n * star (w n) * (q - w m * star (w m))) * u m := by
        simp only [mul_assoc]
    _ = 0 := by rw [h3, mul_zero, zero_mul]

/-- `wₙ* wₘ = wₙ* wₙ` for `n ≤ m`. -/
theorem star_mul_eq (hp : IsStarProjection p) (hq : IsStarProjection q) (hc : IsChain M p q w u)
    {n m : ℕ} (h : n ≤ m) : star (w n) * w m = star (w n) * w n := by
  induction m, h using Nat.le_induction with
  | base => rfl
  | succ m hnm ih => rw [hc.succ_eq m, mul_add, ih, hc.star_mul_ext hp hq hnm, add_zero]

/-- `‖wₘ ξ − wₙ ξ‖² = ⟪ξ, (wₘ* wₘ − wₙ* wₙ) ξ⟫` for `n ≤ m`. -/
theorem norm_sub_sq (hp : IsStarProjection p) (hq : IsStarProjection q) (hc : IsChain M p q w u)
    (ξ : H) {n m : ℕ} (h : n ≤ m) :
    ‖w m ξ - w n ξ‖ ^ 2 =
      (⟪ξ, (star (w m) * w m) ξ⟫_ℂ).re - (⟪ξ, (star (w n) * w n) ξ⟫_ℂ).re := by
  have h2 : star (w n) * w m = star (w n) * w n := hc.star_mul_eq hp hq h
  have h3 : star (w m) * w n = star (w n) * w n := by
    have := congrArg Star.star h2
    rwa [star_mul, star_star, star_mul, star_star] at this
  have h1 : star (w m - w n) * (w m - w n) = star (w m) * w m - star (w n) * w n := by
    rw [star_sub, sub_mul, mul_sub, mul_sub, h2, h3]
    abel
  have key := CommutingRepetition.Resolver.Douglas.re_inner_star_mul (w m - w n) ξ
  rw [h1] at key
  simp only [sub_apply, inner_sub_right, Complex.sub_re] at key
  exact key.symm

/-- The orbits `wₙ ξ` are Cauchy. -/
theorem cauchySeq (hp : IsStarProjection p) (hq : IsStarProjection q) (hc : IsChain M p q w u)
    (ξ : H) : CauchySeq fun n => w n ξ := by
  obtain ⟨a, ha⟩ := tendsto_re_inner (fun n => star (w n) * w n) (hc.init_mono hp hq)
    (star_mul_self_nonneg _) (fun n => le_one_of_isStarProjection (hc.step n).proj) ξ
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp ha.cauchySeq (ε ^ 2) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  wlog hle : n ≤ m generalizing m n
  · rw [dist_comm]
    exact this n hn m hm (not_le.mp hle).le
  have hb := hc.norm_sub_sq hp hq ξ hle
  have hd := hN m hm n hn
  rw [Real.dist_eq] at hd
  rw [dist_eq_norm]
  have hlt : ‖w m ξ - w n ξ‖ ^ 2 < ε ^ 2 := by
    calc ‖w m ξ - w n ξ‖ ^ 2
        = (⟪ξ, (star (w m) * w m) ξ⟫_ℂ).re - (⟪ξ, (star (w n) * w n) ξ⟫_ℂ).re := hb
      _ ≤ |(⟪ξ, (star (w m) * w m) ξ⟫_ℂ).re - (⟪ξ, (star (w n) * w n) ξ⟫_ℂ).re| :=
          le_abs_self _
      _ < ε ^ 2 := hd
  exact lt_of_pow_lt_pow_left₀ 2 hε.le hlt

/-- The strong limit of an increasing chain of partial isometries: an operator `W ∈ M` whose
initial projection `W* W` is a projection below `p` dominating every `wₙ* wₙ` (it is the strong
limit of the increasing sequence `wₙ* wₙ`). -/
theorem exists_limit (hp : IsStarProjection p) (hq : IsStarProjection q) (hc : IsChain M p q w u) :
    ∃ W : H →L[ℂ] H, W ∈ M ∧ (∀ ξ, Tendsto (fun n => w n ξ) atTop (𝓝 (W ξ))) ∧
      IsStarProjection (star W * W) ∧ star W * W * p = star W * W ∧
      ∀ n, star (w n) * w n * (star W * W) = star (w n) * w n := by
  have hmono : Monotone fun n => star (w n) * w n := hc.init_mono hp hq
  have h0 : 0 ≤ star (w 0) * w 0 := star_mul_self_nonneg _
  have h1 : ∀ n, star (w n) * w n ≤ 1 := fun n => le_one_of_isStarProjection (hc.step n).proj
  have hex : ∀ ξ, ∃ l, Tendsto (fun n => w n ξ) atTop (𝓝 l) := fun ξ =>
    cauchySeq_tendsto_of_complete (hc.cauchySeq hp hq ξ)
  have hnorm : ∀ n, ‖w n‖ ≤ 1 := fun n => (hc.step n).norm_le_one
  set W := pointwiseLimit w 1 hnorm hex with hW
  have hWlim : ∀ ξ, Tendsto (fun n => w n ξ) atTop (𝓝 (W ξ)) :=
    pointwiseLimit_tendsto w 1 hnorm hex
  have hWM : W ∈ M := mem_of_tendsto_seq M (fun n => (hc.step n).mem) hWlim
  set R := monotoneLimit (fun n => star (w n) * w n) hmono h0 h1 with hR
  have hRlim : ∀ ξ, Tendsto (fun n => (star (w n) * w n) ξ) atTop (𝓝 (R ξ)) :=
    monotoneLimit_tendsto _ hmono h0 h1
  /- `W* W = R`: the two quadratic forms are the limits of `‖wₙ ξ‖² = ⟪ξ, wₙ* wₙ ξ⟫`. -/
  have hWW : star W * W = R := by
    refine CommutingRepetition.BorelCalc.ext_of_inner_self fun ξ => ?_
    have e1 : Tendsto (fun n => ⟪w n ξ, w n ξ⟫_ℂ) atTop (𝓝 ⟪W ξ, W ξ⟫_ℂ) :=
      (hWlim ξ).inner (hWlim ξ)
    have e2 : Tendsto (fun n => ⟪w n ξ, w n ξ⟫_ℂ) atTop (𝓝 ⟪ξ, R ξ⟫_ℂ) := by
      refine (tendsto_const_nhds.inner (hRlim ξ)).congr fun n => ?_
      rw [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_right]
    rw [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right]
    exact tendsto_nhds_unique e1 e2
  /- `R` is a projection below `p` dominating every `wₙ* wₙ`, by strong limits. -/
  have hrR : ∀ n, star (w n) * w n * R = star (w n) * w n := fun n => by
    refine ContinuousLinearMap.ext fun ξ => ?_
    rw [mul_apply_eq_comp]
    have e1 : Tendsto (fun m => (star (w n) * w n) ((star (w m) * w m) ξ)) atTop
        (𝓝 ((star (w n) * w n) (R ξ))) :=
      ((star (w n) * w n).continuous.tendsto _).comp (hRlim ξ)
    have e2 : Tendsto (fun m => (star (w n) * w n) ((star (w m) * w m) ξ)) atTop
        (𝓝 ((star (w n) * w n) ξ)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop n] with m hm
      rw [← mul_apply_eq_comp (star (w n) * w n) (star (w m) * w m) ξ, hc.init_mul_init hp hq hm]
    exact tendsto_nhds_unique e1 e2
  have hRR : R * R = R := by
    refine ContinuousLinearMap.ext fun ξ => ?_
    rw [mul_apply_eq_comp]
    have e1 : Tendsto (fun m => (star (w m) * w m) (R ξ)) atTop (𝓝 (R (R ξ))) := hRlim (R ξ)
    have e2 : Tendsto (fun m => (star (w m) * w m) (R ξ)) atTop (𝓝 (R ξ)) := by
      refine (hRlim ξ).congr fun m => ?_
      rw [← mul_apply_eq_comp (star (w m) * w m) R ξ, hrR m]
    exact tendsto_nhds_unique e1 e2
  have hRp : R * p = R := by
    refine ContinuousLinearMap.ext fun ξ => ?_
    rw [mul_apply_eq_comp]
    have e1 : Tendsto (fun m => (star (w m) * w m) (p ξ)) atTop (𝓝 (R (p ξ))) := hRlim (p ξ)
    have e2 : Tendsto (fun m => (star (w m) * w m) (p ξ)) atTop (𝓝 (R ξ)) := by
      refine (hRlim ξ).congr fun m => ?_
      rw [← mul_apply_eq_comp (star (w m) * w m) p ξ, (hc.step m).init_le]
    exact tendsto_nhds_unique e1 e2
  refine ⟨W, hWM, hWlim, ?_, ?_, ?_⟩
  · rw [hWW]
    exact ⟨hRR, monotoneLimit_isSelfAdjoint _ hmono h0 h1⟩
  · rw [hWW]
    exact hRp
  · intro n
    rw [hWW]
    exact hrR n

end IsChain

/-- If `Tₙ → S` and `Tₙ* → V` strongly, then `V = S*`. -/
theorem eq_star_of_tendsto {T : ℕ → H →L[ℂ] H} {S V : H →L[ℂ] H}
    (hS : ∀ ξ, Tendsto (fun n => T n ξ) atTop (𝓝 (S ξ)))
    (hV : ∀ ξ, Tendsto (fun n => star (T n) ξ) atTop (𝓝 (V ξ))) : V = star S := by
  refine ContinuousLinearMap.ext fun ξ => ext_inner_left ℂ fun η => ?_
  have e1 : Tendsto (fun n => ⟪η, star (T n) ξ⟫_ℂ) atTop (𝓝 ⟪η, V ξ⟫_ℂ) :=
    tendsto_const_nhds.inner (hV ξ)
  have e2 : Tendsto (fun n => ⟪η, star (T n) ξ⟫_ℂ) atTop (𝓝 ⟪η, star S ξ⟫_ℂ) := by
    simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
    exact (hS η).inner tendsto_const_nhds
  exact tendsto_nhds_unique e1 e2

/-! ### The comparison theorem -/

/-- **Comparison of projections in a factor with a faithful tracial positive functional**
(Anantharaman–Popa 9.1.8): `τ(p) = τ(q)` implies `p ∼ q`. `hpolar` is the polar decomposition
inside `M` (interface field H6). -/
theorem mvNEquiv_of_trace_eq (M : VonNeumannAlgebra H)
    (hfactor : ∀ z ∈ M, (∀ y ∈ M, Commute z y) → ∃ c : ℂ, z = c • (1 : H →L[ℂ] H))
    (τ : (H →L[ℂ] H) →ₗ[ℂ] ℂ) (hτ0 : ∀ x ∈ M, 0 ≤ τ (star x * x))
    (hτtr : ∀ x ∈ M, ∀ y ∈ M, τ (x * y) = τ (y * x))
    (hτf : ∀ x ∈ M, τ (star x * x) = 0 → x = 0)
    (hpolar : ∀ x ∈ M, ∃ u ∈ M, star u * u = rightSupport x ∧ u * star u = leftSupport x ∧
      x = u * CFC.sqrt (star x * x))
    {p q : H →L[ℂ] H} (hp : IsStarProjection p) (hpM : p ∈ M) (hq : IsStarProjection q)
    (hqM : q ∈ M) (h : τ p = τ q) : MvNEquiv M p q := by
  classical
  /- The greedy step, as a function of the current partial isometry. -/
  have hstep : ∀ w, IsPartialBetween M p q w →
      ∃ u, IsPartialBetween M (p - star w * w) (q - w * star w) u ∧
        ∀ u', IsPartialBetween M (p - star w * w) (q - w * star w) u' →
          (τ (star u' * u')).re ≤ 2 * (τ (star u * u)).re :=
    fun w hw => exists_good_extension M τ hτ0 hp hpM hw
  choose! U hU using hstep
  /- The greedy sequence `w₀ = 0`, `wₙ₊₁ = wₙ + U wₙ`. -/
  obtain ⟨w, hw0, hwsucc⟩ : ∃ w : ℕ → H →L[ℂ] H, w 0 = 0 ∧ ∀ n, w (n + 1) = w n + U (w n) :=
    ⟨fun n => Nat.rec 0 (fun _ w => w + U w) n, rfl, fun _ => rfl⟩
  have hw : ∀ n, IsPartialBetween M p q (w n) := by
    intro n
    induction n with
    | zero => rw [hw0]; exact zero_isPartialBetween M p q
    | succ n ih => rw [hwsucc]; exact (IsPartialBetween.add hp hq ih (hU _ ih).1).1
  have hchain : IsChain M p q w (fun n => U (w n)) := ⟨hw, fun n => (hU _ (hw n)).1, hwsucc⟩
  /- The strong limit `W`, with its initial projection `W* W` and final projection `W W*`. -/
  obtain ⟨W, hWM, hWlim, hRP, hRp, hrR⟩ := hchain.exists_limit hp hq
  obtain ⟨V, -, hVlim, hLP, hLq, hlL⟩ := hchain.adjoint.exists_limit hq hp
  have hVW : V = star W := eq_star_of_tendsto hWlim hVlim
  simp only [hVW, star_star] at hLP hLq hlL
  have hWpart : IsPartialBetween M p q W := ⟨hWM, hRP, hRp, hLq⟩
  have hτRL : τ (star W * W) = τ (W * star W) := hτtr _ (star_mem hWM) _ hWM
  /- Maximality: one of the two complements vanishes. Otherwise an extension `u'` of `W` of
  trace `δ > 0` extends every `wₙ`, so `δ ≤ 2 (tₙ₊₁ − tₙ)` for the sequence `tₙ = τ(wₙ* wₙ)`,
  which is bounded by `τ(p)`: absurd. -/
  have hdich : star W * W = p ∨ W * star W = q := by
    by_contra hne
    obtain ⟨hRne, hLne⟩ := not_or.mp hne
    obtain ⟨u', hu', hδ⟩ :=
      exists_extension_of_ne M hfactor hpolar τ hτ0 hτf hp hpM hq hqM hWpart hRne hLne
    have hu'n : ∀ n, IsPartialBetween M (p - star (w n) * w n) (q - w n * star (w n)) u' :=
      fun n => hu'.mono (sub_mul_sub_of_le (hw n).proj hRP hp (hrR n) hRp)
        (sub_mul_sub_of_le (hw n).isStarProjection_mul_star hLP hq (hlL n) hLq)
    have hbound : ∀ n, (τ (star u' * u')).re ≤ 2 * (τ (star (U (w n)) * U (w n))).re :=
      fun n => (hU _ (hw n)).2 u' (hu'n n)
    have ht_succ : ∀ n, (τ (star (w (n + 1)) * w (n + 1))).re =
        (τ (star (w n) * w n)).re + (τ (star (U (w n)) * U (w n))).re := fun n => by
      rw [hchain.init_succ hp hq n, map_add, Complex.add_re]
    have ht_le : ∀ n, (τ (star (w n) * w n)).re ≤ (τ p).re := fun n =>
      re_map_le_of_mem hτ0 (hw n).init_mem hpM ((hw n).init_le_loewner hp)
    have ht_ge : ∀ n : ℕ, n * ((τ (star u' * u')).re / 2) ≤ (τ (star (w n) * w n)).re := by
      intro n
      induction n with
      | zero => simp [hw0]
      | succ n ih =>
        rw [ht_succ n]
        push_cast
        linarith [hbound n]
    obtain ⟨n, hn⟩ := exists_nat_gt ((τ p).re / ((τ (star u' * u')).re / 2))
    rw [div_lt_iff₀ (half_pos hδ)] at hn
    linarith [ht_le n, ht_ge n]
  /- The trace identity `τ(W* W) = τ(W W*)` and faithfulness force the other complement to
  vanish as well. -/
  rcases hdich with hRq | hLq'
  · have hqL : IsStarProjection (q - W * star W) :=
      isStarProjection_sub_of_le hq hLP hLq (proj_mul_left_of_mul_right hLP hq hLq)
    have h0 : τ (star (q - W * star W) * (q - W * star W)) = 0 := by
      rw [hqL.isSelfAdjoint.star_eq, hqL.isIdempotentElem.eq, map_sub, ← h, ← hRq, hτRL,
        sub_self]
    have := hτf _ (sub_mem hqM hWpart.final_mem) h0
    exact ⟨W, hWM, hRq, (sub_eq_zero.mp this).symm⟩
  · have hpR : IsStarProjection (p - star W * W) :=
      isStarProjection_sub_of_le hp hRP hRp (proj_mul_left_of_mul_right hRP hp hRp)
    have h0 : τ (star (p - star W * W) * (p - star W * W)) = 0 := by
      rw [hpR.isSelfAdjoint.star_eq, hpR.isIdempotentElem.eq, map_sub, h, ← hLq', ← hτRL,
        sub_self]
    have := hτf _ (sub_mem hpM hWpart.init_mem) h0
    exact ⟨W, hWM, (sub_eq_zero.mp this).symm, hLq'⟩

end Orthogonalization.MvN
