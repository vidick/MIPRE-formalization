/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/MvN/TypeIIINet.lean
-/
/-
# Tier T3, type III: the net of Lemma 5.1

Lemma 5.1 of the paper: in a type III algebra there is a net `(q_α)` of
projections converging weakly (hence, for projections, strongly) to `1`, with
`1 − q_α ∼ 1` for every `α`. The paper builds, for each positive normal
functional `ψ`, an increasing sequence `q_k` with `ψ(1 − q_k) ≤ 2⁻ᵏ ψ(1)` and
`1 − q_k ∼ 1` by halving (Takesaki V.1.36, field H4 of the interface), then
indexes the net by finite sets of states. Here the net is indexed by pairs
(finite set `α` of unit vectors, `k : ℕ`), with `ψ_α = ∑_{ξ ∈ α} ⟪ξ, · ξ⟫`
and `q_(α,k) := q_{k + |α|, ψ_α}`: for a unit vector `ξ ∈ α`,
`‖(1 − q_(α,k)) ξ‖² ≤ ψ_α(1 − q_(α,k)) ≤ 2⁻ᵏ⁻|α| |α| ≤ 2⁻ᵏ`. Everything is
relative to a central projection `z` (the type III summand). Proof-side only.
-/
import Mathlib
import MIPRE.Background.Orthonormalization.Orthogonalization.Blocks.Corollaries
import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.Local

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace Orthogonalization.MvN

open scoped BigOperators ComplexOrder InnerProductSpace
open Filter Topology CommutingRepetition.VN Blocks

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Partial isometries and Murray–von Neumann equivalence: elementary facts -/

/-- If `v* v` is a projection then `v` is a partial isometry: `v (v* v) = v`. -/
theorem mul_star_mul_self_eq_self {v : H →L[ℂ] H} (h : IsStarProjection (star v * v)) :
    v * (star v * v) = v := by
  have h0 : star (v - v * (star v * v)) * (v - v * (star v * v)) = 0 := by
    have hsa := h.isSelfAdjoint.star_eq
    have hid := h.isIdempotentElem.eq
    calc star (v - v * (star v * v)) * (v - v * (star v * v))
        = star v * v - star v * v * (star v * v) - star (star v * v) * (star v * v)
            + star (star v * v) * (star v * v) * (star v * v) := by
          rw [star_sub, star_mul]
          noncomm_ring
      _ = 0 := by
          rw [hsa]
          simp only [hid]
          abel
  have := (CStarRing.star_mul_self_eq_zero_iff _).mp h0
  exact (sub_eq_zero.mp this).symm

/-- If `v* v` is a projection then so is `v v*`. -/
theorem isStarProjection_mul_star_of {v : H →L[ℂ] H} (h : IsStarProjection (star v * v)) :
    IsStarProjection (v * star v) := by
  refine ⟨?_, IsSelfAdjoint.mul_star_self v⟩
  show v * star v * (v * star v) = v * star v
  calc v * star v * (v * star v) = v * (star v * v) * star v := by noncomm_ring
    _ = v * star v := by rw [mul_star_mul_self_eq_self h]

theorem MvNEquiv.refl {M : VonNeumannAlgebra H} {p : H →L[ℂ] H} (hp : IsStarProjection p)
    (hpM : p ∈ M) : MvNEquiv M p p :=
  ⟨p, hpM, by rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq],
    by rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]⟩

theorem MvNEquiv.symm {M : VonNeumannAlgebra H} {p q : H →L[ℂ] H} (h : MvNEquiv M p q) :
    MvNEquiv M q p := by
  obtain ⟨v, hv, h1, h2⟩ := h
  exact ⟨star v, star_mem hv, by rw [star_star, h2], by rw [star_star, h1]⟩

/-- The target of an equivalence from a projection is a projection. -/
theorem MvNEquiv.isStarProjection_right {M : VonNeumannAlgebra H} {p q : H →L[ℂ] H}
    (hp : IsStarProjection p) (h : MvNEquiv M p q) : IsStarProjection q := by
  obtain ⟨v, -, h1, h2⟩ := h
  rw [← h2]
  exact isStarProjection_mul_star_of (h1.symm ▸ hp)

theorem MvNEquiv.trans {M : VonNeumannAlgebra H} {p q r : H →L[ℂ] H} (hp : IsStarProjection p)
    (h : MvNEquiv M p q) (h' : MvNEquiv M q r) : MvNEquiv M p r := by
  have hq : IsStarProjection q := h.isStarProjection_right hp
  obtain ⟨v, hv, hv1, hv2⟩ := h
  obtain ⟨w, hw, hw1, hw2⟩ := h'
  have hvp : v * (star v * v) = v := mul_star_mul_self_eq_self (hv1.symm ▸ hp)
  have hwq : w * (star w * w) = w := mul_star_mul_self_eq_self (hw1.symm ▸ hq)
  refine ⟨w * v, mul_mem hw hv, ?_, ?_⟩
  · calc star (w * v) * (w * v) = star v * (star w * w) * v := by rw [star_mul]; noncomm_ring
      _ = star v * (v * star v) * v := by rw [hw1, ← hv2]
      _ = (star v * v) * (star v * v) := by noncomm_ring
      _ = p := by rw [hv1, hp.isIdempotentElem.eq]
  · calc w * v * star (w * v) = w * (v * star v) * star w := by rw [star_mul]; noncomm_ring
      _ = w * (star w * w) * star w := by rw [hv2, hw1]
      _ = r := by rw [hwq, hw2]

/-- A projection equivalent to a nonzero projection is nonzero. -/
theorem MvNEquiv.ne_zero_of {M : VonNeumannAlgebra H} {p q : H →L[ℂ] H} (h : MvNEquiv M p q)
    (hq : q ≠ 0) : p ≠ 0 := by
  rintro rfl
  obtain ⟨v, -, h1, h2⟩ := h
  have hv : v = 0 := (CStarRing.star_mul_self_eq_zero_iff v).mp h1
  exact hq (by rw [← h2, hv, zero_mul])

/-- Projections have norm at most one. -/
theorem norm_le_one_of_isStarProjection {p : H →L[ℂ] H} (hp : IsStarProjection p) : ‖p‖ ≤ 1 := by
  have h := CStarRing.norm_star_mul_self (x := p)
  rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq] at h
  nlinarith [norm_nonneg p]

/-! ### The halving sequence for one functional -/

section Sequence

variable (M : VonNeumannAlgebra H) {z : H →L[ℂ] H}

/-- The invariant of the halving sequence: a projection of `M` below `z`, equivalent
to `z`. -/
structure HalfInv (z r : H →L[ℂ] H) : Prop where
  isStarProjection : IsStarProjection r
  mem : r ∈ M
  mul_z : r * z = r
  equiv : MvNEquiv M r z

/-- One halving step. -/
theorem exists_half (hz0 : z ≠ 0)
    (hH4 : ∀ q, IsStarProjection q → q ∈ M → q * z = q → q ≠ 0 →
      ∃ e, IsStarProjection e ∧ e ∈ M ∧ e * q = e ∧ MvNEquiv M e (q - e) ∧ MvNEquiv M e q)
    (ψ : (H →L[ℂ] H) →ₗ[ℂ] ℂ) {r : H →L[ℂ] H} (hr : HalfInv M z r) :
    ∃ r', HalfInv M z r' ∧ r' * r = r' ∧ (ψ r').re ≤ (ψ r).re / 2 := by
  have hr0 : r ≠ 0 := hr.equiv.ne_zero_of hz0
  obtain ⟨e, heP, heM, her, hef, heq⟩ :=
    hH4 r hr.isStarProjection hr.mem hr.mul_z hr0
  have hre : r * e = e := proj_mul_left_of_mul_right heP hr.isStarProjection her
  have hfP : IsStarProjection (r - e) := by
    refine ⟨?_, ?_⟩
    · show (r - e) * (r - e) = r - e
      rw [sub_mul, mul_sub, mul_sub, hr.isStarProjection.isIdempotentElem.eq, hre, her,
        heP.isIdempotentElem.eq]
      abel
    · rw [IsSelfAdjoint, star_sub, hr.isStarProjection.isSelfAdjoint.star_eq,
        heP.isSelfAdjoint.star_eq]
  have hfM : r - e ∈ M := sub_mem hr.mem heM
  have hfr : (r - e) * r = r - e := by
    rw [sub_mul, hr.isStarProjection.isIdempotentElem.eq, her]
  have hez : e * z = e := by rw [← her, mul_assoc, hr.mul_z]
  have hfz : (r - e) * z = r - e := by rw [← hfr, mul_assoc, hr.mul_z]
  have hez' : MvNEquiv M e z := heq.trans heP hr.equiv
  have hfz' : MvNEquiv M (r - e) z := (hef.symm).trans hfP hez'
  have hsum : (ψ e).re + (ψ (r - e)).re = (ψ r).re := by
    rw [map_sub, Complex.sub_re]
    ring
  by_cases hle : (ψ e).re ≤ (ψ (r - e)).re
  · exact ⟨e, ⟨heP, heM, hez, hez'⟩, her, by linarith⟩
  · exact ⟨r - e, ⟨hfP, hfM, hfz, hfz'⟩, hfr, by linarith⟩

/-- The halving sequence attached to a functional `ψ`, as a sequence of
invariant-carrying projections. -/
noncomputable def halfSeq (hz : IsStarProjection z) (hz0 : z ≠ 0)
    (hH4 : ∀ q, IsStarProjection q → q ∈ M → q * z = q → q ≠ 0 →
      ∃ e, IsStarProjection e ∧ e ∈ M ∧ e * q = e ∧ MvNEquiv M e (q - e) ∧ MvNEquiv M e q)
    (hzM : z ∈ M) (ψ : (H →L[ℂ] H) →ₗ[ℂ] ℂ) : ℕ → {r : H →L[ℂ] H // HalfInv M z r}
  | 0 => ⟨z, ⟨hz, hzM, hz.isIdempotentElem.eq, MvNEquiv.refl hz hzM⟩⟩
  | k + 1 =>
    let r := halfSeq hz hz0 hH4 hzM ψ k
    ⟨Classical.choose (exists_half M hz0 hH4 ψ r.2),
      (Classical.choose_spec (exists_half M hz0 hH4 ψ r.2)).1⟩

theorem halfSeq_zero (hz : IsStarProjection z) (hz0 : z ≠ 0)
    (hH4 : ∀ q, IsStarProjection q → q ∈ M → q * z = q → q ≠ 0 →
      ∃ e, IsStarProjection e ∧ e ∈ M ∧ e * q = e ∧ MvNEquiv M e (q - e) ∧ MvNEquiv M e q)
    (hzM : z ∈ M) (ψ : (H →L[ℂ] H) →ₗ[ℂ] ℂ) :
    ((halfSeq M hz hz0 hH4 hzM ψ 0 : {r // HalfInv M z r}) : H →L[ℂ] H) = z := rfl

theorem halfSeq_succ_le (hz : IsStarProjection z) (hz0 : z ≠ 0)
    (hH4 : ∀ q, IsStarProjection q → q ∈ M → q * z = q → q ≠ 0 →
      ∃ e, IsStarProjection e ∧ e ∈ M ∧ e * q = e ∧ MvNEquiv M e (q - e) ∧ MvNEquiv M e q)
    (hzM : z ∈ M) (ψ : (H →L[ℂ] H) →ₗ[ℂ] ℂ) (k : ℕ) :
    (ψ ((halfSeq M hz hz0 hH4 hzM ψ (k + 1) : {r // HalfInv M z r}) : H →L[ℂ] H)).re ≤
      (ψ ((halfSeq M hz hz0 hH4 hzM ψ k : {r // HalfInv M z r}) : H →L[ℂ] H)).re / 2 :=
  (Classical.choose_spec (exists_half M hz0 hH4 ψ (halfSeq M hz hz0 hH4 hzM ψ k).2)).2.2

/-- `ψ(r_k) ≤ 2⁻ᵏ ψ(z)`. -/
theorem halfSeq_le (hz : IsStarProjection z) (hz0 : z ≠ 0)
    (hH4 : ∀ q, IsStarProjection q → q ∈ M → q * z = q → q ≠ 0 →
      ∃ e, IsStarProjection e ∧ e ∈ M ∧ e * q = e ∧ MvNEquiv M e (q - e) ∧ MvNEquiv M e q)
    (hzM : z ∈ M) (ψ : (H →L[ℂ] H) →ₗ[ℂ] ℂ) (k : ℕ) :
    (ψ ((halfSeq M hz hz0 hH4 hzM ψ k : {r // HalfInv M z r}) : H →L[ℂ] H)).re ≤
      (ψ z).re / 2 ^ k := by
  induction k with
  | zero =>
    simp only [pow_zero, div_one]
    exact le_of_eq (congrArg (fun x => (ψ x).re) (halfSeq_zero M hz hz0 hH4 hzM ψ))
  | succ k ih =>
    have h := halfSeq_succ_le M hz hz0 hH4 hzM ψ k
    rw [pow_succ]
    have : (ψ z).re / (2 ^ k * 2) = (ψ z).re / 2 ^ k / 2 := by ring
    rw [this]
    linarith [div_le_div_of_nonneg_right ih (by norm_num : (0 : ℝ) ≤ 2)]

end Sequence

/-! ### The net -/

/-- The finite-sum vector functional `ψ_α = ∑_{ξ ∈ α} ⟪ξ, · ξ⟫`. -/
noncomputable def sumVecFunctional (α : Finset {ξ : H // ‖ξ‖ = 1}) : (H →L[ℂ] H) →ₗ[ℂ] ℂ :=
  ∑ ξ ∈ α, Orthogonalization.Corollaries.vecFunctional (ξ : H)

omit [CompleteSpace H] in
theorem sumVecFunctional_apply (α : Finset {ξ : H // ‖ξ‖ = 1}) (x : H →L[ℂ] H) :
    sumVecFunctional α x = ∑ ξ ∈ α, ⟪(ξ : H), x ξ⟫_ℂ := by
  rw [sumVecFunctional, LinearMap.sum_apply]
  rfl

/-- `⟪ξ, r ξ⟫ = ‖r ξ‖²` for a projection `r`. -/
theorem re_inner_proj_apply {r : H →L[ℂ] H} (hr : IsStarProjection r) (ξ : H) :
    (⟪ξ, r ξ⟫_ℂ).re = ‖r ξ‖ ^ 2 := by
  have h : ⟪ξ, r ξ⟫_ℂ = ⟪r ξ, r ξ⟫_ℂ := by
    conv_lhs => rw [← hr.isIdempotentElem.eq, mul_apply_eq_comp]
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
      hr.isSelfAdjoint.star_eq]
  rw [h, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- **Lemma 5.1.** Under a nonzero type III central projection `z` (given the halving
property H4 at `z`), there is a net of projections `q_α ≤ z` of `M` with
`z − q_α ∼ z` converging strongly to `z`. -/
theorem exists_typeIII_net (M : VonNeumannAlgebra H) {z : H →L[ℂ] H} (hz : IsCentralProj M z)
    (hz0 : z ≠ 0)
    (hH4 : ∀ q, IsStarProjection q → q ∈ M → q * z = q → q ≠ 0 →
      ∃ e, IsStarProjection e ∧ e ∈ M ∧ e * q = e ∧ MvNEquiv M e (q - e) ∧ MvNEquiv M e q) :
    ∃ (κ : Type u) (_ : Preorder κ) (_ : IsDirected κ (· ≤ ·)) (_ : Nonempty κ)
      (q : κ → H →L[ℂ] H),
      (∀ α, IsStarProjection (q α) ∧ q α ∈ M ∧ q α * z = q α ∧ MvNEquiv M (z - q α) z) ∧
        TendstoStrongBdd atTop q z := by
  classical
  have hzP := hz.isStarProjection
  have hzM := hz.mem
  -- the index set: finite sets of unit vectors and a length
  let κ := Finset {ξ : H // ‖ξ‖ = 1} × ℕ
  let r : κ → H →L[ℂ] H := fun a =>
    ((halfSeq M hzP hz0 hH4 hzM (sumVecFunctional a.1) (a.2 + a.1.card) :
      {r // HalfInv M z r}) : H →L[ℂ] H)
  have hr : ∀ a, HalfInv M z (r a) := fun a =>
    (halfSeq M hzP hz0 hH4 hzM (sumVecFunctional a.1) (a.2 + a.1.card)).2
  -- the key bound: for a unit vector `ξ ∈ α`, `‖r_(α,k) ξ‖² ≤ 2⁻ᵏ`
  have hbound : ∀ (a : κ) (ξ : {ξ : H // ‖ξ‖ = 1}), ξ ∈ a.1 →
      ‖r a ξ‖ ^ 2 ≤ (1 / 2) ^ a.2 := by
    intro a ξ hξ
    have h1 := halfSeq_le M hzP hz0 hH4 hzM (sumVecFunctional a.1) (a.2 + a.1.card)
    have h2 : ‖r a ξ‖ ^ 2 ≤ (sumVecFunctional a.1 (r a)).re := by
      rw [sumVecFunctional_apply, Complex.re_sum]
      have : ‖r a ξ‖ ^ 2 = (⟪(ξ : H), r a ξ⟫_ℂ).re := (re_inner_proj_apply (hr a).isStarProjection ξ).symm
      rw [this]
      exact Finset.single_le_sum (f := fun η : {ξ : H // ‖ξ‖ = 1} => (⟪(η : H), r a η⟫_ℂ).re)
        (fun η _ => by rw [re_inner_proj_apply (hr a).isStarProjection]; positivity) hξ
    have h3 : (sumVecFunctional a.1 z).re ≤ a.1.card := by
      rw [sumVecFunctional_apply, Complex.re_sum]
      calc ∑ η ∈ a.1, (⟪(η : H), z η⟫_ℂ).re ≤ ∑ η ∈ a.1, (1 : ℝ) := by
            refine Finset.sum_le_sum fun η _ => ?_
            rw [re_inner_proj_apply hzP]
            have hn : ‖z η‖ ≤ 1 := by
              calc ‖z η‖ ≤ ‖z‖ * ‖(η : H)‖ := z.le_opNorm _
                _ ≤ 1 * 1 := by
                    gcongr
                    · exact norm_le_one_of_isStarProjection hzP
                    · exact η.2.le
                _ = 1 := one_mul 1
            nlinarith [norm_nonneg (z η)]
        _ = a.1.card := by simp
    have h4 : (a.1.card : ℝ) / 2 ^ (a.2 + a.1.card) ≤ (1 / 2) ^ a.2 := by
      rw [div_le_iff₀ (by positivity)]
      have h5 : (1 / 2 : ℝ) ^ a.2 * 2 ^ (a.2 + a.1.card) = 2 ^ a.1.card := by
        rw [pow_add, one_div_pow]
        field_simp
      rw [h5]
      exact_mod_cast Nat.lt_two_pow_self.le
    calc ‖r a ξ‖ ^ 2 ≤ (sumVecFunctional a.1 (r a)).re := h2
      _ ≤ (sumVecFunctional a.1 z).re / 2 ^ (a.2 + a.1.card) := h1
      _ ≤ (a.1.card : ℝ) / 2 ^ (a.2 + a.1.card) := by gcongr
      _ ≤ (1 / 2) ^ a.2 := h4
  -- strong convergence of `r` to `0`
  have hrlim : ∀ ξ : H, Tendsto (fun a => r a ξ) atTop (𝓝 0) := by
    intro ξ
    by_cases hξ0 : ξ = 0
    · simp [hξ0]
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show 0 < (ε / ‖ξ‖) ^ 2 by positivity)
      (show (1 / 2 : ℝ) < 1 by norm_num)
    set ξ' : {ξ : H // ‖ξ‖ = 1} := ⟨((‖ξ‖ : ℂ))⁻¹ • ξ, norm_smul_inv_norm hξ0⟩ with hξ'
    have hev : ∀ᶠ a : κ in atTop, ({ξ'}, N) ≤ a := Filter.eventually_ge_atTop _
    refine hev.mono fun a ha => ?_
    rw [Prod.le_def] at ha
    have hmem : ξ' ∈ a.1 := ha.1 (Finset.mem_singleton_self ξ')
    have hb := hbound a ξ' hmem
    -- `r a ξ = ‖ξ‖ • r a ξ'`
    have hrξ : r a ξ = (‖ξ‖ : ℂ) • r a ξ' := by
      rw [hξ']
      show r a ξ = (‖ξ‖ : ℂ) • r a (((‖ξ‖ : ℂ))⁻¹ • ξ)
      rw [map_smul, smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hξ0)),
        one_smul]
    rw [dist_zero_right, hrξ, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg ξ)]
    have hpow : (1 / 2 : ℝ) ^ a.2 ≤ (1 / 2) ^ N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) ha.2
    have hlt : ‖r a ξ'‖ ^ 2 < (ε / ‖ξ‖) ^ 2 := lt_of_le_of_lt (hb.trans hpow) hN
    have hlt' : ‖r a ξ'‖ < ε / ‖ξ‖ := lt_of_pow_lt_pow_left₀ 2 (by positivity) hlt
    have hξpos : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ0
    calc ‖ξ‖ * ‖r a ξ'‖ < ‖ξ‖ * (ε / ‖ξ‖) := by gcongr
      _ = ε := by field_simp
  -- the net `q_a := z − r_a`
  refine ⟨κ, inferInstance, inferInstance, inferInstance, fun a => z - r a, fun a => ?_, ?_⟩
  · have hra := hr a
    have hzr : z * r a = r a := by rw [(hz.commute _ hra.mem).eq, hra.mul_z]
    refine ⟨?_, sub_mem hzM hra.mem, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · show (z - r a) * (z - r a) = z - r a
        rw [sub_mul, mul_sub, mul_sub, hzP.isIdempotentElem.eq, hzr, hra.mul_z,
          hra.isStarProjection.isIdempotentElem.eq]
        abel
      · rw [IsSelfAdjoint, star_sub, hzP.isSelfAdjoint.star_eq,
          hra.isStarProjection.isSelfAdjoint.star_eq]
    · rw [sub_mul, hzP.isIdempotentElem.eq, hra.mul_z]
    · rw [sub_sub_cancel]
      exact hra.equiv
  · refine ⟨⟨1, fun a => ?_⟩, fun ξ => ?_⟩
    · exact norm_le_one_of_isStarProjection (by
        have hra := hr a
        have hzr : z * r a = r a := by rw [(hz.commute _ hra.mem).eq, hra.mul_z]
        refine ⟨?_, ?_⟩
        · show (z - r a) * (z - r a) = z - r a
          rw [sub_mul, mul_sub, mul_sub, hzP.isIdempotentElem.eq, hzr, hra.mul_z,
            hra.isStarProjection.isIdempotentElem.eq]
          abel
        · rw [IsSelfAdjoint, star_sub, hzP.isSelfAdjoint.star_eq,
            hra.isStarProjection.isSelfAdjoint.star_eq])
    · simp only [sub_apply]
      have := (tendsto_const_nhds (x := z ξ)).sub (hrlim ξ)
      rwa [sub_zero] at this

end Orthogonalization.MvN
