/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/Blocks/Local.lean
-/
/-
# Tier T1b, shared vocabulary: central projections and Theorem 1.2 "at `z`"

Tier T1b (`PLAN.md` §3, §8) proves Theorem 1.2 for an arbitrary von Neumann
algebra `M` on a finite-dimensional Hilbert space by cutting `M` along its
minimal central projections `z_j`, transporting the `B(H)` engine of tier T1a
to each block, and gluing. The intermediate results are all phrased on the
ambient space `H`, relative to a central projection `z` of `M`:

* `IsCentralProj M z`: `z` is a projection of `M` commuting with `M`;
* `OrthAt M z ι`: Theorem 1.2 for POVMs `(a i)` of `M` supported in `z`
  (positive, `∑ a i = z`) and functionals positive on `M` with `φ z = 1`,
  with the PVM produced supported in `z` as well.

`OrthAt M 1 ι` is Theorem 1.2 for `M` (with a functional positive on `M` and
normalized, i.e. the functional of a `NormalState M`). Proof-side only.
-/
import Mathlib
import MIPRE.Background.Orthonormalization.Orthogonalization.Positivity

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace Orthogonalization.Blocks

open scoped BigOperators ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A central projection of `M`: a projection belonging to `M` and commuting with
every element of `M`. -/
structure IsCentralProj (M : VonNeumannAlgebra H) (z : H →L[ℂ] H) : Prop where
  isStarProjection : IsStarProjection z
  mem : z ∈ M
  commute : ∀ x ∈ M, Commute z x

/-- **Theorem 1.2 at `z`** (proof-side): for every functional `φ` positive on `M`
with `φ z = 1` and every POVM `(a i)` in `M` supported in `z` (positive elements
of `M` summing to `z`) with `φ (∑ a i²) > 1 − ε`, there is a PVM `(p i)` in `M`
supported in `z` (projections of `M` with `p i z = p i`, summing to `z`) with
`φ (∑ |a i − p i|²) < 9 ε`. -/
def OrthAt (M : VonNeumannAlgebra H) (z : H →L[ℂ] H) (ι : Type*) [Fintype ι] : Prop :=
  ∀ (φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ), (∀ x ∈ M, 0 ≤ φ (star x * x)) → φ z = 1 →
    ∀ (a : ι → H →L[ℂ] H), (∀ i, a i ∈ M) → (∀ i, 0 ≤ a i) → ∑ i, a i = z →
      ∀ ε : ℝ, 1 - ε < (φ (∑ i, a i * a i)).re →
        ∃ p : ι → H →L[ℂ] H, (∀ i, p i ∈ M) ∧ (∀ i, IsStarProjection (p i)) ∧
          (∀ i, p i * z = p i) ∧ ∑ i, p i = z ∧
          (φ (∑ i, star (a i - p i) * (a i - p i))).re < 9 * ε

/-! ### Elementary facts about operators supported in a projection -/

/-- A positive operator dominated by a projection is supported in it:
`0 ≤ a ≤ z` with `z` a projection gives `a z = a`. -/
theorem mul_eq_self_of_le_proj {a z : H →L[ℂ] H} (hz : IsStarProjection z) (ha0 : 0 ≤ a)
    (haz : a ≤ z) : a * z = a := by
  -- `(1 - z) a (1 - z) ≤ (1 - z) z (1 - z) = 0`, so `√a (1 - z) = 0`, so `a (1 - z) = 0`.
  have hsa : IsSelfAdjoint z := hz.isSelfAdjoint
  have h1z : star (1 - z) = 1 - z := by rw [star_sub, star_one, hsa.star_eq]
  have hconj : star (1 - z) * a * (1 - z) ≤ star (1 - z) * z * (1 - z) := conj_le_conj haz _
  have hzero : star (1 - z) * z * (1 - z) = 0 := by
    rw [h1z]
    have : (1 - z) * z = 0 := by
      rw [sub_mul, one_mul, hz.isIdempotentElem.eq, sub_self]
    rw [this, zero_mul]
  rw [hzero] at hconj
  have hnn : 0 ≤ star (1 - z) * a * (1 - z) := conj_nonneg ha0 _
  have heq : star (1 - z) * a * (1 - z) = 0 := le_antisymm hconj hnn
  -- write `a = √a √a`
  set r := CFC.sqrt a with hr
  have hrr : r * r = a := CFC.sqrt_mul_sqrt_self a ha0
  have hrsa : star r = r := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)).star_eq
  have hkey : star (r * (1 - z)) * (r * (1 - z)) = 0 := by
    rw [star_mul, hrsa, h1z]
    calc (1 - z) * r * (r * (1 - z)) = (1 - z) * (r * r) * (1 - z) := by noncomm_ring
      _ = star (1 - z) * a * (1 - z) := by rw [hrr, h1z]
      _ = 0 := heq
  have hr0 : r * (1 - z) = 0 := CStarRing.star_mul_self_eq_zero_iff _ |>.mp hkey
  have : a * (1 - z) = 0 := by
    rw [← hrr, mul_assoc, hr0, mul_zero]
  rw [mul_sub, mul_one] at this
  exact (sub_eq_zero.mp this).symm

/-- A projection `p ≤ z` (`z` a projection) satisfies `p z = p`. -/
theorem proj_mul_eq_self_of_le {p z : H →L[ℂ] H} (hp : IsStarProjection p) (hz : IsStarProjection z)
    (hpz : p ≤ z) : p * z = p :=
  mul_eq_self_of_le_proj hz hp.nonneg hpz

/-- If `p z = p` for projections `p`, `z`, then also `z p = p`. -/
theorem proj_mul_left_of_mul_right {p z : H →L[ℂ] H} (hp : IsStarProjection p)
    (hz : IsStarProjection z) (h : p * z = p) : z * p = p := by
  have := congrArg star h
  rwa [star_mul, hp.isSelfAdjoint.star_eq, hz.isSelfAdjoint.star_eq] at this

/-- Each term of a family of positive operators summing to `z` is dominated by `z`. -/
theorem le_of_sum_eq {ι : Type*} [Fintype ι] {a : ι → H →L[ℂ] H} {z : H →L[ℂ] H}
    (ha0 : ∀ i, 0 ≤ a i) (haz : ∑ i, a i = z) (i : ι) : a i ≤ z := by
  rw [← haz]
  exact Finset.single_le_sum (fun j _ => ha0 j) (Finset.mem_univ i)

/-- Each term of a family of positive operators summing to a projection `z` is supported
in `z`. -/
theorem mul_eq_self_of_sum_eq {ι : Type*} [Fintype ι] {a : ι → H →L[ℂ] H} {z : H →L[ℂ] H}
    (hz : IsStarProjection z) (ha0 : ∀ i, 0 ≤ a i) (haz : ∑ i, a i = z) (i : ι) :
    a i * z = a i :=
  mul_eq_self_of_le_proj hz (ha0 i) (le_of_sum_eq ha0 haz i)

end Orthogonalization.Blocks
