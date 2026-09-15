/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/Blocks/Glue.lean
-/
/-
# Tier T1b: gluing Theorem 1.2 along a central decomposition

If `1 = ∑ j, z j` is an orthogonal sum of central projections of `M` and Theorem
1.2 holds at every `z j` (`OrthAt M (z j) ι`), then it holds for `M`
(`OrthAt M 1 ι`). This is the direct-sum step **G** of the paper's proof
(`PLAN.md` §1), written out with the slack bookkeeping the paper leaves
implicit: the state splits as `φ = ∑ j, m j • φ_j` with `m j = φ (z j)`, the
blocks of positive mass receive the slack `ε_j = 1 − s_j / m_j + η` where
`s_j = φ ((∑ a_i²) z_j)` and `η = (ε − (1 − φ(∑ a_i²))) / 2 > 0`, the blocks of
mass zero get an arbitrary PVM (their contribution vanishes by the zero-mass
lemma), and the pieces recombine to `< 9 ε` because the cross terms of
`∑_j (a_i z_j − p^j_i)` vanish. Proof-side only.
-/
import Mathlib
import MIPRE.Background.Orthonormalization.Orthogonalization.Blocks.Local
import MIPRE.Background.Orthonormalization.Orthogonalization.Blocks.StateOnM

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace Orthogonalization.Blocks

open scoped BigOperators ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `star (∑ b j) * ∑ b j = ∑ star (b j) * b j` when the cross terms vanish. -/
theorem star_sum_mul_sum {κ : Type*} [Fintype κ] {A : Type*} [NonUnitalNonAssocSemiring A]
    [StarRing A] (b : κ → A) (h : ∀ j k, j ≠ k → star (b j) * b k = 0) :
    star (∑ j, b j) * ∑ j, b j = ∑ j, star (b j) * b j := by
  classical
  rw [star_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single j]
  · intro k _ hk
    exact h j k (Ne.symm hk)
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- Theorem 1.2 at `z` for the functionals satisfying a predicate `P` (`OrthAt M z ι`
is the case `P = fun _ => True`; the normal functionals are the case of tier T3). -/
def OrthAtP (M : VonNeumannAlgebra H) (z : H →L[ℂ] H) (ι : Type*) [Fintype ι]
    (P : ((H →L[ℂ] H) →ₗ[ℂ] ℂ) → Prop) : Prop :=
  ∀ (φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ), P φ → (∀ x ∈ M, 0 ≤ φ (star x * x)) → φ z = 1 →
    ∀ (a : ι → H →L[ℂ] H), (∀ i, a i ∈ M) → (∀ i, 0 ≤ a i) → ∑ i, a i = z →
      ∀ ε : ℝ, 1 - ε < (φ (∑ i, a i * a i)).re →
        ∃ p : ι → H →L[ℂ] H, (∀ i, p i ∈ M) ∧ (∀ i, IsStarProjection (p i)) ∧
          (∀ i, p i * z = p i) ∧ ∑ i, p i = z ∧
          (φ (∑ i, star (a i - p i) * (a i - p i))).re < 9 * ε

theorem orthAtP_true_iff (M : VonNeumannAlgebra H) (z : H →L[ℂ] H) (ι : Type*) [Fintype ι] :
    OrthAtP M z ι (fun _ => True) ↔ OrthAt M z ι :=
  ⟨fun h φ => h φ trivial, fun h φ _ => h φ⟩

/-- **Gluing.** Theorem 1.2 at each block of an orthogonal central decomposition of
`1` gives Theorem 1.2 for `M`, for any class `P` of functionals closed under
positive real scaling. -/
theorem orthAtP_one_of_blocks (M : VonNeumannAlgebra H) {κ : Type*} [Fintype κ]
    (z : κ → H →L[ℂ] H) (hz : ∀ j, IsCentralProj M (z j))
    (hzo : ∀ j k, j ≠ k → z j * z k = 0) (hzs : ∑ j, z j = 1)
    (ι : Type*) [Fintype ι] (P : ((H →L[ℂ] H) →ₗ[ℂ] ℂ) → Prop)
    (hP : ∀ φ, P φ → ∀ c : ℝ, 0 < c → P ((c : ℂ) • φ))
    (h : ∀ j, OrthAtP M (z j) ι P) : OrthAtP M 1 ι P := by
  classical
  intro φ hPφ hφ hφ1 a haM ha0 haz ε hε
  -- the output set is nonempty (otherwise `1 = 0` and `φ 1 = 1` contradict each other)
  rcases isEmpty_or_nonempty ι with hι | hι
  · exfalso
    rw [Fintype.sum_empty] at haz
    have h0 : φ 1 = 0 := by rw [← haz, map_zero]
    rw [hφ1] at h0
    exact one_ne_zero h0
  obtain ⟨i₀⟩ := hι
  have hzP : ∀ j, IsStarProjection (z j) := fun j => (hz j).isStarProjection
  have hzM : ∀ j, z j ∈ M := fun j => (hz j).mem
  have hcomm : ∀ j, ∀ x ∈ M, z j * x = x * z j := fun j x hx => ((hz j).commute x hx).eq
  -- masses and block values
  set m : κ → ℝ := fun j => (φ (z j)).re with hm
  set Q : H →L[ℂ] H := ∑ i, a i * a i with hQ
  set s : κ → ℝ := fun j => (φ (Q * z j)).re with hs
  have hQM : Q ∈ M := sum_mem fun i _ => mul_mem (haM i) (haM i)
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun i _ => by
    have := star_mul_self_nonneg (a i)
    rwa [(IsSelfAdjoint.of_nonneg (ha0 i)).star_eq] at this
  have hQ1 : Q ≤ 1 := by
    rw [← haz]
    exact Finset.sum_le_sum fun i _ => sq_le_self_of_le_one (ha0 i) (le_of_sum_eq ha0 haz i)
  have hQz : ∀ j, z j * Q * z j = Q * z j := fun j => by
    rw [hcomm j Q hQM, mul_assoc, (hzP j).isIdempotentElem.eq]
  have hQz0 : ∀ j, 0 ≤ Q * z j := fun j =>
    mul_nonneg_of_commute hQ0 (hzP j).nonneg ((hz j).commute Q hQM).symm
  have hQzM : ∀ j, Q * z j ∈ M := fun j => mul_mem hQM (hzM j)
  have hm0 : ∀ j, 0 ≤ m j := fun j => re_map_nonneg_of_mem hφ (hzM j) (hzP j).nonneg
  have hmsum : ∑ j, m j = 1 := by
    have h1 : φ (∑ j, z j) = 1 := by rw [hzs, hφ1]
    rw [map_sum] at h1
    have h2 := congrArg Complex.re h1
    rwa [Complex.re_sum, Complex.one_re] at h2
  have hs0 : ∀ j, 0 ≤ s j := fun j => re_map_nonneg_of_mem hφ (hQzM j) (hQz0 j)
  have hsm : ∀ j, s j ≤ m j := fun j => by
    have h1 : Q * z j ≤ z j := by
      have := conj_le_conj hQ1 (z j)
      rwa [(hzP j).isSelfAdjoint.star_eq, mul_one, (hzP j).isIdempotentElem.eq, hQz j] at this
    exact re_map_le_of_mem hφ (hQzM j) (hzM j) h1
  have hssum : ∑ j, s j = (φ Q).re := by
    have h1 : ∑ j, Q * z j = Q := by rw [← Finset.mul_sum, hzs, mul_one]
    show ∑ j, (φ (Q * z j)).re = (φ Q).re
    rw [← Complex.re_sum, ← map_sum, h1]
  -- the slack
  set S := (φ Q).re with hS
  set η : ℝ := (ε - (1 - S)) / 2 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  -- the block POVMs
  have hazj : ∀ j i, a i * z j ∈ M := fun j i => mul_mem (haM i) (hzM j)
  have ha0j : ∀ j i, 0 ≤ a i * z j := fun j i =>
    mul_nonneg_of_commute (ha0 i) (hzP j).nonneg ((hz j).commute _ (haM i)).symm
  have hsumj : ∀ j, ∑ i, a i * z j = z j := fun j => by rw [← Finset.sum_mul, haz, one_mul]
  have hsqj : ∀ j, ∑ i, (a i * z j) * (a i * z j) = Q * z j := fun j => by
    rw [hQ, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc (a i), ← mul_assoc (z j), hcomm j (a i) (haM i), mul_assoc (a i),
      (hzP j).isIdempotentElem.eq, ← mul_assoc]
  -- Theorem 1.2 on each block, with the slack `η`
  have hblock : ∀ j, ∃ q : ι → H →L[ℂ] H, (∀ i, q i ∈ M) ∧ (∀ i, IsStarProjection (q i)) ∧
      (∀ i, q i * z j = q i) ∧ ∑ i, q i = z j ∧
      (φ (∑ i, star (a i * z j - q i) * (a i * z j - q i))).re ≤
        9 * (m j - s j + m j * η) := by
    intro j
    by_cases hmj : m j = 0
    · -- a block of mass zero: any PVM will do
      refine ⟨fun i => if i = i₀ then z j else 0, ?_, ?_, ?_, ?_, ?_⟩
      · intro i
        dsimp only
        split_ifs
        exacts [hzM j, zero_mem M]
      · intro i
        dsimp only
        split_ifs
        exacts [hzP j, IsStarProjection.zero _]
      · intro i
        dsimp only
        split_ifs
        exacts [(hzP j).isIdempotentElem.eq, zero_mul _]
      · simp
      · dsimp only
        have hsj : s j = 0 := le_antisymm (by rw [← hmj]; exact hsm j) (hs0 j)
        have hzero : (φ (∑ i, star (a i * z j - (if i = i₀ then z j else 0)) *
            (a i * z j - (if i = i₀ then z j else 0)))).re = 0 := by
          rw [map_sum, Complex.re_sum]
          refine Finset.sum_eq_zero fun i _ => ?_
          refine re_map_star_mul_self_eq_zero hφ (hzP j) (hzM j) ?_ ?_ hmj
          · exact sub_mem (hazj j i) (by split_ifs; exacts [hzM j, zero_mem M])
          · rw [sub_mul, mul_assoc, (hzP j).isIdempotentElem.eq]
            congr 1
            split_ifs
            exacts [(hzP j).isIdempotentElem.eq, zero_mul _]
        rw [hzero, hmj, hsj]
        simp
    · -- a block of positive mass: the normalized functional `m⁻¹ φ`
      have hmpos : 0 < m j := lt_of_le_of_ne (hm0 j) (Ne.symm hmj)
      set ψ : (H →L[ℂ] H) →ₗ[ℂ] ℂ := ((m j)⁻¹ : ℂ) • φ with hψ
      have hψapp : ∀ x, ψ x = ((m j)⁻¹ : ℂ) * φ x := fun x => by
        rw [hψ, LinearMap.smul_apply, smul_eq_mul]
      have hψre : ∀ x, (ψ x).re = (m j)⁻¹ * (φ x).re := fun x => by
        rw [hψapp, ← Complex.ofReal_inv, Complex.re_ofReal_mul]
      have hψpos : ∀ x ∈ M, 0 ≤ ψ (star x * x) := fun x hx => by
        rw [hψapp]
        have hinv : (0 : ℂ) ≤ ((m j : ℂ))⁻¹ := by
          rw [← Complex.ofReal_inv]
          exact Complex.zero_le_real.mpr (inv_nonneg.mpr (hm0 j))
        exact mul_nonneg hinv (hφ x hx)
      have hψz : ψ (z j) = 1 := by
        rw [hψapp, map_eq_ofReal_re_of_mem hφ (hzM j) (hzP j).nonneg]
        show ((m j)⁻¹ : ℂ) * ((m j : ℝ) : ℂ) = 1
        rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, inv_mul_cancel₀ hmj, Complex.ofReal_one]
      set εj : ℝ := 1 - s j / m j + η with hεj
      have hεj' : 1 - εj < (ψ (∑ i, (a i * z j) * (a i * z j))).re := by
        rw [hψre, hsqj j, hεj]
        show 1 - (1 - s j / m j + η) < (m j)⁻¹ * s j
        rw [inv_mul_eq_div]
        linarith
      have hPψ : P ψ := by
        have := hP φ hPφ (m j)⁻¹ (inv_pos.mpr hmpos)
        rwa [Complex.ofReal_inv] at this
      obtain ⟨q, hqM, hqP, hqz, hqs, hqb⟩ :=
        h j ψ hPψ hψpos hψz (fun i => a i * z j) (hazj j) (ha0j j) (hsumj j) εj hεj'
      refine ⟨q, hqM, hqP, hqz, hqs, ?_⟩
      rw [hψre] at hqb
      have h2 := mul_lt_mul_of_pos_left hqb hmpos
      rw [mul_inv_cancel_left₀ hmj] at h2
      refine le_of_lt (lt_of_lt_of_eq h2 ?_)
      rw [hεj]
      field_simp
  choose q hqM hqP hqz hqs hqb using hblock
  have hzq : ∀ j i, z j * q j i = q j i := fun j i => by rw [hcomm j _ (hqM j i), hqz j i]
  refine ⟨fun i => ∑ j, q j i, fun i => sum_mem fun j _ => hqM j i, ?_, fun i => mul_one _, ?_, ?_⟩
  · -- the sum over the blocks is a projection
    intro i
    refine ⟨?_, isSelfAdjoint_sum _ fun j _ => (hqP j i).isSelfAdjoint⟩
    show (∑ j, q j i) * (∑ j, q j i) = ∑ j, q j i
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single j]
    · exact (hqP j i).isIdempotentElem.eq
    · intro k _ hk
      rw [← hqz j i, ← hzq k i, mul_assoc, ← mul_assoc (z j), hzo j k (Ne.symm hk), zero_mul,
        mul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  · -- the projections sum to `1`
    rw [Finset.sum_comm]
    simp only [hqs]
    exact hzs
  · -- the estimate
    have hbM : ∀ j i, a i * z j - q j i ∈ M := fun j i => sub_mem (hazj j i) (hqM j i)
    have hbz : ∀ j i, (a i * z j - q j i) * z j = a i * z j - q j i := fun j i => by
      rw [sub_mul, mul_assoc, (hzP j).isIdempotentElem.eq, hqz j i]
    have hzb : ∀ j i, z j * (a i * z j - q j i) = a i * z j - q j i := fun j i => by
      rw [hcomm j _ (hbM j i), hbz j i]
    have hdecomp : ∀ i, a i - ∑ j, q j i = ∑ j, (a i * z j - q j i) := fun i => by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hzs, mul_one]
    have horth : ∀ i, ∀ j k, j ≠ k →
        star (a i * z j - q j i) * (a i * z k - q k i) = 0 := fun i j k hjk => by
      have h1 : star (a i * z j - q j i) = star (a i * z j - q j i) * z j := by
        conv_lhs => rw [← hzb j i]
        rw [star_mul, (hzP j).isSelfAdjoint.star_eq]
      rw [h1, ← hzb k i, mul_assoc, ← mul_assoc (z j), hzo j k hjk, zero_mul, mul_zero]
    have hkey : (φ (∑ i, star (a i - ∑ j, q j i) * (a i - ∑ j, q j i))).re =
        ∑ j, (φ (∑ i, star (a i * z j - q j i) * (a i * z j - q j i))).re := by
      simp only [hdecomp]
      rw [← Complex.re_sum, ← map_sum]
      congr 2
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact star_sum_mul_sum (fun j => a i * z j - q j i) (horth i)
    rw [hkey]
    calc ∑ j, (φ (∑ i, star (a i * z j - q j i) * (a i * z j - q j i))).re
        ≤ ∑ j, 9 * (m j - s j + m j * η) := Finset.sum_le_sum fun j _ => hqb j
      _ = 9 * (1 - S + η) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
            hmsum, hssum, one_mul]
      _ < 9 * ε := by rw [hη]; linarith

/-- **Gluing** for arbitrary positive functionals. -/
theorem orthAt_one_of_blocks (M : VonNeumannAlgebra H) {κ : Type*} [Fintype κ]
    (z : κ → H →L[ℂ] H) (hz : ∀ j, IsCentralProj M (z j))
    (hzo : ∀ j k, j ≠ k → z j * z k = 0) (hzs : ∑ j, z j = 1)
    (ι : Type*) [Fintype ι] (h : ∀ j, OrthAt M (z j) ι) : OrthAt M 1 ι :=
  (orthAtP_true_iff M 1 ι).mp (orthAtP_one_of_blocks M z hz hzo hzs ι (fun _ => True)
    (fun _ _ _ _ => trivial) fun j => (orthAtP_true_iff M (z j) ι).mpr (h j))

end Orthogonalization.Blocks
