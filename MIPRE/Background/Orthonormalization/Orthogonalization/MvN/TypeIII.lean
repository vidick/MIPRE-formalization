/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/MvN/TypeIII.lean
-/
/-
# Tier T3, type III: Theorem 1.2 at a type III central projection (Section 5)

The type III case of Theorem 1.2 of the paper, relative to a central projection
`z` (the type III summand) with the halving property of interface field H4, for
the functionals normal on `M`. The argument is the paper's, with `1` replaced
by `z` throughout:

* Lemma 5.1 (`MvN/TypeIIINet.lean`) gives a net `(q_α)` of projections of `M`
  below `z`, converging strongly to `z`, with `z − q_α ∼ z`; the halving gives
  isometries `u_i ∈ M` with `∑ u_i u_i* = z` (`MvN/Isometries.lean`), so
  `1_n ⊗ z ∼ e_{00} ⊗ z` in `M_n(M)` (`mvNEquiv_single_amplify_of_isometries`).
* For each `α`, in `M_n(M)`: the column `v_α = ∑ᵢ e_{i0} ⊗ √aᵢ q_α` is a partial
  isometry with `v_α* v_α = e_{00} ⊗ q_α`, and `1_n ⊗ z − v_α v_α*` is equivalent
  to a subprojection of `e_{00} ⊗ (z − q_α)` through some `w_α`; then
  `u_α = v_α + w_α` satisfies `u_α u_α* = 1_n ⊗ z` and `e_{00} ⊗ q_α ≤ u_α* u_α ≤
  e_{00} ⊗ z`, and the projections `p_{i,α} = (u_α* (e_{ii} ⊗ z) u_α)₀₀` are
  pairwise orthogonal, with `q_α ≤ ∑ᵢ p_{i,α} ≤ z` and `q_α p_{i,α} q_α = q_α aᵢ q_α`
  (`exists_typeIII_projections`).
* The estimate: `aᵢ − p_{i,α} = (aᵢ − q_α aᵢ q_α) − p_{i,α} (z − q_α) − (z − q_α) p_{i,α} q_α`,
  whose three `φ`-norms tend to `0`, are bounded by `φ(z − q_α) → 0`, and tend to
  `φ(∑ᵢ (aᵢ − aᵢ²)) < ε` respectively (Lemma 4.1 along the net), and the PVM is
  completed by `z − ∑ᵢ p_{i,α}` on the output `0`, an error `≤ φ(z − q_α) → 0`
  (`exists_pvm_estimate_of_projections`); the weighted triangle inequality
  `‖x + y‖² ≤ (1 + s)‖x‖² + (1 + s⁻¹)‖y‖²` replaces the paper's square roots.

`orthAtN_of_typeIII_fin` is the theorem for the output set `Fin n`, and
`orthAtN_of_typeIII` transports it to any finite output set. No statement of
the paper is made here; proof-side only.
-/
import Mathlib
import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.BlockCalc
import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.Isometries
import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.Semifinite

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

/- The real-algebra structure of `H^n →L[ℂ] H^n` (needed by `CFC.sqrt`) is found by instance
search only after unfolding `PiLp`, which exceeds the default heartbeat budget. -/
set_option synthInstance.maxHeartbeats 100000

namespace Orthogonalization.MvN

open scoped BigOperators ComplexOrder InnerProductSpace
open Filter Topology CommutingRepetition.VN Blocks FinDim

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Small facts about operators on `H^n`

`star_add`, `star_sub` and `star_zero` do not rewrite on `H^n →L[ℂ] H^n` (the instance path
through `PiLp` is not recognized); the same identities stated on `H →L[ℂ] H` for an arbitrary
`H` and instantiated at `H^n` do. -/

theorem clm_star_add (x y : H →L[ℂ] H) : star (x + y) = star x + star y := star_add x y

theorem clm_star_sub (x y : H →L[ℂ] H) : star (x - y) = star x - star y := star_sub x y

theorem clm_star_zero : star (0 : H →L[ℂ] H) = 0 := star_zero _

/-- The diagonal entries of a positive operator on `H^n` are positive. -/
theorem entry_diag_nonneg {n : ℕ} {X : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n)}
    (hX : 0 ≤ X) (i : Fin n) : 0 ≤ entry X i i := by
  obtain ⟨c, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hX
  rw [entry_star_mul]
  exact Finset.sum_nonneg fun k _ => star_mul_self_nonneg _

/-- The diagonal entries are monotone for the Loewner order. -/
theorem entry_diag_le {n : ℕ} {X Y : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n)}
    (h : X ≤ Y) (i : Fin n) : entry X i i ≤ entry Y i i := by
  rw [← sub_nonneg, ← entry_sub]
  exact entry_diag_nonneg (sub_nonneg.mpr h) i

theorem single_add {n : ℕ} (i : Fin n) (x y : H →L[ℂ] H) :
    single i (x + y) = single i x + single i y := by
  unfold single
  rw [← blockProj_add]
  congr 1
  funext j
  split_ifs <;> simp

theorem single_sub {n : ℕ} (i : Fin n) (x y : H →L[ℂ] H) :
    single i (x - y) = single i x - single i y := by
  unfold single
  rw [← blockProj_sub]
  congr 1
  funext j
  split_ifs <;> simp

/-! ### Two equivalences of projections in `M_n(M)` -/

/-- Equivalent projections of `M` give equivalent single-block projections of `M_n(M)`. -/
theorem mvNEquiv_single {M : VonNeumannAlgebra H} {p q : H →L[ℂ] H} (h : MvNEquiv M p q)
    {n : ℕ} (i : Fin n) : MvNEquiv (matrixAlgebra M n) (single i p) (single i q) := by
  obtain ⟨v, hvM, hv1, hv2⟩ := h
  exact ⟨single i v, single_mem i hvM, by rw [single_star, single_mul_single_same, hv1],
    by rw [single_star, single_mul_single_same, hv2]⟩

/-- Isometries `u_i ∈ M` with `u_i* u_i = z` and orthogonal ranges summing to `z` realize
`e_{00} ⊗ z ∼ 1_n ⊗ z` in `M_n(M)`, through the column `∑ᵢ e_{i0} ⊗ u_i*` (the adjoint of the
paper's row `∑ᵢ e_{0i} ⊗ u_i`). -/
theorem mvNEquiv_single_amplify_of_isometries {M : VonNeumannAlgebra H} {z : H →L[ℂ] H}
    {n : ℕ} [NeZero n] {u : Fin n → H →L[ℂ] H} (huM : ∀ i, u i ∈ M)
    (huu : ∀ i, star (u i) * u i = z) (huo : ∀ i j, i ≠ j → star (u i) * u j = 0)
    (hus : ∑ i, u i * star (u i) = z) :
    MvNEquiv (matrixAlgebra M n) (single 0 z) (amplify n z) := by
  refine ⟨col 0 (fun i => star (u i)), col_mem (fun i => star_mem (huM i)) 0, ?_, ?_⟩
  · rw [star_col_mul_col]
    congr 1
    rw [← hus]
    exact Finset.sum_congr rfl fun i _ => by rw [star_star]
  · refine ext_entry fun i j => ?_
    rw [entry_mul_star, entry_amplify]
    simp only [entry_col]
    rw [Finset.sum_eq_single (0 : Fin n)]
    · simp only [if_true, star_star]
      by_cases hij : i = j
      · subst hij
        simp [huu]
      · simp [hij, huo i j hij]
    · intro k _ hk
      simp [hk]
    · intro h
      exact absurd (Finset.mem_univ _) h

/-! ### The projections `(u* (e_{ii} ⊗ z) u)₀₀` of a partial isometry -/

/-- From a partial isometry `u ∈ M_n(M)` with `u u* = 1_n ⊗ z` and `u (e_{00} ⊗ z) = u`: the
operators `pᵢ = (u* (e_{ii} ⊗ z) u)₀₀` are pairwise orthogonal projections of `M` below `z`
with `e_{00} ⊗ ∑ᵢ pᵢ = u* u` and `u* (e_{ii} ⊗ z) u = e_{00} ⊗ pᵢ`. -/
theorem exists_orth_projections_of_partial_isometry (M : VonNeumannAlgebra H) {z : H →L[ℂ] H}
    (hz : IsStarProjection z) (hzM : z ∈ M) {n : ℕ} [NeZero n]
    {u : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n)} (huM : u ∈ matrixAlgebra M n)
    (huu' : u * star u = amplify n z) (huz : u * single 0 z = u) :
    ∃ p : Fin n → H →L[ℂ] H, (∀ i, p i ∈ M) ∧ (∀ i, IsStarProjection (p i)) ∧
      (∀ i, p i * z = p i) ∧ (∀ i j, i ≠ j → p i * p j = 0) ∧
      single 0 (∑ i, p i) = star u * u ∧ ∀ i, star u * single i z * u = single 0 (p i) := by
  have hZ0 : IsStarProjection (single (0 : Fin n) z) := isStarProjection_single 0 hz
  have hzu : single 0 z * star u = star u := by
    have := congrArg star huz
    rwa [star_mul, hZ0.isSelfAdjoint.star_eq] at this
  /- The projections `Eᵢ = e_{ii} ⊗ z`, summing to `1_n ⊗ z = u u*`. -/
  obtain ⟨E, hE⟩ : ∃ E : Fin n → BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n),
    ∀ i, E i = single i z := ⟨_, fun _ => rfl⟩
  have hEsum : ∑ i, E i = amplify n z := by
    rw [amplify, ← sum_single]
    exact Finset.sum_congr rfl fun i _ => hE i
  have hEZ : ∀ i, E i * amplify n z = E i := fun i => by
    rw [hE i, single_mul_amplify, hz.isIdempotentElem.eq]
  have hEE : ∀ i, E i * E i = E i := fun i => by
    rw [hE i, single_mul_single_same, hz.isIdempotentElem.eq]
  have hEo : ∀ i j, i ≠ j → E i * E j = 0 := fun i j hij => by
    rw [hE i, hE j, single_mul_single_ne hij]
  have hEsa : ∀ i, star (E i) = E i := fun i => by
    rw [hE i, single_star, hz.isSelfAdjoint.star_eq]
  have hEM : ∀ i, E i ∈ matrixAlgebra M n := fun i => by
    rw [hE i]; exact single_mem i hzM
  /- `Yᵢ = u* Eᵢ u` is a projection of `M_n(M)` supported in the `(0, 0)` block. -/
  obtain ⟨Y, hY⟩ : ∃ Y : Fin n → BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n),
    ∀ i, Y i = star u * E i * u := ⟨_, fun _ => rfl⟩
  have hYconj : ∀ i, single 0 z * Y i * single 0 z = Y i := fun i => by
    rw [hY i]
    calc single 0 z * (star u * E i * u) * single 0 z
        = (single 0 z * star u) * E i * (u * single 0 z) := by simp only [mul_assoc]
      _ = star u * E i * u := by rw [hzu, huz]
  have hYM : ∀ i, Y i ∈ matrixAlgebra M n := fun i => by
    rw [hY i]; exact mul_mem (mul_mem (star_mem huM) (hEM i)) huM
  have hYY : ∀ i j, Y i * Y j = star u * (E i * E j) * u := fun i j => by
    rw [hY i, hY j]
    calc star u * E i * u * (star u * E j * u)
        = star u * (E i * (u * star u) * E j) * u := by simp only [mul_assoc]
      _ = star u * (E i * E j) * u := by rw [huu', hEZ i]
  have hYproj : ∀ i, IsStarProjection (Y i) := fun i => by
    refine ⟨?_, ?_⟩
    · show Y i * Y i = Y i
      rw [hYY i i, hEE i, hY i]
    · rw [IsSelfAdjoint, hY i, star_mul, star_mul, star_star, hEsa i, mul_assoc]
  have hYo : ∀ i j, i ≠ j → Y i * Y j = 0 := fun i j hij => by
    rw [hYY i j, hEo i j hij, mul_zero, zero_mul]
  obtain ⟨p, hp⟩ : ∃ p : Fin n → H →L[ℂ] H, ∀ i, p i = entry (Y i) 0 0 := ⟨_, fun _ => rfl⟩
  have hYs : ∀ i, Y i = single 0 (p i) := fun i => by
    rw [hp i]
    exact eq_single_of_conj (hYconj i)
  have hpM : ∀ i, p i ∈ M := fun i => by rw [hp i]; exact entry_mem (hYM i) 0 0
  have hpc : ∀ i, z * p i * z = p i := fun i => by
    rw [hp i]
    exact entry_eq_conj_of_conj (hYconj i)
  have hpz : ∀ i, p i * z = p i := fun i => by
    calc p i * z = z * p i * z * z := by rw [hpc i]
      _ = z * p i * (z * z) := by rw [mul_assoc]
      _ = p i := by rw [hz.isIdempotentElem.eq, hpc i]
  have hpproj : ∀ i, IsStarProjection (p i) := fun i =>
    isStarProjection_of_single (by rw [← hYs i]; exact hYproj i)
  have hpo : ∀ i j, i ≠ j → p i * p j = 0 := fun i j hij => by
    refine single_inj (i := (0 : Fin n)) ?_
    rw [← single_mul_single_same, ← hYs i, ← hYs j, hYo i j hij, single_zero]
  refine ⟨p, hpM, hpproj, hpz, hpo, ?_, fun i => by rw [← hYs i, hY i, hE i]⟩
  /- `∑ᵢ Yᵢ = u* (u u*) u = (u* u)²`, and `u* u` is a projection since `u u*` is one. -/
  have huuP : IsStarProjection (star u * u) := by
    have := isStarProjection_mul_star_of (v := star u)
      (by rw [star_star, huu']; exact isStarProjection_amplify hz)
    rwa [star_star] at this
  calc single 0 (∑ i, p i) = ∑ i, Y i := by
        rw [single_sum]
        exact Finset.sum_congr rfl fun i _ => (hYs i).symm
    _ = star u * (∑ i, E i) * u := by
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => hY i
    _ = star u * (u * star u) * u := by rw [hEsum, huu']
    _ = (star u * u) * (star u * u) := by simp only [mul_assoc]
    _ = star u * u := huuP.isIdempotentElem.eq

/-! ### The projections `p_{i,α}` of Section 5 -/

/-- **The projections `p_{i,α}` of Section 5**, for one index of the net: from a projection
`q ≤ z` of `M` with `z − q ∼ z`, the POVM `(aᵢ)` and isometries `uᵢ` realizing
`1_n ⊗ z ∼ e_{00} ⊗ z`, pairwise orthogonal projections `pᵢ ∈ M` below `z` with
`q ≤ ∑ pᵢ ≤ z` and `q pᵢ q = q aᵢ q`. -/
theorem exists_typeIII_projections (M : VonNeumannAlgebra H) {z : H →L[ℂ] H}
    (hz : IsCentralProj M z) {n : ℕ} [NeZero n]
    {a : Fin n → H →L[ℂ] H} (haM : ∀ i, a i ∈ M) (ha0 : ∀ i, 0 ≤ a i) (haz : ∑ i, a i = z)
    {q : H →L[ℂ] H} (hq : IsStarProjection q) (hqM : q ∈ M) (hqz : q * z = q)
    (hqe : MvNEquiv M (z - q) z)
    {u : Fin n → H →L[ℂ] H} (huM : ∀ i, u i ∈ M) (huu : ∀ i, star (u i) * u i = z)
    (huo : ∀ i j, i ≠ j → star (u i) * u j = 0) (hus : ∑ i, u i * star (u i) = z) :
    ∃ p : Fin n → H →L[ℂ] H, (∀ i, p i ∈ M) ∧ (∀ i, IsStarProjection (p i)) ∧
      (∀ i, p i * z = p i) ∧ (∀ i j, i ≠ j → p i * p j = 0) ∧
      q ≤ ∑ i, p i ∧ ∑ i, p i ≤ z ∧ ∀ i, q * p i * q = q * a i * q := by
  have hzP := hz.isStarProjection
  have hzM := hz.mem
  have hzq : z * q = q := proj_mul_left_of_mul_right hq hzP hqz
  have haz' : ∀ i, a i * z = a i := mul_eq_self_of_sum_eq hzP ha0 haz
  /- The square roots `√aᵢ`, supported in `z`. -/
  obtain ⟨sq, hsq⟩ : ∃ sq : Fin n → H →L[ℂ] H, ∀ i, sq i = CFC.sqrt (a i) := ⟨_, fun _ => rfl⟩
  have hsqM : ∀ i, sq i ∈ M := fun i => by rw [hsq i]; exact sqrt_mem M (haM i) (ha0 i)
  have hsqsa : ∀ i, star (sq i) = sq i := fun i => by
    rw [hsq i]; exact (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (a i))).star_eq
  have hsqsq : ∀ i, sq i * sq i = a i := fun i => by
    rw [hsq i]; exact sqrt_mul_sqrt_self (ha0 i)
  have hsqz : ∀ i, sq i * z = sq i := fun i => by
    rw [hsq i]; exact sqrt_mul_proj_eq_self (ha0 i) (haz' i)
  have hzsq : ∀ i, z * sq i = sq i := fun i => by
    have := congrArg star (hsqz i)
    rwa [star_mul, hsqsa i, hzP.isSelfAdjoint.star_eq] at this
  /- The projections `Z = 1_n ⊗ z`, `Z₀ = e_{00} ⊗ z`, `Q = e_{00} ⊗ q` of `M_n(M)`. -/
  have hZP : IsStarProjection (amplify n z) := isStarProjection_amplify hzP
  have hZM : amplify n z ∈ matrixAlgebra M n := amplify_mem hzM
  have hZ0P : IsStarProjection (single (0 : Fin n) z) := isStarProjection_single 0 hzP
  have hQP : IsStarProjection (single (0 : Fin n) q) := isStarProjection_single 0 hq
  have hQZ0 : single (0 : Fin n) q * single 0 z = single 0 q := by
    rw [single_mul_single_same, hqz]
  have hZ0Q : single (0 : Fin n) z * single 0 q = single 0 q := by
    rw [single_mul_single_same, hzq]
  have hZ0subP : IsStarProjection (single (0 : Fin n) z - single 0 q) :=
    isStarProjection_sub_of_le hZ0P hQP hQZ0 hZ0Q
  have hZ0subQ : (single (0 : Fin n) z - single 0 q) * single 0 q = 0 := by
    rw [sub_mul, hZ0Q, hQP.isIdempotentElem.eq, sub_self]
  /- The column `v = ∑ᵢ e_{i0} ⊗ √aᵢ q`: a partial isometry with `v* v = Q`, `Z v = v`. -/
  obtain ⟨X, hX⟩ : ∃ X : Fin n → H →L[ℂ] H, ∀ i, X i = sq i * q := ⟨_, fun _ => rfl⟩
  have hXM : ∀ i, X i ∈ M := fun i => by rw [hX i]; exact mul_mem (hsqM i) hqM
  have hzX : ∀ i, z * X i = X i := fun i => by rw [hX i, ← mul_assoc, hzsq i]
  obtain ⟨v, hv⟩ : ∃ v : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n), v = col 0 X :=
    ⟨_, rfl⟩
  have hvM : v ∈ matrixAlgebra M n := by rw [hv]; exact col_mem hXM 0
  have hvv : star v * v = single 0 q := by
    rw [hv, star_col_mul_col]
    congr 1
    calc ∑ i, star (X i) * X i = q * (∑ i, sq i * sq i) * q := by
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hX i, star_mul, hsqsa i, hq.isSelfAdjoint.star_eq]
          simp only [mul_assoc]
      _ = q := by
          simp only [hsqsq]
          rw [haz, hqz, hq.isIdempotentElem.eq]
  have hvvP : IsStarProjection (star v * v) := by rw [hvv]; exact hQP
  have hZv : amplify n z * v = v := by
    rw [hv, amplify, blockProj_mul_col]
    congr 1
    funext i
    exact hzX i
  have hvQ : v * single 0 q = v := mul_eq_self_of_star_mul_self_eq hQP hvv
  have hvZ0 : v * single 0 z = v := by
    calc v * single 0 z = v * single 0 q * single 0 z := by rw [hvQ]
      _ = v * (single 0 q * single 0 z) := mul_assoc _ _ _
      _ = v := by rw [hQZ0, hvQ]
  /- The range projection `L = v v*` lies below `Z`. -/
  have hLP : IsStarProjection (v * star v) := isStarProjection_mul_star_of hvvP
  have hLM : v * star v ∈ matrixAlgebra M n := mul_mem hvM (star_mem hvM)
  have hvZ : star v * amplify n z = star v := by
    have := congrArg star hZv
    rwa [star_mul, hZP.isSelfAdjoint.star_eq] at this
  have hLZ : v * star v * amplify n z = v * star v := by rw [mul_assoc, hvZ]
  have hZL : amplify n z * (v * star v) = v * star v := by rw [← mul_assoc, hZv]
  have hLv : v * star v * v = v := by rw [mul_assoc]; exact mul_star_mul_self_eq_self hvvP
  have hvL : star v * (v * star v) = star v := star_mul_self_mul_star hvvP
  /- `Z − L ≤ Z ∼ Z₀ ∼ Z₀ − Q`: `Z − L` is equivalent to a subprojection `R` of `Z₀ − Q`,
  through `w` with `w w* = Z − L`, `w* w = R`. -/
  have hZLP : IsStarProjection (amplify n z - v * star v) :=
    isStarProjection_sub_of_le hZP hLP hLZ hZL
  have hZLM : amplify n z - v * star v ∈ matrixAlgebra M n := sub_mem hZM hLM
  have hZLZ : (amplify n z - v * star v) * amplify n z = amplify n z - v * star v := by
    rw [sub_mul, hZP.isIdempotentElem.eq, hLZ]
  have hequiv : MvNEquiv (matrixAlgebra M n) (amplify n z) (single 0 z - single 0 q) := by
    refine (mvNEquiv_single_amplify_of_isometries huM huu huo hus).symm.trans hZP ?_
    have := (mvNEquiv_single hqe (0 : Fin n)).symm
    rwa [single_sub] at this
  obtain ⟨w', hw'M, hw'1, hw'P, hw'2⟩ :=
    exists_partial_isometry_of_le_of_equiv (matrixAlgebra M n) hZLP hZLM hZLZ hequiv
  obtain ⟨w, hw⟩ : ∃ w : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n), w = star w' := ⟨_, rfl⟩
  have hwM : w ∈ matrixAlgebra M n := by rw [hw]; exact star_mem hw'M
  have hww : w * star w = amplify n z - v * star v := by rw [hw, star_star, hw'1]
  obtain ⟨R, hR⟩ : ∃ R : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n), R = star w * w :=
    ⟨_, rfl⟩
  have hRP : IsStarProjection R := by rw [hR, hw, star_star]; exact hw'P
  have hRsub : R * (single 0 z - single 0 q) = R := by rw [hR, hw, star_star]; exact hw'2
  have hwwP : IsStarProjection (star w * w) := by rw [← hR]; exact hRP
  have hwR : w * R = w := by rw [hR]; exact mul_star_mul_self_eq_self hwwP
  have hZLw : (amplify n z - v * star v) * w = w := by
    have h1 : star w * (w * star w) = star w := star_mul_self_mul_star hwwP
    have := congrArg star h1
    rwa [star_mul, star_star, star_mul, star_star, hww] at this
  /- The partial isometry `u = v + w`: the cross terms vanish, `u u* = Z`, `u* u = Q + R`. -/
  have hwQ : w * single 0 q = 0 := by
    calc w * single 0 q = w * R * (single 0 z - single 0 q) * single 0 q := by
          rw [mul_assoc w R, hRsub, hwR]
      _ = w * R * ((single 0 z - single 0 q) * single 0 q) := by simp only [mul_assoc]
      _ = 0 := by rw [hZ0subQ, mul_zero]
  have hvw : v * star w = 0 := by
    calc v * star w = v * (single 0 q * star w) := by rw [← mul_assoc, hvQ]
      _ = v * star (w * single 0 q) := by rw [star_mul, hQP.isSelfAdjoint.star_eq]
      _ = 0 := by rw [hwQ, clm_star_zero, mul_zero]
  have hwv : w * star v = 0 := by
    have := congrArg star hvw
    rwa [star_mul, star_star, clm_star_zero] at this
  have hLZL : v * star v * (amplify n z - v * star v) = 0 := proj_mul_sub_eq_zero hLP hLZ
  have hvw' : star v * w = 0 := by
    calc star v * w = star v * (v * star v) * ((amplify n z - v * star v) * w) := by
          rw [hvL, hZLw]
      _ = star v * (v * star v * (amplify n z - v * star v)) * w := by simp only [mul_assoc]
      _ = 0 := by rw [hLZL, mul_zero, zero_mul]
  have hwv' : star w * v = 0 := by
    have := congrArg star hvw'
    rwa [star_mul, star_star, clm_star_zero] at this
  have huu' : (v + w) * star (v + w) = amplify n z := by
    rw [clm_star_add, add_mul, mul_add, mul_add, hvw, hwv, hww]
    abel
  have huu : star (v + w) * (v + w) = single 0 q + R := by
    rw [clm_star_add, add_mul, mul_add, mul_add, hvv, hvw', hwv', hR]
    abel
  have hRZ0 : R * single 0 z = R := by
    calc R * single 0 z = R * (single 0 z - single 0 q) * single 0 z := by rw [hRsub]
      _ = R * ((single 0 z - single 0 q) * single 0 z) := mul_assoc _ _ _
      _ = R := by rw [sub_mul, hZ0P.isIdempotentElem.eq, hQZ0, hRsub]
  have hwZ0 : w * single 0 z = w := by
    calc w * single 0 z = w * (R * single 0 z) := by rw [← mul_assoc, hwR]
      _ = w := by rw [hRZ0, hwR]
  have hVZ0 : (v + w) * single 0 z = v + w := by rw [add_mul, hvZ0, hwZ0]
  have hVM : v + w ∈ matrixAlgebra M n := add_mem hvM hwM
  /- The projections `pᵢ = (u* (e_{ii} ⊗ z) u)₀₀`. -/
  obtain ⟨p, hpM, hpP, hpz, hpo, hpsum, hpY⟩ :=
    exists_orth_projections_of_partial_isometry M hzP hzM hVM huu' hVZ0
  refine ⟨p, hpM, hpP, hpz, hpo, ?_, ?_, ?_⟩
  · -- `q ≤ ∑ pᵢ`, from `Q ≤ Q + R`
    have h : single (0 : Fin n) q ≤ single 0 (∑ i, p i) := by
      rw [hpsum, huu]
      exact le_add_of_nonneg_right hRP.nonneg
    have := entry_diag_le h 0
    rwa [entry_single_same, entry_single_same] at this
  · -- `∑ pᵢ ≤ z`, from `Q + R ≤ Z₀` (`Z₀ − Q − R` is a projection)
    have hsubR : (single 0 z - single 0 q) * R = R :=
      proj_mul_left_of_mul_right hRP hZ0subP hRsub
    have hP' : IsStarProjection (single (0 : Fin n) z - single 0 q - R) :=
      isStarProjection_sub_of_le hZ0subP hRP hRsub hsubR
    have h : single 0 (∑ i, p i) ≤ single (0 : Fin n) z := by
      rw [hpsum, huu, ← sub_nonneg]
      have : single (0 : Fin n) z - (single 0 q + R) = single 0 z - single 0 q - R := by abel
      rw [this]
      exact hP'.nonneg
    have := entry_diag_le h 0
    rwa [entry_single_same, entry_single_same] at this
  · -- `q pᵢ q = q aᵢ q`: `Q (u* Eᵢ u) Q = v* (v u*) Eᵢ (u v*) v = v* Eᵢ v`
    intro i
    have hvu : v * star (v + w) = v * star v := by rw [clm_star_add, mul_add, hvw, add_zero]
    have huv : (v + w) * star v = v * star v := by rw [add_mul, hwv, add_zero]
    refine single_inj (i := (0 : Fin n)) ?_
    calc single 0 (q * p i * q) = single 0 q * single 0 (p i) * single 0 q := by
          rw [single_mul_single_same, single_mul_single_same]
      _ = (star v * v) * (star (v + w) * single i z * (v + w)) * (star v * v) := by
          rw [hpY i, hvv]
      _ = star v * (v * star (v + w)) * single i z * ((v + w) * star v) * v := by
          simp only [mul_assoc]
      _ = star v * (v * star v) * single i z * (v * star v) * v := by rw [hvu, huv]
      _ = star v * single i z * v := by
          rw [hvL]
          calc star v * single i z * (v * star v) * v
              = star v * single i z * (v * star v * v) := by simp only [mul_assoc]
            _ = star v * single i z * v := by rw [hLv]
      _ = single 0 (star (X i) * z * X i) := by rw [hv, star_col_mul_single_mul_col]
      _ = single 0 (q * a i * q) := by
          congr 1
          rw [hX i, star_mul, hsqsa i, hq.isSelfAdjoint.star_eq]
          calc q * sq i * z * (sq i * q) = q * (sq i * z) * (sq i * q) := by
                rw [mul_assoc q (sq i) z]
            _ = q * (sq i * sq i) * q := by rw [hsqz i]; simp only [mul_assoc]
            _ = q * a i * q := by rw [hsqsq i]

/-! ### The estimate for one index of the net -/

/-- `|(z − q) p q|² = q p q − (q p q)²` for projections `p`, `q`, `z − q` with `p z = p`. -/
theorem star_mul_self_sub_mul_mul {p q z : H →L[ℂ] H} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hr : IsStarProjection (z - q)) (hpz : p * z = p) :
    star ((z - q) * p * q) * ((z - q) * p * q) = q * p * q - q * p * q * (q * p * q) := by
  have h1 : star ((z - q) * p * q) = q * p * (z - q) := by
    rw [star_mul, star_mul, hq.isSelfAdjoint.star_eq, hp.isSelfAdjoint.star_eq,
      hr.isSelfAdjoint.star_eq, mul_assoc]
  have e1 : q * p * (p * q) = q * p * q := by
    rw [← mul_assoc, mul_assoc q p p, hp.isIdempotentElem.eq]
  have e2 : q * p * q * (q * p * q) = q * p * q * (p * q) := by
    calc q * p * q * (q * p * q) = q * p * (q * q) * (p * q) := by simp only [mul_assoc]
      _ = q * p * q * (p * q) := by rw [hq.isIdempotentElem.eq]
  rw [h1]
  calc q * p * (z - q) * ((z - q) * p * q)
      = q * p * ((z - q) * (z - q)) * (p * q) := by simp only [mul_assoc]
    _ = q * p * (z - q) * (p * q) := by rw [hr.isIdempotentElem.eq]
    _ = q * p * z * (p * q) - q * p * q * (p * q) := by rw [mul_sub, sub_mul]
    _ = q * p * q - q * p * q * (q * p * q) := by rw [mul_assoc q p z, hpz, e1, ← e2]

/-- **The estimate of Section 5 for one index of the net.** With `pᵢ` the projections of
`exists_typeIII_projections`, `P = ∑ pᵢ` and `p'ᵢ = pᵢ + δᵢ₀ (z − P)` (a PVM of `z M z`),
`‖a − p'‖² ≤ (1 + η)((1 + η⁻¹)(2 B + 2 G) + (1 + η) C) + (1 + η⁻¹) G`, where
`B = ‖(aᵢ − q aᵢ q)ᵢ‖²`, `G = φ(z − q)` and `C = φ(∑ᵢ (q aᵢ q − (q aᵢ q)²))`: the decomposition
`aᵢ − pᵢ = (aᵢ − q aᵢ q) − pᵢ (z − q) − (z − q) pᵢ q` and the weighted triangle inequality. -/
theorem exists_pvm_estimate_of_projections (M : VonNeumannAlgebra H) {z : H →L[ℂ] H}
    (hz : IsCentralProj M z) {n : ℕ} [NeZero n] {φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ}
    (hφ : ∀ x ∈ M, 0 ≤ φ (star x * x))
    {a : Fin n → H →L[ℂ] H} (haM : ∀ i, a i ∈ M)
    {q : H →L[ℂ] H} (hq : IsStarProjection q) (hqM : q ∈ M) (hqz : q * z = q)
    {p : Fin n → H →L[ℂ] H} (hpM : ∀ i, p i ∈ M) (hpP : ∀ i, IsStarProjection (p i))
    (hpz : ∀ i, p i * z = p i) (hpo : ∀ i j, i ≠ j → p i * p j = 0)
    (hqp : q ≤ ∑ i, p i) (hpz' : ∑ i, p i ≤ z) (hqpq : ∀ i, q * p i * q = q * a i * q)
    {η : ℝ} (hη : 0 < η) :
    ∃ p' : Fin n → H →L[ℂ] H, (∀ i, p' i ∈ M) ∧ (∀ i, IsStarProjection (p' i)) ∧
      (∀ i, p' i * z = p' i) ∧ ∑ i, p' i = z ∧
      (φ (∑ i, star (a i - p' i) * (a i - p' i))).re ≤
        (1 + η) * ((1 + η⁻¹) *
            (2 * (φ (∑ i, star (a i - q * a i * q) * (a i - q * a i * q))).re
              + 2 * (φ (z - q)).re)
          + (1 + η) * (φ (∑ i, (q * a i * q - q * a i * q * (q * a i * q)))).re)
          + (1 + η⁻¹) * (φ (z - q)).re := by
  classical
  have hzP := hz.isStarProjection
  have hzM := hz.mem
  have hzq : z * q = q := proj_mul_left_of_mul_right hq hzP hqz
  have hzp : ∀ i, z * p i = p i := fun i => proj_mul_left_of_mul_right (hpP i) hzP (hpz i)
  have hrP : IsStarProjection (z - q) := isStarProjection_sub_of_le hzP hq hqz hzq
  have hrsa := hrP.isSelfAdjoint.star_eq
  have hrM : z - q ∈ M := sub_mem hzM hqM
  /- The sum `P = ∑ pᵢ` is a projection of `M` below `z`, and `z − P` is a projection
  orthogonal to every `pᵢ`. -/
  obtain ⟨P, hP⟩ : ∃ P : H →L[ℂ] H, P = ∑ i, p i := ⟨_, rfl⟩
  rw [← hP] at hqp hpz'
  have hPM : P ∈ M := by rw [hP]; exact sum_mem fun i _ => hpM i
  have hpP' : ∀ i, p i * P = p i := fun i => by
    rw [hP, Finset.mul_sum, Finset.sum_eq_single i]
    · exact (hpP i).isIdempotentElem.eq
    · intro j _ hj
      exact hpo i j (Ne.symm hj)
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hPsa : star P = P := by
    rw [hP, star_sum]
    exact Finset.sum_congr rfl fun i _ => (hpP i).isSelfAdjoint.star_eq
  have hPP : IsStarProjection P := by
    refine ⟨?_, hPsa⟩
    show P * P = P
    calc P * P = (∑ i, p i) * P := by rw [← hP]
      _ = ∑ i, p i * P := Finset.sum_mul _ _ _
      _ = ∑ i, p i := Finset.sum_congr rfl fun i _ => hpP' i
      _ = P := hP.symm
  have hPz : P * z = P := by
    rw [hP, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => hpz i
  have hzP' : z * P = P := proj_mul_left_of_mul_right hPP hzP hPz
  have hsP : IsStarProjection (z - P) := isStarProjection_sub_of_le hzP hPP hPz hzP'
  have hsM : z - P ∈ M := sub_mem hzM hPM
  have hpsub : ∀ i, p i * (z - P) = 0 := fun i => by rw [mul_sub, hpz i, hpP' i, sub_self]
  have hsubp : ∀ i, (z - P) * p i = 0 := fun i => by
    have := congrArg star (hpsub i)
    rwa [star_mul, hsP.isSelfAdjoint.star_eq, (hpP i).isSelfAdjoint.star_eq, star_zero] at this
  /- The completed PVM `p'ᵢ = pᵢ + eᵢ`, `eᵢ = δᵢ₀ (z − P)`. -/
  obtain ⟨e, he⟩ : ∃ e : Fin n → H →L[ℂ] H, ∀ i, e i = if i = 0 then z - P else 0 :=
    ⟨_, fun _ => rfl⟩
  have heM : ∀ i, e i ∈ M := fun i => by
    rw [he i]
    split_ifs
    exacts [hsM, zero_mem M]
  refine ⟨fun i => p i + e i, fun i => add_mem (hpM i) (heM i), ?_, ?_, ?_, ?_⟩
  · intro i
    dsimp only
    by_cases hi : i = 0
    · rw [he i, if_pos hi]
      refine ⟨?_, ?_⟩
      · show (p i + (z - P)) * (p i + (z - P)) = p i + (z - P)
        rw [add_mul, mul_add, mul_add, (hpP i).isIdempotentElem.eq, hpsub i, hsubp i,
          hsP.isIdempotentElem.eq]
        abel
      · rw [IsSelfAdjoint, star_add, (hpP i).isSelfAdjoint.star_eq, hsP.isSelfAdjoint.star_eq]
    · rw [he i, if_neg hi, add_zero]
      exact hpP i
  · intro i
    dsimp only
    rw [add_mul, hpz i, he i]
    congr 1
    split_ifs
    · rw [sub_mul, hzP.isIdempotentElem.eq, hPz]
    · exact zero_mul _
  · rw [Finset.sum_add_distrib, ← hP]
    simp only [he]
    rw [Finset.sum_ite_eq' Finset.univ (0 : Fin n)]
    simp
  · /- The estimate. Membership of the three pieces `bᵢ = aᵢ − q aᵢ q`, `dᵢ = pᵢ (z − q)`,
    `cᵢ = (z − q) pᵢ q`. -/
    have hbM : ∀ i, a i - q * a i * q ∈ M := fun i =>
      sub_mem (haM i) (mul_mem (mul_mem hqM (haM i)) hqM)
    have hdM : ∀ i, p i * (z - q) ∈ M := fun i => mul_mem (hpM i) hrM
    have hcM : ∀ i, (z - q) * p i * q ∈ M := fun i => mul_mem (mul_mem hrM (hpM i)) hqM
    have hapM : ∀ i, a i - p i ∈ M := fun i => sub_mem (haM i) (hpM i)
    -- the decompositions
    have hdec1 : ∀ i, a i - (p i + e i) = (a i - p i) + -(e i) := fun i => by abel
    have hdec2 : ∀ i, a i - p i
        = ((a i - q * a i * q) + -(p i * (z - q))) + -((z - q) * p i * q) := fun i => by
      have h1 : p i * (z - q) = p i - p i * q := by rw [mul_sub, hpz i]
      have h2 : (z - q) * p i * q = p i * q - q * a i * q := by
        rw [sub_mul, sub_mul, hzp i, hqpq i]
      rw [h1, h2]
      abel
    -- the weighted triangle inequality, three times
    have hneg : ∀ x : H →L[ℂ] H, star (-x) * (-x) = star x * x := fun x => by
      rw [star_neg, neg_mul_neg]
    have hT1 := sum_re_map_star_add_mul_add_le hφ hapM (fun i => neg_mem (heM i)) hη
    have hT2 := sum_re_map_star_add_mul_add_le hφ
      (fun i => add_mem (hbM i) (neg_mem (hdM i))) (fun i => neg_mem (hcM i)) (inv_pos.mpr hη)
    have hT3 := sum_re_map_star_add_mul_add_le hφ hbM (fun i => neg_mem (hdM i)) one_pos
    simp only [hneg] at hT1 hT2 hT3
    rw [inv_inv] at hT2
    rw [inv_one] at hT3
    have hN1 : (φ (∑ i, star (a i - p i) * (a i - p i))).re
        = (φ (∑ i, star ((a i - q * a i * q) + -(p i * (z - q)) + -((z - q) * p i * q)) *
            ((a i - q * a i * q) + -(p i * (z - q)) + -((z - q) * p i * q)))).re := by
      simp only [hdec2]
    -- the values of the three norms
    have hD : (φ (∑ i, star (p i * (z - q)) * (p i * (z - q)))).re ≤ (φ (z - q)).re := by
      have h1 : ∑ i, star (p i * (z - q)) * (p i * (z - q)) = (z - q) * P * (z - q) := by
        rw [hP, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [star_mul, hrsa, (hpP i).isSelfAdjoint.star_eq]
        calc (z - q) * p i * (p i * (z - q)) = (z - q) * (p i * p i) * (z - q) := by
              simp only [mul_assoc]
          _ = (z - q) * p i * (z - q) := by rw [(hpP i).isIdempotentElem.eq]
      have h2 : (z - q) * P * (z - q) ≤ z - q := by
        have := conj_le_conj hpz' (z - q)
        rw [hrsa] at this
        have h3 : (z - q) * z * (z - q) = z - q := by
          rw [sub_mul, hzP.isIdempotentElem.eq, hqz, hrP.isIdempotentElem.eq]
        rwa [h3] at this
      rw [h1]
      exact re_map_le_of_mem hφ (mul_mem (mul_mem hrM hPM) hrM) hrM h2
    have hC : (φ (∑ i, star ((z - q) * p i * q) * ((z - q) * p i * q))).re
        = (φ (∑ i, (q * a i * q - q * a i * q * (q * a i * q)))).re := by
      congr 2
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [star_mul_self_sub_mul_mul (hpP i) hq hrP (hpz i), hqpq i]
    have hR : (φ (∑ i, star (e i) * e i)).re ≤ (φ (z - q)).re := by
      have h1 : ∑ i, star (e i) * e i = z - P := by
        have : ∀ i, star (e i) * e i = if i = 0 then z - P else 0 := fun i => by
          rw [he i]
          split_ifs
          · rw [hsP.isSelfAdjoint.star_eq, hsP.isIdempotentElem.eq]
          · rw [star_zero, mul_zero]
        simp only [this]
        rw [Finset.sum_ite_eq' Finset.univ (0 : Fin n)]
        simp
      rw [h1]
      exact re_map_le_of_mem hφ hsM hrM (sub_le_sub_left hqp z)
    have h1η : 0 ≤ 1 + η := by positivity
    have h1η' : 0 ≤ 1 + η⁻¹ := by positivity
    -- assembly
    simp only [hdec1]
    rw [hC] at hT2
    have hN2 : (φ (∑ i, star (a i - q * a i * q + -(p i * (z - q))) *
        (a i - q * a i * q + -(p i * (z - q))))).re ≤
        2 * (φ (∑ i, star (a i - q * a i * q) * (a i - q * a i * q))).re + 2 * (φ (z - q)).re := by
      linarith
    have hN1' := mul_le_mul_of_nonneg_left hN2 h1η'
    have hM1 : (1 + η) * (φ (∑ i, star (a i - p i) * (a i - p i))).re
        ≤ (1 + η) * ((1 + η⁻¹) *
            (2 * (φ (∑ i, star (a i - q * a i * q) * (a i - q * a i * q))).re
              + 2 * (φ (z - q)).re)
          + (1 + η) * (φ (∑ i, (q * a i * q - q * a i * q * (q * a i * q)))).re) := by
      refine mul_le_mul_of_nonneg_left ?_ h1η
      rw [hN1]
      linarith
    have hM2 := mul_le_mul_of_nonneg_left hR h1η'
    linarith

/-! ### The theorem -/

/-- **Theorem 1.2 at a type III central projection** (paper, Section 5), for the functionals
normal on `M`, output set `Fin n`. `hH4` is the halving property of interface field H4 at `z`. -/
theorem orthAtN_of_typeIII_fin (M : VonNeumannAlgebra H) {z : H →L[ℂ] H} (hz : IsCentralProj M z)
    (hH4 : ∀ q, IsStarProjection q → q ∈ M → q * z = q → q ≠ 0 →
      ∃ e, IsStarProjection e ∧ e ∈ M ∧ e * q = e ∧ MvNEquiv M e (q - e) ∧ MvNEquiv M e q)
    (n : ℕ) : OrthAtN M z (Fin n) := by
  classical
  intro φ hφn hφ hφz a haM ha0 haz ε hε
  have hzP := hz.isStarProjection
  have hzM := hz.mem
  -- the degenerate cases: `z ≠ 0` and `n ≠ 0`
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [map_zero] at hφz
    exact zero_ne_one hφz
  have hn : n ≠ 0 := by
    rintro rfl
    rw [Fintype.sum_empty] at haz
    exact hz0 haz.symm
  have : NeZero n := ⟨hn⟩
  -- the POVM
  have haz' : ∀ i, a i * z = a i := mul_eq_self_of_sum_eq hzP ha0 haz
  have hza : ∀ i, z * a i = a i := fun i => by rw [(hz.commute _ (haM i)).eq, haz' i]
  have hasa : ∀ i, star (a i) = a i := fun i => (IsSelfAdjoint.of_nonneg (ha0 i)).star_eq
  -- the numbers: `L = φ(∑ (aᵢ − aᵢ²)) = 1 − φ(∑ aᵢ²) < ε`
  have hQM : (∑ i, a i * a i) ∈ M := sum_mem fun i _ => mul_mem (haM i) (haM i)
  have hQle : ∑ i, a i * a i ≤ z := by
    rw [← haz]
    exact Finset.sum_le_sum fun i _ =>
      sq_le_self_of_le_one (ha0 i) (le_trans (le_of_sum_eq ha0 haz i) hzP.le_one)
  have hS1 : (φ (∑ i, a i * a i)).re ≤ 1 := by
    have := re_map_le_of_mem hφ hQM hzM hQle
    rwa [hφz, Complex.one_re] at this
  have hε0 : 0 < ε := by linarith
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = (φ (∑ i, (a i - a i * a i))).re := ⟨_, rfl⟩
  have hL : L = 1 - (φ (∑ i, a i * a i)).re := by
    rw [hLdef, Finset.sum_sub_distrib, haz, map_sub, Complex.sub_re, hφz, Complex.one_re]
  have hL0 : 0 ≤ L := by rw [hL]; linarith
  have hLε : L < ε := by rw [hL]; linarith
  -- the slack `η`: `(1 + η)² L < ε`
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = (ε - L) / (3 * ε) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hηdef]; exact div_pos (by linarith) (by linarith)
  have hη1 : η ≤ 1 := by
    rw [hηdef, div_le_one (by linarith)]
    linarith
  have hkey : (1 + η) * (1 + η) * L < ε := by
    have h1 : (1 + η) * (1 + η) * L ≤ (1 + 3 * η) * L := by
      have : 0 ≤ η * (1 - η) * L := mul_nonneg (mul_nonneg hη0.le (by linarith)) hL0
      nlinarith
    have h2 : (1 + 3 * η) * L < ε := by
      have h3 : (1 + 3 * η) * L = (2 * ε - L) * L / ε := by
        rw [hηdef]
        field_simp
        ring
      rw [h3, div_lt_iff₀ hε0]
      nlinarith [sq_pos_of_pos (sub_pos.mpr hLε)]
    linarith
  -- the net of Lemma 5.1 and the isometries of the halving
  obtain ⟨κ, _, _, _, q, hq, hlim⟩ := exists_typeIII_net M hz hz0 hH4
  obtain ⟨u, huM, huu, huo, hus⟩ :=
    exists_isometries_of_halving M hz hz0 hH4 n (Nat.pos_of_ne_zero hn)
  have hqP : ∀ α, IsStarProjection (q α) := fun α => (hq α).1
  have hqM : ∀ α, q α ∈ M := fun α => (hq α).2.1
  have hqz : ∀ α, q α * z = q α := fun α => (hq α).2.2.1
  -- the projections `p_{i,α}` and the completed PVMs `p'_{i,α}` with their estimates
  choose p hpM hpP hpz hpo hqp hpz' hqpq using fun α =>
    exists_typeIII_projections M hz haM ha0 haz (hqP α) (hqM α) (hqz α) (hq α).2.2.2 huM huu
      huo hus
  choose p' hp'M hp'P hp'z hp'sum hp'est using fun α =>
    exists_pvm_estimate_of_projections M hz hφ haM (hqP α) (hqM α) (hqz α) (hpM α) (hpP α)
      (hpz α) (hpo α) (hqp α) (hpz' α) (hqpq α) hη0
  -- Lemma 4.1 along the net: the three quantities of the estimate converge
  have hb : ∀ i, TendstoStrongBdd atTop (fun α => q α * a i * q α) (a i) := fun i => by
    have := (hlim.mul_right (a i)).mul hlim
    rwa [hza i, haz' i] at this
  have hbM : ∀ α i, q α * a i * q α ∈ M := fun α i => mul_mem (mul_mem (hqM α) (haM i)) (hqM α)
  have hB : Tendsto (fun α => (φ (∑ i, star (a i - q α * a i * q α) *
      (a i - q α * a i * q α))).re) atTop (𝓝 0) := by
    have hsa : ∀ α i, star (a i - q α * a i * q α) = a i - q α * a i * q α := fun α i => by
      rw [star_sub, star_mul, star_mul, hasa i, (hqP α).isSelfAdjoint.star_eq, mul_assoc]
    have h1 : ∀ i, TendstoStrongBdd atTop (fun α => a i - q α * a i * q α) 0 := fun i => by
      have := (TendstoStrongBdd.const (l := atTop) (a i)).sub (hb i)
      rwa [sub_self] at this
    have h2 : ∀ i, TendstoStrongBdd atTop
        (fun α => star (a i - q α * a i * q α) * (a i - q α * a i * q α)) 0 := fun i => by
      have := (h1 i).mul (h1 i)
      simp only [hsa, mul_zero] at this ⊢
      exact this
    have h3 := TendstoStrongBdd.finset_sum Finset.univ fun i _ => h2 i
    rw [Finset.sum_const_zero] at h3
    have := hφn.tendsto_re (fun α => sum_mem fun i _ =>
      mul_mem (star_mem (sub_mem (haM i) (hbM α i))) (sub_mem (haM i) (hbM α i))) (zero_mem M) h3
    rwa [map_zero, Complex.zero_re] at this
  have hG : Tendsto (fun α => (φ (z - q α)).re) atTop (𝓝 0) := by
    have h1 : TendstoStrongBdd atTop (fun α => z - q α) 0 := by
      have := (TendstoStrongBdd.const (l := atTop) z).sub hlim
      rwa [sub_self] at this
    have := hφn.tendsto_re (fun α => sub_mem hzM (hqM α)) (zero_mem M) h1
    rwa [map_zero, Complex.zero_re] at this
  have hC : Tendsto (fun α => (φ (∑ i, (q α * a i * q α -
      q α * a i * q α * (q α * a i * q α)))).re) atTop (𝓝 L) := by
    rw [hLdef]
    refine hφn.tendsto_re (fun α => sum_mem fun i _ => sub_mem (hbM α i)
      (mul_mem (hbM α i) (hbM α i))) (sum_mem fun i _ => sub_mem (haM i) (mul_mem (haM i) (haM i)))
      ?_
    exact TendstoStrongBdd.finset_sum Finset.univ fun i _ => (hb i).sub ((hb i).mul (hb i))
  -- the bound tends to `(1 + η)² L < ε`, so it is `< ε` for some `α`
  have hF : Tendsto (fun α => (1 + η) * ((1 + η⁻¹) *
      (2 * (φ (∑ i, star (a i - q α * a i * q α) * (a i - q α * a i * q α))).re
        + 2 * (φ (z - q α)).re)
      + (1 + η) * (φ (∑ i, (q α * a i * q α - q α * a i * q α * (q α * a i * q α)))).re)
      + (1 + η⁻¹) * (φ (z - q α)).re) atTop
      (𝓝 ((1 + η) * ((1 + η⁻¹) * (2 * 0 + 2 * 0) + (1 + η) * L) + (1 + η⁻¹) * 0)) :=
    (((((hB.const_mul 2).add (hG.const_mul 2)).const_mul (1 + η⁻¹)).add
      (hC.const_mul (1 + η))).const_mul (1 + η)).add (hG.const_mul (1 + η⁻¹))
  have hlt : (1 + η) * ((1 + η⁻¹) * (2 * 0 + 2 * 0) + (1 + η) * L) + (1 + η⁻¹) * 0 < ε := by
    have : (1 + η) * ((1 + η⁻¹) * (2 * 0 + 2 * 0) + (1 + η) * L) + (1 + η⁻¹) * 0
        = (1 + η) * (1 + η) * L := by ring
    rw [this]
    exact hkey
  obtain ⟨α, hα⟩ := (hF.eventually (gt_mem_nhds hlt)).exists
  refine ⟨p' α, hp'M α, hp'P α, hp'z α, hp'sum α, ?_⟩
  calc (φ (∑ i, star (a i - p' α i) * (a i - p' α i))).re
      ≤ _ := hp'est α
    _ < ε := hα
    _ ≤ 9 * ε := by linarith

/-! ### Transport along a bijection of the output set -/

/-- Transport of `OrthAtP` along a bijection of the output set. -/
theorem orthAtP_of_equiv (M : VonNeumannAlgebra H) (z : H →L[ℂ] H) {ι ι' : Type*} [Fintype ι]
    [Fintype ι'] (e : ι ≃ ι') (P : ((H →L[ℂ] H) →ₗ[ℂ] ℂ) → Prop) (h : OrthAtP M z ι' P) :
    OrthAtP M z ι P := by
  intro φ hP hφ hφz a haM ha0 haz ε hε
  have haz' : ∑ j, a (e.symm j) = z := by
    rw [← haz]
    exact Fintype.sum_equiv e.symm _ _ fun j => rfl
  have hε' : 1 - ε < (φ (∑ j, a (e.symm j) * a (e.symm j))).re := by
    have : ∑ j, a (e.symm j) * a (e.symm j) = ∑ i, a i * a i :=
      Fintype.sum_equiv e.symm _ _ fun j => rfl
    rwa [this]
  obtain ⟨p, hpM, hpP, hpz, hps, hpb⟩ :=
    h φ hP hφ hφz (fun j => a (e.symm j)) (fun j => haM _) (fun j => ha0 _) haz' ε hε'
  refine ⟨fun i => p (e i), fun i => hpM _, fun i => hpP _, fun i => hpz _, ?_, ?_⟩
  · rw [← hps]
    exact Fintype.sum_equiv e _ _ fun i => rfl
  · have : ∑ i, star (a i - p (e i)) * (a i - p (e i))
        = ∑ j, star (a (e.symm j) - p j) * (a (e.symm j) - p j) :=
      Fintype.sum_equiv e _ _ fun i => by rw [Equiv.symm_apply_apply]
    rw [this]
    exact hpb

/-- Theorem 1.2 at a type III central projection, any finite output set. -/
theorem orthAtN_of_typeIII (M : VonNeumannAlgebra H) {z : H →L[ℂ] H} (hz : IsCentralProj M z)
    (hH4 : ∀ q, IsStarProjection q → q ∈ M → q * z = q → q ≠ 0 →
      ∃ e, IsStarProjection e ∧ e ∈ M ∧ e * q = e ∧ MvNEquiv M e (q - e) ∧ MvNEquiv M e q)
    (ι : Type*) [Fintype ι] : OrthAtN M z ι :=
  orthAtP_of_equiv M z (Fintype.equivFin ι) (IsNormalOn M) (orthAtN_of_typeIII_fin M hz hH4 _)

end Orthogonalization.MvN
