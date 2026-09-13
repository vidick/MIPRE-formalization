/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/FinDim/Selection.lean
-/
/-
# Step F1 in finite dimension: choosing the commuting projections (Lemma 3.1)

Lemma 3.1 of M. de la Salle, *Orthogonalization of Positive Operator Valued
Measures* (arXiv:2103.14126v2), for `M = B(H)` with `H` finite-dimensional:
given a POVM `(a i)` and a linear functional `φ` on `B(H)`, there are projections
`q i` commuting with `a i`, with `∑ tr(q i) = dim H`, and with
`φ(∑ q i a i) ≥ φ(∑ a i a i)` (real parts).

The paper proves this by Krein–Milman on the convex set of commuting
`[0,1]`-valued families with the right trace, and shows that the extreme points
are made of projections. In finite dimension the same conclusion has a purely
combinatorial proof, used here: diagonalize each `a i` in an orthonormal
eigenbasis `(b^i_k)` with eigenvalues `λ^i_k ∈ [0,1]`, so that
`φ(∑ a i a i) = ∑_{i,k} λ^i_k · c_{i,k}` with `c_{i,k} := λ^i_k φ(P^i_k)` and
`P^i_k` the rank-one eigenprojections. The weights `λ^i_k` lie in `[0,1]` and sum
to `∑ tr(a i) = tr 1 = dim H`, so the weighted sum is dominated by the sum of
the `dim H` largest values `c_{i,k}` (`exists_finset_sum_ge`: the vertices of the
hypersimplex are the `0/1` vectors). Taking `q i := ∑ P^i_k` over the selected
pairs `(i, k)` gives projections diagonal in the eigenbasis of `a i` (hence
commuting with it) with total trace `dim H` and the required inequality.

Everything here is proof-side; no statement of the paper is encoded in this file.
-/
import Mathlib
import MIPRE.Background.Orthonormalization.Orthogonalization.FinDim.JointDiag

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace Orthogonalization.FinDim

open scoped BigOperators ComplexOrder InnerProductSpace
open Module

/-! ### The combinatorial selection lemma -/

section Selection

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **Top-`n` selection.** For every `n ≤ card α` there is a set of `n` indices on
which `c` dominates its values on the complement. -/
theorem exists_dominating_finset (c : α → ℝ) :
    ∀ n : ℕ, n ≤ Fintype.card α →
      ∃ S : Finset α, S.card = n ∧ ∀ x ∈ S, ∀ y ∉ S, c y ≤ c x := by
  intro n
  induction n with
  | zero => exact fun _ => ⟨∅, rfl, fun x hx => absurd hx (Finset.notMem_empty x)⟩
  | succ n ih =>
    intro hn
    obtain ⟨S, hcard, hdom⟩ := ih (Nat.le_of_succ_le hn)
    have hne : Sᶜ.Nonempty := by
      rw [← Finset.card_pos, Finset.card_compl, hcard]
      omega
    obtain ⟨y₀, hy₀, hmax⟩ := Finset.exists_max_image Sᶜ c hne
    refine ⟨insert y₀ S, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp hy₀), hcard]
    · intro x hx y hy
      have hyS : y ∉ S := fun h => hy (Finset.mem_insert_of_mem h)
      rcases Finset.mem_insert.mp hx with rfl | hxS
      · exact hmax y (Finset.mem_compl.mpr hyS)
      · exact hdom x hxS y hyS

/-- A weighted sum with weights in `[0,1]` summing to `card S` is dominated by the
plain sum over a set `S` on which `c` dominates its values off `S`. -/
theorem sum_le_sum_dominating (c w : α → ℝ) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    (S : Finset α) (hdom : ∀ x ∈ S, ∀ y ∉ S, c y ≤ c x) (hsum : ∑ x, w x = S.card) :
    ∑ x, w x * c x ≤ ∑ x ∈ S, c x := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.card_empty, Nat.cast_zero] at hsum
    have hw : ∀ x, w x = 0 := fun x =>
      (Finset.sum_eq_zero_iff_of_nonneg fun x _ => hw0 x).mp hsum x (Finset.mem_univ x)
    simp [hw]
  · obtain ⟨x₀, hx₀, hmin⟩ := Finset.exists_min_image S c hne
    set t := c x₀ with ht
    have h1 : ∑ x ∈ S, (1 - w x) * t ≤ ∑ x ∈ S, (1 - w x) * c x :=
      Finset.sum_le_sum fun x hx =>
        mul_le_mul_of_nonneg_left (hmin x hx) (by linarith [hw1 x])
    have h2 : ∑ x ∈ Sᶜ, w x * c x ≤ ∑ x ∈ Sᶜ, w x * t :=
      Finset.sum_le_sum fun y hy =>
        mul_le_mul_of_nonneg_left (hdom x₀ hx₀ y (Finset.mem_compl.mp hy)) (hw0 y)
    have hsplit : ∑ x ∈ S, w x + ∑ x ∈ Sᶜ, w x = ∑ x, w x := Finset.sum_add_sum_compl S w
    have h3 : ∑ x ∈ S, (1 - w x) * t - ∑ x ∈ Sᶜ, w x * t = 0 := by
      have e1 : ∑ x ∈ S, (1 - w x) * t = ((S.card : ℝ) - ∑ x ∈ S, w x) * t := by
        rw [← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
      have e2 : ∑ x ∈ Sᶜ, w x * t = (∑ x ∈ Sᶜ, w x) * t := by rw [Finset.sum_mul]
      rw [e1, e2]
      have : (S.card : ℝ) - ∑ x ∈ S, w x - ∑ x ∈ Sᶜ, w x = 0 := by linarith
      linear_combination t * this
    have hfin : ∑ x, w x * c x = ∑ x ∈ S, w x * c x + ∑ x ∈ Sᶜ, w x * c x :=
      (Finset.sum_add_sum_compl S _).symm
    have e3 : ∑ x ∈ S, c x - ∑ x ∈ S, w x * c x = ∑ x ∈ S, (1 - w x) * c x := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    linarith

/-- **The vertices of the hypersimplex.** If `w : α → [0,1]` sums to a natural
number `n`, the weighted sum `∑ w x * c x` is dominated by the sum of `c` over some
set of exactly `n` indices. -/
theorem exists_finset_sum_ge (c w : α → ℝ) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    (n : ℕ) (hsum : ∑ x, w x = n) :
    ∃ S : Finset α, S.card = n ∧ ∑ x, w x * c x ≤ ∑ x ∈ S, c x := by
  have hn : n ≤ Fintype.card α := by
    have h : ∑ x, w x ≤ ∑ _x : α, (1 : ℝ) := Finset.sum_le_sum fun x _ => hw1 x
    rw [hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
    exact_mod_cast h
  obtain ⟨S, hS, hdom⟩ := exists_dominating_finset c n hn
  exact ⟨S, hS, sum_le_sum_dominating c w hw0 hw1 S hdom (by rw [hsum, hS])⟩

end Selection

/-! ### Sums of rank-one spectral projections -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

namespace JointEigenbasis

variable {x a : H →L[ℂ] H} (J : JointEigenbasis x a)

include J

set_option linter.unusedSectionVars false

/-- `x P k = λ_k P k`. -/
theorem mul_P (k : Fin (finrank ℂ H)) : x * J.P k = (J.lam k : ℂ) • J.P k := by
  ext w
  simp only [mul_apply_eq_comp, J.P_apply, map_smul, J.apply_fst, smul_apply, smul_smul, mul_comm]

/-- `P k x = λ_k P k`. -/
theorem P_mul (k : Fin (finrank ℂ H)) : J.P k * x = (J.lam k : ℂ) • J.P k := by
  rw [← (J.commute_fst_P k).eq, J.mul_P]

theorem P_mul_P' (k l : Fin (finrank ℂ H)) : J.P k * J.P l = if k = l then J.P k else 0 := by
  split_ifs with h
  · subst h; exact J.P_mul_self k
  · exact J.P_mul_P h

/-- A sum of distinct rank-one spectral projections is a projection. -/
theorem isStarProjection_sum_P (T : Finset (Fin (finrank ℂ H))) :
    IsStarProjection (∑ k ∈ T, J.P k) := by
  refine ⟨?_, isSelfAdjoint_sum _ fun k _ => J.P_isSelfAdjoint k⟩
  show (∑ k ∈ T, J.P k) * (∑ k ∈ T, J.P k) = ∑ k ∈ T, J.P k
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [J.P_mul_P']
  rw [Finset.sum_ite_eq]
  simp [hk]

/-- A sum of rank-one spectral projections commutes with the second operator. -/
theorem commute_sum_P_snd (T : Finset (Fin (finrank ℂ H))) : Commute (∑ k ∈ T, J.P k) a :=
  Commute.sum_left _ _ _ fun k _ => (J.commute_snd_P k).symm

/-- Each rank-one spectral projection has trace `1`. -/
theorem trace_P (k : Fin (finrank ℂ H)) : LinearMap.trace ℂ H (J.P k : H →ₗ[ℂ] H) = 1 := by
  rw [LinearMap.trace_eq_sum_inner _ J.basis]
  simp only [ContinuousLinearMap.coe_coe, J.P_apply_basis]
  rw [Finset.sum_eq_single k]
  · simp
  · intro l _ hl
    simp [Ne.symm hl]
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- The trace of a sum of distinct rank-one spectral projections is their number. -/
theorem trace_sum_P (T : Finset (Fin (finrank ℂ H))) :
    LinearMap.trace ℂ H ((∑ k ∈ T, J.P k : H →L[ℂ] H) : H →ₗ[ℂ] H) = (T.card : ℂ) := by
  rw [ContinuousLinearMap.toLinearMap_sum, map_sum]
  simp [J.trace_P]

/-- `x * x` in the joint eigenbasis. -/
theorem mul_self_eq_sum : x * x = ∑ k, (J.lam k : ℂ) • ((J.lam k : ℂ) • J.P k) := by
  calc x * x = x * ∑ k, (J.lam k : ℂ) • J.P k := by rw [← J.eq_sum_lam_P]
    _ = ∑ k, (J.lam k : ℂ) • ((J.lam k : ℂ) • J.P k) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [mul_smul_comm, J.mul_P]

end JointEigenbasis

/-! ### Lemma 3.1 in finite dimension -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Lemma 3.1 for `B(H)`, `H` finite-dimensional.** For a POVM `(a i)` and any
linear functional `φ` on `B(H)` there are projections `q i` commuting with `a i`,
of total trace `dim H`, with `φ(∑ a i a i) ≤ φ(∑ q i a i)` (real parts). The `q i`
are sums of rank-one spectral projections of `a i`, selected by
`exists_finset_sum_ge`. -/
theorem exists_commuting_projections (φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ) (a : ι → H →L[ℂ] H)
    (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∑ i, a i = 1) :
    ∃ q : ι → H →L[ℂ] H, (∀ i, IsStarProjection (q i)) ∧ (∀ i, Commute (q i) (a i)) ∧
      ∑ i, LinearMap.trace ℂ H (q i : H →ₗ[ℂ] H) = (finrank ℂ H : ℂ) ∧
      (φ (∑ i, a i * a i)).re ≤ (φ (∑ i, q i * a i)).re := by
  classical
  have hsa : ∀ i, IsSelfAdjoint (a i) := fun i => IsSelfAdjoint.of_nonneg (ha0 i)
  have hJ : ∀ i, Nonempty (JointEigenbasis (a i) (a i)) := fun i =>
    exists_jointEigenbasis (hsa i) (hsa i) (Commute.refl _)
  let J : ∀ i, JointEigenbasis (a i) (a i) := fun i => Classical.choice (hJ i)
  have ha1' : ∀ i, a i ≤ 1 := fun i => by
    rw [← ha1]
    exact Finset.single_le_sum (fun j _ => ha0 j) (Finset.mem_univ i)
  -- weights (the eigenvalues) and values
  set N := finrank ℂ H with hN
  let w : ι × Fin N → ℝ := fun p => (J p.1).lam p.2
  let c : ι × Fin N → ℝ := fun p => (J p.1).lam p.2 * (φ ((J p.1).P p.2)).re
  have hw : ∀ p, w p ∈ Set.Icc (0 : ℝ) 1 := fun p =>
    ((J p.1).mem_Icc_iff.mp ⟨ha0 p.1, ha1' p.1⟩) p.2
  -- the eigenvalues sum to the dimension
  have hsum : ∑ p, w p = N := by
    have h1 : ∑ i, LinearMap.trace ℂ H (a i : H →ₗ[ℂ] H) = (N : ℂ) := by
      rw [← map_sum, ← ContinuousLinearMap.toLinearMap_sum, ha1,
        ContinuousLinearMap.toLinearMap_one, LinearMap.trace_one]
    have h2 : ∑ i, LinearMap.trace ℂ H (a i : H →ₗ[ℂ] H) = ∑ p : ι × Fin N, ((w p : ℝ) : ℂ) := by
      rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun i _ => (J i).trace_eq_sum_lam
    have h3 : ((∑ p, w p : ℝ) : ℂ) = (N : ℂ) := by rw [Complex.ofReal_sum, ← h2, h1]
    exact_mod_cast h3
  obtain ⟨S, hS, hle⟩ :=
    exists_finset_sum_ge c w (fun p => (hw p).1) (fun p => (hw p).2) N hsum
  -- the selected projections
  let T : ι → Finset (Fin N) := fun i => Finset.univ.filter fun k => (i, k) ∈ S
  refine ⟨fun i => ∑ k ∈ T i, (J i).P k, fun i => (J i).isStarProjection_sum_P (T i),
    fun i => (J i).commute_sum_P_snd (T i), ?_, ?_⟩
  · -- total trace
    have hT : ∀ i, LinearMap.trace ℂ H ((∑ k ∈ T i, (J i).P k : H →L[ℂ] H) : H →ₗ[ℂ] H) =
        ∑ k, if (i, k) ∈ S then (1 : ℂ) else 0 := fun i => by
      rw [(J i).trace_sum_P, Finset.card_filter]
      push_cast
      rfl
    simp only [hT]
    rw [← Fintype.sum_prod_type (fun p : ι × Fin N => if p ∈ S then (1 : ℂ) else 0),
      Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, hS]
  · -- the inequality
    have hA : ∀ i, (φ (a i * a i)).re = ∑ k, w (i, k) * c (i, k) := fun i => by
      rw [(J i).mul_self_eq_sum, map_sum, Complex.re_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, Complex.re_ofReal_mul,
        Complex.re_ofReal_mul]
    have hQ : ∀ i, (φ ((∑ k ∈ T i, (J i).P k) * a i)).re =
        ∑ k, if (i, k) ∈ S then c (i, k) else 0 := fun i => by
      rw [Finset.sum_mul, ← Finset.sum_filter]
      rw [map_sum, Complex.re_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [(J i).P_mul, map_smul, smul_eq_mul, Complex.re_ofReal_mul]
    rw [map_sum, map_sum, Complex.re_sum, Complex.re_sum]
    simp only [hA, hQ]
    rw [← Fintype.sum_prod_type (fun p : ι × Fin N => w p * c p),
      ← Fintype.sum_prod_type (fun p : ι × Fin N => if p ∈ S then c p else 0),
      Finset.sum_ite_mem, Finset.univ_inter]
    exact hle

end Orthogonalization.FinDim
