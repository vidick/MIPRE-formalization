/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/MvN/Corollaries.lean
-/
/-
# Tier T3 corollaries: Theorems 1.1, 1.4 and Corollary 1.5 under the interface

Formalization of M. de la Salle, *Orthogonalization of Positive Operator Valued
Measures* (arXiv:2103.14126v2, `manuscript/arXiv2103.14126v2.tex`): the three
Section 1 companions of Theorem 1.2 on an arbitrary complex Hilbert space,
conditional on the structure-theory interface `MvNStructureTheory`
(`MvN/Interface.lean`, PLAN.md §9), exactly as `MvN/Main.lean` states
Theorem 1.2 conditionally (`povm_orthogonalization_of_structure`).

* `povm_orthogonalization_hilbert_of_structure` — **Theorem 1.1**
  (`thm:orthonormalization_Hilbert`) with the commutant clause;
* `pvm_almost_commute_of_structure` — **Theorem 1.4** (`thm:pvm_almost_commute`);
* `almost_commuting_unitaries_of_structure` — **Corollary 1.5**
  (`cor:almost_commuting`).

Each statement is the signed statement of `Orthogonalization/Basic.lean` with the
binder `(hS : MvNStructureTheory.{u})` and the explicit binders
`{H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]`
prepended, byte-identical otherwise (FIDELITY.md, tier T3 statement layer). The
proofs are those of tier T1b (`Blocks/Corollaries.lean`, `Blocks/Fourier.lean`)
re-run with the T3 engine `povm_orthogonalization_of_structure hS` in place of
the finite-dimensional engine `povm_orthogonalization_finDim_vn`:
finite-dimensionality entered those proofs only through that call. The
proof-side helpers of `Blocks/Corollaries.lean` (vector states, restriction of a
normal state, the compressed POVM `∑_j q_j p_i q_j`, the identity of Section 5,
the triangle inequality for `‖·‖_φ`) and the Fourier dictionary of
`Blocks/Fourier.lean` are generic and are reused as they stand; the few operator
lemmas of `Blocks/Fourier.lean` that were stated with `[FiniteDimensional ℂ H]`
without needing it are re-proved here on any complete `H` under primed names.
-/
import Mathlib
import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.Main
import MIPRE.Background.Orthonormalization.Orthogonalization.Blocks.Corollaries
import MIPRE.Background.Orthonormalization.Orthogonalization.Blocks.Fourier

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace Orthogonalization

open scoped BigOperators ComplexOrder InnerProductSpace
open Corollaries

universe u

/-! ### Operators on any complete `H`: PVMs, membership in `M`, and Parseval for `‖·‖_φ`

The `[CompleteSpace H]` versions of the `Operators` section of `Blocks/Fourier.lean`
(there stated under `[FiniteDimensional ℂ H]`; the proofs are unchanged). -/

section Operators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The projections of a PVM are pairwise orthogonal: `q j' * q j = δ_{j' j} q j`
(`IsPVM.mul_eq_ite` of `Blocks/Fourier.lean` on any complete `H`). -/
theorem IsPVM.mul_eq_ite' {M : VonNeumannAlgebra H} {N : ℕ} {q : Fin N → H →L[ℂ] H}
    (hq : IsPVM M q) (j' j : Fin N) : q j' * q j = if j' = j then q j else 0 := by
  obtain ⟨_, hproj, hsum⟩ := hq
  have hsa : ∀ k, star (q k) = q k := fun k => (hproj k).isSelfAdjoint.star_eq
  have hidem : ∀ k, q k * q k = q k := fun k => (hproj k).isIdempotentElem.eq
  have key : ∀ k, k ≠ j → q k * q j = 0 := by
    intro k hk
    have h1 : ∑ k' ∈ Finset.univ.erase j, star (q k' * q j) * (q k' * q j) = 0 := by
      have h2 : ∀ k', star (q k' * q j) * (q k' * q j) = q j * q k' * q j := by
        intro k'
        rw [star_mul, hsa, hsa, mul_assoc, ← mul_assoc (q k'), hidem, ← mul_assoc]
      simp_rw [h2]
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ j)]
      have h4 : ∑ k', q j * q k' * q j = q j := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, hsum, mul_one, hidem]
      rw [h4, hidem, hidem, sub_self]
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg
      fun k' _ => star_mul_self_nonneg (q k' * q j)).mp h1 k
      (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩)
    exact (CStarRing.star_mul_self_eq_zero_iff _).mp h3
  by_cases h : j' = j
  · rw [if_pos h, h, hidem]
  · rw [if_neg h]
    exact key j' h

variable {N : ℕ} {ζ : ℂ}

/-- The spectral projections of `w ∈ M` lie in `M`. -/
theorem spectralProj_mem' (M : VonNeumannAlgebra H) {w : H →L[ℂ] H} (hw : w ∈ M) (i : Fin N) :
    spectralProj ζ N w i ∈ M :=
  Blocks.smul_mem_vn M _ (sum_mem fun k _ => Blocks.smul_mem_vn M _ (pow_mem hw k))

/-- The reconstructed unitary of a family of elements of `M` lies in `M`. -/
theorem fourierUnitary_mem' (M : VonNeumannAlgebra H) {r : Fin N → H →L[ℂ] H}
    (hr : ∀ j, r j ∈ M) : fourierUnitary ζ r ∈ M :=
  sum_mem fun j _ => Blocks.smul_mem_vn M _ (hr j)

/-- The spectral projections of a unitary `w ∈ M` of order `N` form a PVM in `M`. -/
theorem isPVM_spectralProj' (M : VonNeumannAlgebra H) (hζ : IsPrimitiveRoot ζ N) (hN : 0 < N)
    {w : H →L[ℂ] H} (hw : w ∈ M) (hw1 : star w * w = 1) (hwN : w ^ N = 1) :
    IsPVM M (spectralProj ζ N w) :=
  ⟨fun i => spectralProj_mem' M hw i, fun i => isStarProjection_spectralProj hζ hN hwN hw1 i,
    sum_spectralProj hζ hN⟩

/-- `‖-x‖_φ² = ‖x‖_φ²`. -/
theorem NormalState.normSq_neg' {M : VonNeumannAlgebra H} (φ : NormalState M) (x : H →L[ℂ] H) :
    φ.normSq (-x) = φ.normSq x := by
  simp only [NormalState.normSq, star_neg, neg_mul_neg]

/-- **Parseval** for the seminorm `‖·‖_φ`: `∑_j ‖Y j‖_φ² = N⁻¹ ∑_{l<N} ‖d l‖_φ²` for the
Fourier coefficients `Y j = N⁻¹ ∑_{l<N} ζ^{-jl} d l` (only linearity of `φ` is used). -/
theorem sum_normSq_fourierCoeff' {M : VonNeumannAlgebra H} (φ : NormalState M)
    (hζ : IsPrimitiveRoot ζ N) (hN : 0 < N) (d : ℕ → H →L[ℂ] H) :
    ∑ j : Fin N, φ.normSq (fourierCoeff ζ N d ((j : ℕ) : ℤ))
      = (N : ℝ)⁻¹ * ∑ l ∈ Finset.range N, φ.normSq (d l) := by
  simp only [NormalState.normSq]
  rw [← Complex.re_sum, ← map_sum, sum_star_mul_fourierCoeff hζ hN, map_smul, smul_eq_mul,
    ← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul, map_sum,
    Complex.re_sum]

/-- The hypothesis of Corollary 1.5 is the hypothesis of Theorem 1.4 for the spectral
PVMs: `∑_{i,j} ‖p_i q_j − q_j p_i‖_φ² = (nm)⁻¹ ∑_{k<n} ∑_{l<m} ‖u^{k+1} v^{l+1} − v^{l+1} u^{k+1}‖_φ²`. -/
theorem sum_normSq_spectralProj_comm' {M : VonNeumannAlgebra H} (φ : NormalState M)
    {n m : ℕ} {ω ζ : ℂ} (hω : IsPrimitiveRoot ω n) (hn : 0 < n) (hζ : IsPrimitiveRoot ζ m)
    (hm : 0 < m) {u v : H →L[ℂ] H} (hun : u ^ n = 1) (hvm : v ^ m = 1) :
    ∑ i : Fin n, ∑ j : Fin m, φ.normSq (spectralProj ω n u i * spectralProj ζ m v j
        - spectralProj ζ m v j * spectralProj ω n u i)
      = ((n : ℝ) * m)⁻¹ * ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range m,
          φ.normSq (u ^ (k + 1) * v ^ (l + 1) - v ^ (l + 1) * u ^ (k + 1)) := by
  -- the commutators are the double Fourier coefficients of `c k l = u^k v^l − v^l u^k`
  have hX : ∀ (i : Fin n) (j : Fin m),
      spectralProj ω n u i * spectralProj ζ m v j - spectralProj ζ m v j * spectralProj ω n u i
        = fourierCoeff ω n (fun k => fourierCoeff ζ m
            (fun l => u ^ k * v ^ l - v ^ l * u ^ k) ((j : ℕ) : ℤ)) ((i : ℕ) : ℤ) := by
    intro i j
    simp only [spectralProj]
    simp only [fourierCoeff_mul_right ω n, fourierCoeff_mul_left ω n]
    simp only [fourierCoeff_mul_right ζ m, fourierCoeff_mul_left ζ m]
    simp only [fourierCoeff_sub]
  simp only [hX]
  -- Parseval in `i`, then in `j`
  rw [Finset.sum_comm]
  simp only [sum_normSq_fourierCoeff' φ hω hn]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [sum_normSq_fourierCoeff' φ hζ hm]
  rw [← Finset.mul_sum, ← mul_assoc, ← mul_inv]
  congr 1
  -- reindex `k ↦ k + 1`, `l ↦ l + 1` using `u ^ n = 1 = u ^ 0`, `v ^ m = 1 = v ^ 0`
  refine (Finset.sum_congr rfl fun k _ => (sum_range_succ_shift
    (fun l => φ.normSq (u ^ k * v ^ l - v ^ l * u ^ k)) m ?_).symm).trans ?_
  · simp only [pow_zero, hvm]
  refine (sum_range_succ_shift
    (fun k => ∑ l ∈ Finset.range m, φ.normSq (u ^ k * v ^ (l + 1) - v ^ (l + 1) * u ^ k)) n
    ?_).symm
  simp only [pow_zero, hun]

end Operators

/-! ### Theorem 1.1 -/

/-- **Theorem 1.1, conditional form** (`thm:orthonormalization_Hilbert`; tier T3): the
statement of `povm_orthogonalization_hilbert` on every complex Hilbert space, with the
commutant clause, under the structure-theory interface. Proof: Theorem 1.2
(`povm_orthogonalization_of_structure`) in the von Neumann algebra `W*(a_i)` with the
vector state `x ↦ ⟪ξ, x ξ⟫`; the projections lie in `W*(a_i)`, so they commute with every
`b` commuting with the `a_i` (bicommutant). -/
theorem povm_orthogonalization_hilbert_of_structure (hS : MvNStructureTheory.{u})
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ι : Type*} [Fintype ι]
    (a : ι → H →L[ℂ] H) (ha : (∀ i, (a i).IsPositive) ∧ ∑ i, a i = 1)
    (ξ : H) (hξ : ‖ξ‖ = 1) (ε : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (h : 1 - ε < ∑ i, ‖a i ξ‖ ^ 2) :
    ∃ p : ι → H →L[ℂ] H, (∀ i, IsStarProjection (p i)) ∧ ∑ i, p i = 1 ∧
      (∑ i, ‖a i ξ - p i ξ‖ ^ 2 < 9 * ε) ∧
      ∀ b : H →L[ℂ] H, (∀ i, Commute b (a i)) → ∀ i, ∀ v : H, p i v = v → p i (b v) = b v := by
  -- the hypothesis `ε ∈ [0, 1]` of the paper is not needed for the proof
  have _ := hε
  set M := CommutingRepetition.VN.wstar (Set.range a)
  have hPOVM : IsPOVM M a :=
    ⟨fun i => CommutingRepetition.VN.subset_wstar (Set.mem_range_self i), ha.1, ha.2⟩
  have hsa : ∀ i, IsSelfAdjoint (a i) := fun i => (ha.1 i).isSelfAdjoint
  have hφ : 1 - ε < (vecState M ξ hξ (∑ i, a i * a i)).re := by
    rw [vecState_apply, re_vecFunctional_sum_mul_self ξ a hsa]
    exact h
  obtain ⟨p, hp, hbound⟩ :=
    povm_orthogonalization_of_structure hS M (vecState M ξ hξ) a hPOVM ε hφ
  refine ⟨p, hp.2.1, hp.2.2, ?_, ?_⟩
  · rwa [vecState_apply, re_vecFunctional_sum_star_sub_mul_sub] at hbound
  · intro b hb i v hv
    have hbc : b ∈ StarSubalgebra.centralizer ℂ (Set.range a) := by
      rw [StarSubalgebra.mem_centralizer_iff ℂ]
      rintro _ ⟨i', rfl⟩
      exact ⟨(hb i').eq.symm, by rw [(hsa i').star_eq]; exact (hb i').eq.symm⟩
    have hcomm : b * p i = p i * b := CommutingRepetition.VN.mem_wstar_iff.mp (hp.1 i) b hbc
    calc p i (b v) = (p i * b) v := (mul_apply_eq_comp _ _ _).symm
      _ = (b * p i) v := by rw [hcomm]
      _ = b (p i v) := mul_apply_eq_comp _ _ _
      _ = b v := by rw [hv]

/-! ### Theorem 1.4 -/

/-- **Theorem 1.4, conditional form** (`thm:pvm_almost_commute`; tier T3): the statement
of `pvm_almost_commute` for every von Neumann algebra, under the structure-theory
interface. Proof (Section 5 of the paper): with `a_i = ∑_j q_j p_i q_j`,
`∑_{i,j} ‖p_i q_j − q_j p_i‖_φ² = ∑_i ‖p_i − a_i‖_φ² + (1 − φ(∑ a_i²))`; Theorem 1.2
(`povm_orthogonalization_of_structure`) in `W*(a_i)` (whose elements commute with the
`q_j`) gives a PVM `p'` with `∑ ‖a_i − p'_i‖_φ² < 9 (ε − ∑ ‖p_i − a_i‖_φ²)`, and the
triangle inequality together with `(√D + √E)² ≤ 10 (D + E/9)` concludes. -/
theorem pvm_almost_commute_of_structure (hS : MvNStructureTheory.{u})
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) (φ : NormalState M)
    {ι κ : Type*} [Fintype ι] [Fintype κ] (p : ι → H →L[ℂ] H) (q : κ → H →L[ℂ] H)
    (hp : IsPVM M p) (hq : IsPVM M q) (ε : ℝ)
    (h : ∑ i, ∑ j, φ.normSq (p i * q j - q j * p i) < ε) :
    ∃ p' : ι → H →L[ℂ] H, IsPVM M p' ∧ (∀ i j, Commute (p' i) (q j)) ∧
      ∑ i, φ.normSq (p i - p' i) < 10 * ε := by
  -- the compressed POVM `a_i = ∑_j q_j p_i q_j`
  obtain ⟨a, ha⟩ : ∃ a : ι → H →L[ℂ] H, a = compress p q := ⟨_, rfl⟩
  have haM : ∀ i, a i ∈ M := by rw [ha]; exact compress_mem hp hq
  have haPOVM : IsPOVM M a := by rw [ha]; exact isPOVM_compress hp hq
  have hastar : ∀ i, star (a i) = a i := by rw [ha]; exact compress_star hp hq
  have hacomm : ∀ i k, Commute (a i) (q k) := by rw [ha]; exact compress_comm hq
  have hkey := key_identity hp hq
  rw [← ha] at hkey
  -- `D = ∑ ‖p_i − a_i‖_φ²` and the identity of Section 5
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = ∑ i, φ.normSq (p i - a i) := ⟨_, rfl⟩
  have hDnn : 0 ≤ D := by
    rw [hD]
    exact Finset.sum_nonneg fun i _ => normSq_nonneg_of_mem φ (sub_mem (hp.1 i) (haM i))
  have hid : ∑ i, ∑ j, φ.normSq (p i * q j - q j * p i) = D + (1 - ∑ i, (φ (a i * a i)).re) := by
    have := congrArg (fun x => (φ.toLinearMap x).re) hkey
    simp only [map_sum, map_add, map_sub, φ.map_one', Complex.re_sum, Complex.add_re,
      Complex.sub_re, Complex.one_re] at this
    rw [hD]
    exact this
  have hεD : 1 - (ε - D) < (φ (∑ i, a i * a i)).re := by
    rw [map_sum, Complex.re_sum]
    linarith [hid, h]
  -- Theorem 1.2 in the von Neumann algebra `N = W*(a_i)`, with `φ` restricted to `N`
  set N := CommutingRepetition.VN.wstar (Set.range a)
  have hNM : ∀ x ∈ N, x ∈ M := fun x hx =>
    CommutingRepetition.VN.wstar_le (Set.range_subset_iff.mpr haM) hx
  have haN : ∀ i, a i ∈ N := fun i => CommutingRepetition.VN.subset_wstar (Set.mem_range_self i)
  have haPOVM_N : IsPOVM N a := ⟨haN, haPOVM.2.1, haPOVM.2.2⟩
  obtain ⟨p', hp'N, hbound⟩ :=
    povm_orthogonalization_of_structure hS N (restrictState φ hNM) a haPOVM_N (ε - D) hεD
  have hp'M : ∀ i, p' i ∈ M := fun i => hNM _ (hp'N.1 i)
  -- `E = ∑ ‖a_i − p'_i‖_φ² < 9 (ε − D)`
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = ∑ i, φ.normSq (a i - p' i) := ⟨_, rfl⟩
  have hEnn : 0 ≤ E := by
    rw [hE]
    exact Finset.sum_nonneg fun i _ => normSq_nonneg_of_mem φ (sub_mem (haM i) (hp'M i))
  have hE9 : E < 9 * (ε - D) := by
    rw [hE]
    refine lt_of_eq_of_lt ?_ hbound
    show ∑ i, (φ.toLinearMap (star (a i - p' i) * (a i - p' i))).re
      = (φ.toLinearMap (∑ i, star (a i - p' i) * (a i - p' i))).re
    rw [map_sum, Complex.re_sum]
  refine ⟨p', ⟨hp'M, hp'N.2.1, hp'N.2.2⟩, ?_, ?_⟩
  · -- `p'_i ∈ W*(a_i)` commutes with `q_j`, which commutes with every `a_i`
    intro i j
    have hqc : q j ∈ StarSubalgebra.centralizer ℂ (Set.range a) := by
      rw [StarSubalgebra.mem_centralizer_iff ℂ]
      rintro _ ⟨i', rfl⟩
      exact ⟨(hacomm i' j).eq, by rw [hastar]; exact (hacomm i' j).eq⟩
    exact (CommutingRepetition.VN.mem_wstar_iff.mp (hp'N.1 i) (q j) hqc).symm
  · -- the triangle inequality and `(√D + √E)² ≤ 10 (D + E/9) < 10 ε`
    have htri := sum_normSq_add_le φ (fun i => p i - a i) (fun i => a i - p' i)
      (fun i => sub_mem (hp.1 i) (haM i)) (fun i => sub_mem (haM i) (hp'M i))
    simp only [sub_add_sub_cancel] at htri
    rw [← hD, ← hE] at htri
    have hsq : (Real.sqrt D + Real.sqrt E) ^ 2 ≤ 10 * (D + E / 9) := by
      nlinarith [sq_nonneg (3 * Real.sqrt D - Real.sqrt E / 3), Real.sq_sqrt hDnn,
        Real.sq_sqrt hEnn]
    calc ∑ i, φ.normSq (p i - p' i) ≤ (Real.sqrt D + Real.sqrt E) ^ 2 := htri
      _ ≤ 10 * (D + E / 9) := hsq
      _ < 10 * ε := by linarith

/-! ### Corollary 1.5 -/

/-- **Corollary 1.5, conditional form** (`cor:almost_commuting`; tier T3): the statement
of `almost_commuting_unitaries` for every von Neumann algebra, under the structure-theory
interface (conclusion normalized as in DIFFERENCES.md D5). Proof: the paper's Fourier
dictionary (`Blocks/Fourier.lean`) converts the hypothesis and the conclusion of
Theorem 1.4 (`pvm_almost_commute_of_structure`, applied with the spectral PVM of `v` in
the perturbed slot) into those of Corollary 1.5. -/
theorem almost_commuting_unitaries_of_structure (hS : MvNStructureTheory.{u})
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) (φ : NormalState M)
    (u v : H →L[ℂ] H) (hu : u ∈ M) (hv : v ∈ M)
    (hu' : u ∈ unitary (H →L[ℂ] H)) (hv' : v ∈ unitary (H →L[ℂ] H))
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (hun : u ^ n = 1) (hvm : v ^ m = 1) (ε : ℝ)
    (h : ((n : ℝ) * m)⁻¹ * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m,
        φ.normSq (u ^ (i + 1) * v ^ (j + 1) - v ^ (j + 1) * u ^ (i + 1)) < ε) :
    ∃ v' : H →L[ℂ] H, v' ∈ M ∧ v' ∈ unitary (H →L[ℂ] H) ∧ Commute u v' ∧
      (m : ℝ)⁻¹ * ∑ j ∈ Finset.range m, φ.normSq (v ^ (j + 1) - v' ^ (j + 1)) < 10 * ε := by
  -- the roots of unity and the spectral PVMs `p` of `u` and `q` of `v`
  have hω : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / n)) n :=
    Complex.isPrimitiveRoot_exp n hn.ne'
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / m)) m :=
    Complex.isPrimitiveRoot_exp m hm.ne'
  set ω := Complex.exp (2 * Real.pi * Complex.I / n)
  set ζ := Complex.exp (2 * Real.pi * Complex.I / m)
  have hu1 : star u * u = 1 := Unitary.star_mul_self_of_mem hu'
  have hv1 : star v * v = 1 := Unitary.star_mul_self_of_mem hv'
  have hp : IsPVM M (spectralProj ω n u) := isPVM_spectralProj' M hω hn hu hu1 hun
  have hq : IsPVM M (spectralProj ζ m v) := isPVM_spectralProj' M hζ hm hv hv1 hvm
  -- the hypothesis of Theorem 1.4, with `q` in the perturbed (first) slot
  have hsum : ∑ j : Fin m, ∑ i : Fin n, φ.normSq (spectralProj ζ m v j * spectralProj ω n u i
      - spectralProj ω n u i * spectralProj ζ m v j) < ε := by
    calc ∑ j : Fin m, ∑ i : Fin n, φ.normSq (spectralProj ζ m v j * spectralProj ω n u i
            - spectralProj ω n u i * spectralProj ζ m v j)
        = ∑ i : Fin n, ∑ j : Fin m, φ.normSq (spectralProj ω n u i * spectralProj ζ m v j
            - spectralProj ζ m v j * spectralProj ω n u i) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [← NormalState.normSq_neg' φ (spectralProj ω n u i * spectralProj ζ m v j - _),
            neg_sub]
      _ = ((n : ℝ) * m)⁻¹ * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m,
            φ.normSq (u ^ (i + 1) * v ^ (j + 1) - v ^ (j + 1) * u ^ (i + 1)) :=
          sum_normSq_spectralProj_comm' φ hω hn hζ hm hun hvm
      _ < ε := h
  -- Theorem 1.4
  obtain ⟨q', hq', hcomm, hclose⟩ :=
    pvm_almost_commute_of_structure hS M φ (spectralProj ζ m v) (spectralProj ω n u) hq hp ε hsum
  have horth : ∀ j' j, q' j' * q' j = if j' = j then q' j else 0 := hq'.mul_eq_ite'
  have hsa : ∀ j, star (q' j) = q' j := fun j => (hq'.2.1 j).isSelfAdjoint.star_eq
  have hsum' : ∑ j, q' j = 1 := hq'.2.2
  -- the unitary `v' = ∑_j ζ^j q'_j`
  refine ⟨fourierUnitary ζ q', fourierUnitary_mem' M hq'.1, ?_, ?_, ?_⟩
  · exact Unitary.mem_iff.mpr ⟨star_fourierUnitary_mul_self horth hζ hm hsum' hsa,
      fourierUnitary_mul_star_self horth hζ hm hsum' hsa⟩
  · -- `u = ∑_i ω^i p_i` commutes with `v'` since each `p_i` commutes with each `q'_j`
    have hc : Commute (∑ i : Fin n, ω ^ ((i : ℕ) : ℤ) • spectralProj ω n u i)
        (fourierUnitary ζ q') :=
      Commute.sum_left _ _ _ fun i _ => Commute.smul_left
        (Commute.sum_right _ _ _ fun j _ => Commute.smul_right (hcomm j i).symm _) _
    rwa [← eq_sum_zpow_smul_spectralProj hω hn hun] at hc
  · -- `q_j − q'_j` is the `j`-th Fourier coefficient of `l ↦ v^l − v'^l`; Parseval
    have hqq' : ∀ j : Fin m, spectralProj ζ m v j - q' j
        = fourierCoeff ζ m (fun l => v ^ l - fourierUnitary ζ q' ^ l) ((j : ℕ) : ℤ) := by
      intro j
      rw [← spectralProj_fourierUnitary horth hζ hm hsum' j]
      exact fourierCoeff_sub ζ m (fun l => v ^ l) (fun l => fourierUnitary ζ q' ^ l) _
    have hpars : ∑ j : Fin m, φ.normSq (spectralProj ζ m v j - q' j)
        = (m : ℝ)⁻¹ * ∑ l ∈ Finset.range m, φ.normSq (v ^ l - fourierUnitary ζ q' ^ l) := by
      simp only [hqq']
      exact sum_normSq_fourierCoeff' φ hζ hm _
    have hshift : ∑ l ∈ Finset.range m, φ.normSq (v ^ (l + 1) - fourierUnitary ζ q' ^ (l + 1))
        = ∑ l ∈ Finset.range m, φ.normSq (v ^ l - fourierUnitary ζ q' ^ l) :=
      sum_range_succ_shift (fun l => φ.normSq (v ^ l - fourierUnitary ζ q' ^ l)) m
        (by simp only [pow_zero, hvm, fourierUnitary_pow_eq_one horth hζ hm hsum'])
    rw [hshift, ← hpars]
    exact hclose

end Orthogonalization
