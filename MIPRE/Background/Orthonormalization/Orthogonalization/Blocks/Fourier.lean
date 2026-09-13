/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/Blocks/Fourier.lean
-/
/-
# Tier T1b: Corollary 1.5 from Theorem 1.4 through the Fourier dictionary

M. de la Salle, *Orthogonalization of Positive Operator Valued Measures*,
arXiv:2103.14126v2, Corollary 1.5 (`cor:almost_commuting`, lines 149–153 of
`manuscript/arXiv2103.14126v2.tex`), in finite dimension. The theorem
`almost_commuting_unitaries_finDim` below is the signed statement
`almost_commuting_unitaries` of `Orthogonalization/Basic.lean` with the
hypothesis `[FiniteDimensional ℂ H]` added; its conclusion is normalized as
explained in `DIFFERENCES.md` D5 (the average over the `m` powers of the
approximated unitary `v`).

The proof is the paper's Fourier dictionary (line 149): a unitary `w` of finite
order `N` corresponds to the PVM of its spectral projections
`P i = N⁻¹ ∑_{k<N} ζ^{-ik} w^k` (`ζ = e^{2πi/N}`), with inverse
`w = ∑_i ζ^i P i`; character orthogonality gives the PVM axioms, and the
algebraic Parseval identity `∑_j (Y_j)* Y_j = N⁻¹ ∑_l (d_l)* d_l` for the
Fourier coefficients `Y_j = N⁻¹ ∑_l ζ^{-jl} d_l` (proved in the algebra, before
any state is applied) converts the hypothesis and the conclusion of
Theorem 1.4 (`pvm_almost_commute_finDim`, applied with the PVM of `v` in the
perturbed slot) into those of Corollary 1.5. Finite-dimensionality enters
only through Theorem 1.4.
-/
import Mathlib
import MIPRE.Background.Orthonormalization.Orthogonalization.Basic
import MIPRE.Background.Orthonormalization.Orthogonalization.Blocks.Corollaries
import MIPRE.Background.Orthonormalization.Orthogonalization.Blocks.StateOnM

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace Orthogonalization
open scoped BigOperators ComplexOrder
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

/-! ### Scalar facts: character orthogonality for a primitive root of unity -/

section Scalars

variable {N : ℕ} {ζ : ℂ}

/-- Reindexing a sum over `range N` by `k ↦ k + 1` for an `N`-periodic summand. -/
theorem sum_range_succ_shift {β : Type*} [AddCommGroup β] (f : ℕ → β) (N : ℕ) (h : f 0 = f N) :
    ∑ k ∈ Finset.range N, f (k + 1) = ∑ k ∈ Finset.range N, f k := by
  have h2 := Finset.sum_range_succ f N
  rw [Finset.sum_range_succ' f N, h] at h2
  exact add_right_cancel h2

/-- The conjugate of an integer power of a root of unity is its inverse power. -/
theorem star_zpow_of_isPrimitiveRoot (hζ : IsPrimitiveRoot ζ N) (hN : 0 < N) (z : ℤ) :
    star (ζ ^ z) = ζ ^ (-z) := by
  rw [star_zpow₀, Complex.star_def, ← Complex.inv_eq_conj (hζ.norm'_eq_one hN.ne'), inv_zpow']

/-- **Character orthogonality**: `∑_{k<N} ζ^{dk} = N` if `N ∣ d` and `0` otherwise. -/
theorem sum_zpow_mul_range (hζ : IsPrimitiveRoot ζ N) (d : ℤ) :
    ∑ k ∈ Finset.range N, ζ ^ (d * (k : ℤ)) = if (N : ℤ) ∣ d then (N : ℂ) else 0 := by
  simp_rw [zpow_mul, zpow_natCast]
  have hη : (ζ ^ d) ^ N = 1 := by
    rw [← zpow_natCast, ← zpow_mul, hζ.zpow_eq_one_iff_dvd]
    exact dvd_mul_left _ _
  split_ifs with hd
  · rw [(hζ.zpow_eq_one_iff_dvd d).mpr hd]
    simp
  · have h1 : ζ ^ d ≠ 1 := fun h => hd ((hζ.zpow_eq_one_iff_dvd d).mp h)
    have := geom_sum_mul (ζ ^ d) N
    rw [hη, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr h1)

/-- Character orthogonality, summed over `Fin N`. -/
theorem sum_zpow_mul_fin (hζ : IsPrimitiveRoot ζ N) (d : ℤ) :
    ∑ j : Fin N, ζ ^ (d * ((j : ℕ) : ℤ)) = if (N : ℤ) ∣ d then (N : ℂ) else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => ζ ^ (d * (k : ℤ))) N]
  exact sum_zpow_mul_range hζ d

/-- Two elements of `Fin N` are congruent mod `N` only if they are equal. -/
theorem natCast_dvd_sub_iff_fin (i i' : Fin N) :
    (N : ℤ) ∣ ((i : ℕ) : ℤ) - ((i' : ℕ) : ℤ) ↔ i = i' := by
  constructor
  · intro h
    have := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_sub_lt_iff]; constructor <;> omega)
    exact Fin.ext (by omega)
  · rintro rfl
    simp

/-- Two elements of `range N` are congruent mod `N` only if they are equal. -/
theorem natCast_dvd_sub_iff_lt {k k' : ℕ} (hk : k < N) (hk' : k' < N) :
    (N : ℤ) ∣ (k : ℤ) - (k' : ℤ) ↔ k = k' := by
  constructor
  · intro h
    have := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_sub_lt_iff]; constructor <;> omega)
    omega
  · rintro rfl
    simp

end Scalars

/-! ### Discrete Fourier coefficients in a star-algebra over `ℂ` -/

section Fourier

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- The `j`-th discrete Fourier coefficient `N⁻¹ ∑_{l<N} ζ^{-jl} d l` of a family
`d : ℕ → A` (only the values `d 0, …, d (N-1)` matter). -/
noncomputable def fourierCoeff (ζ : ℂ) (N : ℕ) (d : ℕ → A) (j : ℤ) : A :=
  (N : ℂ)⁻¹ • ∑ l ∈ Finset.range N, ζ ^ (-(j * (l : ℤ))) • d l

variable (ζ : ℂ) (N : ℕ)

theorem fourierCoeff_mul_right (d : ℕ → A) (j : ℤ) (y : A) :
    fourierCoeff ζ N d j * y = fourierCoeff ζ N (fun l => d l * y) j := by
  simp only [fourierCoeff, smul_mul_assoc, Finset.sum_mul]

theorem fourierCoeff_mul_left (d : ℕ → A) (j : ℤ) (y : A) :
    y * fourierCoeff ζ N d j = fourierCoeff ζ N (fun l => y * d l) j := by
  simp only [fourierCoeff, mul_smul_comm, Finset.mul_sum]

theorem fourierCoeff_sub (d d' : ℕ → A) (j : ℤ) :
    fourierCoeff ζ N d j - fourierCoeff ζ N d' j = fourierCoeff ζ N (fun l => d l - d' l) j := by
  simp only [fourierCoeff, smul_sub, Finset.sum_sub_distrib]

/-- Two Fourier transforms in independent variables commute. -/
theorem fourierCoeff_swap (ω : ℂ) (N' : ℕ) (c : ℕ → ℕ → A) (i j : ℤ) :
    fourierCoeff ζ N (fun l => fourierCoeff ω N' (fun k => c k l) i) j
      = fourierCoeff ω N' (fun k => fourierCoeff ζ N (fun l => c k l) j) i := by
  simp only [fourierCoeff, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  congr 1
  ring

variable {ζ N}

/-- The **orthogonality kernel** of the Fourier transform: transforming twice, in the
variables `l` and `l'`, with opposite frequencies and summing over the frequency
recovers the diagonal. -/
theorem sum_fourierCoeff_fourierCoeff_neg (hζ : IsPrimitiveRoot ζ N) (hN : 0 < N)
    (F : ℕ → ℕ → A) :
    ∑ j : Fin N, fourierCoeff ζ N (fun l' => fourierCoeff ζ N (fun l => F l l') (-((j : ℕ) : ℤ)))
        ((j : ℕ) : ℤ)
      = (N : ℂ)⁻¹ • ∑ l ∈ Finset.range N, F l l := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN.ne'
  simp only [fourierCoeff, Finset.smul_sum, smul_smul]
  -- reorder the triple sum to `∑ l', ∑ l, ∑ j`
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun l' _ => Finset.sum_comm).trans ?_
  simp_rw [← Finset.sum_smul]
  -- evaluate the scalar `∑ j, …` by character orthogonality
  have hscal : ∀ l l' : ℕ, l < N → l' < N →
      ∑ j : Fin N, (N : ℂ)⁻¹ * (ζ ^ (-(((j : ℕ) : ℤ) * (l' : ℤ))) *
          ((N : ℂ)⁻¹ * ζ ^ (-(-((j : ℕ) : ℤ) * (l : ℤ)))))
        = if l = l' then (N : ℂ)⁻¹ else 0 := by
    intro l l' hl hl'
    have h1 : ∀ j : Fin N, (N : ℂ)⁻¹ * (ζ ^ (-(((j : ℕ) : ℤ) * (l' : ℤ))) *
          ((N : ℂ)⁻¹ * ζ ^ (-(-((j : ℕ) : ℤ) * (l : ℤ)))))
        = ((N : ℂ)⁻¹ * (N : ℂ)⁻¹) * ζ ^ (((l : ℤ) - (l' : ℤ)) * ((j : ℕ) : ℤ)) := by
      intro j
      rw [show (N : ℂ)⁻¹ * (ζ ^ (-(((j : ℕ) : ℤ) * (l' : ℤ))) *
            ((N : ℂ)⁻¹ * ζ ^ (-(-((j : ℕ) : ℤ) * (l : ℤ)))))
          = ((N : ℂ)⁻¹ * (N : ℂ)⁻¹) *
            (ζ ^ (-(((j : ℕ) : ℤ) * (l' : ℤ))) * ζ ^ (-(-((j : ℕ) : ℤ) * (l : ℤ)))) by ring,
        ← zpow_add₀ hζ0]
      congr 2
      ring
    rw [Finset.sum_congr rfl fun j _ => h1 j, ← Finset.mul_sum, sum_zpow_mul_fin hζ]
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    by_cases hll : l = l'
    · rw [if_pos ((natCast_dvd_sub_iff_lt hl hl').mpr hll), if_pos hll]
      field_simp
    · rw [if_neg (fun h => hll ((natCast_dvd_sub_iff_lt hl hl').mp h)), if_neg hll]
      simp
  rw [Finset.sum_congr rfl fun l' hl' => Finset.sum_congr rfl fun l hl =>
    congrArg (· • F l l') (hscal l l' (Finset.mem_range.mp hl) (Finset.mem_range.mp hl'))]
  simp only [ite_smul, zero_smul, Finset.sum_ite_eq']
  refine Finset.sum_congr rfl fun l' hl' => ?_
  rw [if_pos hl']

variable [StarRing A] [StarModule ℂ A]

/-- The adjoint of a Fourier coefficient is the `(-j)`-th coefficient of the adjoints. -/
theorem star_fourierCoeff (hζ : IsPrimitiveRoot ζ N) (hN : 0 < N) (d : ℕ → A) (j : ℤ) :
    star (fourierCoeff ζ N d j) = fourierCoeff ζ N (fun l => star (d l)) (-j) := by
  simp only [fourierCoeff, star_smul, star_sum, star_zpow_of_isPrimitiveRoot hζ hN]
  rw [show star ((N : ℂ)⁻¹) = (N : ℂ)⁻¹ by simp]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 2
  ring

/-- **Parseval's identity** in the algebra: for the Fourier coefficients
`Y j = N⁻¹ ∑_{l<N} ζ^{-jl} d l`, `∑_j (Y j)* (Y j) = N⁻¹ ∑_{l<N} (d l)* (d l)`. -/
theorem sum_star_mul_fourierCoeff (hζ : IsPrimitiveRoot ζ N) (hN : 0 < N) (d : ℕ → A) :
    ∑ j : Fin N, star (fourierCoeff ζ N d ((j : ℕ) : ℤ)) * fourierCoeff ζ N d ((j : ℕ) : ℤ)
      = (N : ℂ)⁻¹ • ∑ l ∈ Finset.range N, star (d l) * d l := by
  have h : ∀ j : Fin N,
      star (fourierCoeff ζ N d ((j : ℕ) : ℤ)) * fourierCoeff ζ N d ((j : ℕ) : ℤ)
        = fourierCoeff ζ N (fun l' => fourierCoeff ζ N (fun l => star (d l) * d l')
            (-((j : ℕ) : ℤ))) ((j : ℕ) : ℤ) := by
    intro j
    rw [star_fourierCoeff hζ hN, fourierCoeff_mul_left]
    simp only [fourierCoeff_mul_right]
  rw [Finset.sum_congr rfl fun j _ => h j]
  exact sum_fourierCoeff_fourierCoeff_neg hζ hN _

end Fourier

/-! ### The dictionary: spectral projections of a unitary of finite order -/

section Dictionary

variable {A : Type*} [Ring A] [Algebra ℂ A]
variable {N : ℕ} {ζ : ℂ}

/-- If `x` acts on `p` by the scalar `ζ ^ e`, then `x ^ l` acts by `ζ ^ (e l)`. -/
theorem pow_mul_eq_zpow_smul_of_mul_eq (hζ0 : ζ ≠ 0) {x p : A} {e : ℤ}
    (h : x * p = ζ ^ e • p) (l : ℕ) : x ^ l * p = ζ ^ (e * (l : ℤ)) • p := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [pow_succ, mul_assoc, h, mul_smul_comm, ih, smul_smul, ← zpow_add₀ hζ0]
    congr 2
    push_cast
    ring

/-- The Fourier coefficient of an eigenfamily: if `x l * p = ζ ^ (e l) • p` for every `l`,
then `(N⁻¹ ∑_{l<N} ζ^{-jl} x l) * p` is `p` when `j ≡ e (mod N)` and `0` otherwise. -/
theorem fourierCoeff_mul_of_eigen (hζ : IsPrimitiveRoot ζ N) (hN : 0 < N) {x : ℕ → A} {p : A}
    {e : ℤ} (h : ∀ l, x l * p = ζ ^ (e * (l : ℤ)) • p) (j : ℤ) :
    fourierCoeff ζ N x j * p = if (N : ℤ) ∣ e - j then p else 0 := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN.ne'
  rw [fourierCoeff_mul_right]
  simp only [fourierCoeff, h, smul_smul]
  have h1 : ∀ l : ℕ, ζ ^ (-(j * (l : ℤ))) * ζ ^ (e * (l : ℤ)) = ζ ^ ((e - j) * (l : ℤ)) := by
    intro l
    rw [← zpow_add₀ hζ0]
    congr 1
    ring
  simp_rw [h1, ← Finset.sum_smul, sum_zpow_mul_range hζ, smul_smul]
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  split_ifs
  · rw [inv_mul_cancel₀ hN', one_smul]
  · rw [mul_zero, zero_smul]

/-- Scalars pass through the Fourier transform. -/
theorem smul_fourierCoeff (c : ℂ) (d : ℕ → A) (j : ℤ) :
    c • fourierCoeff ζ N d j = fourierCoeff ζ N (fun l => c • d l) j := by
  simp only [fourierCoeff, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  ring

/-- The **spectral projections** of a unitary `w` of order `N` (the paper's
`p_j = n⁻¹ ∑_k e^{-2ijkπ/n} u^k`, line 149): `P i = N⁻¹ ∑_{k<N} ζ^{-ik} w^k`. -/
noncomputable def spectralProj (ζ : ℂ) (N : ℕ) (w : A) (i : Fin N) : A :=
  fourierCoeff ζ N (fun k => w ^ k) ((i : ℕ) : ℤ)

variable (hζ : IsPrimitiveRoot ζ N) (hN : 0 < N) {w : A} (hwN : w ^ N = 1)
include hζ hN hwN

/-- The eigen-relation `w * P i = ζ ^ i • P i`. -/
theorem mul_spectralProj (i : Fin N) :
    w * spectralProj ζ N w i = ζ ^ ((i : ℕ) : ℤ) • spectralProj ζ N w i := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN.ne'
  rw [spectralProj, fourierCoeff_mul_left, smul_fourierCoeff]
  unfold fourierCoeff
  congr 1
  set f : ℕ → A := fun k => (ζ ^ ((i : ℕ) : ℤ) * ζ ^ (-(((i : ℕ) : ℤ) * (k : ℤ)))) • w ^ k with hf
  have h1 : ∀ k ∈ Finset.range N, ζ ^ (-(((i : ℕ) : ℤ) * (k : ℤ))) • (w * w ^ k) = f (k + 1) := by
    intro k _
    simp only [hf]
    rw [← pow_succ', ← zpow_add₀ hζ0]
    congr 2
    push_cast
    ring
  have h2 : ∀ k ∈ Finset.range N,
      ζ ^ (-(((i : ℕ) : ℤ) * (k : ℤ))) • (ζ ^ ((i : ℕ) : ℤ) • w ^ k) = f k := by
    intro k _
    simp only [hf]
    rw [smul_smul, mul_comm]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2]
  apply sum_range_succ_shift
  simp only [hf, hwN, pow_zero, Nat.cast_zero, mul_zero, neg_zero, zpow_zero, mul_one]
  rw [(hζ.zpow_eq_one_iff_dvd (-(((i : ℕ) : ℤ) * (N : ℤ)))).mpr
    (by rw [dvd_neg]; exact dvd_mul_left _ _), mul_one]

/-- The powers of `w` act on `P i` by `ζ ^ (i l)`. -/
theorem pow_mul_spectralProj (i : Fin N) (l : ℕ) :
    w ^ l * spectralProj ζ N w i = ζ ^ (((i : ℕ) : ℤ) * (l : ℤ)) • spectralProj ζ N w i :=
  pow_mul_eq_zpow_smul_of_mul_eq (hζ.ne_zero hN.ne') (mul_spectralProj hζ hN hwN i) l

/-- The spectral projections are pairwise orthogonal idempotents: `P i' * P i = δ_{i' i} P i`. -/
theorem spectralProj_mul_spectralProj (i' i : Fin N) :
    spectralProj ζ N w i' * spectralProj ζ N w i = if i' = i then spectralProj ζ N w i else 0 := by
  refine (fourierCoeff_mul_of_eigen hζ hN (fun l => pow_mul_spectralProj hζ hN hwN i l)
    ((i' : ℕ) : ℤ)).trans ?_
  by_cases h : i' = i
  · rw [if_pos ((natCast_dvd_sub_iff_fin i i').mpr h.symm), if_pos h]
  · rw [if_neg (fun h' => h ((natCast_dvd_sub_iff_fin i i').mp h').symm), if_neg h]

omit hwN in
/-- The spectral projections sum to `1`. -/
theorem sum_spectralProj : ∑ i, spectralProj ζ N w i = 1 := by
  simp only [spectralProj, fourierCoeff, ← Finset.smul_sum]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have hcoef : ∀ k ∈ Finset.range N,
      (∑ i : Fin N, ζ ^ (-(((i : ℕ) : ℤ) * (k : ℤ)))) • w ^ k
        = if k = 0 then (N : ℂ) • w ^ k else 0 := by
    intro k hk
    have h1 : ∀ i : Fin N, ζ ^ (-(((i : ℕ) : ℤ) * (k : ℤ))) = ζ ^ ((-(k : ℤ)) * ((i : ℕ) : ℤ)) :=
      fun i => by congr 1; ring
    have h2 : ((N : ℤ) ∣ -(k : ℤ)) ↔ k = 0 := by
      rw [show -(k : ℤ) = ((0 : ℕ) : ℤ) - (k : ℤ) by simp,
        natCast_dvd_sub_iff_lt hN (Finset.mem_range.mp hk), eq_comm]
    simp_rw [h1]
    rw [sum_zpow_mul_fin hζ]
    by_cases hk0 : k = 0
    · rw [if_pos (h2.mpr hk0), if_pos hk0]
    · rw [if_neg (fun h => hk0 (h2.mp h)), if_neg hk0, zero_smul]
  rw [Finset.sum_congr rfl hcoef, Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr hN), pow_zero,
    smul_smul, inv_mul_cancel₀ (by exact_mod_cast hN.ne'), one_smul]

/-- The **inverse Fourier transform**: `w = ∑_i ζ^i P i` (the paper's `u = ∑_k e^{2ikπ/n} p_k`). -/
theorem eq_sum_zpow_smul_spectralProj :
    w = ∑ i : Fin N, ζ ^ ((i : ℕ) : ℤ) • spectralProj ζ N w i := by
  conv_lhs => rw [← mul_one w, ← sum_spectralProj hζ hN (w := w), Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => mul_spectralProj hζ hN hwN i

section Star

variable [StarRing A] [StarModule ℂ A] (hw : star w * w = 1)
include hw

/-- `P i* P i' = δ_{i i'} P i'` (using `w* = w⁻¹`). -/
theorem star_spectralProj_mul_spectralProj (i i' : Fin N) :
    star (spectralProj ζ N w i) * spectralProj ζ N w i'
      = if i = i' then spectralProj ζ N w i' else 0 := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN.ne'
  have h1 : star w * spectralProj ζ N w i'
      = ζ ^ (-((i' : ℕ) : ℤ)) • spectralProj ζ N w i' := by
    calc star w * spectralProj ζ N w i'
        = ζ ^ (-((i' : ℕ) : ℤ)) • (star w * (ζ ^ ((i' : ℕ) : ℤ) • spectralProj ζ N w i')) := by
          rw [mul_smul_comm, smul_smul, ← zpow_add₀ hζ0, neg_add_cancel, zpow_zero, one_smul]
      _ = ζ ^ (-((i' : ℕ) : ℤ)) • spectralProj ζ N w i' := by
          rw [← mul_spectralProj hζ hN hwN i', ← mul_assoc, hw, one_mul]
  have h2 : ∀ l : ℕ, star w ^ l * spectralProj ζ N w i'
      = ζ ^ ((-((i' : ℕ) : ℤ)) * (l : ℤ)) • spectralProj ζ N w i' :=
    pow_mul_eq_zpow_smul_of_mul_eq hζ0 h1
  show star (fourierCoeff ζ N (fun k => w ^ k) ((i : ℕ) : ℤ)) * spectralProj ζ N w i' = _
  rw [star_fourierCoeff hζ hN]
  simp only [star_pow]
  refine (fourierCoeff_mul_of_eigen hζ hN h2 _).trans ?_
  have h3 : ((N : ℤ) ∣ -((i' : ℕ) : ℤ) - -((i : ℕ) : ℤ)) ↔ i = i' := by
    rw [show -((i' : ℕ) : ℤ) - -((i : ℕ) : ℤ) = ((i : ℕ) : ℤ) - ((i' : ℕ) : ℤ) by ring]
    exact natCast_dvd_sub_iff_fin i i'
  by_cases h : i = i'
  · rw [if_pos (h3.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (h3.mp h')), if_neg h]

/-- The spectral projections are self-adjoint. -/
theorem star_spectralProj (i : Fin N) : star (spectralProj ζ N w i) = spectralProj ζ N w i := by
  calc star (spectralProj ζ N w i)
      = star (spectralProj ζ N w i) * ∑ i', spectralProj ζ N w i' := by
        rw [sum_spectralProj hζ hN, mul_one]
    _ = ∑ i', if i = i' then spectralProj ζ N w i' else 0 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i' _ => star_spectralProj_mul_spectralProj hζ hN hwN hw i i'
    _ = spectralProj ζ N w i := by
        rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ i)]

/-- The spectral projections are (star) projections. -/
theorem isStarProjection_spectralProj (i : Fin N) : IsStarProjection (spectralProj ζ N w i) :=
  ⟨show spectralProj ζ N w i * spectralProj ζ N w i = spectralProj ζ N w i by
      rw [spectralProj_mul_spectralProj hζ hN hwN i i, if_pos rfl],
    star_spectralProj hζ hN hwN hw i⟩

end Star

end Dictionary

/-! ### The inverse dictionary: the unitary of an orthogonal family of projections -/

section Reconstruction

variable {A : Type*} [Ring A] [Algebra ℂ A]
variable {N : ℕ} {ζ : ℂ}

/-- The unitary `∑_j ζ^j r j` of a family `r` of projections (the paper's
`u = ∑_k e^{2ikπ/n} p_k`, line 149). -/
noncomputable def fourierUnitary (ζ : ℂ) (r : Fin N → A) : A :=
  ∑ j : Fin N, ζ ^ ((j : ℕ) : ℤ) • r j

variable {r : Fin N → A} (horth : ∀ j' j, r j' * r j = if j' = j then r j else 0)
include horth

theorem fourierUnitary_mul (j : Fin N) : fourierUnitary ζ r * r j = ζ ^ ((j : ℕ) : ℤ) • r j := by
  simp only [fourierUnitary, Finset.sum_mul, smul_mul_assoc, horth, smul_ite, smul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem mul_fourierUnitary (j : Fin N) : r j * fourierUnitary ζ r = ζ ^ ((j : ℕ) : ℤ) • r j := by
  simp only [fourierUnitary, Finset.mul_sum, mul_smul_comm, horth, smul_ite, smul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

variable (hζ : IsPrimitiveRoot ζ N) (hN : 0 < N) (hsum : ∑ j, r j = 1)
include hζ hN hsum

omit hsum in
theorem pow_fourierUnitary_mul (j : Fin N) (l : ℕ) :
    fourierUnitary ζ r ^ l * r j = ζ ^ (((j : ℕ) : ℤ) * (l : ℤ)) • r j :=
  pow_mul_eq_zpow_smul_of_mul_eq (hζ.ne_zero hN.ne') (fourierUnitary_mul horth j) l

/-- The powers of the reconstructed unitary: `(∑_j ζ^j r j)^l = ∑_j ζ^{jl} r j`. -/
theorem fourierUnitary_pow (l : ℕ) :
    fourierUnitary ζ r ^ l = ∑ j : Fin N, ζ ^ (((j : ℕ) : ℤ) * (l : ℤ)) • r j := by
  conv_lhs => rw [← mul_one (fourierUnitary ζ r ^ l), ← hsum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => pow_fourierUnitary_mul horth hζ hN j l

/-- The reconstructed unitary has order dividing `N`. -/
theorem fourierUnitary_pow_eq_one : fourierUnitary ζ r ^ N = 1 := by
  rw [fourierUnitary_pow horth hζ hN hsum, ← hsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [(hζ.zpow_eq_one_iff_dvd _).mpr (dvd_mul_left _ _), one_smul]

/-- The spectral projections of the reconstructed unitary are the original projections. -/
theorem spectralProj_fourierUnitary (j : Fin N) : spectralProj ζ N (fourierUnitary ζ r) j = r j := by
  calc spectralProj ζ N (fourierUnitary ζ r) j
      = spectralProj ζ N (fourierUnitary ζ r) j * ∑ j', r j' := by rw [hsum, mul_one]
    _ = ∑ j', if j' = j then r j' else 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j' _ => ?_
        refine (fourierCoeff_mul_of_eigen hζ hN
          (fun l => pow_fourierUnitary_mul horth hζ hN j' l) ((j : ℕ) : ℤ)).trans ?_
        by_cases h : j' = j
        · rw [if_pos ((natCast_dvd_sub_iff_fin j' j).mpr h), if_pos h]
        · rw [if_neg (fun h' => h ((natCast_dvd_sub_iff_fin j' j).mp h')), if_neg h]
    _ = r j := by rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ j)]

section Star

variable [StarRing A] [StarModule ℂ A] (hsa : ∀ j, star (r j) = r j)
include hsa

omit horth hsum in
theorem star_fourierUnitary :
    star (fourierUnitary ζ r) = ∑ j : Fin N, ζ ^ (-((j : ℕ) : ℤ)) • r j := by
  simp only [fourierUnitary, star_sum, star_smul, star_zpow_of_isPrimitiveRoot hζ hN, hsa]

theorem star_fourierUnitary_mul_self : star (fourierUnitary ζ r) * fourierUnitary ζ r = 1 := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN.ne'
  rw [star_fourierUnitary hζ hN hsa, Finset.sum_mul]
  simp only [smul_mul_assoc, mul_fourierUnitary horth, smul_smul, ← zpow_add₀ hζ0, neg_add_cancel,
    zpow_zero, one_smul]
  exact hsum

theorem fourierUnitary_mul_star_self : fourierUnitary ζ r * star (fourierUnitary ζ r) = 1 := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN.ne'
  rw [star_fourierUnitary hζ hN hsa, Finset.mul_sum]
  simp only [mul_smul_comm, fourierUnitary_mul horth, smul_smul, ← zpow_add₀ hζ0, neg_add_cancel,
    zpow_zero, one_smul]
  exact hsum

end Star

end Reconstruction

/-! ### Operators on `H`: PVMs, membership in `M`, and Parseval for `‖·‖_φ` -/

section Operators

/-- The projections of a PVM are pairwise orthogonal: `q j' * q j = δ_{j' j} q j`.
(From `q j = q j (∑ k, q k) q j = q j + ∑_{k ≠ j} (q k q j)* (q k q j)` and positivity.) -/
theorem IsPVM.mul_eq_ite {M : VonNeumannAlgebra H} {N : ℕ} {q : Fin N → H →L[ℂ] H}
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

theorem spectralProj_mem (M : VonNeumannAlgebra H) {w : H →L[ℂ] H} (hw : w ∈ M) (i : Fin N) :
    spectralProj ζ N w i ∈ M :=
  Blocks.smul_mem_vn M _ (sum_mem fun k _ => Blocks.smul_mem_vn M _ (pow_mem hw k))

theorem fourierUnitary_mem (M : VonNeumannAlgebra H) {r : Fin N → H →L[ℂ] H}
    (hr : ∀ j, r j ∈ M) : fourierUnitary ζ r ∈ M :=
  sum_mem fun j _ => Blocks.smul_mem_vn M _ (hr j)

/-- The spectral projections of a unitary `w ∈ M` of order `N` form a PVM in `M`. -/
theorem isPVM_spectralProj (M : VonNeumannAlgebra H) (hζ : IsPrimitiveRoot ζ N) (hN : 0 < N)
    {w : H →L[ℂ] H} (hw : w ∈ M) (hw1 : star w * w = 1) (hwN : w ^ N = 1) :
    IsPVM M (spectralProj ζ N w) :=
  ⟨fun i => spectralProj_mem M hw i, fun i => isStarProjection_spectralProj hζ hN hwN hw1 i,
    sum_spectralProj hζ hN⟩

/-- `‖-x‖_φ² = ‖x‖_φ²`. -/
theorem NormalState.normSq_neg {M : VonNeumannAlgebra H} (φ : NormalState M) (x : H →L[ℂ] H) :
    φ.normSq (-x) = φ.normSq x := by
  simp only [NormalState.normSq, star_neg, neg_mul_neg]

/-- **Parseval** for the seminorm `‖·‖_φ`: `∑_j ‖Y j‖_φ² = N⁻¹ ∑_{l<N} ‖d l‖_φ²` for the
Fourier coefficients `Y j = N⁻¹ ∑_{l<N} ζ^{-jl} d l` (only linearity of `φ` is used). -/
theorem sum_normSq_fourierCoeff {M : VonNeumannAlgebra H} (φ : NormalState M)
    (hζ : IsPrimitiveRoot ζ N) (hN : 0 < N) (d : ℕ → H →L[ℂ] H) :
    ∑ j : Fin N, φ.normSq (fourierCoeff ζ N d ((j : ℕ) : ℤ))
      = (N : ℝ)⁻¹ * ∑ l ∈ Finset.range N, φ.normSq (d l) := by
  simp only [NormalState.normSq]
  rw [← Complex.re_sum, ← map_sum, sum_star_mul_fourierCoeff hζ hN, map_smul, smul_eq_mul,
    ← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul, map_sum,
    Complex.re_sum]

/-- The hypothesis of Corollary 1.5 is the hypothesis of Theorem 1.4 for the spectral
PVMs: `∑_{i,j} ‖p_i q_j − q_j p_i‖_φ² = (nm)⁻¹ ∑_{k<n} ∑_{l<m} ‖u^{k+1} v^{l+1} − v^{l+1} u^{k+1}‖_φ²`. -/
theorem sum_normSq_spectralProj_comm {M : VonNeumannAlgebra H} (φ : NormalState M)
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
  simp only [sum_normSq_fourierCoeff φ hω hn]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [sum_normSq_fourierCoeff φ hζ hm]
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

/-! ### Corollary 1.5 in finite dimension -/

/-- **Corollary 1.5** (`cor:almost_commuting`) in finite dimension. -/
theorem almost_commuting_unitaries_finDim (M : VonNeumannAlgebra H) (φ : NormalState M)
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
  have hp : IsPVM M (spectralProj ω n u) := isPVM_spectralProj M hω hn hu hu1 hun
  have hq : IsPVM M (spectralProj ζ m v) := isPVM_spectralProj M hζ hm hv hv1 hvm
  -- the hypothesis of Theorem 1.4, with `q` in the perturbed (first) slot
  have hsum : ∑ j : Fin m, ∑ i : Fin n, φ.normSq (spectralProj ζ m v j * spectralProj ω n u i
      - spectralProj ω n u i * spectralProj ζ m v j) < ε := by
    calc ∑ j : Fin m, ∑ i : Fin n, φ.normSq (spectralProj ζ m v j * spectralProj ω n u i
            - spectralProj ω n u i * spectralProj ζ m v j)
        = ∑ i : Fin n, ∑ j : Fin m, φ.normSq (spectralProj ω n u i * spectralProj ζ m v j
            - spectralProj ζ m v j * spectralProj ω n u i) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [← NormalState.normSq_neg φ (spectralProj ω n u i * spectralProj ζ m v j - _),
            neg_sub]
      _ = ((n : ℝ) * m)⁻¹ * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m,
            φ.normSq (u ^ (i + 1) * v ^ (j + 1) - v ^ (j + 1) * u ^ (i + 1)) :=
          sum_normSq_spectralProj_comm φ hω hn hζ hm hun hvm
      _ < ε := h
  -- Theorem 1.4
  obtain ⟨q', hq', hcomm, hclose⟩ :=
    pvm_almost_commute_finDim M φ (spectralProj ζ m v) (spectralProj ω n u) hq hp ε hsum
  have horth : ∀ j' j, q' j' * q' j = if j' = j then q' j else 0 := hq'.mul_eq_ite
  have hsa : ∀ j, star (q' j) = q' j := fun j => (hq'.2.1 j).isSelfAdjoint.star_eq
  have hsum' : ∑ j, q' j = 1 := hq'.2.2
  -- the unitary `v' = ∑_j ζ^j q'_j`
  refine ⟨fourierUnitary ζ q', fourierUnitary_mem M hq'.1, ?_, ?_, ?_⟩
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
      exact sum_normSq_fourierCoeff φ hζ hm _
    have hshift : ∑ l ∈ Finset.range m, φ.normSq (v ^ (l + 1) - fourierUnitary ζ q' ^ (l + 1))
        = ∑ l ∈ Finset.range m, φ.normSq (v ^ l - fourierUnitary ζ q' ^ l) :=
      sum_range_succ_shift (fun l => φ.normSq (v ^ l - fourierUnitary ζ q' ^ l)) m
        (by simp only [pow_zero, hvm, fourierUnitary_pow_eq_one horth hζ hm hsum'])
    rw [hshift, ← hpars]
    exact hclose

end Orthogonalization
