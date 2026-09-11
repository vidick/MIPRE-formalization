/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/Modular/HaarSpectrum.lean
-/
/-
# The spectral measure of a Haar-distributed unitary (density stage E6.5b)

Let `E` be self-adjoint with `spectrum E ⊆ [0, 2π]`, so that `u := e^{iE}` is a unitary
with `E = −i Log u`, and let `ζ` be a vector for which the "moments" vanish,
`⟪ζ, e^{ikE} ζ⟫ = 0` for every nonzero integer `k` (HJX Lemma 2.2: this is what
`λ(2^{-n})` does to `Ω̂` in the crossed product, where `e^{ikE} = λ(k2^{-n})`).

The only consequence needed downstream is a **uniform tail estimate for the spectral
measure `ν = ν_{E,ζ}` near the branch cut**: for `0 < δ ≤ 1`,

    ν((δ, 2π−δ)ᶜ) ≤ 4 ‖ζ‖² δ ,

with a constant that does not depend on `E`. It follows from the Fejér majorant
`Q_N := 4(N+1)^{-2}|∑_{k≤N} e^{ikθ}|²`: this is a nonnegative trigonometric polynomial
which is `≥ 1` on `|θ| ≤ 1/N` (because `cos x ≥ 1 − x²/2 ≥ 1/2` there) and whose
`ν`-integral is `4‖ζ‖²/(N+1)` (because the vectors `e^{ikE}ζ` are orthonormal up to the
factor `‖ζ‖`).

Combined with `‖·‖`-approximation of the identity function by trigonometric polynomials
away from the cut, this gives `‖Eζ − P(u)ζ‖` small with `P` independent of `E`.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.Modular.CentralExp
import MIPRE.Background.Repetition.CommutingRepetition.VN.Modular.UnitaryLog

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace VN

namespace Modular

open scoped InnerProductSpace ComplexConjugate Real
open Filter Topology MeasureTheory BorelCalc

set_option linter.unusedSectionVars false

variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [CompleteSpace 𝓗]

/-! ## Finite sums in the complex Borel calculus -/

theorem cbdd_finset_sum {ι : Type*} (s : Finset ι) {G : ι → ℝ → ℂ} (hG : ∀ i, CBdd (G i)) :
    CBdd fun t => ∑ i ∈ s, G i t := by
  classical
  induction s using Finset.induction with
  | empty => simpa using CBdd.const (0 : ℂ)
  | insert a s ha ih =>
      have e : (fun t => ∑ i ∈ insert a s, G i t) = G a + fun t => ∑ i ∈ s, G i t := by
        funext t; rw [Finset.sum_insert ha]; rfl
      rw [e]; exact (hG a).add ih

theorem cbfc_finset_sum (E : 𝓗 →L[ℂ] 𝓗) (hE : IsSelfAdjoint E) {ι : Type*} (s : Finset ι)
    {G : ι → ℝ → ℂ} (hG : ∀ i, CBdd (G i)) :
    cbfc E hE (fun t => ∑ i ∈ s, G i t) = ∑ i ∈ s, cbfc E hE (G i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [cbfc_const E hE (0 : ℂ)]
  | insert a s ha ih =>
      have e : (fun t => ∑ i ∈ insert a s, G i t) = G a + fun t => ∑ i ∈ s, G i t := by
        funext t; rw [Finset.sum_insert ha]; rfl
      rw [e, cbfc_add E hE (hG a) (cbdd_finset_sum s hG), ih, Finset.sum_insert ha]

/-! ## The Dirichlet kernel and the Fejér majorant -/

/-- `D_N(θ) = ∑_{k ≤ N} e^{ikθ}`. -/
noncomputable def dirK (N : ℕ) (t : ℝ) : ℂ := ∑ k ∈ Finset.range (N + 1), eitf (k : ℝ) t

theorem cbdd_dirK (N : ℕ) : CBdd (dirK N) :=
  cbdd_finset_sum _ fun k => cbdd_eitf (k : ℝ)

theorem cbfc_dirK (E : 𝓗 →L[ℂ] 𝓗) (hE : IsSelfAdjoint E) (N : ℕ) :
    cbfc E hE (dirK N) = ∑ k ∈ Finset.range (N + 1), eit E hE (k : ℝ) :=
  cbfc_finset_sum E hE _ fun k => cbdd_eitf (k : ℝ)

theorem re_eitf (t l : ℝ) : (eitf t l).re = Real.cos (t * l) := by
  unfold eitf; exact Complex.exp_ofReal_mul_I_re _

/-- On `|t| ≤ 1/N` the Dirichlet kernel is at least `(N+1)/2`. -/
theorem norm_dirK_ge {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (ht : |t| ≤ 1 / N) :
    ((N : ℝ) + 1) / 2 ≤ ‖dirK N t‖ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hcos : ∀ k ∈ Finset.range (N + 1), (1 : ℝ) / 2 ≤ Real.cos ((k : ℝ) * t) := by
    intro k hk
    have hkN : (k : ℝ) ≤ N := by
      exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h1 : |(k : ℝ) * t| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
      calc (k : ℝ) * |t| ≤ (N : ℝ) * (1 / N) :=
            mul_le_mul hkN ht (abs_nonneg t) (Nat.cast_nonneg N)
        _ = 1 := by field_simp
    have h2 : ((k : ℝ) * t) ^ 2 ≤ 1 := by
      nlinarith [(abs_le.mp h1).1, (abs_le.mp h1).2]
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := (k : ℝ) * t)]
  have hre : ((N : ℝ) + 1) / 2 ≤ (dirK N t).re := by
    have e : (dirK N t).re = ∑ k ∈ Finset.range (N + 1), Real.cos ((k : ℝ) * t) := by
      rw [dirK, Complex.re_sum]
      exact Finset.sum_congr rfl fun k _ => re_eitf _ _
    rw [e]
    calc ((N : ℝ) + 1) / 2 = ∑ _k ∈ Finset.range (N + 1), (1 : ℝ) / 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
      _ ≤ _ := Finset.sum_le_sum hcos
  exact hre.trans (Complex.re_le_norm _)

/-- The Fejér majorant `Q_N = 4(N+1)^{-2}|D_N|²`. -/
noncomputable def fejerMaj (N : ℕ) (t : ℝ) : ℝ := 4 / ((N : ℝ) + 1) ^ 2 * ‖dirK N t‖ ^ 2

theorem bdd_fejerMaj (N : ℕ) : Bdd (fejerMaj N) := by
  have h := ((cbdd_dirK (N := N)).norm_sq).const_mul (4 / ((N : ℝ) + 1) ^ 2)
  exact h

theorem fejerMaj_nonneg (N : ℕ) (t : ℝ) : 0 ≤ fejerMaj N t := by
  unfold fejerMaj; positivity

theorem one_le_fejerMaj {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (ht : |t| ≤ 1 / N) :
    1 ≤ fejerMaj N t := by
  have h := norm_dirK_ge hN ht
  have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have h2 : (((N : ℝ) + 1) / 2) ^ 2 ≤ ‖dirK N t‖ ^ 2 :=
    pow_le_pow_left₀ (by positivity) h 2
  have key : 4 / ((N : ℝ) + 1) ^ 2 * (((N : ℝ) + 1) / 2) ^ 2 = 1 := by field_simp; ring
  rw [fejerMaj]
  calc (1 : ℝ) = 4 / ((N : ℝ) + 1) ^ 2 * (((N : ℝ) + 1) / 2) ^ 2 := key.symm
    _ ≤ 4 / ((N : ℝ) + 1) ^ 2 * ‖dirK N t‖ ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

theorem eitf_add_two_pi (k : ℕ) (t : ℝ) : eitf (k : ℝ) (t + 2 * π) = eitf (k : ℝ) t := by
  unfold eitf
  have e : (((k : ℝ) * (t + 2 * π) : ℝ) : ℂ) * Complex.I
      = (((k : ℝ) * t : ℝ) : ℂ) * Complex.I + (k : ℤ) * (2 * π * Complex.I) := by
    push_cast
    ring
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem dirK_add_two_pi (N : ℕ) (t : ℝ) : dirK N (t + 2 * π) = dirK N t :=
  Finset.sum_congr rfl fun k _ => eitf_add_two_pi k t

theorem fejerMaj_add_two_pi (N : ℕ) (t : ℝ) : fejerMaj N (t + 2 * π) = fejerMaj N t := by
  rw [fejerMaj, fejerMaj, dirK_add_two_pi]

/-! ## Haar-distributed vectors -/

section Haar

variable {E : 𝓗 →L[ℂ] 𝓗} (hE : IsSelfAdjoint E) (ζ : 𝓗)

/-- `ζ` is **Haar distributed** for `E`: the Fourier moments `⟪ζ, e^{ikE}ζ⟫` vanish for
every nonzero integer `k` (HJX Lemma 2.2). -/
def IsHaarVec : Prop := ∀ k : ℤ, k ≠ 0 → ⟪ζ, eit E hE (k : ℝ) ζ⟫_ℂ = 0

theorem inner_eit_eit (h : IsHaarVec hE ζ) (j k : ℤ) :
    ⟪eit E hE (j : ℝ) ζ, eit E hE (k : ℝ) ζ⟫_ℂ = if j = k then ⟪ζ, ζ⟫_ℂ else 0 := by
  have e : ⟪eit E hE (j : ℝ) ζ, eit E hE (k : ℝ) ζ⟫_ℂ
      = ⟪ζ, eit E hE ((k - j : ℤ) : ℝ) ζ⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
      eit_star hE, ← mul_apply_eq_comp, ← eit_add hE]
    congr 2
    push_cast
    ring
  rw [e]
  by_cases hjk : j = k
  · rw [if_pos hjk, hjk, sub_self]
    simp only [Int.cast_zero]
    rw [eit_zero hE, one_apply_eq_self]
  · rw [if_neg hjk]
    exact h _ (sub_ne_zero.mpr fun hh => hjk hh.symm)

theorem inner_eit_eit_nat (h : IsHaarVec hE ζ) (j k : ℕ) :
    ⟪eit E hE (j : ℝ) ζ, eit E hE (k : ℝ) ζ⟫_ℂ = if j = k then ⟪ζ, ζ⟫_ℂ else 0 := by
  have e1 : ((j : ℕ) : ℝ) = (((j : ℕ) : ℤ) : ℝ) := by push_cast; ring
  have e2 : ((k : ℕ) : ℝ) = (((k : ℕ) : ℤ) : ℝ) := by push_cast; ring
  rw [e1, e2, inner_eit_eit hE ζ h]
  by_cases hjk : j = k
  · rw [if_pos hjk, if_pos (by exact_mod_cast hjk)]
  · rw [if_neg hjk, if_neg (by exact_mod_cast hjk)]

theorem norm_sum_eit_sq (h : IsHaarVec hE ζ) (N : ℕ) :
    ‖(∑ k ∈ Finset.range (N + 1), eit E hE (k : ℝ)) ζ‖ ^ 2 = ((N : ℝ) + 1) * ‖ζ‖ ^ 2 := by
  have happ : (∑ k ∈ Finset.range (N + 1), eit E hE (k : ℝ)) ζ
      = ∑ k ∈ Finset.range (N + 1), eit E hE (k : ℝ) ζ := by
    simp
  set v := ∑ k ∈ Finset.range (N + 1), eit E hE (k : ℝ) ζ with hv
  have key : ⟪v, v⟫_ℂ = ((((N : ℝ) + 1 : ℝ)) : ℂ) * ⟪ζ, ζ⟫_ℂ := by
    calc ⟪v, v⟫_ℂ = ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
            ⟪eit E hE (j : ℝ) ζ, eit E hE (k : ℝ) ζ⟫_ℂ := by
          rw [hv, sum_inner]
          exact Finset.sum_congr rfl fun j _ => inner_sum _ _ _
      _ = ∑ _j ∈ Finset.range (N + 1), ⟪ζ, ζ⟫_ℂ := by
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [Finset.sum_congr rfl fun k _ => inner_eit_eit_nat hE ζ h j k,
            Finset.sum_ite_eq (Finset.range (N + 1)) j fun _ => ⟪ζ, ζ⟫_ℂ, if_pos hj]
      _ = ((((N : ℝ) + 1 : ℝ)) : ℂ) * ⟪ζ, ζ⟫_ℂ := by
          rw [Finset.sum_const, Finset.card_range]
          push_cast
          ring
  have hre := congrArg Complex.re key
  rw [Complex.re_ofReal_mul] at hre
  rw [happ, ← inner_self_eq_norm_sq (𝕜 := ℂ) v, ← inner_self_eq_norm_sq (𝕜 := ℂ) ζ]
  exact hre

theorem integral_fejerMaj (h : IsHaarVec hE ζ) (N : ℕ) :
    ∫ t, fejerMaj N t ∂(ν E hE ζ) = 4 * ‖ζ‖ ^ 2 / ((N : ℝ) + 1) := by
  have h1 : ∫ t, ‖dirK N t‖ ^ 2 ∂(ν E hE ζ) = ((N : ℝ) + 1) * ‖ζ‖ ^ 2 := by
    rw [← norm_sq_cbfc E hE (cbdd_dirK (N := N)) ζ, cbfc_dirK, norm_sum_eit_sq hE ζ h N]
  have h2 : ∫ t, fejerMaj N t ∂(ν E hE ζ)
      = 4 / ((N : ℝ) + 1) ^ 2 * ∫ t, ‖dirK N t‖ ^ 2 ∂(ν E hE ζ) := by
    rw [← integral_const_mul]
    rfl
  rw [h2, h1]
  have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  field_simp

/-- The spectral measure is concentrated on `[0, 2π]`. -/
theorem ν_compl_Icc (hspec : spectrum ℝ E ⊆ Set.Icc 0 (2 * π)) :
    ν E hE ζ (Set.Icc (0 : ℝ) (2 * π))ᶜ = 0 :=
  measure_mono_null (Set.compl_subset_compl.mpr hspec) (ν_compl_spectrum E hE ζ)

/-- **The uniform tail estimate** near the branch cut: `ν((δ, 2π−δ)ᶜ) ≤ 4‖ζ‖²δ`, with a
constant independent of `E`. -/
theorem measureReal_compl_Icc_le (h : IsHaarVec hE ζ)
    (hspec : spectrum ℝ E ⊆ Set.Icc 0 (2 * π)) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (ν E hE ζ).real (Set.Icc δ (2 * π - δ))ᶜ ≤ 4 * ‖ζ‖ ^ 2 * δ := by
  set N := ⌊1 / δ⌋₊ with hNdef
  have hinv : (1 : ℝ) ≤ 1 / δ := by rw [le_div_iff₀ hδ0]; linarith
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hinv)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hδN : δ ≤ 1 / N := by
    have h1 : (N : ℝ) ≤ 1 / δ := Nat.floor_le (le_trans zero_le_one hinv)
    rw [le_div_iff₀ hN0]
    rw [le_div_iff₀ hδ0] at h1
    linarith
  have hNδ : 4 * ‖ζ‖ ^ 2 / ((N : ℝ) + 1) ≤ 4 * ‖ζ‖ ^ 2 * δ := by
    have h1 : (1 : ℝ) / δ < (N : ℝ) + 1 := Nat.lt_floor_add_one (1 / δ)
    have h2 : (1 : ℝ) / ((N : ℝ) + 1) ≤ δ := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ hδ0] at h1
      linarith
    calc 4 * ‖ζ‖ ^ 2 / ((N : ℝ) + 1) = 4 * ‖ζ‖ ^ 2 * (1 / ((N : ℝ) + 1)) := by ring
      _ ≤ 4 * ‖ζ‖ ^ 2 * δ := by
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
  -- the a.e. pointwise majorization
  have hae : ∀ᵐ t ∂(ν E hE ζ),
      (Set.Icc δ (2 * π - δ))ᶜ.indicator (1 : ℝ → ℝ) t ≤ fejerMaj N t := by
    have hmem : ∀ᵐ t ∂(ν E hE ζ), t ∈ Set.Icc (0 : ℝ) (2 * π) :=
      MeasureTheory.mem_ae_iff.mpr (ν_compl_Icc hE ζ hspec)
    filter_upwards [hmem] with t ht
    by_cases hin : t ∈ Set.Icc δ (2 * π - δ)
    · rw [Set.indicator_of_notMem (by simpa using hin)]
      exact fejerMaj_nonneg N t
    · rw [Set.indicator_of_mem (Set.mem_compl hin), Pi.one_apply]
      simp only [Set.mem_Icc, not_and_or, not_le] at hin
      rcases hin with hlt | hgt
      · refine one_le_fejerMaj hN1 ?_
        rw [abs_of_nonneg ht.1]
        exact le_trans hlt.le hδN
      · have e := fejerMaj_add_two_pi N (t - 2 * π)
        rw [sub_add_cancel] at e
        rw [e]
        refine one_le_fejerMaj hN1 ?_
        rw [abs_of_nonpos (by linarith [ht.2])]
        have : 2 * π - t < δ := by linarith
        exact le_trans (by linarith) hδN
  calc (ν E hE ζ).real (Set.Icc δ (2 * π - δ))ᶜ
      = ∫ t, (Set.Icc δ (2 * π - δ))ᶜ.indicator (1 : ℝ → ℝ) t ∂(ν E hE ζ) :=
        (integral_indicator_one measurableSet_Icc.compl).symm
    _ ≤ ∫ t, fejerMaj N t ∂(ν E hE ζ) :=
        integral_mono_ae ((Bdd.indicator measurableSet_Icc.compl).integrable _)
          ((bdd_fejerMaj N).integrable _) hae
    _ = 4 * ‖ζ‖ ^ 2 / ((N : ℝ) + 1) := integral_fejerMaj hE ζ h N
    _ ≤ 4 * ‖ζ‖ ^ 2 * δ := hNδ

/-! ## From the tail estimate to an operator estimate -/

/-- `E ζ − G(E) ζ = (id − G)(E) ζ`, with `id` truncated to the spectrum. -/
theorem sub_cbfc_eq {E : 𝓗 →L[ℂ] 𝓗} (hE : IsSelfAdjoint E) (ζ : 𝓗) {G : ℝ → ℂ}
    (hG : CBdd G) :
    E ζ - cbfc E hE G ζ = cbfc E hE (fun t => ((trunc E t : ℝ) : ℂ) - G t) ζ := by
  have e1 : E ζ = cbfc E hE (fun t => ((trunc E t : ℝ) : ℂ)) ζ := by
    rw [cbfc_ofReal, bfc_trunc]
  have e2 : cbfc E hE (fun t => ((trunc E t : ℝ) : ℂ) - G t)
      = cbfc E hE (fun t => ((trunc E t : ℝ) : ℂ)) - cbfc E hE G :=
    cbfc_sub E hE (CBdd.ofReal (bdd_trunc E)) hG
  rw [e2, ContinuousLinearMap.sub_apply, e1]

/-- **The key `‖·‖`-estimate**: if the symbol `G` approximates the identity to `η` away from
the branch cut and to `B` everywhere, then `‖Eζ − G(E)ζ‖² ≤ η²‖ζ‖² + 4B²‖ζ‖²δ`. Both the
constants and `G` are independent of `E`. -/
theorem norm_sub_cbfc_le {E : 𝓗 →L[ℂ] 𝓗} (hE : IsSelfAdjoint E) (ζ : 𝓗) {G : ℝ → ℂ}
    (hG : CBdd G) (h : IsHaarVec hE ζ) (hspec : spectrum ℝ E ⊆ Set.Icc 0 (2 * π))
    {δ η B : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (h1 : ∀ t ∈ Set.Icc δ (2 * π - δ), ‖(t : ℂ) - G t‖ ≤ η)
    (h2 : ∀ t ∈ Set.Icc (0 : ℝ) (2 * π), ‖(t : ℂ) - G t‖ ≤ B) :
    ‖E ζ - cbfc E hE G ζ‖ ^ 2 ≤ η ^ 2 * ‖ζ‖ ^ 2 + B ^ 2 * (4 * ‖ζ‖ ^ 2 * δ) := by
  classical
  set S : Set ℝ := (Set.Icc δ (2 * π - δ))ᶜ with hSdef
  have hSm : MeasurableSet S := measurableSet_Icc.compl
  set Gd : ℝ → ℂ := fun t => ((trunc E t : ℝ) : ℂ) - G t with hGddef
  have hGd : CBdd Gd := (CBdd.ofReal (bdd_trunc E)).sub hG
  have hmajBdd : Bdd fun t => η ^ 2 + B ^ 2 * S.indicator (1 : ℝ → ℝ) t :=
    (Bdd.const _).add ((Bdd.indicator hSm).const_mul _)
  have hmem : ∀ᵐ t ∂(ν E hE ζ), t ∈ Set.Icc (0 : ℝ) (2 * π) :=
    MeasureTheory.mem_ae_iff.mpr (ν_compl_Icc hE ζ hspec)
  have hmaj : ∀ᵐ t ∂(ν E hE ζ),
      ‖Gd t‖ ^ 2 ≤ η ^ 2 + B ^ 2 * S.indicator (1 : ℝ → ℝ) t := by
    filter_upwards [ae_norm_le E hE ζ, hmem] with t ht htm
    have htr : trunc E t = t := trunc_of_mem E (Set.mem_Icc.mpr (abs_le.mp ht))
    have hGdt : Gd t = (t : ℂ) - G t := by
      show ((trunc E t : ℝ) : ℂ) - G t = (t : ℂ) - G t
      rw [htr]
    rw [hGdt]
    by_cases hin : t ∈ Set.Icc δ (2 * π - δ)
    · rw [Set.indicator_of_notMem (by simpa [hSdef] using hin), mul_zero, add_zero]
      nlinarith [h1 t hin, norm_nonneg ((t : ℂ) - G t)]
    · rw [Set.indicator_of_mem (by simpa [hSdef] using hin), Pi.one_apply, mul_one]
      nlinarith [h2 t htm, norm_nonneg ((t : ℂ) - G t), sq_nonneg η]
  rw [sub_cbfc_eq hE ζ hG, norm_sq_cbfc E hE hGd ζ]
  calc ∫ t, ‖Gd t‖ ^ 2 ∂(ν E hE ζ)
      ≤ ∫ t, (η ^ 2 + B ^ 2 * S.indicator (1 : ℝ → ℝ) t) ∂(ν E hE ζ) :=
        integral_mono_ae (hGd.norm_sq.integrable _) (hmajBdd.integrable _) hmaj
    _ = η ^ 2 * ‖ζ‖ ^ 2 + B ^ 2 * (ν E hE ζ).real S := by
        rw [integral_add (integrable_const _)
          (((Bdd.indicator hSm).const_mul _).integrable _), integral_const,
          integral_const_mul, integral_indicator_one hSm, ν_univ_real, smul_eq_mul, mul_comm]
    _ ≤ η ^ 2 * ‖ζ‖ ^ 2 + B ^ 2 * (4 * ‖ζ‖ ^ 2 * δ) := by
        have := measureReal_compl_Icc_le hE ζ h hspec hδ0 hδ1
        nlinarith [sq_nonneg B, this]

end Haar

/-! ## Trigonometric approximation of the identity away from the branch cut -/

section Trig

theorem cmap_sum_apply {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [AddCommMonoid Y] [ContinuousAdd Y] {ι : Type*} (s : Finset ι) (f : ι → C(X, Y)) (x : X) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ContinuousMap.add_apply, ih]

/-- The piecewise-linear sawtooth on `[0, 2π]`: it equals `t·2π/(2π−δ)` on `[0, 2π−δ]` and
drops linearly back to `0` on `[2π−δ, 2π]`, so it vanishes at both endpoints and is within
`δ` of the identity on `[0, 2π−δ]`. -/
noncomputable def ramp (δ t : ℝ) : ℝ :=
  min (t * (2 * π / (2 * π - δ))) ((2 * π - t) * (2 * π / δ))

theorem continuous_ramp (δ : ℝ) : Continuous (ramp δ) := by unfold ramp; fun_prop

section RampFacts

variable {δ : ℝ} (hδ0 : 0 < δ) (hδ2 : δ < 2 * π)

include hδ0 hδ2

theorem ramp_zero : ramp δ 0 = 0 := by
  have h : (0 : ℝ) ≤ (2 * π - 0) * (2 * π / δ) := by
    rw [sub_zero]
    have : (0 : ℝ) < π := Real.pi_pos
    positivity
  rw [ramp, zero_mul]
  exact min_eq_left h

theorem ramp_two_pi : ramp δ (2 * π) = 0 := by
  have hd : (0 : ℝ) < 2 * π - δ := by linarith
  have h : (0 : ℝ) ≤ 2 * π * (2 * π / (2 * π - δ)) :=
    mul_nonneg (by linarith [Real.pi_pos]) (le_of_lt (div_pos (by linarith [Real.pi_pos]) hd))
  rw [ramp, sub_self, zero_mul]
  exact min_eq_right h

theorem ramp_eq_of_le {t : ℝ} (ht : t ≤ 2 * π - δ) :
    ramp δ t = t * (2 * π / (2 * π - δ)) := by
  have hd : (0 : ℝ) < 2 * π - δ := by linarith
  refine min_eq_left ?_
  rw [← sub_nonneg]
  have e : (2 * π - t) * (2 * π / δ) - t * (2 * π / (2 * π - δ))
      = 2 * π * (2 * π * (2 * π - δ - t)) / (δ * (2 * π - δ)) := by
    field_simp
    ring
  rw [e]
  apply div_nonneg
  · have : (0 : ℝ) < π := Real.pi_pos
    have h2 : (0 : ℝ) ≤ 2 * π - δ - t := by linarith
    positivity
  · positivity

theorem abs_ramp_sub_le {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 2 * π - δ) :
    |ramp δ t - t| ≤ δ := by
  have hd : (0 : ℝ) < 2 * π - δ := by linarith
  rw [ramp_eq_of_le hδ0 hδ2 ht]
  have e : t * (2 * π / (2 * π - δ)) - t = t * δ / (2 * π - δ) := by
    field_simp
    ring
  rw [e, abs_of_nonneg (by positivity)]
  rw [div_le_iff₀ hd]
  nlinarith

theorem ramp_nonneg {t : ℝ} (ht0 : 0 ≤ t) (_ht : t ≤ 2 * π) : 0 ≤ ramp δ t := by
  have hd : (0 : ℝ) < 2 * π - δ := by linarith
  refine le_min ?_ ?_
  · positivity
  · have : (0 : ℝ) ≤ 2 * π - t := by linarith
    positivity

theorem ramp_le {t : ℝ} (_ht : t ≤ 2 * π) : ramp δ t ≤ 2 * π := by
  have hd : (0 : ℝ) < 2 * π - δ := by linarith
  by_cases hc : t ≤ 2 * π - δ
  · rw [ramp_eq_of_le hδ0 hδ2 hc, mul_div_assoc' , div_le_iff₀ hd]
    nlinarith [Real.pi_pos]
  · refine le_trans (min_le_right _ _) ?_
    rw [mul_div_assoc', div_le_iff₀ hδ0]
    nlinarith [Real.pi_pos, not_le.mp hc]

theorem abs_ramp_le {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 2 * π) : |ramp δ t| ≤ 2 * π :=
  abs_le.mpr ⟨by linarith [ramp_nonneg hδ0 hδ2 ht0 ht, Real.pi_pos],
    ramp_le hδ0 hδ2 ht⟩

end RampFacts

/-- A trigonometric polynomial as a symbol on `ℝ`. -/
noncomputable def trigSym (s : Finset ℤ) (c : ℤ → ℂ) (t : ℝ) : ℂ :=
  ∑ k ∈ s, c k * eitf (k : ℝ) t

theorem cbdd_trigSym (s : Finset ℤ) (c : ℤ → ℂ) : CBdd (trigSym s c) :=
  cbdd_finset_sum _ fun k => (cbdd_eitf (k : ℝ)).smul (c k)

theorem cbfc_trigSym {E : 𝓗 →L[ℂ] 𝓗} (hE : IsSelfAdjoint E) (s : Finset ℤ) (c : ℤ → ℂ) :
    cbfc E hE (trigSym s c) = ∑ k ∈ s, c k • eit E hE (k : ℝ) := by
  have e : cbfc E hE (trigSym s c) = ∑ k ∈ s, cbfc E hE (fun t => c k * eitf (k : ℝ) t) :=
    cbfc_finset_sum E hE _ fun k => (cbdd_eitf (k : ℝ)).smul (c k)
  rw [e]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e2 : cbfc E hE (fun t => c k * eitf (k : ℝ) t)
      = cbfc E hE (fun _ => c k) * cbfc E hE (eitf (k : ℝ)) :=
    cbfc_mul E hE (CBdd.const _) (cbdd_eitf _)
  rw [e2, cbfc_const, eit, smul_mul_assoc, one_mul]

theorem fourier_eq_eitf (k : ℤ) {t : ℝ} :
    (fourier k ((t : ℝ) : AddCircle (2 * π)) : ℂ) = eitf (k : ℝ) t := by
  rw [fourier_coe_apply, eitf]
  have hπ : ((π : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  congr 1
  push_cast
  field_simp

/-- **Trigonometric approximation of the identity** on `[δ, 2π−δ]`, with a global bound that
does not depend on the polynomial. -/
theorem exists_trigSym {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ (s : Finset ℤ) (c : ℤ → ℂ),
      (∀ t ∈ Set.Icc δ (2 * π - δ), ‖(t : ℂ) - trigSym s c t‖ ≤ 2 * δ) ∧
      (∀ t : ℝ, ‖trigSym s c t‖ ≤ 2 * π + 1) := by
  have hfact : Fact (0 < 2 * π) := ⟨by positivity⟩
  have hδ2 : δ < 2 * π := by nlinarith [Real.pi_gt_three]
  -- the continuous periodic sawtooth
  have hcont : Continuous (AddCircle.liftIco (2 * π) 0 (ramp δ)) :=
    AddCircle.liftIco_continuous (by rw [zero_add, ramp_zero hδ0 hδ2, ramp_two_pi hδ0 hδ2])
      (continuous_ramp δ).continuousOn
  set F : C(AddCircle (2 * π), ℂ) :=
    ⟨fun y => ((AddCircle.liftIco (2 * π) 0 (ramp δ) y : ℝ) : ℂ),
      Complex.continuous_ofReal.comp hcont⟩ with hFdef
  -- every point of the circle is represented in `[0, 2π)`
  have hrep : ∀ y : AddCircle (2 * π), ∃ t : ℝ, t ∈ Set.Ico (0 : ℝ) (2 * π) ∧
      ((t : ℝ) : AddCircle (2 * π)) = y := by
    intro y
    refine ⟨(AddCircle.equivIco (2 * π) 0 y : ℝ), ?_, AddCircle.coe_equivIco⟩
    simpa using (AddCircle.equivIco (2 * π) 0 y).2
  have hFval : ∀ t : ℝ, t ∈ Set.Ico (0 : ℝ) (2 * π) →
      F ((t : ℝ) : AddCircle (2 * π)) = ((ramp δ t : ℝ) : ℂ) := by
    intro t ht
    show ((AddCircle.liftIco (2 * π) 0 (ramp δ) ((t : ℝ) : AddCircle (2 * π)) : ℝ) : ℂ)
      = ((ramp δ t : ℝ) : ℂ)
    rw [AddCircle.liftIco_zero_coe_apply ht]
  have hFnorm : ∀ y : AddCircle (2 * π), ‖F y‖ ≤ 2 * π := by
    intro y
    obtain ⟨t, ht, rfl⟩ := hrep y
    rw [hFval t ht, Complex.norm_real, Real.norm_eq_abs]
    exact abs_ramp_le hδ0 hδ2 ht.1 ht.2.le
  -- Stone–Weierstrass on the circle
  have hclosure : F ∈ closure ((Submodule.span ℂ (Set.range (@fourier (2 * π)))) :
      Set C(AddCircle (2 * π), ℂ)) := by
    have h := span_fourier_closure_eq_top (T := 2 * π)
    have : F ∈ (Submodule.span ℂ (Set.range (@fourier (2 * π)))).topologicalClosure := by
      rw [h]; exact Submodule.mem_top
    exact this
  obtain ⟨P, hPmem, hPdist⟩ := Metric.mem_closure_iff.mp hclosure δ hδ0
  obtain ⟨cf, hcf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hPmem
  refine ⟨cf.support, fun k => cf k, ?_, ?_⟩
  · intro t ht
    have htI := Set.mem_Icc.mp ht
    have ht' : t ∈ Set.Ico (0 : ℝ) (2 * π) :=
      Set.mem_Ico.mpr ⟨by linarith [htI.1], by linarith [htI.2]⟩
    have hPt : P ((t : ℝ) : AddCircle (2 * π)) = trigSym cf.support (fun k => cf k) t := by
      rw [← hcf, Finsupp.sum, cmap_sum_apply, trigSym]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [ContinuousMap.smul_apply, smul_eq_mul, fourier_eq_eitf]
    have h1 : ‖(t : ℂ) - ((ramp δ t : ℝ) : ℂ)‖ ≤ δ := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
      exact abs_ramp_sub_le hδ0 hδ2 (Set.mem_Ico.mp ht').1 htI.2
    have h2 : ‖((ramp δ t : ℝ) : ℂ) - trigSym cf.support (fun k => cf k) t‖ ≤ δ := by
      rw [← hFval t ht', ← hPt]
      have hd : dist (F ((t : ℝ) : AddCircle (2 * π))) (P ((t : ℝ) : AddCircle (2 * π)))
          ≤ dist F P := ContinuousMap.dist_apply_le_dist _
      rw [dist_eq_norm] at hd
      exact hd.trans hPdist.le
    calc ‖(t : ℂ) - trigSym cf.support (fun k => cf k) t‖
        = ‖((t : ℂ) - ((ramp δ t : ℝ) : ℂ))
            + (((ramp δ t : ℝ) : ℂ) - trigSym cf.support (fun k => cf k) t)‖ := by
          rw [sub_add_sub_cancel]
      _ ≤ ‖(t : ℂ) - ((ramp δ t : ℝ) : ℂ)‖
          + ‖((ramp δ t : ℝ) : ℂ) - trigSym cf.support (fun k => cf k) t‖ := norm_add_le _ _
      _ ≤ 2 * δ := by linarith
  · intro t
    have hPt : P ((t : ℝ) : AddCircle (2 * π)) = trigSym cf.support (fun k => cf k) t := by
      rw [← hcf, Finsupp.sum, cmap_sum_apply, trigSym]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [ContinuousMap.smul_apply, smul_eq_mul, fourier_eq_eitf]
    rw [← hPt]
    have hb : ‖P ((t : ℝ) : AddCircle (2 * π)) - F ((t : ℝ) : AddCircle (2 * π))‖ ≤ δ := by
      have hd : dist (F ((t : ℝ) : AddCircle (2 * π))) (P ((t : ℝ) : AddCircle (2 * π)))
          ≤ dist F P := ContinuousMap.dist_apply_le_dist _
      rw [dist_eq_norm] at hd
      rw [norm_sub_rev]
      exact hd.trans hPdist.le
    calc ‖P ((t : ℝ) : AddCircle (2 * π))‖
        = ‖(P ((t : ℝ) : AddCircle (2 * π)) - F ((t : ℝ) : AddCircle (2 * π)))
            + F ((t : ℝ) : AddCircle (2 * π))‖ := by rw [sub_add_cancel]
      _ ≤ ‖P ((t : ℝ) : AddCircle (2 * π)) - F ((t : ℝ) : AddCircle (2 * π))‖
          + ‖F ((t : ℝ) : AddCircle (2 * π))‖ := norm_add_le _ _
      _ ≤ δ + 2 * π := add_le_add hb (hFnorm _)
      _ ≤ 2 * π + 1 := by linarith

/-- **Uniform trigonometric approximation of a Haar-distributed self-adjoint operator**
(HJX Lemma 2.6(i)'s analytic input). Given a bound `r` on `‖ζ‖` and an `ε > 0`, *one* fixed
trigonometric polynomial `∑_{k∈s} c k z^k` satisfies `‖Eζ − ∑_{k∈s} c k e^{ikE} ζ‖ ≤ ε`
simultaneously for every Haar pair `(E, ζ)`. -/
theorem exists_trig_uniform {r : ℝ} (_hr : 0 ≤ r) {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Finset ℤ) (c : ℤ → ℂ), ∀ (E : 𝓗 →L[ℂ] 𝓗) (hE : IsSelfAdjoint E) (ζ : 𝓗),
      IsHaarVec hE ζ → spectrum ℝ E ⊆ Set.Icc 0 (2 * π) → ‖ζ‖ ≤ r →
      ‖E ζ - (∑ k ∈ s, c k • eit E hE (k : ℝ)) ζ‖ ≤ ε := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  set B : ℝ := 4 * π + 1 with hBdef
  have hB0 : (0 : ℝ) < B := by rw [hBdef]; positivity
  set δ : ℝ := min 1 (ε ^ 2 / (4 * (r ^ 2 + 1) * (1 + B ^ 2))) with hδdef
  have hden : (0 : ℝ) < 4 * (r ^ 2 + 1) * (1 + B ^ 2) := by positivity
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ ε ^ 2 / (4 * (r ^ 2 + 1) * (1 + B ^ 2)) := min_le_right _ _
  obtain ⟨s, c, h1, h2⟩ := exists_trigSym hδ0 hδ1
  refine ⟨s, c, fun E hE ζ hhaar hspec hζ => ?_⟩
  have hζ2 : ‖ζ‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hζ 2
  have hglob : ∀ t ∈ Set.Icc (0 : ℝ) (2 * π), ‖(t : ℂ) - trigSym s c t‖ ≤ B := by
    intro t ht
    have htI := Set.mem_Icc.mp ht
    have hn1 : ‖(t : ℂ)‖ ≤ 2 * π := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg htI.1]
      exact htI.2
    calc ‖(t : ℂ) - trigSym s c t‖ ≤ ‖(t : ℂ)‖ + ‖trigSym s c t‖ := norm_sub_le _ _
      _ ≤ 2 * π + (2 * π + 1) := add_le_add hn1 (h2 t)
      _ = B := by rw [hBdef]; ring
  have hkey := norm_sub_cbfc_le hE ζ (cbdd_trigSym s c) hhaar hspec hδ0 hδ1 h1 hglob
  rw [cbfc_trigSym hE s c] at hkey
  have hfin : ‖E ζ - (∑ k ∈ s, c k • eit E hE (k : ℝ)) ζ‖ ^ 2 ≤ ε ^ 2 := by
    refine hkey.trans ?_
    have hz : (0 : ℝ) ≤ ‖ζ‖ ^ 2 := sq_nonneg _
    have hδB : (0 : ℝ) ≤ δ + B ^ 2 := by linarith [hδ0.le, sq_nonneg B]
    have hstep : (2 * δ) ^ 2 * ‖ζ‖ ^ 2 + B ^ 2 * (4 * ‖ζ‖ ^ 2 * δ)
        ≤ 4 * δ * (r ^ 2 + 1) * (1 + B ^ 2) := by
      have e : (2 * δ) ^ 2 * ‖ζ‖ ^ 2 + B ^ 2 * (4 * ‖ζ‖ ^ 2 * δ)
          = 4 * δ * ‖ζ‖ ^ 2 * (δ + B ^ 2) := by ring
      have hmul : ‖ζ‖ ^ 2 * (δ + B ^ 2) ≤ (r ^ 2 + 1) * (1 + B ^ 2) :=
        mul_le_mul (by linarith) (by linarith) hδB (by positivity)
      rw [e]
      calc 4 * δ * ‖ζ‖ ^ 2 * (δ + B ^ 2) = 4 * δ * (‖ζ‖ ^ 2 * (δ + B ^ 2)) := by ring
        _ ≤ 4 * δ * ((r ^ 2 + 1) * (1 + B ^ 2)) :=
            mul_le_mul_of_nonneg_left hmul (by linarith [hδ0.le])
        _ = 4 * δ * (r ^ 2 + 1) * (1 + B ^ 2) := by ring
    refine hstep.trans ?_
    rw [le_div_iff₀ hden] at hδ2
    calc 4 * δ * (r ^ 2 + 1) * (1 + B ^ 2) = δ * (4 * (r ^ 2 + 1) * (1 + B ^ 2)) := by ring
      _ ≤ ε ^ 2 := hδ2
  have h0 : 0 ≤ ‖E ζ - (∑ k ∈ s, c k • eit E hE (k : ℝ)) ζ‖ := norm_nonneg _
  nlinarith [hfin, h0, hε]

end Trig

/-! ## The unitary group as a strong limit of its exponential partial sums -/

section ExpSeries

theorem cbdd_trunc_pow (E : 𝓗 →L[ℂ] 𝓗) (k : ℕ) :
    CBdd fun l => ((trunc E l : ℝ) : ℂ) ^ k := by
  induction k with
  | zero => simpa using CBdd.one
  | succ k ih =>
      have e : (fun l => ((trunc E l : ℝ) : ℂ) ^ (k + 1))
          = (fun l => ((trunc E l : ℝ) : ℂ) ^ k) * fun l => ((trunc E l : ℝ) : ℂ) := by
        funext l; rw [pow_succ]; rfl
      rw [e]
      exact ih.mul (CBdd.ofReal (bdd_trunc E))

theorem cbfc_trunc_pow {E : 𝓗 →L[ℂ] 𝓗} (hE : IsSelfAdjoint E) (k : ℕ) :
    cbfc E hE (fun l => ((trunc E l : ℝ) : ℂ) ^ k) = E ^ k := by
  induction k with
  | zero => simpa using cbfc_one E hE
  | succ k ih =>
      have e : (fun l => ((trunc E l : ℝ) : ℂ) ^ (k + 1))
          = (fun l => ((trunc E l : ℝ) : ℂ) ^ k) * fun l => ((trunc E l : ℝ) : ℂ) := by
        funext l; rw [pow_succ]; rfl
      rw [e, cbfc_mul E hE (cbdd_trunc_pow E k) (CBdd.ofReal (bdd_trunc E)), ih,
        cbfc_ofReal, bfc_trunc, pow_succ]

/-- The coefficients of the exponential series. -/
noncomputable def expCoef (t : ℝ) (k : ℕ) : ℂ :=
  (Complex.I * (t : ℂ)) ^ k / (Nat.factorial k : ℂ)

theorem expCoef_zero (t : ℝ) : expCoef t 0 = 1 := by norm_num [expCoef]

theorem norm_expCoef (t : ℝ) (k : ℕ) :
    ‖expCoef t k‖ = |t| ^ k / (Nat.factorial k : ℝ) := by
  rw [expCoef, norm_div, norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_natCast]

/-- The partial sums of the exponential series `∑_{k<N} (it)^k E^k / k!`. -/
noncomputable def expPoly (E : 𝓗 →L[ℂ] 𝓗) (t : ℝ) (N : ℕ) : 𝓗 →L[ℂ] 𝓗 :=
  ∑ k ∈ Finset.range N, expCoef t k • E ^ k

theorem expPoly_zero (E : 𝓗 →L[ℂ] 𝓗) (t : ℝ) : expPoly E t 0 = 0 := by
  rw [expPoly, Finset.range_zero, Finset.sum_empty]

theorem expPoly_succ (E : 𝓗 →L[ℂ] 𝓗) (t : ℝ) (N : ℕ) :
    expPoly E t (N + 1)
      = (∑ i ∈ Finset.range N, expCoef t (i + 1) • E ^ (i + 1)) + 1 := by
  rw [expPoly, Finset.sum_range_succ', pow_zero, expCoef_zero, one_smul]

/-- The `N`-th partial sum of the symbol `e^{itl}`, with `l` truncated to the spectrum. -/
noncomputable def expSym (E : 𝓗 →L[ℂ] 𝓗) (t : ℝ) (N : ℕ) (l : ℝ) : ℂ :=
  ∑ k ∈ Finset.range N, (Complex.I * (t : ℂ) * ((trunc E l : ℝ) : ℂ)) ^ k / (Nat.factorial k : ℂ)

theorem cbdd_expSym (E : 𝓗 →L[ℂ] 𝓗) (t : ℝ) (N : ℕ) : CBdd (expSym E t N) := by
  refine cbdd_finset_sum _ fun k => ?_
  have e : (fun l => (Complex.I * (t : ℂ) * ((trunc E l : ℝ) : ℂ)) ^ k / (Nat.factorial k : ℂ))
      = fun l => ((Complex.I * (t : ℂ)) ^ k / (Nat.factorial k : ℂ)) * ((trunc E l : ℝ) : ℂ) ^ k := by
    funext l; rw [mul_pow]; ring
  rw [e]
  exact (cbdd_trunc_pow E k).smul _

theorem cbfc_expSym {E : 𝓗 →L[ℂ] 𝓗} (hE : IsSelfAdjoint E) (t : ℝ) (N : ℕ) :
    cbfc E hE (expSym E t N) = expPoly E t N := by
  rw [expPoly]
  simp only [expCoef]
  have e : expSym E t N
      = fun l => ∑ k ∈ Finset.range N,
          ((Complex.I * (t : ℂ)) ^ k / (Nat.factorial k : ℂ)) * ((trunc E l : ℝ) : ℂ) ^ k := by
    funext l
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_pow]; ring
  rw [e, cbfc_finset_sum E hE _ fun k => (cbdd_trunc_pow E k).smul _]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e2 : (fun l => (Complex.I * (t : ℂ)) ^ k / (Nat.factorial k : ℂ)
        * ((trunc E l : ℝ) : ℂ) ^ k)
      = (fun _ : ℝ => (Complex.I * (t : ℂ)) ^ k / (Nat.factorial k : ℂ))
        * fun l => ((trunc E l : ℝ) : ℂ) ^ k := rfl
  rw [e2, cbfc_mul E hE (CBdd.const _) (cbdd_trunc_pow E k), cbfc_const, cbfc_trunc_pow,
    smul_mul_assoc, one_mul]

theorem norm_expSym_le (E : 𝓗 →L[ℂ] 𝓗) (t : ℝ) (N : ℕ) (l : ℝ) :
    ‖expSym E t N l‖ ≤ Real.exp (|t| * ‖E‖) := by
  set z : ℂ := Complex.I * (t : ℂ) * ((trunc E l : ℝ) : ℂ) with hz
  have habs : |trunc E l| ≤ ‖E‖ := by
    rw [trunc, abs_le]
    exact ⟨le_max_left _ _,
      max_le (by linarith [norm_nonneg E]) (min_le_right _ _)⟩
  have hzn : ‖z‖ ≤ |t| * ‖E‖ := by
    rw [hz, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left habs (abs_nonneg t)
  calc ‖expSym E t N l‖ ≤ ∑ k ∈ Finset.range N, ‖z ^ k / (Nat.factorial k : ℂ)‖ := norm_sum_le _ _
    _ = ∑ k ∈ Finset.range N, ‖z‖ ^ k / (Nat.factorial k : ℝ) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [norm_div, norm_pow, Complex.norm_natCast]
    _ ≤ Real.exp ‖z‖ := Real.sum_le_exp_of_nonneg (norm_nonneg z) N
    _ ≤ Real.exp (|t| * ‖E‖) := Real.exp_le_exp.mpr hzn

theorem tendsto_expSym (E : 𝓗 →L[ℂ] 𝓗) (t : ℝ) (l : ℝ) :
    Tendsto (fun N => expSym E t N l) atTop (𝓝 (eitf t (trunc E l))) := by
  set z : ℂ := Complex.I * (t : ℂ) * ((trunc E l : ℝ) : ℂ) with hz
  have hsum : HasSum (fun n : ℕ => z ^ n / (Nat.factorial n : ℂ)) (Complex.exp z) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp z
  have he : Complex.exp z = eitf t (trunc E l) := by
    rw [eitf, hz]
    congr 1
    push_cast
    ring
  rw [← he]
  exact hsum.tendsto_sum_nat

/-- **The unitary group is the strong limit of the exponential partial sums**:
`∑_{k<N} (it)^k E^k / k! ζ → e^{itE} ζ`. -/
theorem tendsto_expPoly_apply {E : 𝓗 →L[ℂ] 𝓗} (hE : IsSelfAdjoint E) (t : ℝ) (ζ : 𝓗) :
    Tendsto (fun N => expPoly E t N ζ) atTop (𝓝 (eit E hE t ζ)) := by
  have hC : ∀ l : ℝ, ‖eitf t (trunc E l)‖ ≤ Real.exp (|t| * ‖E‖) := fun l => by
    rw [norm_eitf]
    exact Real.one_le_exp (by positivity)
  have h := tendsto_cbfc E hE (G := fun N => expSym E t N)
    (Ginf := fun l => eitf t (trunc E l)) (l := atTop)
    (fun N => cbdd_expSym E t N) (cbdd_eitf_trunc E t)
    (C := Real.exp (|t| * ‖E‖)) (fun N l => norm_expSym_le E t N l) hC
    (fun l => tendsto_expSym E t l) ζ
  rw [cbfc_comp_trunc hE (cbdd_eitf t) (continuous_eitf t)] at h
  simp only [cbfc_expSym hE t] at h
  exact h

end ExpSeries

end Modular

end VN

end CommutingRepetition
