/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/MvN/Local.lean
-/
/-
# Tier T3, proof-side vocabulary: Theorem 1.2 at `z` for normal functionals

`OrthAtN M z ι` is Theorem 1.2 for the corner `z M z` (as `OrthAt`) restricted
to functionals *normal* on `M` — the class the general proof needs (the
semifinite reduction and Lemma 3.1 consume normality). This file collects the
closure properties of that class, the gluing for it, the weighted triangle
inequality `‖x + y‖² ≤ (1 + s)‖x‖² + (1 + s⁻¹)‖y‖²` for functionals positive
on `M` (which replaces Cauchy–Schwarz in the limiting arguments), and
Lemma 4.1 of the paper in the form "`φ` of bounded strongly convergent nets of
`M` converges" (`TendstoStrongBdd` and `IsNormalOn`). Proof-side only.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.Normal
import MIPRE.Background.Orthonormalization.Orthogonalization.Basic
import MIPRE.Background.Orthonormalization.Orthogonalization.Blocks.Glue
import MIPRE.Background.Orthonormalization.Orthogonalization.Blocks.StateOnM
import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.Defs

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace Orthogonalization.MvN

open scoped BigOperators ComplexOrder
open Filter Topology CommutingRepetition.VN Blocks

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Theorem 1.2 at `z` for the functionals normal on `M`. -/
abbrev OrthAtN (M : VonNeumannAlgebra H) (z : H →L[ℂ] H) (ι : Type*) [Fintype ι] : Prop :=
  OrthAtP M z ι (IsNormalOn M)

theorem IsNormalOn.smul {M : VonNeumannAlgebra H} {φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ}
    (h : IsNormalOn M φ) (c : ℂ) : IsNormalOn M (c • φ) := by
  intro κ l T L hT hL hTL
  have := h l T L hT hL hTL
  simp only [LinearMap.smul_apply, smul_eq_mul]
  exact this.const_mul c

theorem NormalState.isNormalOn {M : VonNeumannAlgebra H} (φ : NormalState M) :
    IsNormalOn M φ.toLinearMap :=
  fun l T L hT hL hTL => φ.normal' l T L hT hL hTL

/-- **Gluing** for normal functionals (`Blocks/Glue.lean`). -/
theorem orthAtN_one_of_blocks (M : VonNeumannAlgebra H) {κ : Type*} [Fintype κ]
    (z : κ → H →L[ℂ] H) (hz : ∀ j, IsCentralProj M (z j))
    (hzo : ∀ j k, j ≠ k → z j * z k = 0) (hzs : ∑ j, z j = 1)
    (ι : Type*) [Fintype ι] (h : ∀ j, OrthAtN M (z j) ι) : OrthAtN M 1 ι :=
  orthAtP_one_of_blocks M z hz hzo hzs ι (IsNormalOn M) (fun _ hφ _ _ => hφ.smul _) h

/-! ### The weighted triangle inequality for functionals positive on `M` -/

/-- `φ(|x + y|²) ≤ (1 + s) φ(|x|²) + (1 + s⁻¹) φ(|y|²)` for `x, y ∈ M`, `s > 0`, and
`φ` positive on `M`: from `0 ≤ φ(|s x − y|²)`. -/
theorem re_map_star_add_mul_add_le {M : VonNeumannAlgebra H} {φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ}
    (hφ : ∀ x ∈ M, 0 ≤ φ (star x * x)) {x y : H →L[ℂ] H} (hx : x ∈ M) (hy : y ∈ M)
    {s : ℝ} (hs : 0 < s) :
    (φ (star (x + y) * (x + y))).re ≤
      (1 + s) * (φ (star x * x)).re + (1 + s⁻¹) * (φ (star y * y)).re := by
  have hmem : (s : ℂ) • x - y ∈ M := sub_mem (smul_mem_vn M _ hx) hy
  have h0 := hφ _ hmem
  have hstar : star ((s : ℂ) • x - y) = (s : ℂ) • star x - star y := by
    rw [star_sub, star_smul, Complex.star_def, Complex.conj_ofReal]
  set A := (φ (star x * x)).re
  set B := (φ (star x * y)).re
  set C := (φ (star y * x)).re
  set D := (φ (star y * y)).re
  have hexp : (φ (star ((s : ℂ) • x - y) * ((s : ℂ) • x - y))).re
      = s * s * A - s * (B + C) + D := by
    rw [hstar]
    have : ((s : ℂ) • star x - star y) * ((s : ℂ) • x - y)
        = (s : ℂ) • ((s : ℂ) • (star x * x)) - (s : ℂ) • (star x * y)
          - (s : ℂ) • (star y * x) + star y * y := by
      simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_sub]
      abel
    rw [this, map_add, map_sub, map_sub, map_smul, map_smul, map_smul, map_smul,
      smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, Complex.add_re, Complex.sub_re,
      Complex.sub_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
      Complex.re_ofReal_mul]
    ring
  have hpos : 0 ≤ s * s * A - s * (B + C) + D := by
    rw [← hexp]
    exact (Complex.nonneg_iff.mp h0).1
  have hsum : (φ (star (x + y) * (x + y))).re = A + B + C + D := by
    have : star (x + y) * (x + y) = star x * x + star x * y + star y * x + star y * y := by
      rw [star_add]
      noncomm_ring
    rw [this, map_add, map_add, map_add, Complex.add_re, Complex.add_re, Complex.add_re]
  rw [hsum]
  have hkey : B + C ≤ s * A + s⁻¹ * D := by
    have h1 : 0 ≤ s⁻¹ * (s * s * A - s * (B + C) + D) := mul_nonneg (inv_nonneg.mpr hs.le) hpos
    have h2 : s⁻¹ * (s * s * A - s * (B + C) + D) = s * A - (B + C) + s⁻¹ * D := by
      field_simp
    linarith
  linarith

/-- The tuple form of the weighted triangle inequality. -/
theorem sum_re_map_star_add_mul_add_le {M : VonNeumannAlgebra H} {φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ}
    (hφ : ∀ x ∈ M, 0 ≤ φ (star x * x)) {ι : Type*} [Fintype ι] {x y : ι → H →L[ℂ] H}
    (hx : ∀ i, x i ∈ M) (hy : ∀ i, y i ∈ M) {s : ℝ} (hs : 0 < s) :
    (φ (∑ i, star (x i + y i) * (x i + y i))).re ≤
      (1 + s) * (φ (∑ i, star (x i) * x i)).re + (1 + s⁻¹) * (φ (∑ i, star (y i) * y i)).re := by
  rw [map_sum, map_sum, map_sum, Complex.re_sum, Complex.re_sum, Complex.re_sum,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => re_map_star_add_mul_add_le hφ (hx i) (hy i) hs

/-! ### Lemma 4.1: normal functionals along bounded strongly convergent nets -/

theorem IsNormalOn.tendsto_re {M : VonNeumannAlgebra H} {φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ}
    (hφ : IsNormalOn M φ) {κ : Type u} {l : Filter κ} {T : κ → H →L[ℂ] H} {L : H →L[ℂ] H}
    (hT : ∀ k, T k ∈ M) (hL : L ∈ M) (h : TendstoStrongBdd l T L) :
    Tendsto (fun k => (φ (T k)).re) l (𝓝 (φ L).re) :=
  (Complex.continuous_re.tendsto _).comp (hφ l T L hT hL h)

end Orthogonalization.MvN

namespace CommutingRepetition.VN.TendstoStrongBdd

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {κ : Type*} {l : Filter κ}

theorem sub {T S : κ → H →L[ℂ] H} {L L' : H →L[ℂ] H} (h : TendstoStrongBdd l T L)
    (h' : TendstoStrongBdd l S L') : TendstoStrongBdd l (fun i => T i - S i) (L - L') := by
  have := h.add (h'.smul (-1))
  simp only [neg_one_smul] at this
  simpa [sub_eq_add_neg] using this

theorem finset_sum {γ : Type*} (s : Finset γ) {T : γ → κ → H →L[ℂ] H} {L : γ → H →L[ℂ] H}
    (h : ∀ j ∈ s, TendstoStrongBdd l (T j) (L j)) :
    TendstoStrongBdd l (fun i => ∑ j ∈ s, T j i) (∑ j ∈ s, L j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using TendstoStrongBdd.const (l := l) (0 : H →L[ℂ] H)
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact (h j (Finset.mem_insert_self j s)).add (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

end CommutingRepetition.VN.TendstoStrongBdd
