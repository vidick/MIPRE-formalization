/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/Haagerup/Density.lean
-/
/-
# Haagerup's reduction: density of `⋃ ℛ_n` (density stage E6.5)

`Φ_n(x) → x` in `‖·‖_{ψ̂}` for every `x ∈ ℛ`, hence `⋃_n ℛ_n` is `‖·‖_{ψ̂}`-dense
in `ℛ`. Following HJX §2 (`manuscript/external/HJX0806.3635v2/hjx.tex`), the
chain is

    ‖(Φ_n x − x)Ω̂‖ ≤ sup_t ‖σ^{ξ_n}_t(x) − x‖_{ψ̂}
                    = sup_t ‖σ̂_t(x) − e^{ita_n} x e^{−ita_n}‖_{ψ̂}
                    ≤ sup_{|s|≤2^{−n}} ‖σ̂_s(x) − x‖_{ψ̂}
                      + sup_{|s|≤1} ‖[e^{isb_n}, x]‖_{ψ̂} ,

and the last term is controlled by `e^{2π}‖[b_n, x]‖_{ψ̂}`, which tends to `0`
because `b_n = −i Log λ(2^{−n})` is Haar distributed and `Log ∈ L²(𝕋)`.

This file starts with the `‖·‖_{ψ̂}`-toolkit (stage E6.5a), which is about a
general pair `(M, Ω)`: conjugation by a unitary of the centralizer is
`‖·‖_ψ`-isometric, a self-adjoint central element acts on `Ω` through the
commutant (HJX Lemma 2.5(ii)), and left-bounded elements give the commutator
estimate `‖[y, x]‖_ψ ≤ (√c + ‖x‖)‖y‖_ψ`. The `‖·‖_ψ`-dense supply of
left-bounded elements is the Gaussian smearing of E4.5 (`re_inner_xk_le`),
which replaces HJX's analytic elements.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.Haagerup.Reduction
import MIPRE.Background.Repetition.CommutingRepetition.VN.Modular.HaarSpectrum

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace VN

namespace Haagerup

open scoped InnerProductSpace ComplexConjugate Real
open Filter Topology MeasureTheory BorelCalc ClosedSubmodule
open CommutingRepetition.VN.Modular CommutingRepetition.VN.Crossed

set_option linter.unusedSectionVars false

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ## The `‖·‖_ψ` toolkit -/

section CentralNorm

variable (M : VonNeumannAlgebra K) (Ω : K)
variable (hs : IsSeparating (M : Set (K →L[ℂ] K)) Ω) (hc : IsCyclic (M : Set (K →L[ℂ] K)) Ω)

theorem norm_apply_Ω_sq (y : K →L[ℂ] K) : ‖y Ω‖ ^ 2 = (⟪Ω, (star y * y) Ω⟫_ℂ).re :=
  (Resolver.Douglas.re_inner_star_mul y Ω).symm

/-- The trivial half: `‖x y Ω‖ ≤ ‖x‖ ‖y Ω‖`. -/
theorem norm_mul_apply_Ω_le (x y : K →L[ℂ] K) : ‖(x * y) Ω‖ ≤ ‖x‖ * ‖y Ω‖ := by
  rw [mul_apply_eq_comp]; exact x.le_opNorm _

theorem norm_eq_of_sq_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 = b ^ 2) : a = b := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]

include hs hc in
/-- **A self-adjoint central element acts on `Ω` through the commutant**: `w Ω = (J w J) Ω`
for `w ∈ M` self-adjoint and commuting with `R`. -/
theorem conjJm_apply_Ω_of_isCentral {w : K →L[ℂ] K} (hw : IsCentral M Ω w)
    (hwsa : IsSelfAdjoint w) : conjJm M Ω w Ω = w Ω := by
  rw [conjJm_apply, Jm_Ω M Ω hs hc]
  refine Jm_eq_self_of_R_eq M Ω hs hc (mem_Kre_of_sa M Ω hw.1 hwsa) ?_
  rw [← mul_apply_eq_comp, ← hw.2.eq, mul_apply_eq_comp, R_Ω]

include hs hc in
/-- **HJX Lemma 2.5(ii)**: `‖y w Ω‖ ≤ ‖w‖ ‖y Ω‖` for `w` self-adjoint in the centralizer. -/
theorem norm_mul_right_apply_Ω_le {w y : K →L[ℂ] K} (hw : IsCentral M Ω w)
    (hwsa : IsSelfAdjoint w) (hy : y ∈ M) : ‖(y * w) Ω‖ ≤ ‖w‖ * ‖y Ω‖ := by
  have hc' : conjJm M Ω w ∈ M.commutant := conjJm_mem_commutant M Ω hs hc hw.1
  have hcΩ : conjJm M Ω w Ω = w Ω := conjJm_apply_Ω_of_isCentral M Ω hs hc hw hwsa
  have h : (y * w) Ω = conjJm M Ω w (y Ω) :=
    calc (y * w) Ω = y (w Ω) := mul_apply_eq_comp _ _ _
      _ = y (conjJm M Ω w Ω) := by rw [hcΩ]
      _ = (y * conjJm M Ω w) Ω := (mul_apply_eq_comp _ _ _).symm
      _ = (conjJm M Ω w * y) Ω := by
          rw [VonNeumannAlgebra.mem_commutant_iff.mp hc' y hy]
      _ = conjJm M Ω w (y Ω) := mul_apply_eq_comp _ _ _
  rw [h]
  exact ((conjJm M Ω w).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (norm_conjJm_le M Ω hs hc w) (norm_nonneg _))

include hs hc in
/-- **Conjugation by a unitary of the centralizer is `‖·‖_ψ`-isometric.** -/
theorem norm_conj_unitary_apply_Ω {u y : K →L[ℂ] K} (hu : IsCentral M Ω u)
    (hu1 : star u * u = 1) (hy : y ∈ M) : ‖(u * y * star u) Ω‖ = ‖y Ω‖ := by
  have hstar : star (u * y * star u) = u * star y * star u := by
    rw [star_mul, star_mul, star_star, mul_assoc]
  have e : star (u * y * star u) * (u * y * star u) = u * (star y * y * star u) := by
    rw [hstar]
    calc u * star y * star u * (u * y * star u)
        = u * star y * (star u * u) * (y * star u) := by simp only [mul_assoc]
      _ = u * (star y * y * star u) := by rw [hu1, mul_one]; simp only [mul_assoc]
  have e2 : star y * y * star u * u = star y * y := by rw [mul_assoc, hu1, mul_one]
  have h1 := IsCentral.tracial hs hc hu
    (mul_mem (mul_mem (star_mem hy) hy) (star_mem hu.1))
  refine norm_eq_of_sq_eq (norm_nonneg _) (norm_nonneg _) ?_
  rw [norm_apply_Ω_sq, norm_apply_Ω_sq, e, h1, e2]

include hs hc in
/-- **Multiplying on the right by a unitary of the centralizer is `‖·‖_ψ`-isometric.** -/
theorem norm_mul_unitary_apply_Ω {u y : K →L[ℂ] K} (hu : IsCentral M Ω u)
    (hu2 : u * star u = 1) (hy : y ∈ M) : ‖(y * u) Ω‖ = ‖y Ω‖ := by
  have e : star (y * u) * (y * u) = star u * (star y * y * u) := by
    rw [star_mul]; simp only [mul_assoc]
  have e2 : star y * y * u * star u = star y * y := by rw [mul_assoc, hu2, mul_one]
  have h1 := IsCentral.tracial hs hc hu.star (mul_mem (mul_mem (star_mem hy) hy) hu.1)
  refine norm_eq_of_sq_eq (norm_nonneg _) (norm_nonneg _) ?_
  rw [norm_apply_Ω_sq, norm_apply_Ω_sq, e, h1, e2]

include hs hc in
/-- `‖[w, y]Ω‖ ≤ 2‖w‖‖yΩ‖` for `w` self-adjoint in the centralizer. -/
theorem norm_commutator_central_le {w y : K →L[ℂ] K} (hw : IsCentral M Ω w)
    (hwsa : IsSelfAdjoint w) (hy : y ∈ M) :
    ‖(w * y - y * w) Ω‖ ≤ 2 * ‖w‖ * ‖y Ω‖ := by
  calc ‖(w * y - y * w) Ω‖ ≤ ‖(w * y) Ω‖ + ‖(y * w) Ω‖ := by
        rw [_root_.sub_apply]; exact norm_sub_le _ _
    _ ≤ ‖w‖ * ‖y Ω‖ + ‖w‖ * ‖y Ω‖ :=
        add_le_add (norm_mul_apply_Ω_le Ω w y)
          (norm_mul_right_apply_Ω_le M Ω hs hc hw hwsa hy)
    _ = 2 * ‖w‖ * ‖y Ω‖ := by ring

theorem isCentral_pow {w : K →L[ℂ] K} (hw : IsCentral M Ω w) (k : ℕ) :
    IsCentral M Ω (w ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact IsCentral.one
  | succ k ih => rw [pow_succ]; exact ih.mul hw

include hs hc in
/-- `‖[w^{k+1}, y]Ω‖ ≤ (k+1)‖w‖^k‖[w,y]Ω‖` for `w` self-adjoint in the centralizer. -/
theorem norm_commutator_pow_le {w y : K →L[ℂ] K} (hw : IsCentral M Ω w)
    (hwsa : IsSelfAdjoint w) (hy : y ∈ M) (k : ℕ) :
    ‖(w ^ (k + 1) * y - y * w ^ (k + 1)) Ω‖
      ≤ ((k : ℝ) + 1) * ‖w‖ ^ k * ‖(w * y - y * w) Ω‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hid : w ^ (k + 1 + 1) * y - y * w ^ (k + 1 + 1)
          = w * (w ^ (k + 1) * y - y * w ^ (k + 1)) + (w * y - y * w) * w ^ (k + 1) := by
        have e1 : w ^ (k + 1 + 1) = w * w ^ (k + 1) := by rw [← pow_succ']
        rw [e1]
        simp only [mul_sub, sub_mul, mul_assoc]
        abel
      have hnp : ‖w ^ (k + 1)‖ ≤ ‖w‖ ^ (k + 1) := norm_pow_le' w (Nat.succ_pos k)
      have hstep : ‖(w ^ (k + 1 + 1) * y - y * w ^ (k + 1 + 1)) Ω‖
          ≤ ‖w‖ * (((k : ℝ) + 1) * ‖w‖ ^ k * ‖(w * y - y * w) Ω‖)
            + ‖w‖ ^ (k + 1) * ‖(w * y - y * w) Ω‖ := by
        calc ‖(w ^ (k + 1 + 1) * y - y * w ^ (k + 1 + 1)) Ω‖
            = ‖(w * (w ^ (k + 1) * y - y * w ^ (k + 1))) Ω
                + ((w * y - y * w) * w ^ (k + 1)) Ω‖ := by
              rw [hid, _root_.add_apply]
          _ ≤ ‖(w * (w ^ (k + 1) * y - y * w ^ (k + 1))) Ω‖
              + ‖((w * y - y * w) * w ^ (k + 1)) Ω‖ := norm_add_le _ _
          _ ≤ ‖w‖ * ‖(w ^ (k + 1) * y - y * w ^ (k + 1)) Ω‖
              + ‖w‖ ^ (k + 1) * ‖(w * y - y * w) Ω‖ := by
              refine add_le_add (norm_mul_apply_Ω_le Ω _ _) ?_
              refine le_trans (norm_mul_right_apply_Ω_le M Ω hs hc
                (isCentral_pow M Ω hw (k + 1)) (hwsa.pow (k + 1))
                (sub_mem (mul_mem hw.1 hy) (mul_mem hy hw.1))) ?_
              exact mul_le_mul_of_nonneg_right hnp (norm_nonneg _)
          _ ≤ ‖w‖ * (((k : ℝ) + 1) * ‖w‖ ^ k * ‖(w * y - y * w) Ω‖)
              + ‖w‖ ^ (k + 1) * ‖(w * y - y * w) Ω‖ :=
              add_le_add (mul_le_mul_of_nonneg_left ih (norm_nonneg w)) le_rfl
      refine hstep.trans (le_of_eq ?_)
      push_cast
      rw [pow_succ]
      ring

include hs hc in
/-- **HJX Lemma 2.6(ii)**: `‖[e^{itw}, y]Ω‖ ≤ |t| e^{|t|‖w‖}‖[w,y]Ω‖`. -/
theorem norm_commutator_eit_le {w y : K →L[ℂ] K} (hw : IsCentral M Ω w)
    (hwsa : IsSelfAdjoint w) (hy : y ∈ M) (t : ℝ) :
    ‖(eit w hwsa t * y - y * eit w hwsa t) Ω‖
      ≤ |t| * Real.exp (|t| * ‖w‖) * ‖(w * y - y * w) Ω‖ := by
  have hbound : ∀ N : ℕ,
      ‖(expPoly w t N * y - y * expPoly w t N) Ω‖
        ≤ |t| * Real.exp (|t| * ‖w‖) * ‖(w * y - y * w) Ω‖ := by
    intro N
    cases N with
    | zero =>
        rw [expPoly_zero]
        simp only [zero_mul, mul_zero, sub_zero, ContinuousLinearMap.zero_apply, norm_zero]
        positivity
    | succ Np =>
        have hsplit : expPoly w t (Np + 1) * y - y * expPoly w t (Np + 1)
            = ∑ i ∈ Finset.range Np,
                expCoef t (i + 1) • (w ^ (i + 1) * y - y * w ^ (i + 1)) := by
          have key : ∀ i : ℕ, expCoef t (i + 1) • (w ^ (i + 1) * y - y * w ^ (i + 1))
              = expCoef t (i + 1) • w ^ (i + 1) * y - y * (expCoef t (i + 1) • w ^ (i + 1)) :=
            fun i => by rw [smul_sub, smul_mul_assoc, mul_smul_comm]
          rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.range Np) => key i,
            Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum, expPoly_succ,
            add_mul, mul_add, one_mul, mul_one]
          abel
        rw [hsplit, ContinuousLinearMap.sum_apply]
        refine (norm_sum_le _ _).trans ?_
        have hterm : ∀ i ∈ Finset.range Np,
            ‖(expCoef t (i + 1) • (w ^ (i + 1) * y - y * w ^ (i + 1))) Ω‖
              ≤ |t| * ‖(w * y - y * w) Ω‖ * ((|t| * ‖w‖) ^ i / (Nat.factorial i : ℝ)) := by
          intro i _
          rw [ContinuousLinearMap.smul_apply, norm_smul, norm_expCoef]
          have h1 := norm_commutator_pow_le M Ω hs hc hw hwsa hy i
          have h2 : |t| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)
                * ‖(w ^ (i + 1) * y - y * w ^ (i + 1)) Ω‖
              ≤ |t| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)
                * (((i : ℝ) + 1) * ‖w‖ ^ i * ‖(w * y - y * w) Ω‖) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
          refine h2.trans (le_of_eq ?_)
          rw [Nat.factorial_succ]
          have hfac : (0 : ℝ) < (Nat.factorial i : ℝ) := by positivity
          push_cast
          field_simp
          ring
        refine (Finset.sum_le_sum hterm).trans ?_
        rw [← Finset.mul_sum]
        calc |t| * ‖(w * y - y * w) Ω‖
              * ∑ i ∈ Finset.range Np, (|t| * ‖w‖) ^ i / (Nat.factorial i : ℝ)
            ≤ |t| * ‖(w * y - y * w) Ω‖ * Real.exp (|t| * ‖w‖) :=
              mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg (by positivity) Np)
                (by positivity)
          _ = |t| * Real.exp (|t| * ‖w‖) * ‖(w * y - y * w) Ω‖ := by ring
  have h1 := Modular.tendsto_expPoly_apply hwsa t (y Ω)
  have h2 : Tendsto (fun N : ℕ => y (expPoly w t N Ω)) atTop (𝓝 (y (eit w hwsa t Ω))) :=
    (y.continuous.tendsto _).comp (Modular.tendsto_expPoly_apply hwsa t Ω)
  have h3 : Tendsto (fun N : ℕ => ‖(expPoly w t N * y - y * expPoly w t N) Ω‖) atTop
      (𝓝 ‖(eit w hwsa t * y - y * eit w hwsa t) Ω‖) := by
    have h4 : Tendsto (fun N : ℕ => (expPoly w t N * y - y * expPoly w t N) Ω) atTop
        (𝓝 ((eit w hwsa t * y - y * eit w hwsa t) Ω)) := by
      simp only [_root_.sub_apply, mul_apply_eq_comp]
      exact h1.sub h2
    exact h4.norm
  exact le_of_tendsto h3 (Eventually.of_forall hbound)

/-! ### Left-bounded elements -/

/-- `x` is **left bounded** with constant `c`: `ψ(x* y x) ≤ c ψ(y)` for `0 ≤ y ∈ M`
(HJX Lemma 2.5). -/
def LeftBounded (x : K →L[ℂ] K) (c : ℝ) : Prop :=
  ∀ y : K →L[ℂ] K, y ∈ M → 0 ≤ y → (⟪Ω, (star x * y * x) Ω⟫_ℂ).re ≤ c * (⟪Ω, y Ω⟫_ℂ).re

/-- `‖y x Ω‖ ≤ √c ‖y Ω‖` for a left-bounded `x`. -/
theorem norm_mul_apply_Ω_le_of_leftBounded {x : K →L[ℂ] K} {c : ℝ} (hc0 : 0 ≤ c)
    (hx : LeftBounded M Ω x c) {y : K →L[ℂ] K} (hy : y ∈ M) :
    ‖(y * x) Ω‖ ≤ Real.sqrt c * ‖y Ω‖ := by
  have h := hx (star y * y) (mul_mem (star_mem hy) hy) (star_mul_self_nonneg y)
  have e : star x * (star y * y) * x = star (y * x) * (y * x) := by
    rw [star_mul]; simp only [mul_assoc]
  rw [e, ← norm_apply_Ω_sq, ← norm_apply_Ω_sq] at h
  have hB : 0 ≤ Real.sqrt c * ‖y Ω‖ := mul_nonneg (Real.sqrt_nonneg c) (norm_nonneg _)
  have h2 : ‖(y * x) Ω‖ ^ 2 ≤ (Real.sqrt c * ‖y Ω‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hc0]; exact h
  calc ‖(y * x) Ω‖ = Real.sqrt (‖(y * x) Ω‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((Real.sqrt c * ‖y Ω‖) ^ 2) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt c * ‖y Ω‖ := Real.sqrt_sq hB

/-- **The commutator estimate**: `‖[y, x] Ω‖ ≤ (√c + ‖x‖) ‖y Ω‖` for a left-bounded `x`. -/
theorem norm_commutator_apply_Ω_le {x : K →L[ℂ] K} {c : ℝ} (hc0 : 0 ≤ c)
    (hx : LeftBounded M Ω x c) {y : K →L[ℂ] K} (hy : y ∈ M) :
    ‖(y * x - x * y) Ω‖ ≤ (Real.sqrt c + ‖x‖) * ‖y Ω‖ := by
  calc ‖(y * x - x * y) Ω‖ ≤ ‖(y * x) Ω‖ + ‖(x * y) Ω‖ := by
        rw [_root_.sub_apply]; exact norm_sub_le _ _
    _ ≤ Real.sqrt c * ‖y Ω‖ + ‖x‖ * ‖y Ω‖ :=
        add_le_add (norm_mul_apply_Ω_le_of_leftBounded M Ω hc0 hx hy)
          (norm_mul_apply_Ω_le Ω x y)
    _ = (Real.sqrt c + ‖x‖) * ‖y Ω‖ := by ring

include hs hc in
/-- The Gaussian-smeared elements are left bounded (E4.5, HJX Lemma 2.5(i)). -/
theorem leftBounded_xk {k : ℝ} (hk : 0 < k) {x : K →L[ℂ] K} (hx : x ∈ M) :
    LeftBounded M Ω (xk M Ω k hk x) (‖xkFlat M Ω k hk x‖ ^ 2) :=
  fun _ hy hy0 => re_inner_xk_le M Ω hs hc hk hx hy hy0

end CentralNorm

/-! ## The bounded logarithms `b_n = 2^{-n} a_n` -/

theorem norm_ulog_le {u : K →L[ℂ] K} (hu1 : star u * u = 1) (hu2 : u * star u = 1) :
    ‖ulog u hu1 hu2‖ ≤ 2 * π :=
  norm_jbfc_le _ _ _ _ _ bdd2_logSym fun p =>
    abs_le.mpr ⟨by linarith [logSym_nonneg p, Real.pi_pos], logSym_le p⟩

theorem spectrum_ulog {u : K →L[ℂ] K} (hu1 : star u * u = 1) (hu2 : u * star u = 1) :
    spectrum ℝ (ulog u hu1 hu2) ⊆ Set.Icc 0 (2 * π) := fun _ hl =>
  ⟨spectrum_nonneg_of_nonneg (ulog_nonneg u hu1 hu2) hl,
    (abs_le.mp (abs_le_of_mem_spectrum hl)).2.trans (norm_ulog_le hu1 hu2)⟩

section Bn

variable (M : VonNeumannAlgebra K) (Ω : K)
variable (hs : IsSeparating (M : Set (K →L[ℂ] K)) Ω) (hc : IsCyclic (M : Set (K →L[ℂ] K)) Ω)

/-- `b_n = −i Log λ(2^{-n})`, so that `a_n = 2^n b_n`. -/
noncomputable def bn (n : ℕ) : L2Q K →L[ℂ] L2Q K :=
  ulog (un (K := K) n) (star_un_mul n) (un_mul_star n)

theorem isSelfAdjoint_bn (n : ℕ) : IsSelfAdjoint (bn (K := K) n) :=
  isSelfAdjoint_ulog _ _ _

theorem norm_bn_le (n : ℕ) : ‖bn (K := K) n‖ ≤ 2 * π := norm_ulog_le _ _

theorem spectrum_bn (n : ℕ) : spectrum ℝ (bn (K := K) n) ⊆ Set.Icc 0 (2 * π) :=
  spectrum_ulog _ _

theorem bn_mem (n : ℕ) : bn (K := K) n ∈ crossed M Ω :=
  ulog_mem _ _ _ (un_mem M Ω n)

theorem commute_bn_amp (n : ℕ) (y : K →L[ℂ] K) : Commute (bn (K := K) n) (amp y) :=
  commute_ulog _ _ _ (commute_un_amp n y) (commute_star_un_amp n y)

include hs hc in
theorem commute_bn_R (n : ℕ) :
    Commute (bn (K := K) n) (R (crossed M Ω) (Ωh Ω)) := by
  rw [R_crossed M Ω hs hc]
  exact commute_bn_amp n _

include hs hc in
theorem isCentral_bn (n : ℕ) : IsCentral (crossed M Ω) (Ωh Ω) (bn (K := K) n) :=
  ⟨bn_mem M Ω n, commute_bn_R M Ω hs hc n⟩

/-- `e^{ikb_n} = λ(k2^{-n})` for every integer `k`. -/
theorem eit_bn_int (n : ℕ) (k : ℤ) :
    eit (bn (K := K) n) (isSelfAdjoint_bn n) ((k : ℤ) : ℝ) = shift ((k : ℚ) * qn n) := by
  have hnat : ∀ m : ℕ, eit (bn (K := K) n) (isSelfAdjoint_bn n) ((m : ℕ) : ℝ)
      = shift ((m : ℚ) * qn n) := by
    intro m
    induction m with
    | zero =>
        simp only [Nat.cast_zero, zero_mul]
        rw [eit_zero, shift_zero]
    | succ m ih =>
        have e : (((m + 1 : ℕ) : ℝ)) = ((m : ℕ) : ℝ) + 1 := by push_cast; ring
        rw [e, eit_add, ih]
        have e2 : eit (bn (K := K) n) (isSelfAdjoint_bn n) 1 = shift (qn n) :=
          eit_ulog _ _ _
        rw [e2, ← shift_add]
        congr 1
        push_cast
        ring
  rcases le_total 0 k with hk | hk
  · lift k to ℕ using hk with m
    simpa using hnat m
  · have hk' : 0 ≤ -k := by omega
    lift (-k) to ℕ using hk' with m hm
    have h1 := hnat m
    have e : ((k : ℤ) : ℝ) = -(((m : ℕ) : ℝ)) := by
      have h2 : ((m : ℕ) : ℝ) = -((k : ℤ) : ℝ) := by
        exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hm
      linarith
    rw [e, ← eit_star, h1, shift_star]
    congr 1
    have : ((m : ℕ) : ℚ) = -(k : ℚ) := by exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) hm
    rw [this]
    ring

include hs hc in
/-- **HJX Lemma 2.2 in this model**: `Ω̂` is Haar distributed for `b_n`, because the vectors
`λ(k2^{-n})Ω̂ = δ_{k2^{-n}} ⊗ Ω` are pairwise orthogonal. -/
theorem isHaarVec_bn (n : ℕ) :
    IsHaarVec (isSelfAdjoint_bn (K := K) n) (Ωh Ω) := by
  intro k hk
  rw [eit_bn_int, Ωh, shift_sgl, inner_sgl_sgl, if_neg]
  intro hcon
  have hq : (0 : ℚ) = (k : ℚ) * qn n := by
    have := hcon
    linarith [this]
  rcases mul_eq_zero.mp hq.symm with h | h
  · exact hk (by exact_mod_cast h)
  · exact absurd h (ne_of_gt (qn_pos n))

/-! ## HJX Lemma 2.6(i): `‖[b_n, x]Ω̂‖ → 0` -/

include hs hc in
/-- `‖[λ(q), x]Ω̂‖ = ‖xΩ̂ − Δ̂^{-iq}(xΩ̂)‖`, because `λ(q)` is unitary and
`λ(-q)xλ(q) = σ̂_{-q}(x)`. -/
theorem norm_commutator_shift (q : ℚ) {x : L2Q K →L[ℂ] L2Q K} (hx : x ∈ crossed M Ω) :
    ‖(shift (K := K) q * x - x * shift (K := K) q) (Ωh Ω)‖
      = ‖x (Ωh Ω) - Δit (crossed M Ω) (Ωh Ω) (((-q : ℚ) : ℝ)) (x (Ωh Ω))‖ := by
  have hσ := σ_crossed_rat M Ω hs hc (-q) hx
  have hfac : shift (K := K) q * x - x * shift (K := K) q
      = shift (K := K) q * (x - σ (crossed M Ω) (Ωh Ω) (((-q : ℚ) : ℝ)) x) := by
    rw [hσ, mul_sub]
    congr 1
    rw [neg_neg]
    calc x * shift (K := K) q = shift (K := K) q * shift (K := K) (-q) * x * shift (K := K) q := by
          rw [shift_mul_neg, one_mul]
      _ = shift (K := K) q * (shift (K := K) (-q) * x * shift (K := K) q) := by simp only [mul_assoc]
  rw [hfac, mul_apply_eq_comp, norm_shift_apply, _root_.sub_apply, σ_apply_Ω]

theorem tendsto_qn_mul (k : ℤ) :
    Tendsto (fun n : ℕ => ((-((k : ℚ) * qn n) : ℚ) : ℝ)) atTop (𝓝 0) := by
  have hbase : Tendsto (fun n : ℕ => ((1 : ℝ) / 2 ^ n)) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa [one_div, inv_pow] using h
  have e : ∀ n : ℕ, ((-((k : ℚ) * qn n) : ℚ) : ℝ) = -(k : ℝ) * ((1 : ℝ) / 2 ^ n) := by
    intro n
    rw [Rat.cast_neg, Rat.cast_mul, qn_cast, Rat.cast_intCast]
    ring
  simp only [e]
  simpa using hbase.const_mul (-(k : ℝ))

include hs hc in
theorem tendsto_commutator_shift {x : L2Q K →L[ℂ] L2Q K} (hx : x ∈ crossed M Ω) (k : ℤ) :
    Tendsto (fun n : ℕ =>
        ‖(shift (K := K) ((k : ℚ) * qn n) * x
            - x * shift (K := K) ((k : ℚ) * qn n)) (Ωh Ω)‖) atTop (𝓝 0) := by
  have hcont : Continuous fun t : ℝ => Δit (crossed M Ω) (Ωh Ω) t (x (Ωh Ω)) :=
    continuous_Δit_comp (crossed M Ω) (Ωh Ω) continuous_const
  have h1 : Tendsto (fun n : ℕ =>
      Δit (crossed M Ω) (Ωh Ω) ((-((k : ℚ) * qn n) : ℚ) : ℝ) (x (Ωh Ω))) atTop
      (𝓝 (x (Ωh Ω))) := by
    have h := (hcont.tendsto 0).comp (tendsto_qn_mul k)
    rwa [Δit_zero, one_apply_eq_self] at h
  have h2 : Tendsto (fun n : ℕ => x (Ωh Ω)
      - Δit (crossed M Ω) (Ωh Ω) ((-((k : ℚ) * qn n) : ℚ) : ℝ) (x (Ωh Ω))) atTop (𝓝 0) := by
    have := h1.const_sub (x (Ωh Ω))
    rwa [sub_self] at this
  have e : ∀ n : ℕ, ‖(shift (K := K) ((k : ℚ) * qn n) * x
        - x * shift (K := K) ((k : ℚ) * qn n)) (Ωh Ω)‖
      = ‖x (Ωh Ω) - Δit (crossed M Ω) (Ωh Ω) ((-((k : ℚ) * qn n) : ℚ) : ℝ) (x (Ωh Ω))‖ :=
    fun n => norm_commutator_shift M Ω hs hc _ hx
  simp only [e]
  exact (tendsto_zero_iff_norm_tendsto_zero.mp h2)

include hs hc in
/-- **HJX Lemma 2.6(i)**: `‖[b_n, x] Ω̂‖ → 0` for every `x ∈ ℛ`. -/
theorem tendsto_commutator_bn {x : L2Q K →L[ℂ] L2Q K} (hx : x ∈ crossed M Ω) :
    Tendsto (fun n : ℕ => ‖(bn (K := K) n * x - x * bn (K := K) n) (Ωh Ω)‖) atTop (𝓝 0) := by
  have hsΩ := isSeparating_Ωh M Ω hs hc
  have hcΩ := isCyclic_Ωh M Ω hc
  have hπ : (0 : ℝ) < π := Real.pi_pos
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  -- (1) replace `x` by a Gaussian-smeared, left-bounded approximant `x₀`
  obtain ⟨m, hm⟩ := Metric.tendsto_atTop.mp
    (tendsto_xk_apply_Ω (crossed M Ω) (Ωh Ω) x) (ε / (3 * (4 * π + 1))) (by positivity)
  set x₀ := xk (crossed M Ω) (Ωh Ω) ((m : ℝ) + 1) (Nat.cast_add_one_pos m) x with hx₀def
  have hx₀ : x₀ ∈ crossed M Ω := xk_mem (crossed M Ω) (Ωh Ω) hsΩ hcΩ _ hx
  have hd : ‖x₀ (Ωh Ω) - x (Ωh Ω)‖ < ε / (3 * (4 * π + 1)) := by
    have := hm m le_rfl
    rwa [dist_eq_norm] at this
  set c₀ := ‖xkFlat (crossed M Ω) (Ωh Ω) ((m : ℝ) + 1) (Nat.cast_add_one_pos m) x‖ ^ 2 with hc₀def
  have hc₀ : 0 ≤ c₀ := sq_nonneg _
  have hlb : LeftBounded (crossed M Ω) (Ωh Ω) x₀ c₀ :=
    leftBounded_xk (crossed M Ω) (Ωh Ω) hsΩ hcΩ _ hx
  set L := Real.sqrt c₀ + ‖x₀‖ with hLdef
  have hL : 0 ≤ L := by positivity
  -- (2) one trigonometric polynomial for all `n`
  obtain ⟨sset, cf, htrig⟩ := Modular.exists_trig_uniform (𝓗 := L2Q K)
    (r := ‖Ωh Ω‖) (norm_nonneg _) (ε := ε / (3 * (L + 1))) (by positivity)
  set Pn : ℕ → L2Q K →L[ℂ] L2Q K :=
    fun n => ∑ k ∈ sset, cf k • eit (bn (K := K) n) (isSelfAdjoint_bn n) ((k : ℤ) : ℝ) with hPndef
  have hPmem : ∀ n, Pn n ∈ crossed M Ω := fun n =>
    sum_mem fun k _ => VN.smul_mem_vn _ _
      (eit_mem (isSelfAdjoint_bn (K := K) n) (crossed M Ω) (bn_mem M Ω n) _)
  have hPapprox : ∀ n, ‖bn (K := K) n (Ωh Ω) - Pn n (Ωh Ω)‖ ≤ ε / (3 * (L + 1)) := fun n =>
    htrig (bn (K := K) n) (isSelfAdjoint_bn n) (Ωh Ω) (isHaarVec_bn M Ω hs hc n)
      (spectrum_bn n) le_rfl
  -- (3) the commutator with the trigonometric polynomial tends to `0`
  have hPcomm : Tendsto (fun n : ℕ => ∑ k ∈ sset,
      ‖cf k‖ * ‖(shift (K := K) ((k : ℚ) * qn n) * x₀
        - x₀ * shift (K := K) ((k : ℚ) * qn n)) (Ωh Ω)‖) atTop (𝓝 0) := by
    have h := tendsto_finset_sum sset fun k (_ : k ∈ sset) =>
      (tendsto_commutator_shift M Ω hs hc hx₀ k).const_mul ‖cf k‖
    simpa using h
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hPcomm (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  -- the three-term decomposition
  have hsplit : bn (K := K) n * x - x * bn (K := K) n
      = (bn (K := K) n * (x - x₀) - (x - x₀) * bn (K := K) n)
        + ((bn (K := K) n - Pn n) * x₀ - x₀ * (bn (K := K) n - Pn n))
        + (Pn n * x₀ - x₀ * Pn n) := by
    simp only [mul_sub, sub_mul]
    abel
  have hcen := isCentral_bn M Ω hs hc n
  have hbsa := isSelfAdjoint_bn (K := K) n
  -- term (a)
  have ha : ‖(bn (K := K) n * (x - x₀) - (x - x₀) * bn (K := K) n) (Ωh Ω)‖ < ε / 3 := by
    have h1 := norm_commutator_central_le (crossed M Ω) (Ωh Ω) hsΩ hcΩ hcen hbsa
      (sub_mem hx hx₀)
    have h2 : ‖(x - x₀) (Ωh Ω)‖ < ε / (3 * (4 * π + 1)) := by
      rw [_root_.sub_apply, ← norm_neg, neg_sub]
      exact hd
    have h3 : 2 * ‖bn (K := K) n‖ ≤ 4 * π := by
      have := norm_bn_le (K := K) n; linarith
    have h4 : 2 * ‖bn (K := K) n‖ * ‖(x - x₀) (Ωh Ω)‖
        ≤ 4 * π * ‖(x - x₀) (Ωh Ω)‖ :=
      mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
    have h5 : 4 * π * ‖(x - x₀) (Ωh Ω)‖ < 4 * π * (ε / (3 * (4 * π + 1))) := by
      exact mul_lt_mul_of_pos_left h2 (by positivity)
    have h6 : 4 * π * (ε / (3 * (4 * π + 1))) < ε / 3 := by
      have hpos : (0 : ℝ) < 3 * (4 * π + 1) := by positivity
      rw [← mul_div_assoc, div_lt_div_iff₀ hpos (by norm_num : (0 : ℝ) < 3)]
      nlinarith [hε, hπ]
    linarith [h1, h4, h5, h6]
  -- term (b)
  have hb : ‖((bn (K := K) n - Pn n) * x₀ - x₀ * (bn (K := K) n - Pn n)) (Ωh Ω)‖ ≤ ε / 3 := by
    have h1 := norm_commutator_apply_Ω_le (crossed M Ω) (Ωh Ω) hc₀ hlb
      (sub_mem (bn_mem M Ω n) (hPmem n))
    have h2 : ‖(bn (K := K) n - Pn n) (Ωh Ω)‖ ≤ ε / (3 * (L + 1)) := by
      rw [_root_.sub_apply]; exact hPapprox n
    have h3 : L * ‖(bn (K := K) n - Pn n) (Ωh Ω)‖ ≤ L * (ε / (3 * (L + 1))) :=
      mul_le_mul_of_nonneg_left h2 hL
    have h4 : L * (ε / (3 * (L + 1))) ≤ ε / 3 := by
      have hpos : (0 : ℝ) < 3 * (L + 1) := by positivity
      rw [← mul_div_assoc, div_le_div_iff₀ hpos (by norm_num : (0 : ℝ) < 3)]
      nlinarith [hε.le, hL]
    have hLeq : Real.sqrt c₀ + ‖x₀‖ = L := hLdef.symm
    rw [hLeq] at h1
    linarith [h1, h3, h4]
  -- term (c)
  have hc' : ‖(Pn n * x₀ - x₀ * Pn n) (Ωh Ω)‖ < ε / 3 := by
    have hexp : Pn n * x₀ - x₀ * Pn n
        = ∑ k ∈ sset, cf k • (shift (K := K) ((k : ℚ) * qn n) * x₀
            - x₀ * shift (K := K) ((k : ℚ) * qn n)) := by
      rw [hPndef]
      simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, smul_sub,
        smul_mul_assoc, mul_smul_comm, eit_bn_int]
    have hbound : ‖(Pn n * x₀ - x₀ * Pn n) (Ωh Ω)‖
        ≤ ∑ k ∈ sset, ‖cf k‖ * ‖(shift (K := K) ((k : ℚ) * qn n) * x₀
            - x₀ * shift (K := K) ((k : ℚ) * qn n)) (Ωh Ω)‖ := by
      rw [hexp, ContinuousLinearMap.sum_apply]
      refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
      rw [ContinuousLinearMap.smul_apply, norm_smul]
    have hlt := hN n hn
    rw [Real.dist_eq, sub_zero] at hlt
    have := (le_abs_self _).trans hlt.le
    calc ‖(Pn n * x₀ - x₀ * Pn n) (Ωh Ω)‖ ≤ _ := hbound
      _ ≤ |∑ k ∈ sset, ‖cf k‖ * ‖(shift (K := K) ((k : ℚ) * qn n) * x₀
            - x₀ * shift (K := K) ((k : ℚ) * qn n)) (Ωh Ω)‖| := le_abs_self _
      _ < ε / 3 := hlt
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _), hsplit]
  simp only [_root_.add_apply]
  refine lt_of_le_of_lt norm_add₃_le ?_
  linarith [ha, hb, hc']

/-! ## HJX Lemma 2.6(iii) and the density theorem -/

include hs hc in
theorem isCentral_eit_an (n : ℕ) (t : ℝ) :
    IsCentral (crossed M Ω) (Ωh Ω) (eit (an (K := K) n) (isSelfAdjoint_an n) t) :=
  ⟨eit_mem (isSelfAdjoint_an n) _ (an_mem M Ω n) t,
    commute_eit (isSelfAdjoint_an n) (commute_an_R M Ω hs hc n) t⟩

include hs hc in
/-- **HJX Lemma 2.6(iii)**, pointwise in `t`: on `ℛ`,
`‖σ^{ξ_n}_t(x)Ω̂ − xΩ̂‖ ≤ ‖Δ̂^{it}(xΩ̂) − xΩ̂‖ + ‖[e^{ita_n}, x]Ω̂‖`. -/
theorem norm_σ_xin_sub_le (n : ℕ) (t : ℝ) {x : L2Q K →L[ℂ] L2Q K} (hx : x ∈ crossed M Ω) :
    ‖σ (crossed M Ω) (xin Ω n) t x (Ωh Ω) - x (Ωh Ω)‖
      ≤ ‖Δit (crossed M Ω) (Ωh Ω) t (x (Ωh Ω)) - x (Ωh Ω)‖
        + ‖(eit (an (K := K) n) (isSelfAdjoint_an n) t * x
            - x * eit (an (K := K) n) (isSelfAdjoint_an n) t) (Ωh Ω)‖ := by
  have hsΩ := isSeparating_Ωh M Ω hs hc
  have hcΩ := isCyclic_Ωh M Ω hc
  have hsa := isSelfAdjoint_an (K := K) n
  set u := eit (an (K := K) n) hsa (-t) with hudef
  set v := eit (an (K := K) n) hsa t with hvdef
  have hvu : v * u = 1 := by rw [hvdef, hudef]; exact eit_mul_neg hsa t
  have huv : u * v = 1 := by rw [hvdef, hudef]; exact eit_neg_mul hsa t
  have hstu : star u = v := by rw [hudef, hvdef, eit_star, neg_neg]
  have hu1 : star u * u = 1 := by rw [hstu]; exact hvu
  have hu2 : u * star u = 1 := by rw [hstu]; exact huv
  have hucen : IsCentral (crossed M Ω) (Ωh Ω) u := isCentral_eit_an M Ω hs hc n (-t)
  have hvcen : IsCentral (crossed M Ω) (Ωh Ω) v := isCentral_eit_an M Ω hs hc n t
  -- the conjugation identity
  have hid : σ (crossed M Ω) (xin Ω n) t x - x
      = u * (σ (crossed M Ω) (Ωh Ω) t x - v * x * u) * star u := by
    rw [hstu, σ_xin M Ω hs hc n t hx, ← hudef, ← hvdef, mul_sub, sub_mul]
    congr 1
    calc x = u * v * x * (u * v) := by rw [huv, one_mul, mul_one]
      _ = u * (v * x * u) * v := by simp only [mul_assoc]
  have hmem : σ (crossed M Ω) (Ωh Ω) t x - v * x * u ∈ crossed M Ω :=
    sub_mem (σ_mem (crossed M Ω) (Ωh Ω) hsΩ hcΩ hx t)
      (mul_mem (mul_mem hvcen.1 hx) hucen.1)
  have h1 : ‖σ (crossed M Ω) (xin Ω n) t x (Ωh Ω) - x (Ωh Ω)‖
      = ‖(σ (crossed M Ω) (Ωh Ω) t x - v * x * u) (Ωh Ω)‖ := by
    rw [← _root_.sub_apply, hid]
    exact norm_conj_unitary_apply_Ω (crossed M Ω) (Ωh Ω) hsΩ hcΩ hucen hu1 hmem
  -- the second term is the commutator
  have hcomm : ‖(x - v * x * u) (Ωh Ω)‖ = ‖(v * x - x * v) (Ωh Ω)‖ := by
    have hxv : x - v * x * u = (x * v - v * x) * u := by
      rw [sub_mul]
      congr 1
      rw [mul_assoc, hvu, mul_one]
    rw [hxv, norm_mul_unitary_apply_Ω (crossed M Ω) (Ωh Ω) hsΩ hcΩ hucen hu2
        (sub_mem (mul_mem hx hvcen.1) (mul_mem hvcen.1 hx)),
      show x * v - v * x = -(v * x - x * v) from by abel,
      ContinuousLinearMap.neg_apply, norm_neg]
  rw [h1]
  calc ‖(σ (crossed M Ω) (Ωh Ω) t x - v * x * u) (Ωh Ω)‖
      = ‖(σ (crossed M Ω) (Ωh Ω) t x - x) (Ωh Ω) + (x - v * x * u) (Ωh Ω)‖ := by
        simp only [_root_.sub_apply]
        congr 1
        abel
    _ ≤ ‖(σ (crossed M Ω) (Ωh Ω) t x - x) (Ωh Ω)‖ + ‖(x - v * x * u) (Ωh Ω)‖ :=
        norm_add_le _ _
    _ = ‖Δit (crossed M Ω) (Ωh Ω) t (x (Ωh Ω)) - x (Ωh Ω)‖ + ‖(v * x - x * v) (Ωh Ω)‖ := by
        rw [hcomm, _root_.sub_apply, σ_apply_Ω]

include hs hc in
/-- The averaging bound: a uniform bound on `[0, 2^{-n}]` bounds `‖(Φ_n x − x)Ω̂‖`. -/
theorem norm_Phi_sub_le (n : ℕ) {x : L2Q K →L[ℂ] L2Q K} {C : ℝ}
    (h : ∀ t ∈ Set.Ioc (0 : ℝ) (Tn n),
      ‖σ (crossed M Ω) (xin Ω n) t x (Ωh Ω) - x (Ωh Ω)‖ ≤ C) :
    ‖Phi M Ω n x (Ωh Ω) - x (Ωh Ω)‖ ≤ C := by
  have hI0 : Integrable fun t : ℝ => wt n t • σ (crossed M Ω) (xin Ω n) t x (Ωh Ω) :=
    integrable_smul_apply (wt n) (integrable_wt n) (fun t => σ (crossed M Ω) (xin Ω n) t x)
      (fun v => continuous_σ_apply (crossed M Ω) (xin Ω n) x v)
      (fun t => norm_σ_le (crossed M Ω) (xin Ω n) t x) (Ωh Ω)
  have hI1 : Integrable fun t : ℝ => wt n t • x (Ωh Ω) :=
    (integrable_wt n).smul_const _
  have hxint : ∫ t : ℝ, wt n t • x (Ωh Ω) = x (Ωh Ω) := by
    rw [integral_smul_const, integral_wt, one_smul]
  have e : Phi M Ω n x (Ωh Ω) - x (Ωh Ω)
      = ∫ t : ℝ, wt n t • (σ (crossed M Ω) (xin Ω n) t x (Ωh Ω) - x (Ωh Ω)) := by
    rw [Phi, smear_apply,
      show (fun t : ℝ => wt n t • (σ (crossed M Ω) (xin Ω n) t x (Ωh Ω) - x (Ωh Ω)))
          = fun t : ℝ => wt n t • σ (crossed M Ω) (xin Ω n) t x (Ωh Ω) - wt n t • x (Ωh Ω) from
        funext fun t => smul_sub _ _ _,
      integral_sub hI0 hI1, hxint]
    rfl
  have hg : ∀ t : ℝ,
      ‖wt n t • (σ (crossed M Ω) (xin Ω n) t x (Ωh Ω) - x (Ωh Ω))‖ ≤ ‖wt n t‖ * C := by
    intro t
    rw [norm_smul]
    by_cases ht : t ∈ Set.Ioc (0 : ℝ) (Tn n)
    · exact mul_le_mul_of_nonneg_left (h t ht) (norm_nonneg _)
    · rw [wt, wtR_of_notMem ht, Complex.ofReal_zero, norm_zero, zero_mul, zero_mul]
  rw [e]
  calc ‖∫ t : ℝ, wt n t • (σ (crossed M Ω) (xin Ω n) t x (Ωh Ω) - x (Ωh Ω))‖
      ≤ ∫ t : ℝ, ‖wt n t‖ * C :=
        norm_integral_le_of_norm_le (((integrable_wt n).norm).mul_const C)
          (Eventually.of_forall hg)
    _ = (∫ t : ℝ, ‖wt n t‖) * C := integral_mul_const _ _
    _ = C := by rw [integral_norm_wt, one_mul]

include hs hc in
/-- **Haagerup's density theorem** (the final lemma of HJX §2): `Φ_n(x)Ω̂ → xΩ̂` for every
`x ∈ ℛ`. Since `Φ_n(x) ∈ ℛ_n` (E6.4), the union `⋃_n ℛ_n` is `‖·‖_{ψ̂}`-dense in `ℛ`. -/
theorem tendsto_Phi_apply {x : L2Q K →L[ℂ] L2Q K} (hx : x ∈ crossed M Ω) :
    Tendsto (fun n : ℕ => Phi M Ω n x (Ωh Ω)) atTop (𝓝 (x (Ωh Ω))) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  -- the modular-flow term is small on a short interval
  have hcont : Continuous fun t : ℝ => Δit (crossed M Ω) (Ωh Ω) t (x (Ωh Ω)) :=
    continuous_Δit_comp (crossed M Ω) (Ωh Ω) continuous_const
  have hc0 : Tendsto (fun t : ℝ => Δit (crossed M Ω) (Ωh Ω) t (x (Ωh Ω))) (𝓝 0)
      (𝓝 (x (Ωh Ω))) := by
    have h := hcont.tendsto 0
    rwa [Δit_zero, one_apply_eq_self] at h
  obtain ⟨δ, hδ0, hδ⟩ := Metric.tendsto_nhds_nhds.mp hc0 (ε / 4) (by positivity)
  obtain ⟨N₂, hN₂⟩ := exists_pow_lt_of_lt_one hδ0 (by norm_num : (1 : ℝ) / 2 < 1)
  have hTN₂ : Tn N₂ < δ := by
    rw [Tn]
    simpa [one_div, inv_pow] using hN₂
  -- the commutator term is small for large `n`
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp (tendsto_commutator_bn M Ω hs hc hx)
    (ε / (4 * Real.exp (2 * π))) (by positivity)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hn₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn₂ : N₂ ≤ n := le_trans (le_max_right _ _) hn
  have hTn : Tn n ≤ Tn N₂ := by
    rw [Tn, Tn]
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ (by norm_num) hn₂
  have hcomm : ‖(bn (K := K) n * x - x * bn (K := K) n) (Ωh Ω)‖
      < ε / (4 * Real.exp (2 * π)) := by
    have h := hN₁ n hn₁
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at h
  -- the uniform bound on `(0, 2^{-n}]`
  have hkey : ∀ t ∈ Set.Ioc (0 : ℝ) (Tn n),
      ‖σ (crossed M Ω) (xin Ω n) t x (Ωh Ω) - x (Ωh Ω)‖ ≤ ε / 2 := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have htT : t ≤ Tn n := ht.2
    -- the modular-flow term
    have hA : ‖Δit (crossed M Ω) (Ωh Ω) t (x (Ωh Ω)) - x (Ωh Ω)‖ < ε / 4 := by
      have hdist : dist t 0 < δ := by
        rw [Real.dist_eq, sub_zero, abs_of_pos ht0]
        exact lt_of_le_of_lt (htT.trans hTn) hTN₂
      have h := hδ hdist
      rwa [dist_eq_norm] at h
    -- the commutator term
    have hean : eit (an (K := K) n) (isSelfAdjoint_an n) t
        = eit (bn (K := K) n) (isSelfAdjoint_bn n) (t * 2 ^ n) := eit_an n t
    have hts : |t * 2 ^ n| ≤ 1 := by
      rw [abs_of_pos (by positivity)]
      calc t * 2 ^ n ≤ Tn n * 2 ^ n :=
            mul_le_mul_of_nonneg_right htT (by positivity)
        _ = 1 := by rw [mul_comm]; exact two_pow_mul_Tn n
    have hB : ‖(eit (an (K := K) n) (isSelfAdjoint_an n) t * x
        - x * eit (an (K := K) n) (isSelfAdjoint_an n) t) (Ωh Ω)‖ < ε / 4 := by
      rw [hean]
      have h1 := norm_commutator_eit_le (crossed M Ω) (Ωh Ω) (isSeparating_Ωh M Ω hs hc)
        (isCyclic_Ωh M Ω hc) (isCentral_bn M Ω hs hc n) (isSelfAdjoint_bn n) hx (t * 2 ^ n)
      have h2 : |t * 2 ^ n| * Real.exp (|t * 2 ^ n| * ‖bn (K := K) n‖)
          ≤ Real.exp (2 * π) := by
        have h3 : |t * 2 ^ n| * ‖bn (K := K) n‖ ≤ 2 * π := by
          calc |t * 2 ^ n| * ‖bn (K := K) n‖ ≤ 1 * (2 * π) :=
                mul_le_mul hts (norm_bn_le (K := K) n) (norm_nonneg _) zero_le_one
            _ = 2 * π := one_mul _
        calc |t * 2 ^ n| * Real.exp (|t * 2 ^ n| * ‖bn (K := K) n‖)
            ≤ 1 * Real.exp (2 * π) :=
              mul_le_mul hts (Real.exp_le_exp.mpr h3) (Real.exp_nonneg _) zero_le_one
          _ = Real.exp (2 * π) := one_mul _
      have h4 : |t * 2 ^ n| * Real.exp (|t * 2 ^ n| * ‖bn (K := K) n‖)
            * ‖(bn (K := K) n * x - x * bn (K := K) n) (Ωh Ω)‖
          ≤ Real.exp (2 * π) * ‖(bn (K := K) n * x - x * bn (K := K) n) (Ωh Ω)‖ :=
        mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      have h5 : Real.exp (2 * π) * ‖(bn (K := K) n * x - x * bn (K := K) n) (Ωh Ω)‖
          < Real.exp (2 * π) * (ε / (4 * Real.exp (2 * π))) :=
        mul_lt_mul_of_pos_left hcomm (Real.exp_pos _)
      have h6 : Real.exp (2 * π) * (ε / (4 * Real.exp (2 * π))) = ε / 4 := by
        have hex : (0 : ℝ) < Real.exp (2 * π) := Real.exp_pos _
        field_simp
      linarith [h1, h4, h5, h6]
    have hsum := norm_σ_xin_sub_le M Ω hs hc n t hx
    linarith [hsum, hA, hB]
  have hfin := norm_Phi_sub_le M Ω hs hc n (C := ε / 2) hkey
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  linarith [hfin, hε]

include hs hc in
/-- **`⋃_n ℛ_n` is `‖·‖_{ψ̂}`-dense in `ℛ`**: every `x ∈ ℛ` is `‖·‖_{ψ̂}`-approximated by
`Φ_n(x) ∈ ℛ_n`. -/
theorem exists_mem_Rn_approx {x : L2Q K →L[ℂ] L2Q K} (hx : x ∈ crossed M Ω) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ (n : ℕ) (y : L2Q K →L[ℂ] L2Q K), y ∈ Rn M Ω n ∧ ‖y (Ωh Ω) - x (Ωh Ω)‖ < ε := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (tendsto_Phi_apply M Ω hs hc hx) ε hε
  refine ⟨N, Phi M Ω N x, Phi_mem_Rn M Ω hs hc N hx, ?_⟩
  have h := hN N le_rfl
  rwa [dist_eq_norm] at h

end Bn

end Haagerup

end VN

end CommutingRepetition
