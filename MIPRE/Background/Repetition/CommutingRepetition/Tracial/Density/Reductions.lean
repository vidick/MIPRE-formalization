/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Tracial/Density/Reductions.lean
-/
/-
# The faithful perturbation of a commuting strategy (stage E1)

Lin's proof of the density theorem needs Alice's algebra with a *faithful*
normal state. Here a commuting strategy (compressed to a separable space, see
`Compress.lean`) is perturbed: the state becomes `φ = (1−ε) ω_ψ + ε φ₀` with `φ₀`
the faithful state of `FaithfulState.lean`, and Bob is encoded by the
functionals `ω_b^y = (1−ε)⟪ψ, · F_b^y ψ⟫ + (ε/|B|) φ₀`, which are positive on
every operator commuting with `F_b^y` (in particular on Alice's algebra) and sum
to `φ`. The correlation `re ω_b^y(E_a^x)` is `2ε`-close to the original one
entrywise. This is the reduction of PLAN-density.md §1.3 / stage E1. Proof-side.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Tracial.Density.Compress
import MIPRE.Background.Repetition.CommutingRepetition.Tracial.Density.FaithfulState
import MIPRE.Background.Repetition.CommutingRepetition.Tracial.Density

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace Density

open scoped InnerProductSpace ComplexOrder
open TopologicalSpace

set_option linter.unusedSectionVars false

variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-! ### The vector state and Bob's functionals of a commuting strategy -/

section Functionals

variable (S : CommutingStrategy.{0} X Y A B)

/-- The vector state `T ↦ ⟪ψ, T ψ⟫`. -/
noncomputable def vecState : (S.H →L[ℂ] S.H) →ₗ[ℂ] ℂ where
  toFun T := ⟪S.ψ, T S.ψ⟫_ℂ
  map_add' T U := by rw [_root_.add_apply, inner_add_right]
  map_smul' c T := by rw [_root_.smul_apply, inner_smul_right, RingHom.id_apply, smul_eq_mul]

theorem vecState_apply (T : S.H →L[ℂ] S.H) : vecState S T = ⟪S.ψ, T S.ψ⟫_ℂ := rfl

/-- Bob's functional `T ↦ ⟪ψ, T F_b^y ψ⟫` on `B(H)`. -/
noncomputable def bobFun (y : Y) (b : B) : (S.H →L[ℂ] S.H) →ₗ[ℂ] ℂ where
  toFun T := ⟪S.ψ, T (S.F y b S.ψ)⟫_ℂ
  map_add' T U := by rw [_root_.add_apply, inner_add_right]
  map_smul' c T := by rw [_root_.smul_apply, inner_smul_right, RingHom.id_apply, smul_eq_mul]

theorem bobFun_apply (y : Y) (b : B) (T : S.H →L[ℂ] S.H) :
    bobFun S y b T = ⟪S.ψ, T (S.F y b S.ψ)⟫_ℂ := rfl

theorem bobFun_sum (y : Y) : ∑ b, bobFun S y b = vecState S := by
  ext T
  rw [LinearMap.sum_apply]
  simp only [bobFun_apply, vecState_apply]
  rw [← inner_sum, ← map_sum, ← ContinuousLinearMap.sum_apply, S.F_sum y, one_apply_eq_self]

theorem bobFun_correlation (x : X) (y : Y) (a : A) (b : B) :
    (bobFun S y b (S.E x a)).re = S.correlation x y a b := rfl

theorem vecState_one : vecState S 1 = 1 := by
  rw [vecState_apply, one_apply_eq_self, inner_self_eq_norm_sq_to_K, S.ψ_norm]
  simp

theorem vecState_nonneg (T : S.H →L[ℂ] S.H) : 0 ≤ vecState S (star T * T) := by
  rw [vecState_apply, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  exact pow_nonneg (Complex.zero_le_real.mpr (norm_nonneg (T S.ψ))) 2

/-- Bob's functionals are positive on operators commuting with Bob's effect. -/
theorem bobFun_nonneg_of_commute (y : Y) (b : B) {T : S.H →L[ℂ] S.H}
    (hT : Commute T (S.F y b)) : 0 ≤ bobFun S y b (star T * T) := by
  rw [bobFun_apply, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  have h : T (S.F y b S.ψ) = S.F y b (T S.ψ) := by
    rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, hT.eq]
  rw [h]
  exact (S.F_pos y b).inner_nonneg_right _

theorem vecState_traceClass : IsTraceClassFunctional (vecState S) := by
  refine ⟨fun k => if k = 0 then S.ψ else 0, fun k => if k = 0 then S.ψ else 0, ?_, fun T => ?_⟩
  · refine summable_of_ne_finset_zero (s := {0}) fun k hk => ?_
    simp only [Finset.mem_singleton] at hk
    simp [hk]
  · rw [vecState_apply, tsum_eq_single 0 fun k hk => by simp [hk]]
    simp

theorem bobFun_traceClass (y : Y) (b : B) : IsTraceClassFunctional (bobFun S y b) := by
  refine ⟨fun k => if k = 0 then S.ψ else 0, fun k => if k = 0 then S.F y b S.ψ else 0, ?_,
    fun T => ?_⟩
  · refine summable_of_ne_finset_zero (s := {0}) fun k hk => ?_
    simp only [Finset.mem_singleton] at hk
    simp [hk]
  · rw [bobFun_apply, tsum_eq_single 0 fun k hk => by simp [hk]]
    simp

end Functionals

/-! ### Sums of trace-class functionals -/

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Interleaving two sequences. -/
noncomputable def interleave (v v' : ℕ → K) (k : ℕ) : K :=
  if Even k then v (k / 2) else v' (k / 2)

theorem interleave_even (v v' : ℕ → K) (k : ℕ) : interleave v v' (2 * k) = v k := by
  have h : (2 * k) / 2 = k := by omega
  simp [interleave, h]

theorem interleave_odd (v v' : ℕ → K) (k : ℕ) : interleave v v' (2 * k + 1) = v' k := by
  have h : (2 * k + 1) / 2 = k := by omega
  have h2 : ¬ Even (2 * k + 1) := Nat.not_even_iff_odd.mpr (odd_two_mul_add_one k)
  simp [interleave, h, h2]

theorem summable_inner_of_summable_norm {v w : ℕ → K} (hs : Summable fun k => ‖v k‖ * ‖w k‖)
    (T : K →L[ℂ] K) : Summable fun k => ⟪v k, T (w k)⟫_ℂ :=
  Summable.of_norm_bounded (hs.mul_left ‖T‖) fun k => by
    calc ‖⟪v k, T (w k)⟫_ℂ‖ ≤ ‖v k‖ * ‖T (w k)‖ := norm_inner_le_norm _ _
      _ ≤ ‖v k‖ * (‖T‖ * ‖w k‖) := mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
      _ = ‖T‖ * (‖v k‖ * ‖w k‖) := by ring

theorem IsTraceClassFunctional.add {φ ψ : (K →L[ℂ] K) →ₗ[ℂ] ℂ} (hφ : IsTraceClassFunctional φ)
    (hψ : IsTraceClassFunctional ψ) : IsTraceClassFunctional (φ + ψ) := by
  obtain ⟨v, w, hs, h⟩ := hφ
  obtain ⟨v', w', hs', h'⟩ := hψ
  have hsum : Summable fun k => ‖interleave v v' k‖ * ‖interleave w w' k‖ := by
    refine (HasSum.even_add_odd (f := fun k => ‖interleave v v' k‖ * ‖interleave w w' k‖)
      (m := ∑' k, ‖v k‖ * ‖w k‖) (m' := ∑' k, ‖v' k‖ * ‖w' k‖) ?_ ?_).summable
    · simp only [interleave_even]
      exact hs.hasSum
    · simp only [interleave_odd]
      exact hs'.hasSum
  refine ⟨interleave v v', interleave w w', hsum, fun T => ?_⟩
  have he : Summable fun k => ⟪interleave v v' (2 * k), T (interleave w w' (2 * k))⟫_ℂ := by
    simp only [interleave_even]
    exact summable_inner_of_summable_norm hs T
  have ho : Summable fun k =>
      ⟪interleave v v' (2 * k + 1), T (interleave w w' (2 * k + 1))⟫_ℂ := by
    simp only [interleave_odd]
    exact summable_inner_of_summable_norm hs' T
  rw [LinearMap.add_apply, h, h',
    ← tsum_even_add_odd (f := fun k => ⟪interleave v v' k, T (interleave w w' k)⟫_ℂ) he ho]
  simp only [interleave_even, interleave_odd]

/-! ### The faithful perturbation -/

theorem vecState_star_mul_self (S : CommutingStrategy.{0} X Y A B) (T : S.H →L[ℂ] S.H) :
    vecState S (star T * T) = ((‖T S.ψ‖ ^ 2 : ℝ) : ℂ) := by
  rw [vecState_apply, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
  rfl

/-- The data of a faithful perturbation: a strategy, a dense sequence in its Hilbert space and
`ε ∈ (0, 1]`. -/
structure Perturbed (X Y A B : Type) [Fintype X] [Fintype Y] [Fintype A] [Fintype B] where
  S : CommutingStrategy.{0} X Y A B
  u : ℕ → S.H
  u_dense : DenseRange u
  ε : ℝ
  ε_pos : 0 < ε
  ε_le : ε ≤ 1

namespace Perturbed

variable (P : Perturbed X Y A B)

theorem u_ne : ∃ k, P.u k ≠ 0 := by
  by_contra h
  push_neg at h
  have hr : Set.range P.u ⊆ {0} := by
    rintro _ ⟨k, rfl⟩
    exact h k
  have hd : Dense ({0} : Set P.S.H) := P.u_dense.mono hr
  have hc := hd.closure_eq
  rw [isClosed_singleton.closure_eq] at hc
  have hmem : P.S.ψ ∈ ({0} : Set P.S.H) := by rw [hc]; exact Set.mem_univ _
  have hψ := P.S.ψ_norm
  rw [Set.mem_singleton_iff.mp hmem, norm_zero] at hψ
  exact zero_ne_one hψ

/-- The perturbed (faithful) state `(1−ε) ω_ψ + ε φ₀`. -/
noncomputable def φ : (P.S.H →L[ℂ] P.S.H) →ₗ[ℂ] ℂ :=
  ((1 - P.ε : ℝ) : ℂ) • vecState P.S + ((P.ε : ℝ) : ℂ) • faithfulState P.u

/-- Bob's perturbed functionals `(1−ε)⟪ψ, · F_b^y ψ⟫ + (ε/|B|) φ₀`. -/
noncomputable def ω (y : Y) (b : B) : (P.S.H →L[ℂ] P.S.H) →ₗ[ℂ] ℂ :=
  ((1 - P.ε : ℝ) : ℂ) • bobFun P.S y b + ((P.ε / Fintype.card B : ℝ) : ℂ) • faithfulState P.u

/-- The perturbed correlation `re ω_b^y(E_a^x)`. -/
noncomputable def corr : Correlation X Y A B := fun x y a b => (P.ω y b (P.S.E x a)).re

theorem φ_apply (T : P.S.H →L[ℂ] P.S.H) :
    P.φ T = ((1 - P.ε : ℝ) : ℂ) * vecState P.S T + ((P.ε : ℝ) : ℂ) * faithfulState P.u T := by
  simp [φ]

theorem ω_apply (y : Y) (b : B) (T : P.S.H →L[ℂ] P.S.H) :
    P.ω y b T = ((1 - P.ε : ℝ) : ℂ) * bobFun P.S y b T +
      ((P.ε / Fintype.card B : ℝ) : ℂ) * faithfulState P.u T := by
  simp [ω]

theorem φ_one : P.φ 1 = 1 := by
  rw [φ_apply, vecState_one, faithfulState_one P.u P.u_ne]
  push_cast
  ring

theorem φ_star_mul_self (T : P.S.H →L[ℂ] P.S.H) :
    P.φ (star T * T) = (((1 - P.ε) * ‖T P.S.ψ‖ ^ 2 +
      P.ε * ((Z P.u)⁻¹ * ∑' k, wt k * ‖T (nv P.u k)‖ ^ 2) : ℝ) : ℂ) := by
  rw [φ_apply, vecState_star_mul_self, faithfulState_star_mul_self]
  push_cast
  ring

theorem φ_nonneg (T : P.S.H →L[ℂ] P.S.H) : 0 ≤ P.φ (star T * T) := by
  rw [φ_star_mul_self]
  refine Complex.zero_le_real.mpr (add_nonneg ?_ ?_)
  · exact mul_nonneg (sub_nonneg.mpr P.ε_le) (sq_nonneg _)
  · exact mul_nonneg P.ε_pos.le
      (mul_nonneg (inv_nonneg.mpr (Z_nonneg _)) (tsum_nonneg fun k => mul_nonneg (wt_nonneg k) (sq_nonneg _)))

/-- The perturbed state is faithful on `B(H)`. -/
theorem φ_faithful (T : P.S.H →L[ℂ] P.S.H) (h : P.φ (star T * T) = 0) : T = 0 := by
  rw [φ_star_mul_self, Complex.ofReal_eq_zero] at h
  have h1 : 0 ≤ (1 - P.ε) * ‖T P.S.ψ‖ ^ 2 := mul_nonneg (sub_nonneg.mpr P.ε_le) (sq_nonneg _)
  have h2 : 0 ≤ (Z P.u)⁻¹ * ∑' k, wt k * ‖T (nv P.u k)‖ ^ 2 :=
    mul_nonneg (inv_nonneg.mpr (Z_nonneg _)) (tsum_nonneg fun k => mul_nonneg (wt_nonneg k) (sq_nonneg _))
  have h3 : P.ε * ((Z P.u)⁻¹ * ∑' k, wt k * ‖T (nv P.u k)‖ ^ 2) = 0 := by
    nlinarith [mul_nonneg P.ε_pos.le h2]
  have h4 : faithfulState P.u (star T * T) = 0 := by
    rw [faithfulState_star_mul_self, Complex.ofReal_eq_zero]
    exact (mul_eq_zero.mp h3).resolve_left P.ε_pos.ne'
  exact faithfulState_faithful P.u P.u_dense P.u_ne T h4

variable [Nonempty B]

theorem ω_sum (y : Y) : ∑ b, P.ω y b = P.φ := by
  simp only [ω, φ, Finset.sum_add_distrib, ← Finset.smul_sum, bobFun_sum, Finset.sum_const,
    Finset.card_univ]
  congr 1
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 1
  have hB : (Fintype.card B : ℝ) ≠ 0 := by
    have := Fintype.card_pos (α := B)
    positivity
  push_cast
  field_simp

/-- Bob's perturbed functionals are positive on operators commuting with Bob's effect. -/
theorem ω_nonneg_of_commute (y : Y) (b : B) {T : P.S.H →L[ℂ] P.S.H}
    (hT : Commute T (P.S.F y b)) : 0 ≤ P.ω y b (star T * T) := by
  rw [ω_apply]
  refine add_nonneg (mul_nonneg ?_ (bobFun_nonneg_of_commute P.S y b hT))
    (mul_nonneg ?_ (faithfulState_nonneg P.u T))
  · exact Complex.zero_le_real.mpr (sub_nonneg.mpr P.ε_le)
  · exact Complex.zero_le_real.mpr (div_nonneg P.ε_pos.le (Nat.cast_nonneg _))

theorem φ_traceClass : IsTraceClassFunctional P.φ :=
  ((vecState_traceClass P.S).smul _).add ((faithfulState_traceClass P.u).smul _)

theorem ω_traceClass (y : Y) (b : B) : IsTraceClassFunctional (P.ω y b) :=
  ((bobFun_traceClass P.S y b).smul _).add ((faithfulState_traceClass P.u).smul _)

theorem corr_eq (x : X) (y : Y) (a : A) (b : B) :
    P.corr x y a b = (1 - P.ε) * P.S.correlation x y a b +
      P.ε / Fintype.card B * (faithfulState P.u (P.S.E x a)).re := by
  rw [corr, ω_apply, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
    bobFun_correlation]

/-- POVM elements are contractions. -/
theorem norm_E_le_one (x : X) (a : A) : ‖P.S.E x a‖ ≤ 1 := by
  classical
  have h0 : (0 : P.S.H →L[ℂ] P.S.H) ≤ P.S.E x a :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).mpr (P.S.E_pos x a)
  have h1 : P.S.E x a ≤ 1 := by
    rw [ContinuousLinearMap.le_def]
    have hsum := P.S.E_sum x
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)] at hsum
    rw [← hsum, add_sub_cancel_left]
    exact ContinuousLinearMap.isPositive_sum _ fun a' _ => P.S.E_pos x a'
  exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ h0).mpr h1

theorem abs_corr_sub_le (x : X) (y : Y) (a : A) (b : B) :
    |P.corr x y a b - P.S.correlation x y a b| ≤ 2 * P.ε := by
  rw [corr_eq]
  have hp0 := P.S.correlation_nonneg x y a b
  have hp1 := P.S.correlation_le_one x y a b
  have hr : |(faithfulState P.u (P.S.E x a)).re| ≤ 1 :=
    (Complex.abs_re_le_norm _).trans
      ((norm_faithfulState_le P.u P.u_ne _).trans (P.norm_E_le_one x a))
  have hB : (1 : ℝ) ≤ Fintype.card B := by exact_mod_cast Fintype.card_pos (α := B)
  have hεB : P.ε / Fintype.card B ≤ P.ε := div_le_self P.ε_pos.le hB
  have hεB0 : 0 ≤ P.ε / Fintype.card B := div_nonneg P.ε_pos.le (by linarith)
  rw [abs_le]
  constructor
  · nlinarith [abs_le.mp hr, abs_nonneg (faithfulState P.u (P.S.E x a)).re]
  · nlinarith [abs_le.mp hr, abs_nonneg (faithfulState P.u (P.S.E x a)).re]

theorem l1Dist_le :
    l1Dist P.S.correlation P.corr ≤
      2 * P.ε * (Fintype.card X * Fintype.card Y * Fintype.card A * Fintype.card B) := by
  unfold l1Dist
  calc ∑ x, ∑ y, ∑ a, ∑ b, |P.S.correlation x y a b - P.corr x y a b|
      ≤ ∑ x : X, ∑ y : Y, ∑ a : A, ∑ b : B, 2 * P.ε := by
        refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => Finset.sum_le_sum
          fun a _ => Finset.sum_le_sum fun b _ => ?_
        rw [abs_sub_comm]
        exact P.abs_corr_sub_le x y a b
    _ = 2 * P.ε * (Fintype.card X * Fintype.card Y * Fintype.card A * Fintype.card B) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

end Perturbed

/-- **Stage E1**: every commuting correlation is approximated in `ℓ¹` by the perturbed
correlation of a separable strategy whose perturbed state is faithful. -/
theorem exists_perturbed [Nonempty B] (S : CommutingStrategy.{0} X Y A B) {δ : ℝ} (hδ : 0 < δ) :
    ∃ P : Perturbed X Y A B, SeparableSpace P.S.H ∧ l1Dist S.correlation P.corr < δ := by
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = ((Fintype.card X * Fintype.card Y * Fintype.card A *
    Fintype.card B : ℕ) : ℝ) := ⟨_, rfl⟩
  have hN0 : 0 ≤ N := by rw [hN]; positivity
  have hε0 : 0 < min 1 (δ / (2 * (N + 1))) := lt_min one_pos (by positivity)
  have hε1 : min 1 (δ / (2 * (N + 1))) ≤ 1 := min_le_left _ _
  haveI : Nonempty (compress S).H := ⟨(compress S).ψ⟩
  let P : Perturbed X Y A B :=
    { S := compress S
      u := denseSeq (compress S).H
      u_dense := denseRange_denseSeq (compress S).H
      ε := min 1 (δ / (2 * (N + 1)))
      ε_pos := hε0
      ε_le := hε1 }
  refine ⟨P, inferInstance, ?_⟩
  have hbound := Perturbed.l1Dist_le P
  have hcorr : P.S.correlation = S.correlation := compress_correlation S
  rw [hcorr] at hbound
  refine hbound.trans_lt ?_
  have hNeq : (Fintype.card X * Fintype.card Y * Fintype.card A * Fintype.card B : ℝ) = N := by
    rw [hN]; push_cast; ring
  show 2 * min 1 (δ / (2 * (N + 1))) * (Fintype.card X * Fintype.card Y * Fintype.card A *
    Fintype.card B : ℝ) < δ
  rw [hNeq]
  have hmin : min 1 (δ / (2 * (N + 1))) ≤ δ / (2 * (N + 1)) := min_le_right _ _
  calc 2 * min 1 (δ / (2 * (N + 1))) * N ≤ 2 * (δ / (2 * (N + 1))) * N := by gcongr
    _ = δ * (N / (N + 1)) := by field_simp
    _ < δ := by
        refine mul_lt_of_lt_one_right hδ ?_
        rw [div_lt_one (by positivity)]
        linarith

end Density

end CommutingRepetition
