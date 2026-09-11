/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Tracial/Density/Main.lean
-/
/-
# Lin's tracial density theorem (stage E7)

`tracialDensity : TracialDensityHypothesis` — the end of the density programme
E1–E7. Given a commuting-operator correlation `p` and `δ > 0`:

* **E1** compresses a realizing strategy to a separable Hilbert space
  (`Tracial/Density/Compress.lean`);
* **E7.1/E7.2** perturb its vector state to a faithful normal state and put the
  strategy in standard form, with Alice in a von Neumann algebra `M`, Bob in `M′`
  and a cyclic separating unit vector — at an entrywise cost `2ε/(1−ε)`
  (`GVec.lean`, `StandardStrategy.lean`);
* **E4/E5** build the bounded Rieffel–van Daele modular data of `(M, Ω)` and the
  discrete crossed product `ℛ = M ⋊_σ ℚ`;
* **E6** runs Haagerup's reduction: the tracial subalgebras `ℛ_n` with the
  conditional expectations `Φ_n` and `Φ_n(x)Ω̂ → xΩ̂`;
* **E7.3** reads off a tracially embeddable correlation at an entrywise cost `η`
  (`CrossedTracial.lean`).

Choosing `ε` and `η` small compared with `δ/(2·|X|²|A|²)` closes the ℓ¹ estimate.

This file is what let the `hLin : TracialDensityHypothesis` binder be deleted
from the root statements and their intermediates; the unconditional roots live
in `MainTheorem/Main.lean`, and `MainStatement.tracialDensity`
(`StatementBridge.lean`) is the same theorem in the vocabulary of the
standalone `Statement.lean`. Audit node 1.1.1.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Tracial.Density.CrossedTracial
import MIPRE.Background.Repetition.CommutingRepetition.Tracial.Density.Reductions

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace Density

open scoped InnerProductSpace ComplexOrder
open VN VN.Crossed VN.Haagerup VN.Modular
open TopologicalSpace

set_option linter.unusedSectionVars false

/-! ## The ℓ¹ estimate from an entrywise estimate -/

theorem l1Dist_le_of_forall {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (p r : Correlation X Y A B) {C : ℝ} (h : ∀ x y a b, |p x y a b - r x y a b| ≤ C) :
    l1Dist p r ≤ C * (Fintype.card X * Fintype.card Y * Fintype.card A * Fintype.card B) := by
  unfold l1Dist
  calc ∑ x : X, ∑ y : Y, ∑ a : A, ∑ b : B, |p x y a b - r x y a b|
      ≤ ∑ _x : X, ∑ _y : Y, ∑ _a : A, ∑ _b : B, C :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => Finset.sum_le_sum
          fun a _ => Finset.sum_le_sum fun b _ => h x y a b
    _ = C * (Fintype.card X * Fintype.card Y * Fintype.card A * Fintype.card B) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

/-! ## The standard-form step -/

theorem abs_corr_sub_stdOf_le {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (S : CommutingStrategy.{0} X Y A B) [SeparableSpace S.H] [Nonempty S.H]
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (x : X) (y : Y) (a : A) (b : B) :
    |S.correlation x y a b - (stdOf S hε0 hε1).corr x y a b| ≤ 2 * ε / (1 - ε) := by
  have hEF : ‖S.E x a * S.F y b‖ ≤ 1 := by
    refine (norm_mul_le _ _).trans ?_
    have h1 : ‖S.E x a‖ ≤ 1 :=
      norm_povm_le_one (fun a => S.E x a) (fun a => S.E_pos x a) (S.E_sum x) a
    have h2 : ‖S.F y b‖ ≤ 1 :=
      norm_povm_le_one (fun b => S.F y b) (fun b => S.F_pos y b) (S.F_sum y) b
    calc ‖S.E x a‖ * ‖S.F y b‖ ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = 1 := by ring
  have hcorr : S.correlation x y a b = (⟪S.ψ, (S.E x a * S.F y b) S.ψ⟫_ℂ).re := by
    rw [CommutingStrategy.correlation, ContinuousLinearMap.mul_apply]
  have hbound := norm_gvecState_sub_le S.ψ (denseSeq S.H) S.ψ_norm hε0 hε1
    (S.E x a * S.F y b)
  rw [stdOf_corr S hε0 hε1 x y a b, hcorr, abs_sub_comm, ← Complex.sub_re]
  refine (Complex.abs_re_le_norm _).trans ?_
  refine hbound.trans ?_
  have hε' : (0 : ℝ) < 1 - ε := by linarith
  rw [div_le_div_iff₀ hε' hε']
  nlinarith [mul_nonneg (sub_nonneg.mpr hEF)
    (mul_pos (by linarith : (0 : ℝ) < 2 * ε) hε').le]

/-! ## Lin's density theorem -/

/-- **Stage E7 / audit node 1.1.1: Lin's tracial density theorem.** Every
commuting-operator correlation on common finite alphabets is an ℓ¹-limit of
tracially embeddable correlations. -/
theorem tracialDensity : TracialDensityHypothesis := by
  classical
  intro Xc Ac _ _ _ _ p hp δ hδ
  obtain ⟨S, hS⟩ := hp
  -- the cardinality factor
  set N : ℝ := ((Fintype.card Xc * Fintype.card Xc * Fintype.card Ac * Fintype.card Ac : ℕ) : ℝ)
    with hNdef
  have hN0 : 0 ≤ N := by rw [hNdef]; positivity
  have hN1 : (0 : ℝ) < N + 1 := by linarith
  -- the two error budgets
  set η : ℝ := δ / (4 * (N + 1)) with hηdef
  have hη0 : 0 < η := by rw [hηdef]; exact div_pos hδ (by linarith)
  set ε : ℝ := min (1 / 2) (δ / (16 * (N + 1))) with hεdef
  have hε0 : 0 < ε := by
    rw [hεdef]
    exact lt_min (by norm_num) (div_pos hδ (by linarith))
  have hεhalf : ε ≤ 1 / 2 := min_le_left _ _
  have hε1 : ε < 1 := by linarith
  have hεsmall : ε ≤ δ / (16 * (N + 1)) := min_le_right _ _
  -- compress and put in standard form
  have : Nonempty (compress S).H := ⟨(compress S).ψ⟩
  set q := stdOf (compress S) hε0 hε1 with hqdef
  -- the tracial step
  obtain ⟨t, ht⟩ := StdStrategy.exists_tracial_approx q hη0
  refine ⟨t, ?_⟩
  -- entrywise estimate
  have hentry : ∀ x y a b, |p x y a b - t.toCorrelation x y a b| ≤ 2 * ε / (1 - ε) + η := by
    intro x y a b
    have h1 : |p x y a b - q.corr x y a b| ≤ 2 * ε / (1 - ε) := by
      rw [← hS, ← compress_correlation S]
      exact abs_corr_sub_stdOf_le (compress S) hε0 hε1 x y a b
    have h2 : |q.corr x y a b - t.toCorrelation x y a b| ≤ η := by
      rw [abs_sub_comm]
      exact ht x y a b
    calc |p x y a b - t.toCorrelation x y a b|
        ≤ |p x y a b - q.corr x y a b| + |q.corr x y a b - t.toCorrelation x y a b| := by
          exact abs_sub_le _ _ _
      _ ≤ 2 * ε / (1 - ε) + η := add_le_add h1 h2
  refine lt_of_le_of_lt (l1Dist_le_of_forall p t.toCorrelation hentry) ?_
  -- arithmetic
  have hNeq : ((Fintype.card Xc : ℝ) * (Fintype.card Xc : ℝ) * (Fintype.card Ac : ℝ) *
      (Fintype.card Ac : ℝ)) = N := by rw [hNdef]; push_cast; ring
  rw [hNeq]
  have hhalf : (0 : ℝ) < 1 - ε := by linarith
  have hεbound : 2 * ε / (1 - ε) ≤ 4 * ε := by
    rw [div_le_iff₀ hhalf]
    nlinarith [hε0.le, hεhalf]
  have h4ε : 4 * ε ≤ δ / (4 * (N + 1)) := by
    calc 4 * ε ≤ 4 * (δ / (16 * (N + 1))) := by linarith
      _ = δ / (4 * (N + 1)) := by field_simp; ring
  have hsum : 2 * ε / (1 - ε) + η ≤ δ / (2 * (N + 1)) := by
    have : δ / (4 * (N + 1)) + δ / (4 * (N + 1)) = δ / (2 * (N + 1)) := by
      field_simp; ring
    rw [hηdef] at *
    linarith [hεbound, h4ε]
  calc (2 * ε / (1 - ε) + η) * N ≤ δ / (2 * (N + 1)) * N := by
        refine mul_le_mul_of_nonneg_right hsum hN0
    _ = δ * (N / (2 * (N + 1))) := by ring
    _ < δ := by
        refine mul_lt_of_lt_one_right hδ ?_
        rw [div_lt_one (by linarith)]
        linarith

end Density

end CommutingRepetition
