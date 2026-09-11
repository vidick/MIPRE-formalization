/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Game/Strategy.lean
-/
/-
# Commuting-operator strategies

Encoding decision D2: a commuting strategy lives on ONE Hilbert space, with
Alice's and Bob's POVM effects commuting elementwise — not the
finite-dimensional Kronecker encoding of the ten-proofs artifact.
Anchors: 02_preliminaries.tex ("commuting-operator strategy": Hilbert space
H, unit vector ψ, POVMs (E_x^a), (F_y^b) with [E_x^a, F_y^b] = 0); audit
definition `commuting_strategy`.

A strategy depends only on the alphabets, not on a particular game.
-/
import Mathlib

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped BigOperators InnerProductSpace

universe u

/-- A commuting-operator strategy over question alphabets `X, Y` and answer
alphabets `A, B`: a complex Hilbert space `H`, a unit vector `ψ`, and
POVM families `E x` (Alice) and `F y` (Bob) of positive continuous linear
maps summing to `1`, with every Alice effect commuting with every Bob
effect. [02_preliminaries.tex; audit def `commuting_strategy`] -/
structure CommutingStrategy (X Y A B : Type)
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] where
  H : Type u
  [normedAddCommGroup : NormedAddCommGroup H]
  [innerProductSpace : InnerProductSpace ℂ H]
  [completeSpace : CompleteSpace H]
  ψ : H
  ψ_norm : ‖ψ‖ = 1
  E : X → A → H →L[ℂ] H
  F : Y → B → H →L[ℂ] H
  E_pos : ∀ x a, (E x a).IsPositive
  F_pos : ∀ y b, (F y b).IsPositive
  E_sum : ∀ x, (∑ a : A, E x a) = 1
  F_sum : ∀ y, (∑ b : B, F y b) = 1
  commutes : ∀ x y a b, Commute (E x a) (F y b)

attribute [instance] CommutingStrategy.normedAddCommGroup
  CommutingStrategy.innerProductSpace CommutingStrategy.completeSpace

namespace CommutingStrategy

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The correlation table of a strategy:
`p(a, b | x, y) = ⟪ψ, E_x^a F_y^b ψ⟫` (a real number; the inner product is
real because the commuting product of self-adjoint effects is
self-adjoint). [02_preliminaries.tex, success-probability display] -/
noncomputable def correlation (S : CommutingStrategy.{u} X Y A B)
    (x : X) (y : Y) (a : A) (b : B) : ℝ :=
  (⟪S.ψ, S.E x a (S.F y b S.ψ)⟫_ℂ).re

/-- Each Alice–Bob joint effect is a positive operator: a commuting
product of positive operators is positive (`Commute.mul_nonneg`, via the
continuous functional calculus on `H →L[ℂ] H` and the Loewner order). -/
theorem jointEffect_isPositive (S : CommutingStrategy.{u} X Y A B)
    (x : X) (y : Y) (a : A) (b : B) :
    ((S.E x a) ∘L (S.F y b)).IsPositive := by
  have hE : (0 : S.H →L[ℂ] S.H) ≤ S.E x a := by
    rw [ContinuousLinearMap.le_def]
    simpa using S.E_pos x a
  have hF : (0 : S.H →L[ℂ] S.H) ≤ S.F y b := by
    rw [ContinuousLinearMap.le_def]
    simpa using S.F_pos y b
  have hmul := Commute.mul_nonneg hE hF (S.commutes x y a b)
  rw [ContinuousLinearMap.le_def] at hmul
  simp only [sub_zero] at hmul
  exact hmul

/-- The correlation's defining inner product is real: `E_x^a F_y^b` is
symmetric (commuting product of positive operators), so `⟪ψ, EFψ⟫` equals
its own conjugate. Certifies that the `.re` in `correlation` is lossless
(DIFFERENCES.md D7). -/
theorem correlation_inner_im_eq_zero (S : CommutingStrategy.{u} X Y A B)
    (x : X) (y : Y) (a : A) (b : B) :
    (⟪S.ψ, S.E x a (S.F y b S.ψ)⟫_ℂ).im = 0 := by
  have hsym := (S.jointEffect_isPositive x y a b).1
  have h := hsym S.ψ S.ψ
  rw [← Complex.conj_eq_iff_im]
  calc (starRingEnd ℂ) (⟪S.ψ, S.E x a (S.F y b S.ψ)⟫_ℂ)
      = ⟪S.E x a (S.F y b S.ψ), S.ψ⟫_ℂ := inner_conj_symm _ _
    _ = ⟪S.ψ, S.E x a (S.F y b S.ψ)⟫_ℂ := h

theorem correlation_nonneg (S : CommutingStrategy.{u} X Y A B)
    (x : X) (y : Y) (a : A) (b : B) :
    0 ≤ S.correlation x y a b := by
  have h := (S.jointEffect_isPositive x y a b).2 S.ψ
  rw [correlation, ← RCLike.re_to_complex, inner_re_symm]
  simpa [ContinuousLinearMap.reApplyInnerSelf,
    ContinuousLinearMap.comp_apply] using h

/-- Completeness: for every question pair the answers exhaust the state:
`∑_{a,b} p(a,b|x,y) = 1`. -/
theorem correlation_sum (S : CommutingStrategy.{u} X Y A B) (x : X) (y : Y) :
    (∑ a : A, ∑ b : B, S.correlation x y a b) = 1 := by
  classical
  have key : (∑ a : A, ∑ b : B, (⟪S.ψ, S.E x a (S.F y b S.ψ)⟫_ℂ)) = 1 := by
    calc
      (∑ a : A, ∑ b : B, (⟪S.ψ, S.E x a (S.F y b S.ψ)⟫_ℂ))
          = ⟪S.ψ, (∑ a : A, S.E x a) ((∑ b : B, S.F y b) S.ψ)⟫_ℂ := by
            simp [sum_apply, inner_sum, map_sum]
            rw [Finset.sum_comm]
      _ = ⟪S.ψ, S.ψ⟫_ℂ := by rw [S.E_sum, S.F_sum]; simp
      _ = 1 := by
            rw [inner_self_eq_norm_sq_to_K, S.ψ_norm]; norm_num
  calc
    (∑ a : A, ∑ b : B, S.correlation x y a b)
        = (∑ a : A, ∑ b : B, (⟪S.ψ, S.E x a (S.F y b S.ψ)⟫_ℂ)).re := by
          simp only [correlation, Complex.re_sum]
    _ = 1 := by rw [key]; simp

theorem correlation_le_one (S : CommutingStrategy.{u} X Y A B)
    (x : X) (y : Y) (a : A) (b : B) :
    S.correlation x y a b ≤ 1 := by
  classical
  have hsum := S.correlation_sum x y
  have hle : S.correlation x y a b ≤ ∑ a' : A, ∑ b' : B,
      S.correlation x y a' b' := by
    calc S.correlation x y a b
        ≤ ∑ b' : B, S.correlation x y a b' :=
          Finset.single_le_sum (fun b' _ => S.correlation_nonneg x y a b')
            (Finset.mem_univ b)
      _ ≤ ∑ a' : A, ∑ b' : B, S.correlation x y a' b' :=
          Finset.single_le_sum
            (fun a' _ => Finset.sum_nonneg fun b' _ =>
              S.correlation_nonneg x y a' b')
            (Finset.mem_univ a)
  exact hle.trans hsum.le

/-- The trivial strategy on `H = ℂ`: answers a fixed pair deterministically.
Witnesses nonemptiness of the strategy space. -/
noncomputable def trivial [Nonempty A] [Nonempty B] :
    CommutingStrategy.{0} X Y A B := by
  classical
  exact
  { H := ℂ
    ψ := 1
    ψ_norm := by simp
    E := fun _ a => if a = Classical.arbitrary A then 1 else 0
    F := fun _ b => if b = Classical.arbitrary B then 1 else 0
    E_pos := by
      intro x a
      by_cases h : a = Classical.arbitrary A
      · simpa [h] using ContinuousLinearMap.isPositive_one (E := ℂ) (𝕜 := ℂ)
      · simpa [h] using ContinuousLinearMap.isPositive_zero (E := ℂ) (𝕜 := ℂ)
    F_pos := by
      intro y b
      by_cases h : b = Classical.arbitrary B
      · simpa [h] using ContinuousLinearMap.isPositive_one (E := ℂ) (𝕜 := ℂ)
      · simpa [h] using ContinuousLinearMap.isPositive_zero (E := ℂ) (𝕜 := ℂ)
    E_sum := by intro x; simp [Finset.sum_ite_eq']
    F_sum := by intro y; simp [Finset.sum_ite_eq']
    commutes := by
      intro x y a b
      by_cases ha : a = Classical.arbitrary A <;>
        by_cases hb : b = Classical.arbitrary B <;>
          simp [ha, hb, Commute, SemiconjBy] }

end CommutingStrategy

end CommutingRepetition
