/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Tracial/Strategy.lean
-/
/-
# Tracially embeddable strategies

Encoding decision D4: the working object of the entire proof after the
reduction of Section 3. Anchors: 03_tracial_reduction.tex (eqs
lin-density-vector, left-right-actions, tracial-correlation-formula);
audit def `tracially_embeddable`, node 1.1.4.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Tracial.Interface
import MIPRE.Background.Repetition.CommutingRepetition.Game.Strategy
import MIPRE.Background.Repetition.CommutingRepetition.Game.Value

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped BigOperators InnerProductSpace

universe u

/-- A tracially embeddable strategy on alphabets `X, Y, A, B`: a tracial
standard-form algebra `(M, τ)`, a positive density `σ ∈ M₊` with
`τ(σ²) = 1`, Alice POVMs in `M` (acting from the left), and Bob POVMs in
`M` (acting from the right, i.e. already pulled back through the canonical
anti-isomorphism of node 1.1.4).
[03_tracial_reduction.tex; audit def `tracially_embeddable`] -/
structure TracialStrategy (X Y A B : Type)
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] : Type (u + 1) where
  M : StdTracialAlgebra.{u}
  σ : M.A
  σ_pos : IsPosElem σ
  σ_normalized : M.τ (star σ * σ) = 1
  E : X → A → M.A
  F : Y → B → M.A
  E_pos : ∀ x a, IsPosElem (E x a)
  F_pos : ∀ y b, IsPosElem (F y b)
  E_sum : ∀ x, (∑ a : A, E x a) = 1
  F_sum : ∀ y, (∑ b : B, F y b) = 1

namespace TracialStrategy

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The tracial correlation `q(a, b | x, y) = τ(σ* E_x^a σ F_y^b)`.
[03_tracial_reduction.tex, eq tracial-correlation-formula] -/
def correlation (T : TracialStrategy.{u} X Y A B)
    (x : X) (y : Y) (a : A) (b : B) : ℝ :=
  (T.M.τ (star T.σ * (T.E x a * T.σ * T.F y b))).re

/-- The tracial correlation is entrywise nonnegative — Born-rule
positivity through the standard form (`pairing_nonneg`). -/
theorem correlation_nonneg (T : TracialStrategy.{u} X Y A B)
    (x : X) (y : Y) (a : A) (b : B) : 0 ≤ T.correlation x y a b :=
  T.M.pairing_nonneg T.σ (T.E_pos x a) (T.F_pos y b)

/-- Legality: every tracially embeddable strategy is a commuting-operator
strategy — Alice through the left representation, Bob through the right,
on the standard-form Hilbert space, with state `ι σ`. This is what closes
the final contradiction against `omegaCO`. The obligations (positivity
transport via `L_isPositive`/`Rop_isPositive`, unit norm, commutation)
are discharged here. [03_tracial_reduction.tex, eq left-right-actions] -/
noncomputable def toCommutingStrategy (T : TracialStrategy.{u} X Y A B) :
    CommutingStrategy.{u} X Y A B where
  H := T.M.H
  ψ := T.M.ι T.σ
  ψ_norm := by
    have h : (⟪T.M.ι T.σ, T.M.ι T.σ⟫_ℂ) = 1 := by
      rw [T.M.ι_inner, T.σ_normalized]
    have h3 : ‖T.M.ι T.σ‖ ^ 2 = 1 := by
      have h4 := inner_self_eq_norm_sq (𝕜 := ℂ) (T.M.ι T.σ)
      rw [h] at h4
      simpa using h4.symm
    nlinarith [norm_nonneg (T.M.ι T.σ)]
  E x a := T.M.L (T.E x a)
  F y b := T.M.Rop (T.F y b)
  E_pos x a := T.M.L_isPositive (T.E_pos x a)
  F_pos y b := T.M.Rop_isPositive (T.F_pos y b)
  E_sum x := by
    rw [← map_sum, T.E_sum x, map_one]
  F_sum y := by
    simp only [StdTracialAlgebra.Rop]
    rw [← map_sum, ← Finset.op_sum, T.F_sum y, MulOpposite.op_one, map_one]
  commutes x y a b := T.M.LR_commute (T.E x a) (T.F y b)

/-- The commuting strategy induced by a tracial one realizes exactly the
tracial correlation, via the evaluation identity `inner_L_R`. -/
theorem toCommutingStrategy_correlation (T : TracialStrategy.{u} X Y A B) :
    T.toCommutingStrategy.correlation = T.correlation := by
  funext x y a b
  show (⟪T.M.ι T.σ, T.M.L (T.E x a) (T.M.Rop (T.F y b) (T.M.ι T.σ))⟫_ℂ).re
    = T.correlation x y a b
  rw [T.M.inner_L_R]
  rfl

end TracialStrategy

end CommutingRepetition
