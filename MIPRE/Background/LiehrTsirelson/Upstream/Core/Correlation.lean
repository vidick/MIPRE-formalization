/-
Vendored from `lukasliehr/MIPRE` (https://github.com/lukasliehr/MIPRE), a Lean 4 formalization of
Tsirelson's problem, by scripts/vendor-liehr.py; do not edit by hand. Upstream path:
Tsirelson/Core/Correlation.lean, from a snapshot of the `main` branch supplied on 2026-09-25
(archive, no commit recorded). The import prefix `Tsirelson.` is rewritten to
`MIPRE.Background.LiehrTsirelson.Upstream.`; the Lean namespace `Tsirelson` is unchanged, and
nothing outside `MIPRE/Background/LiehrTsirelson/` may name it. Upstream carries no license file;
see README.md.
-/
import MIPRE.Background.LiehrTsirelson.Upstream.Core.FiniteProbability

/-!
# Generic correlations and their finite / square aliases

Canonical owner of the correlation **carrier types**.

Source: `Blueprint/Nodes/B30-Tsirelson-Consequence/Math.tex`,
`def:terminal-correlation-sets` ("the set of arrays `p = (p(a,b | x,y))`"), and
`Blueprint/Nodes/B05-NPA-Core/Math.tex`, `def:n7b` (the game functional
`ℓ_G : ℝ^{n²k²} → ℝ`).

The correlation **sets** `TensorCorrelations`, `TensorCorrelationClosure`,
`CommutingCorrelations` and their square aliases `Cq`, `Cqa`, `Cqc` are owned by
`Tsirelson/Core/Strategy.lean`: they are by specification the ranges of strategy
correlations, so they cannot be introduced before strategies exist.  See
`API_REVIEW.md` §1.1 for the recorded module-boundary deviation from
`LEAN_CORE_AND_BRIDGE.md` §4.
-/

namespace Tsirelson

/-- A generic correlation array `p(a,b | x,y)`, indexed by the two question
alphabets and the two answer alphabets.

This is a *raw* real array: no normalization or positivity is assumed.  Payoff
bounds therefore always carry an explicit realization hypothesis. -/
abbrev Correlation (X Y A B : Type*) : Type _ := X → Y → A → B → ℝ

/-- Correlations on finite index sets given by cardinalities. -/
abbrev FinCorrelation (nX nY nA nB : ℕ) : Type :=
  Correlation (Fin nX) (Fin nY) (Fin nA) (Fin nB)

/-- The square alias used by the terminal statements: `n` questions and `k`
answers for each player. -/
abbrev Corr (n k : ℕ) : Type := FinCorrelation n n k k

section Topology

variable (X Y A B : Type*)

/-- Currying/uncurrying is a homeomorphism between the correlation array and the
plain function space on the product index type. -/
def correlationHomeomorphPi :
    Correlation X Y A B ≃ₜ ((X × Y × A × B) → ℝ) where
  toFun f := fun p => f p.1 p.2.1 p.2.2.1 p.2.2.2
  invFun g := fun x y a b => g (x, y, a, b)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    refine continuous_pi fun p => ?_
    exact ((continuous_apply p.2.2.2).comp
      ((continuous_apply p.2.2.1).comp
        ((continuous_apply p.2.1).comp (continuous_apply p.1))))
  continuous_invFun := by
    refine continuous_pi fun x => continuous_pi fun y => continuous_pi fun a =>
      continuous_pi fun b => ?_
    exact continuous_apply (x, y, a, b)

/-- **CORR-2.**  The topology carried by a finite correlation array is the
Euclidean topology on `ℝ^{|X|·|Y|·|A|·|B|}` used by
`def:terminal-correlation-sets`.

The product (Pi) topology that `Correlation X Y A B` inherits from `ℝ` is
canonically homeomorphic to `EuclideanSpace ℝ (X × Y × A × B)`, so the closure
taken in `Cqa` is literally the Euclidean closure. -/
noncomputable def correlationHomeomorphEuclidean
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] :
    Correlation X Y A B ≃ₜ EuclideanSpace ℝ (X × Y × A × B) :=
  (correlationHomeomorphPi X Y A B).trans
    (EuclideanSpace.equiv (X × Y × A × B) ℝ).toHomeomorph.symm

end Topology

end Tsirelson
