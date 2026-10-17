/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AdaptiveStageBudget.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Introspection_ErrorBounds

/-! # One common quantitative budget for the adaptive stage

The three actual-test estimates share one budget. The malformed-answer
contribution is included in the marginal constant. The replacement loss
has three square roots, and the same recurrence can be used at every level.
-/

namespace MIPRE.Introspection

/-- `e` is ordered-edge count times game failure; `z` and `h` are the
primitive Z and fixed hiding errors. `r` is the remaining CL depth. -/
def adaptiveStageBudget (r : ℕ) (e z h : ℝ) : ℝ :=
  64 * z + (512 * (r : ℝ) ^ 2 + 224) * e + 64 * h

/-- The exact game-value loss from mixing, common-ancilla dilation, and
projective measurement replacement. -/
noncomputable def adaptiveStepLoss (δ : ℝ) : ℝ :=
  2 * Real.sqrt (2 * Real.sqrt (56 * Real.sqrt δ))

/-- An explicit failure recurrence with fixed primitive errors. It records
the loss from each replacement; constructing the strategies is separate. -/
noncomputable def adaptiveFailureBudget (r : ℕ) (edges z h initial : ℝ) : ℕ → ℝ
  | 0 => initial
  | n + 1 => let e := adaptiveFailureBudget r edges z h initial n
      e + adaptiveStepLoss (adaptiveStageBudget r (edges * e) z h)

end MIPRE.Introspection
