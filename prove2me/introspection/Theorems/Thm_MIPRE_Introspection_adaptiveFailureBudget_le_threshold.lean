/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AdaptiveIterationBudget.lean (statement stub of MIPRE.Introspection.adaptiveFailureBudget_le_threshold);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Introspection_ErrorBounds
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveStageBudget
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveIterationBudget

open MIPRE
open MIPRE.Introspection

theorem MIPRE.Introspection.adaptiveFailureBudget_le_threshold (r N : ℕ) {edges z h initial : ℝ}
    (hE : 0 ≤ edges) (hi : initial ≤ adaptiveSmallThreshold r edges N)
    (hz : z ≤ adaptiveSmallThreshold r edges N)
    (hh : h ≤ adaptiveSmallThreshold r edges N) :
    ∀ n, n ≤ N → adaptiveFailureBudget r edges z h initial n ≤
      adaptiveSmallThreshold r edges (N - n) := by sorry
