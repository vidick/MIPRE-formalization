/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AdaptivePowerBudget.lean (statement stub of MIPRE.Introspection.one_le_soundness_power_of_threshold_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Introspection_ErrorBounds
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveStageBudget
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveIterationBudget
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePowerBudget

open MIPRE
open MIPRE.Introspection

theorem MIPRE.Introspection.one_le_soundness_power_of_threshold_le (r n : ℕ) {edges t : ℝ}
    (hE : 0 ≤ edges) (ht : adaptiveSmallThreshold r edges n ≤ t) :
    1 ≤ adaptiveSoundnessCoefficient r edges n * iteratedRoot (3 * n) t := by sorry
