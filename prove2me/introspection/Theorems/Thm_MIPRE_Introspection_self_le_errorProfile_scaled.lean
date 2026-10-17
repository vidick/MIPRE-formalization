/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/RestrictedErrorBounds.lean (statement stub of MIPRE.Introspection.self_le_errorProfile_scaled);
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

theorem MIPRE.Introspection.self_le_errorProfile_scaled {a b c x ε : ℝ}
    (ha : 1 ≤ a) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hc : 1 ≤ c)
    (hx : 1 ≤ x) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ε ≤ errorProfile a b x (c * ε) := by sorry
