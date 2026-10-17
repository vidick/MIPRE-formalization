/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/ErrorBounds.lean (statement stub of MIPRE.Introspection.errorProfile_scale_input);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Introspection_ErrorBounds

open MIPRE
open MIPRE.Introspection

theorem MIPRE.Introspection.errorProfile_scale_input {a b c x ε : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hx : 0 ≤ x) (hε : 0 ≤ ε) :
    errorProfile a b x (c * ε) ≤ max 1 (c ^ b) * errorProfile a b x ε := by sorry
