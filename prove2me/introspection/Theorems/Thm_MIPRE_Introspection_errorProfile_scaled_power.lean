/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/ErrorBounds.lean (statement stub of MIPRE.Introspection.errorProfile_scaled_power);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Introspection_ErrorBounds

open MIPRE
open MIPRE.Introspection

theorem MIPRE.Introspection.errorProfile_scaled_power {C a b c r x ε : ℝ}
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hc : 0 ≤ c) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hx : 1 ≤ x) (hε : 0 ≤ ε) :
    C * (errorProfile a b x (c * ε)) ^ r ≤
      errorProfile (powerCoefficient (C * (max 1 (c ^ b)) ^ r) a r) (b * r) x ε := by sorry
