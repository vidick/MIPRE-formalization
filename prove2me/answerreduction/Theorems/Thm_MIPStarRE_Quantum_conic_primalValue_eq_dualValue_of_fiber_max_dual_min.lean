/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/Quantum/FiniteConicDuality.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/Quantum/FiniteConicDuality.lean (statement stub of MIPStarRE.Quantum.conic_primalValue_eq_dualValue_of_fiber_max_dual_min);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteConicDuality

open MIPStarRE
open MIPStarRE.Quantum
set_option backward.isDefEq.respectTransparency false

theorem MIPStarRE.Quantum.conic_primalValue_eq_dualValue_of_fiber_max_dual_min
    {F : Type*}
    [TopologicalSpace F] [AddCommGroup F] [IsTopologicalAddGroup F]
    [Module ℝ F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
    (C : ProperCone ℝ (F × ℝ))
    {y : F} {p d : ℝ}
    (hprimalMem : (y, p) ∈ C)
    (hprimalMax : ∀ {t : ℝ}, (y, t) ∈ C → t ≤ p)
    (hdualMin : ∀ ψ : StrongDual ℝ F,
      (∀ z ∈ C, z.2 ≤ ψ z.1) → d ≤ ψ y)
    (hweak : p ≤ d) :
    p = d := by sorry
