/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/Quantum/FiniteConicDuality.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/Quantum/FiniteConicDuality.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

set_option backward.isDefEq.respectTransparency false

/-!
# Finite conic-duality separation lemmas

This module contains the product-space part of the finite-dimensional conic
duality argument used by the Section 9 SDP.  A separator on a product space
`E × ℝ` decomposes into a constraint-coordinate functional and an objective
coefficient.  If the separator is nonnegative on a conic image and negative at
a point with the same constraint coordinate but larger objective coordinate,
then the objective coefficient is negative.  After normalizing by this negative
coefficient one obtains the functional dual bound.

The matrix trace-pairing representation and the paper-form SDP witness remain
in the Section 9 matrix-realization layer.

## References

- `references/ldt-paper/self_improvement.tex`
- `docs/reports/issue-2386-finite-sdp-duality-theorem-design.md`
-/

namespace MIPStarRE.Quantum

/-- The constraint-coordinate part of a separator on a product space. -/
noncomputable def conicSeparatorConstraintFunctional
    {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    (φ : StrongDual ℝ (E × ℝ)) :
    StrongDual ℝ E :=
  φ.comp (ContinuousLinearMap.inl ℝ E ℝ)

/-- The objective-coordinate coefficient of a separator on a product space. -/
noncomputable def conicSeparatorObjectiveCoefficient
    {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    (φ : StrongDual ℝ (E × ℝ)) : ℝ :=
  (φ.comp (ContinuousLinearMap.inr ℝ E ℝ)) (1 : ℝ)

/-- The normalized constraint-coordinate functional associated to a separator.

This definition is useful when the objective-coordinate coefficient is known to
be negative. -/
noncomputable def conicNormalizedSeparatorFunctional
    {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    (φ : StrongDual ℝ (E × ℝ)) :
    StrongDual ℝ E :=
  ((-conicSeparatorObjectiveCoefficient φ)⁻¹) •
    conicSeparatorConstraintFunctional φ

@[simp]
theorem conicNormalizedSeparatorFunctional_apply
    {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    (φ : StrongDual ℝ (E × ℝ)) (y : E) :
    conicNormalizedSeparatorFunctional φ y =
      ((-conicSeparatorObjectiveCoefficient φ)⁻¹) *
        conicSeparatorConstraintFunctional φ y := by
  try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal

end MIPStarRE.Quantum
