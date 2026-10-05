/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
MainInductionStep/Theorems/InductionParameterBounds/SelfImprovement.lean, to the symmetric model
of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.MainInductionStep.Theorems.InductionParameterBounds.Preliminaries
public import MIPStarRE.LDT.MainInductionStep.Theorems.InductionParameterBounds.SelfImprovement

@[expose] public section

/-!
# Section 6 — Self-improvement error bounds

The scalar consequences of the non-vacuous hypothesis `selfImprovementInInductionError ≤ 1` for a
good strategy, namely the bounds `eps ≤ 1` and `delta ≤ 1` used before applying self-improvement
inside the induction step. This is the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/MainInductionStep/Theorems/InductionParameterBounds/SelfImprovement.lean`
in the port of `planning/c6b-plan.md` (milestone M12, section "Port conventions").

## Translation

Two declarations read a strategy and are ported, for a good `SymStrat params.next 𝔓 K`
(`Co/Test/StrategyCore.lean`). A strategy enters only through the nonnegativity of `eps` and
`delta` that its `IsGood` gives (`eps_nonneg_of_isGood`, `delta_nonneg_of_isGood` of
`Co/Test/StrategyFailures.lean`). No lemma of the file has a swap, density or normalization
hypothesis, so none is dropped, and no declaration takes a new hypothesis. The other two
declarations are arithmetic on the classical error function `selfImprovementInInductionError`:
this file imports the vendored file and names them through an explicit
`open MIPStarRE.LDT.MainInductionStep (…)` list. The vendored file's only import is the vendored
`InductionParameterBounds/Preliminaries`, which the ported `Preliminaries` already imports, so
importing it adds no operator content. The vendored file-wide `respectTransparency false` is not
needed: the file sets no option.

## Proofs that differ from the vendored ones

The scaled bound `3000 · m_next · x^{1/32} ≤ selfImprovementInInductionError params.next …` is
proved by `mul_le_mul_of_nonneg_left` on the unfolded error, with `linarith` for the summand
comparison, in place of the vendored `simpa` with commutativity lemmas around
`selfImprovementInInduction_scaled_component_le`.

## Not ported

- `selfImprovementInInduction_scaled_component_le`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `blueprint/src/chapter/ch10_induction.tex`
- `references/ldt-paper/inductive_step.tex`
-/

namespace MIPRE.LIDT.Co.MainInductionStep

open MIPStarRE.LDT (Parameters FieldModel)
open MIPStarRE.LDT.MainInductionStep (selfImprovementInInductionError le_one_of_rpow_le_one)

/-- Upstream keeps this helper `private` since its Lean-module port (`LionSR/MIPStarRE` at
`5fc363b`); the port carries its own copy, with upstream's proof. -/
theorem le_one_of_selfImprovementInInductionError_le_one_of_scaled_bound (params : Parameters)
    {eps delta gamma x : ℝ} (hzeta_le : selfImprovementInInductionError params.next eps delta gamma ≤ 1)
    (hscaled_le : 3000 * (params.next.m : ℝ) * Real.rpow x (1 / (32 : ℝ)) ≤
      selfImprovementInInductionError params.next eps delta gamma) :
    x ≤ 1 := by
  have hcoef_ge_one : (1 : ℝ) ≤ 3000 * (params.next.m : ℝ) := by
    have hm_one : (1 : ℝ) ≤ (params.next.m : ℝ) := by exact_mod_cast params.next.hm
    nlinarith
  have hroot_le_one : Real.rpow x (1 / (32 : ℝ)) ≤ 1 := by
    by_contra hroot
    have hroot_gt : 1 < Real.rpow x (1 / (32 : ℝ)) := lt_of_not_ge hroot
    have : 1 < 3000 * (params.next.m : ℝ) * Real.rpow x (1 / (32 : ℝ)) := by nlinarith [hcoef_ge_one]
    linarith [hscaled_le, hzeta_le]
  exact le_one_of_rpow_le_one (by positivity) hroot_le_one
open MIPRE.LIDT.Co (SymStrat eps_nonneg_of_isGood delta_nonneg_of_isGood)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Internal helper: under `selfImprovementInInductionError ≤ 1`, the axis-parallel error
`eps ≤ 1`.

Exposed for cross-module use in `AvgSliceErrors` and `PastingAssembly`. -/
lemma eps_le_one_of_selfImprovementInInductionError_le_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    {eps delta gamma : ℝ}
    (hgood : strategy.IsGood eps delta gamma)
    (hzeta_le : selfImprovementInInductionError params.next eps delta gamma ≤ 1) :
    eps ≤ 1 := by
  have hdelta : 0 ≤ Real.rpow delta (1 / (32 : ℝ)) :=
    Real.rpow_nonneg (delta_nonneg_of_isGood params.next strategy hgood) _
  have hratio : 0 ≤ Real.rpow ((params.d : ℝ) / (params.q : ℝ)) (1 / (32 : ℝ)) :=
    Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _
  refine le_one_of_selfImprovementInInductionError_le_one_of_scaled_bound params hzeta_le ?_
  show 3000 * (params.next.m : ℝ) * Real.rpow eps (1 / (32 : ℝ)) ≤
    3000 * (params.next.m : ℝ) *
      (Real.rpow eps (1 / (32 : ℝ)) + Real.rpow delta (1 / (32 : ℝ)) +
        Real.rpow ((params.d : ℝ) / (params.q : ℝ)) (1 / (32 : ℝ)))
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- Internal helper: under `selfImprovementInInductionError ≤ 1`,
the self-consistency error `delta ≤ 1`.

Exposed for cross-module use in `AvgSliceErrors` and `PastingAssembly`. -/
lemma delta_le_one_of_selfImprovementInInductionError_le_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    {eps delta gamma : ℝ}
    (hgood : strategy.IsGood eps delta gamma)
    (hzeta_le : selfImprovementInInductionError params.next eps delta gamma ≤ 1) :
    delta ≤ 1 := by
  have heps : 0 ≤ Real.rpow eps (1 / (32 : ℝ)) :=
    Real.rpow_nonneg (eps_nonneg_of_isGood params.next strategy hgood) _
  have hratio : 0 ≤ Real.rpow ((params.d : ℝ) / (params.q : ℝ)) (1 / (32 : ℝ)) :=
    Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _
  refine le_one_of_selfImprovementInInductionError_le_one_of_scaled_bound params hzeta_le ?_
  show 3000 * (params.next.m : ℝ) * Real.rpow delta (1 / (32 : ℝ)) ≤
    3000 * (params.next.m : ℝ) *
      (Real.rpow eps (1 / (32 : ℝ)) + Real.rpow delta (1 / (32 : ℝ)) +
        Real.rpow ((params.d : ℝ) / (params.q : ℝ)) (1 / (32 : ℝ)))
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

end MIPRE.LIDT.Co.MainInductionStep

end
