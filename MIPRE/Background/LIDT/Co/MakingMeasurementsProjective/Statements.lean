/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122),
MIPStarRE/LDT/MakingMeasurementsProjective/Statements.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Test.Defs
public import MIPRE.Background.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.Defs

@[expose] public section

/-!
# Section 5 — Statements

The conclusion structures of the steps of rounding a measurement to a projective one, and the
completion of a submeasurement by a fresh outcome: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/Statements.lean` in the port of
`planning/c6b-plan.md` (milestone M8, section "Port conventions").

The vendored state of these statements lives on one space (the input state, or a state tensored
with an ancilla), so by the same-space rule they are `VecState` statements about joint operators
in `K →L[ℂ] K`: the vendored `AlmostProjMeasStatement ψ A ζ` is
`AlmostProjMeasStatement V A ζ` for a vector state `V`. The completion `optionCompletion` mentions
no state and is generic over an ordered `⋆`-ring, so it serves the local algebra `𝔓` of a
symmetric model and the joint operators alike; it was written in milestone M2 for Theorem G
(`Co/Doubling/Orthonormalization.lean`) and lives here, its vendored home. The vendored file
imports `MakingMeasurementsProjective/Defs.lean`, whose error functions are classical; this file
imports it for them, so that the ports downstream find them through it.

## Not ported

- `OneMeasNaimarkLemma`: matrix-only (a dilation of a matrix submeasurement to a larger finite
  space); no consumer in the model route, which orthonormalizes inside the algebra (T1).
- `NaimarkStatement`: matrix-only (normalized traces of the dilated densities); no consumer.
- `naimarkProductExtensionDensity`: matrix-only (a density matrix on four finite registers); no
  consumer.
- `naimarkProductExtensionEquiv`: matrix-only (a reindexing of the four finite registers); no
  consumer.
- `naimarkProductExtensionDensity_eq_reindex_opTensor`: matrix-only (Kronecker reindexing); no
  consumer.
- `naimarkProductExtensionDensity_nonneg`: matrix-only (PSD density); no consumer.
- `naimarkProductExtensionState`: matrix-only (a state on `FiniteHilbertSpace` registers); no
  consumer.
- `naimarkProductExtensionState_density`: matrix-only (density); no consumer.
- `naimarkProductExtensionState_isNormalized`: matrix-only (normalized trace); no consumer.
- `NaimarkTensorProductCorrelationData`: matrix-only (`FiniteHilbertSpace` ancillas, densities,
  Kronecker products); no consumer.
- `NaimarkTensorProductCorrelationStatement`: matrix-only (as its data); no consumer.
- `SpectralTruncationStatement`: no producer; it is the conclusion of the spectral-truncation
  step of the finite-dimensional route (a step-function calculus legal only on finite spectrum),
  which the orthonormalization tier T1 replaces.
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.MakingMeasurementsProjective

open MIPStarRE.LDT (uniformDistribution)

/-! ### Orthonormalization statements -/

section Statements

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Paper origin: `references/ldt-paper/preliminaries.tex:348-376`
(`\label{def:approx_delta}`) and `references/ldt-paper/orthonormalization.tex`
§4 prose around `\label{lem:projective-non-measurement}` (lines 414-538).

Conclusion of the intermediate almost-projective step: a measurement which is
ζ-strongly self-consistent and ζ-self-close in the state-dependent distance,
and whose effects satisfy `Σₐ (Aₐ − Aₐ²) ≤ ζ`. -/
structure AlmostProjMeasStatement {Outcome : Type*} [Fintype Outcome]
    (V : VecState K) (A : Measurement Outcome (K →L[ℂ] K)) (ζ : ℝ) : Prop where
  /-- `A` is `ζ`-strongly self-consistent. -/
  strongSelfConsistency :
    V.SSCRel (uniformDistribution Unit) (constSubMeasFamily A.toSubMeas) ζ
  /-- `A` is `2ζ`-close to itself in the state-dependent distance. -/
  selfDistance :
    V.SDDRel (uniformDistribution Unit) (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily A.toSubMeas) (2 * ζ)
  /-- `∑ₐ ev(Aₐ − Aₐ²) ≤ ζ`. -/
  sourceAlmostProjective :
    ∑ a, V.ev (A.outcome a - A.outcome a * A.outcome a) ≤ ζ

/-- Paper origin: `references/ldt-paper/orthonormalization.tex:414-538`
(`\label{lem:projective-non-measurement}`).

Conclusion of the rounding-to-projective step: a genuine projective
sub-measurement `P` which is `ζ`-close to the input measurement `A` in the
state-dependent distance. -/
structure RoundedProjMeasStatement {Outcome : Type*} [Fintype Outcome]
    (V : VecState K) (A : Measurement Outcome (K →L[ℂ] K))
    (P : ProjSubMeas Outcome (K →L[ℂ] K)) (ζ : ℝ) : Prop where
  /-- `P` is `ζ`-close to `A` in the state-dependent distance. -/
  closeness :
    V.SDDRel (uniformDistribution Unit) (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily P.toSubMeas) ζ

end Statements

/-! ### The completion of a submeasurement -/

section Completion

variable {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
  {Outcome : Type*} [Fintype Outcome]

/-- **The completion of a submeasurement** by the residual `1 − ∑ₐ Aₐ` at the fresh outcome
`none` (the vendored `optionCompletion`, over an ordered `⋆`-ring).

This is the completion used in the paper's proof of `thm:orthonormalization`: the original
outcomes are kept as `some a`, and the missing mass is recorded separately at `none`. -/
def optionCompletion (A : SubMeas Outcome R) : Measurement (Option Outcome) R where
  outcome o := o.elim (1 - A.total) A.outcome
  total := 1
  outcome_pos
    | none => sub_nonneg.2 A.total_le_one
    | some a => A.outcome_pos a
  sum_eq_total := (Fintype.sum_option _).trans <|
    (congrArg (1 - A.total + ·) A.sum_eq_total).trans (sub_add_cancel 1 A.total)
  total_le_one := le_rfl
  total_eq_one := rfl

/-- The outcome `none` of the completion is the residual `1 − ∑ₐ Aₐ`. -/
@[simp] theorem optionCompletion_outcome_none (A : SubMeas Outcome R) :
    (optionCompletion A).outcome none = 1 - A.total :=
  rfl

/-- The outcomes `some a` of the completion are those of the submeasurement. -/
@[simp] theorem optionCompletion_outcome_some (A : SubMeas Outcome R) (a : Outcome) :
    (optionCompletion A).outcome (some a) = A.outcome a :=
  rfl

end Completion

end MIPRE.LIDT.Co.MakingMeasurementsProjective

end
