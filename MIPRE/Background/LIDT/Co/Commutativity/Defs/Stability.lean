/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/Defs/Stability.lean, to the symmetric model of `planning/c6b-plan.md`; not a
vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.Defs.Core

@[expose] public section

/-!
# Section 11 commutativity: stability definitions

Reindexing and postprocessing infrastructure used in the full-slice and stability reductions,
including the weighted reindex of raw operator families: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/Defs/Stability.lean` in the port of
`planning/c6b-plan.md` (milestone M7, section "Port conventions").

The stability families are joint operator families of a symmetric strategy
`strategy : SymStrat params.next 𝔓 K`: the vendored placements `leftTensor (ι₂ := ι)` and
`rightTensor (ι₁ := ι)` are `strategy.state.L` and `strategy.state.R`, so each outcome lemma
holds by `rfl`, as in the vendored file. `weightedReindexOpFamily` is generic over any type with
an addition and a multiplication. The weights `CFC.sqrt G_h` are taken in the local
C*-algebra `𝔓` before placement.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Commutativity

open MIPStarRE.LDT (Parameters FieldModel Fq truncatePoint pointHeight)
open MIPStarRE.LDT.Commutativity (EvaluatedSliceQuestion EvaluatedSliceOutcome StabilityOneOutcome
  StabilityTwoOutcome fullSliceQuestionOfEvaluatedSlice evaluateFullSliceOutcomeAtQuestion
  evaluateStabilityOneOutcomeAtQuestion evaluateStabilityTwoOutcomeAtQuestion)
open MIPRE.LIDT.Co.CommutativityPoints (orderedProductOpFamily)

/-- Reindex a raw operator family and append an explicit weight.

The outcome type `β` must retain every coordinate that still appears in
`weight`; otherwise any later postprocessing would sum over an irrelevant fiber
and change the operator by a multiplicity factor. -/
noncomputable def weightedReindexOpFamily
    {α β : Type*} [Fintype β] {R : Type*} [AddCommMonoid R] [Mul R]
    (base : OpFamily α R)
    (reindex : β → α)
    (weight : β → R) :
    OpFamily β R :=
  let body := fun b => base.outcome (reindex b) * weight b
  { outcome := body
    total := ∑ b : β, body b }

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Postprocess the full-slice ordered product at sampled points. -/
noncomputable def evaluatedFromFullSliceProductLeft (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓) :
    IdxOpFamily (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) (K →L[ℂ] K) :=
  fun q =>
    let xy := fullSliceQuestionOfEvaluatedSlice params q
    OpFamily.postprocess (fullSliceProductLeft params strategy family xy)
      (evaluateFullSliceOutcomeAtQuestion params q)

/-- Postprocess the full-slice reversed product at sampled points. -/
noncomputable def evaluatedFromFullSliceProductRight (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓) :
    IdxOpFamily (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) (K →L[ℂ] K) :=
  fun q =>
    let xy := fullSliceQuestionOfEvaluatedSlice params q
    OpFamily.postprocess (fullSliceProductRight params strategy family xy)
      (evaluateFullSliceOutcomeAtQuestion params q)

/-- Internal overlap family from the `G^y` insertion/removal step.

The paper writes the extra factor as the left-register total `G^y = ∑_h G^y_h`.
For the `SDDOpRel` packaging we keep the polynomial `h` explicit and attach the
right-register weight `(G_h^y)^{1/2}` to each outcome. Summing the squared
differences over `h` then recovers the total `G^y` without introducing a fiber
multiplicity from unrelated `g` values.

This is deliberately an overlap estimate family, not the scalar
`clm:g-comm-stability` expression from the paper.  The paper claim keeps the
right-register factor `A_b^{v,y}` and is driven by the boundedness witness
`Z^y`; the overlap family below instead measures a stronger-looking SDD package
against `G_h^y` weights. -/
noncomputable def commDataProcessedGStabilityOneLeft (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    IdxOpFamily (EvaluatedSliceQuestion params) (StabilityOneOutcome params) (K →L[ℂ] K) :=
  fun q =>
    let xy := fullSliceQuestionOfEvaluatedSlice params q
    weightedReindexOpFamily
      (appendRightTotalOpFamily
        ((evaluatedSliceSandwichFirstFactor params strategy family q) :
          OpFamily (EvaluatedSliceOutcome params) (K →L[ℂ] K))
        (strategy.state.L ((fullSliceSecondFactor params family xy).total)))
      (evaluateStabilityOneOutcomeAtQuestion params q)
      (fun ah => strategy.state.R (CFC.sqrt ((G (pointHeight params q.2)).outcome ah.2)))

/-- Internal overlap family after removing the trailing `G^y`, while keeping
the `G_h^y` right-register square-root weight used by the SDD package. -/
noncomputable def commDataProcessedGStabilityOneRight (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    IdxOpFamily (EvaluatedSliceQuestion params) (StabilityOneOutcome params) (K →L[ℂ] K) :=
  fun q =>
    weightedReindexOpFamily
      ((evaluatedSliceSandwichFirstFactor params strategy family q) :
        OpFamily (EvaluatedSliceOutcome params) (K →L[ℂ] K))
      (evaluateStabilityOneOutcomeAtQuestion params q)
      (fun ah => strategy.state.R (CFC.sqrt ((G (pointHeight params q.2)).outcome ah.2)))

/-- Internal overlap family from the `G^x` insertion/removal step.

As for `commDataProcessedGStabilityOneLeft`, this packages an overlap-style SDD
comparison.  The paper's `clm:g-comm-stability2` is a scalar boundedness argument
with right-register factor `A_a^{u,x} A_b^{v,y}` and an internal
`commutativityPoints` transport step. -/
noncomputable def commDataProcessedGStabilityTwoLeft (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    IdxOpFamily (EvaluatedSliceQuestion params) (StabilityTwoOutcome params) (K →L[ℂ] K) :=
  fun q =>
    let xy := fullSliceQuestionOfEvaluatedSlice params q
    weightedReindexOpFamily
      (appendRightTotalOpFamily
        (evaluatedSliceProductLeft params strategy family q)
        (strategy.state.L ((fullSliceFirstFactor params family xy).total)))
      (evaluateStabilityTwoOutcomeAtQuestion params q)
      (fun gb => strategy.state.R (CFC.sqrt ((G (pointHeight params q.1)).outcome gb.1)))

/-- Internal overlap family after removing the trailing `G^x`, while keeping
the `G_g^x` right-register square-root weight used by the SDD package. -/
noncomputable def commDataProcessedGStabilityTwoRight (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    IdxOpFamily (EvaluatedSliceQuestion params) (StabilityTwoOutcome params) (K →L[ℂ] K) :=
  fun q =>
    weightedReindexOpFamily
      (evaluatedSliceProductLeft params strategy family q)
      (evaluateStabilityTwoOutcomeAtQuestion params q)
      (fun gb => strategy.state.R (CFC.sqrt ((G (pointHeight params q.1)).outcome gb.1)))

/-- Expand one outcome of the first `G^y` stability family. -/
lemma commDataProcessedGStabilityOneLeft_outcome
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (q : EvaluatedSliceQuestion params)
    (ah : StabilityOneOutcome params) :
    (commDataProcessedGStabilityOneLeft params strategy family G q).outcome ah =
      (strategy.state.leftPlacedSubMeas
          (evaluatedSliceSandwichRaw params strategy family q)).outcome
          (ah.1, ah.2 (truncatePoint params q.2)) *
        strategy.state.L
          ((fullSliceSecondFactor params family
            (fullSliceQuestionOfEvaluatedSlice params q)).total) *
        strategy.state.R (CFC.sqrt ((G (pointHeight params q.2)).outcome ah.2)) :=
  rfl

/-- Expand one outcome of the second `G^y` stability family. -/
lemma commDataProcessedGStabilityOneRight_outcome
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (q : EvaluatedSliceQuestion params)
    (ah : StabilityOneOutcome params) :
    (commDataProcessedGStabilityOneRight params strategy family G q).outcome ah =
      strategy.state.L
          ((evaluatedSliceSandwichRaw params strategy family q).outcome
              (ah.1, ah.2 (truncatePoint params q.2))) *
        strategy.state.R (CFC.sqrt ((G (pointHeight params q.2)).outcome ah.2)) :=
  rfl

/-- Expand one outcome of the first `G^x` stability family. -/
lemma commDataProcessedGStabilityTwoLeft_outcome
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (q : EvaluatedSliceQuestion params)
    (gb : StabilityTwoOutcome params) :
    (commDataProcessedGStabilityTwoLeft params strategy family G q).outcome gb =
      (evaluatedSliceProductLeft params strategy family q).outcome
          (gb.1 (truncatePoint params q.1), gb.2) *
        strategy.state.L
          ((fullSliceFirstFactor params family
            (fullSliceQuestionOfEvaluatedSlice params q)).total) *
        strategy.state.R (CFC.sqrt ((G (pointHeight params q.1)).outcome gb.1)) :=
  rfl

/-- Expand one outcome of the second `G^x` stability family. -/
lemma commDataProcessedGStabilityTwoRight_outcome
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (q : EvaluatedSliceQuestion params)
    (gb : StabilityTwoOutcome params) :
    (commDataProcessedGStabilityTwoRight params strategy family G q).outcome gb =
      strategy.state.L
          ((orderedProductOpFamily
              (evaluatedSliceFirstFactor params family q)
              (evaluatedSliceSecondFactor params family q)).outcome
              (gb.1 (truncatePoint params q.1), gb.2)) *
        strategy.state.R (CFC.sqrt ((G (pointHeight params q.1)).outcome gb.1)) :=
  rfl

end MIPRE.LIDT.Co.Commutativity

end
