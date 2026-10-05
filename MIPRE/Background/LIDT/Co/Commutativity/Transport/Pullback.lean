/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/Transport/Pullback.lean, to the symmetric model of `planning/c6b-plan.md`; not a
vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.Transport.EvaluationSpecialization
public import MIPStarRE.LDT.Commutativity.Transport.Pullback

@[expose] public section

/-!
# Section 11 commutativity: evaluated-slice pullback

Pulling a family on full-slice questions back to evaluated-slice questions preserves the
averaged squared distance, used to transport full-slice bounds: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/Transport/Pullback.lean` in the port of
`planning/c6b-plan.md` (milestone M7, section "Port conventions").

The two lemmas use only the state vector, so they take a vector state `V : VecState K` and joint
operator families, by the rule for same-space quantities; a strategy passes `strategy.state`.
The reindexing equivalence `evaluatedSliceQuestionEquiv` is classical and is imported from the
vendored file, which this file imports alongside its mirrored import.

## Not ported

- `evaluatedSliceQuestionEquiv`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Commutativity

open MIPStarRE.LDT (Parameters FieldModel uniformDistribution avgOver_uniform_equiv_snd)
open MIPStarRE.LDT.Commutativity (EvaluatedSliceQuestion FullSliceQuestion
  fullSliceQuestionOfEvaluatedSlice evaluatedSliceQuestionEquiv)

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Pulling a family on `FullSliceQuestion` back along
`fullSliceQuestionOfEvaluatedSlice` preserves the averaged `sddErrorOp`. -/
lemma sddErrorOp_pullback_fullSliceQuestion_eq
    (params : Parameters) [FieldModel params.q]
    (V : VecState K)
    {Outcome : Type*} [Fintype Outcome]
    (A B : IdxOpFamily (FullSliceQuestion params) Outcome (K →L[ℂ] K)) :
    V.sddErrorOp
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => A (fullSliceQuestionOfEvaluatedSlice params q))
      (fun q => B (fullSliceQuestionOfEvaluatedSlice params q)) =
    V.sddErrorOp (uniformDistribution (FullSliceQuestion params)) A B :=
  avgOver_uniform_equiv_snd (evaluatedSliceQuestionEquiv params)
    (fun xy => V.qSDDOp (A xy) (B xy))

/-- Any `SDDOpRel` bound proved after pulling back along
`fullSliceQuestionOfEvaluatedSlice` descends to `FullSliceQuestion`. -/
lemma sddOpRel_of_pullback_fullSliceQuestion
    (params : Parameters) [FieldModel params.q]
    (V : VecState K)
    {Outcome : Type*} [Fintype Outcome]
    (A B : IdxOpFamily (FullSliceQuestion params) Outcome (K →L[ℂ] K))
    (δ : ℝ) :
    V.SDDOpRel
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => A (fullSliceQuestionOfEvaluatedSlice params q))
      (fun q => B (fullSliceQuestionOfEvaluatedSlice params q))
      δ →
    V.SDDOpRel (uniformDistribution (FullSliceQuestion params)) A B δ :=
  fun ⟨h⟩ => ⟨(sddErrorOp_pullback_fullSliceQuestion_eq params V A B).symm.trans_le h⟩

end MIPRE.LIDT.Co.Commutativity

end
