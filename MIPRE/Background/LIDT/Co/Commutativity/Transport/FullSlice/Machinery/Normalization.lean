/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/Transport/FullSlice/Machinery/Normalization.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.Transport.FullSlice.Averages

@[expose] public section

/-!
# Full-slice normalization and self-consistency machinery

Normalization-condition bounds, evaluated projective submeasurements, and full-slice and
evaluated-slice self-consistency estimates used by the scalar-to-tensor comparison: the
counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/Transport/FullSlice/Machinery/Normalization.lean`
in the port of `planning/c6b-plan.md` (milestone M7, section "Port conventions").

`normalizationCondition_sandwich_bound` and `evaluateAtProjSubMeas` are stated over any
C*-algebra with its order, so they serve the local algebra `𝔓` and the joint operators
`K →L[ℂ] K` alike. The two placed normalization bounds take the model `(S : SymModel 𝔓 K)` as
their first explicit argument, the placement lemma rule of M3: the vendored `leftTensor (ι₂ := ι)`
is `S.L`, and `ᴴ` is `star`. The self-consistency bounds are stated with `strategy.state.qSDDCore`
on `strategy.state.L` and `strategy.state.R`; they read the average of a function of one
coordinate as the average over that coordinate (`avgOver_uniform_fst`, `avgOver_uniform_snd`,
the classical `avgOver_xEvaluatedQuestion_to_pointNext`), where the vendored proofs restate it
in a `calc`.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Commutativity

open MIPStarRE.LDT (Parameters FieldModel Point Fq appendPoint truncatePoint_appendPoint
  pointHeight_appendPoint avgOver avgOver_congr avgOver_uniform_fst avgOver_uniform_snd
  uniformDistribution)
open MIPStarRE.LDT.Commutativity (EvaluatedSliceQuestion FullSliceQuestion
  avgOver_xEvaluatedQuestion_to_pointNext)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Paper `lem:normalization-condition` (`commutativity-G.tex` line 309).

For a sub-measurement `P` and projective sub-measurement `Q`, the sandwiched
family `C_{a,b} = Q_b · P_a · Q_b` satisfies the `closenessOfIP` normalization
condition `∑_a (∑_b C_{a,b}) (∑_b C_{a,b})^* ≤ I`. -/
lemma normalizationCondition_sandwich_bound
    {α β : Type*} [Fintype α] [Fintype β]
    (P : SubMeas α 𝔓) (Q : ProjSubMeas β 𝔓) :
    ∑ a : α,
        (∑ b : β, Q.outcome b * P.outcome a * Q.outcome b) *
          star (∑ b : β, Q.outcome b * P.outcome a * Q.outcome b) ≤ 1 :=
  (normalizationConditionSquareFamily P Q).total_le_one

/-- Evaluate a polynomial-indexed projective submeasurement at a point, retaining
projectivity of the postprocessed outcomes.

This reuses the shared postprocessing projectivity lemma rather than
reproving the orthogonality/postprocessing infrastructure locally. -/
noncomputable def evaluateAtProjSubMeas
    (params : Parameters) [FieldModel params.q] (u : Point params)
    (P : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) : ProjSubMeas (Fq params) 𝔓 where
  toSubMeas := evaluateAt params u P.toSubMeas
  proj := ProjSubMeas.postprocess_outcome_proj P (fun g => g u)

/-- Placed form of `normalizationCondition_sandwich_bound`, used as the
`C`-normalization hypothesis in `closenessOfIP`.

For `C_{a,b} = Q_b P_a Q_b ⊗ I`, the square-sum condition on the joint operators follows by
applying the placement `S.L` to paper `lem:normalization-condition`. -/
lemma leftTensor_normalizationCondition_sandwich_bound
    {α β : Type*} [Fintype α] [Fintype β]
    (S : SymModel 𝔓 K) (P : SubMeas α 𝔓) (Q : ProjSubMeas β 𝔓) :
    ∑ a : α,
        (∑ b : β, S.L (Q.outcome b * P.outcome a * Q.outcome b)) *
          star (∑ b : β, S.L (Q.outcome b * P.outcome a * Q.outcome b)) ≤ 1 := by
  simp only [S.leftTensor_finset_sum, S.leftTensor_conjTranspose, S.leftTensor_mul_leftTensor]
  exact S.leftTensor_le_one (normalizationCondition_sandwich_bound P Q)

/-- Adjoint-side placed normalization condition used with `closenessOfIPAdjoint`. -/
lemma leftTensor_normalizationCondition_sandwich_adjoint_bound
    {α β : Type*} [Fintype α] [Fintype β]
    (S : SymModel 𝔓 K) (P : SubMeas α 𝔓) (Q : ProjSubMeas β 𝔓) :
    ∑ a : α,
        star (∑ b : β, S.L (Q.outcome b * P.outcome a * Q.outcome b)) *
          (∑ b : β, S.L (Q.outcome b * P.outcome a * Q.outcome b)) ≤ 1 := by
  simp only [S.leftTensor_finset_sum, S.leftTensor_conjTranspose, S.leftTensor_mul_leftTensor]
  exact S.leftTensor_le_one (normalizationConditionAdjointSquareFamily P Q).total_le_one

/-- Full-slice strong self-consistency pulled to the first coordinate of a
full-slice question.

This is the `A^x_g = G^x_g ⊗ I`, `B^x_g = I ⊗ G^x_g` input for the
`closenessOfIP` applications in paper `commutativity-G.tex` line 334. -/
lemma fullSlice_selfConsistency_fst_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (zeta : ℝ)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    avgOver (uniformDistribution (FullSliceQuestion params))
        (fun xy =>
          strategy.state.qSDDCore
            (fun g : MIPStarRE.LDT.Polynomial params =>
              strategy.state.L ((family.meas xy.1).toSubMeas.outcome g))
            (fun g : MIPStarRE.LDT.Polynomial params =>
              strategy.state.R ((family.meas xy.1).toSubMeas.outcome g))) ≤
      zeta :=
  (avgOver_uniform_fst (β := Fq params) fun x =>
    strategy.state.qSDD
      ((IdxSubMeas.liftLeft strategy.state (IdxProjSubMeas.toIdxSubMeas family.meas)) x)
      ((IdxSubMeas.liftRight strategy.state (IdxProjSubMeas.toIdxSubMeas family.meas)) x)).trans_le
    hself.sliceSelfConsistency.squaredDistanceBound

/-- Full-slice strong self-consistency pulled to the second coordinate of a
full-slice question. -/
lemma fullSlice_selfConsistency_snd_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (zeta : ℝ)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    avgOver (uniformDistribution (FullSliceQuestion params))
        (fun xy =>
          strategy.state.qSDDCore
            (fun h : MIPStarRE.LDT.Polynomial params =>
              strategy.state.L ((family.meas xy.2).toSubMeas.outcome h))
            (fun h : MIPStarRE.LDT.Polynomial params =>
              strategy.state.R ((family.meas xy.2).toSubMeas.outcome h))) ≤
      zeta :=
  (avgOver_uniform_snd (α := Fq params) fun y =>
    strategy.state.qSDD
      ((IdxSubMeas.liftLeft strategy.state (IdxProjSubMeas.toIdxSubMeas family.meas)) y)
      ((IdxSubMeas.liftRight strategy.state (IdxProjSubMeas.toIdxSubMeas family.meas)) y)).trans_le
    hself.sliceSelfConsistency.squaredDistanceBound

/-- Evaluated-slice point self-consistency pulled to the second coordinate of an
evaluated-slice question. -/
lemma evaluatedSlice_selfConsistency_snd_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (zeta : ℝ)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          strategy.state.qSDDCore
            (fun b : Fq params =>
              strategy.state.L ((evaluatedSliceSecondFactor params family q).outcome b))
            (fun b : Fq params =>
              strategy.state.R ((evaluatedSliceSecondFactor params family q).outcome b))) ≤
      zeta :=
  (avgOver_uniform_snd (α := Point params.next) fun u =>
    strategy.state.qSDD
      (evaluatedPointFamilyLeft strategy.state params family u)
      (evaluatedPointFamilyRight strategy.state params family u)).trans_le
    (evaluatedPointFamily_selfConsistency_of_stronglySelfConsistent
      params strategy family zeta hself).squaredDistanceBound

/-- Point-level self-consistency pulled to mixed `(u, x, y)` data for the already
x-evaluated first coordinate. -/
lemma xEvaluated_selfConsistency_fst_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (zeta : ℝ)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    avgOver (uniformDistribution (Point params × FullSliceQuestion params))
        (fun ux =>
          strategy.state.qSDDCore
            (fun a : Fq params => strategy.state.L
              ((evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)).outcome a))
            (fun a : Fq params => strategy.state.R
              ((evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)).outcome a))) ≤
      zeta := by
  let f : Point params.next → ℝ := fun w =>
    strategy.state.qSDD
      (evaluatedPointFamilyLeft strategy.state params family w)
      (evaluatedPointFamilyRight strategy.state params family w)
  have hf : ∀ ux : Point params × FullSliceQuestion params,
      strategy.state.qSDDCore
          (fun a : Fq params => strategy.state.L
            ((evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)).outcome a))
          (fun a : Fq params => strategy.state.R
            ((evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)).outcome a)) =
        f (appendPoint params ux.1 ux.2.1) := fun ux => by
    simp only [f, evaluatedPointFamilyLeft, evaluatedPointFamilyRight, evaluatedPointFamily,
      IdxPolyFamily.evaluatedAtNextPoint, truncatePoint_appendPoint, pointHeight_appendPoint]
    rfl
  rw [avgOver_congr _ _ _ hf, avgOver_xEvaluatedQuestion_to_pointNext params f]
  exact (evaluatedPointFamily_selfConsistency_of_stronglySelfConsistent
    params strategy family zeta hself).squaredDistanceBound

end MIPRE.LIDT.Co.Commutativity

end
