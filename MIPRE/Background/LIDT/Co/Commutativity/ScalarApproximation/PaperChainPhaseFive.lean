/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/ScalarApproximation/PaperChainPhaseFive.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.ScalarApproximation.PaperChainBasic.Normalization
public import MIPRE.Background.LIDT.Co.Commutativity.ScalarApproximation.PaperChainBasic.PointSwap
public import MIPRE.Background.LIDT.Co.Commutativity.ScalarApproximation.PaperChainBasic.Reindexing
public import MIPRE.Background.LIDT.Co.Commutativity.GCommStability.Scalar.RawSecond

@[expose] public section

/-!
# Section 11 commutativity: the phase-five endpoint of the evaluated-slice paper chain

The paper line-87 removal endpoint and the finite reindexing to the raw scalar
`G`-commutativity stability defect: the counterpart of
`Commutativity/ScalarApproximation/PaperChainPhaseFive.lean` under
`MIPRE/Background/LIDT/MIPStarRE/LDT/` in the port of `planning/c6b-plan.md` (milestone M7,
section "Port conventions").

The endpoints and defects are real expectations `strategy.state.ev (strategy.state.L … *
strategy.state.R …)` on the symmetric model of the strategy, with the vendored arguments
unchanged. `phaseFivePaper_fiber_sum_ev` takes the symmetric model `S` where the vendored lemma
takes the state `ψ`, in the same position.

The vendored proof of `evaluatedSlice_phaseFivePaper_term_diff` computes with Kronecker products
and `Matrix.smul_kronecker`; here it is `mul_sub`, the keystone's `leftTensor_sub` and `ev_sub`,
and `ring` on the scalars. The fiber collapse is `Finset.sum_fiberwise` after expanding the
fiber sum into the left placement, and the last step of the reindexing holds by definitional
equality, `evaluatedSlicePointMeas` being the strategy's point measurement.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Commutativity

open MIPStarRE.LDT (Parameters FieldModel Point Fq appendPoint pointHeight avgOver avgOver_congr
  avgOver_sub avgOver_uniform_prod avgOver_uniform_comm uniformDistribution)
open MIPStarRE.LDT.Commutativity (EvaluatedSliceQuestion)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ### Paper-faithful phase-five removal after the right-register swap -/

/-- Paper line-87 endpoint after removing the trailing `G^x.total`.

At question `q = ((u,x),(v,y))` and outcome `(a,b)`, this is
`G^{u,x}_a G^{v,y}_b ⊗ A^{u,x}_a A^{v,y}_b`. -/
noncomputable def evaluatedSlicePhaseFivePaperRemoved
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (q : EvaluatedSliceQuestion params) : ℝ :=
  ∑ a : Fq params, ∑ b : Fq params,
    strategy.state.ev
      (strategy.state.L
          (((evaluatedSliceFirstFactor params family q).outcome a) *
            ((evaluatedSliceSecondFactor params family q).outcome b)) *
        strategy.state.R
          (((evaluatedSlicePointMeas params strategy q.1).outcome a) *
            ((evaluatedSlicePointMeas params strategy q.2).outcome b)))

/-- Paper line 101 endpoint after reversing the first `eq:add-an-a` insertion. -/
noncomputable def evaluatedSlicePhaseSixFirstReverse
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (q : EvaluatedSliceQuestion params) : ℝ :=
  ∑ a : Fq params, ∑ b : Fq params,
    strategy.state.ev
      (strategy.state.L
          (((evaluatedSliceFirstFactor params family q).outcome a) *
            ((evaluatedSliceFirstFactor params family q).outcome a) *
            ((evaluatedSliceSecondFactor params family q).outcome b)) *
        strategy.state.R
          ((evaluatedSlicePointMeas params strategy q.2).outcome b))

/-- Paper line 102 endpoint after simplifying the first-coordinate projector. -/
noncomputable def evaluatedSlicePhaseSixFirstRemoved
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (q : EvaluatedSliceQuestion params) : ℝ :=
  ∑ a : Fq params, ∑ b : Fq params,
    strategy.state.ev
      (strategy.state.L
          (((evaluatedSliceFirstFactor params family q).outcome a) *
            ((evaluatedSliceSecondFactor params family q).outcome b)) *
        strategy.state.R
          ((evaluatedSlicePointMeas params strategy q.2).outcome b))

/-- Paper line 104 endpoint `eq:gonna-cite-this-in-just-a-bit`. -/
noncomputable def evaluatedSlicePhaseSevenGonnaCite
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (q : EvaluatedSliceQuestion params) : ℝ :=
  ∑ a : Fq params, ∑ b : Fq params,
    strategy.state.ev
      (strategy.state.L
        (((evaluatedSliceFirstFactor params family q).outcome a) *
          ((evaluatedSliceSecondFactor params family q).outcome b) *
          ((evaluatedSliceSecondFactor params family q).outcome b)))

/-- Paper line 118 endpoint after moving the second factor to the right register. -/
noncomputable def evaluatedSlicePhaseEightTailRight
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (q : EvaluatedSliceQuestion params) : ℝ :=
  ∑ a : Fq params, ∑ b : Fq params,
    strategy.state.ev
      (strategy.state.L
          (((evaluatedSliceFirstFactor params family q).outcome a) *
            ((evaluatedSliceSecondFactor params family q).outcome b)) *
        strategy.state.R
          ((evaluatedSliceSecondFactor params family q).outcome b))

/-- Ordered missing-mass defect for the paper phase-five removal.

This is the defect before swapping the two right-register point measurements:
`G^{u,x}_a G^{v,y}_b (1-G^x) ⊗ A^{u,x}_a A^{v,y}_b`. -/
noncomputable def evaluatedSlicePhaseFivePaperOrderedDefect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (q : EvaluatedSliceQuestion params) : ℝ :=
  ∑ a : Fq params, ∑ b : Fq params,
    strategy.state.ev
      (strategy.state.L
          (((evaluatedSliceFirstFactor params family q).outcome a) *
            ((evaluatedSliceSecondFactor params family q).outcome b) *
            (1 - (G (pointHeight params q.1)).total)) *
        strategy.state.R
          (((evaluatedSlicePointMeas params strategy q.1).outcome a) *
            ((evaluatedSlicePointMeas params strategy q.2).outcome b)))

/-- Swapped missing-mass defect for the paper phase-five removal.

After the right-register point swap, this reindexes to
`gCommStabilityTwoRawScalarDefect`: the right register is
`A^{v,y}_b A^{u,x}_a`. -/
noncomputable def evaluatedSlicePhaseFivePaperSwappedDefect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (q : EvaluatedSliceQuestion params) : ℝ :=
  ∑ a : Fq params, ∑ b : Fq params,
    strategy.state.ev
      (strategy.state.L
          (((evaluatedSliceFirstFactor params family q).outcome a) *
            ((evaluatedSliceSecondFactor params family q).outcome b) *
            (1 - (G (pointHeight params q.1)).total)) *
        strategy.state.R
          (((evaluatedSlicePointMeas params strategy q.2).outcome b) *
            ((evaluatedSlicePointMeas params strategy q.1).outcome a)))

/-- Pointwise algebra for the paper phase-five removal.

The swapped phase-four endpoint contains the left factor
`A_a B_b G^x.total`; subtracting the line-87 removed endpoint gives the negative
of the ordered defect `A_a B_b (1-G^x.total)`. -/
lemma evaluatedSlice_phaseFivePaper_term_diff
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (q : EvaluatedSliceQuestion params)
    (a b : Fq params) :
    strategy.state.ev
        (strategy.state.L
            (((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b) *
              (evaluatedSliceFirstFactor params family q).total) *
          strategy.state.R
            (((evaluatedSlicePointMeas params strategy q.1).outcome a) *
              ((evaluatedSlicePointMeas params strategy q.2).outcome b))) -
      strategy.state.ev
        (strategy.state.L
            (((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b)) *
          strategy.state.R
            (((evaluatedSlicePointMeas params strategy q.1).outcome a) *
              ((evaluatedSlicePointMeas params strategy q.2).outcome b))) =
    - strategy.state.ev
        (strategy.state.L
            (((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b) *
              (1 - (G (pointHeight params q.1)).total)) *
          strategy.state.R
            (((evaluatedSlicePointMeas params strategy q.1).outcome a) *
              ((evaluatedSlicePointMeas params strategy q.2).outcome b))) := by
  have htotal : (evaluatedSliceFirstFactor params family q).total =
      (G (pointHeight params q.1)).total :=
    evaluatedPointFamily_total_eq_G_total params family G hG q.1
  rw [htotal, mul_sub, mul_one, ← strategy.state.leftTensor_sub, sub_mul, strategy.state.ev_sub]
  ring

/-- Average the paper phase-five algebra over evaluated-slice questions. -/
lemma evaluatedSlice_phaseFivePaper_avg_diff_eq_neg_orderedDefect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hG : ∀ x, G x = (family.meas x).toSubMeas) :
    let 𝒟 := uniformDistribution (EvaluatedSliceQuestion params)
    let inserted : EvaluatedSliceQuestion params → ℝ := fun q =>
      ∑ a : Fq params, ∑ b : Fq params,
        strategy.state.ev
          (strategy.state.L
              (((evaluatedSliceFirstFactor params family q).outcome a) *
                ((evaluatedSliceSecondFactor params family q).outcome b) *
                (evaluatedSliceFirstFactor params family q).total) *
            strategy.state.R
              (((evaluatedSlicePointMeas params strategy q.1).outcome a) *
                ((evaluatedSlicePointMeas params strategy q.2).outcome b)))
    let removed : EvaluatedSliceQuestion params → ℝ :=
      evaluatedSlicePhaseFivePaperRemoved params strategy family
    avgOver 𝒟 inserted - avgOver 𝒟 removed =
      -avgOver 𝒟 (evaluatedSlicePhaseFivePaperOrderedDefect params strategy family G) := by
  intro 𝒟 inserted removed
  rw [← avgOver_sub]
  calc avgOver 𝒟 (fun q => inserted q - removed q)
      = avgOver 𝒟
          (fun q => -evaluatedSlicePhaseFivePaperOrderedDefect params strategy family G q) :=
        avgOver_congr 𝒟 _ _ fun q => by
          simp only [inserted, removed, evaluatedSlicePhaseFivePaperRemoved,
            evaluatedSlicePhaseFivePaperOrderedDefect, ← Finset.sum_sub_distrib,
            ← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
            evaluatedSlice_phaseFivePaper_term_diff params strategy family G hG q a b
    _ = -avgOver 𝒟 (evaluatedSlicePhaseFivePaperOrderedDefect params strategy family G) := by
        simp only [avgOver, mul_neg, Finset.sum_neg_distrib]

/-- Collapse the first-coordinate postprocessing fiber in the raw paper defect.

For fixed `(u,x)` and right prefix `P₂`, summing over evaluated outcomes `a`
expands `G^{u,x}_a = ∑_{g : g(u)=a} G^x_g` and collapses to a polynomial sum. -/
lemma phaseFivePaper_fiber_sum_ev
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (u : Point params)
    (B T P₂ : 𝔓)
    (Gx : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (P₁ : Fq params → 𝔓) :
    (∑ a : Fq params,
      S.ev
        (S.L
            (((∑ g ∈ Finset.univ.filter
                    (fun g : MIPStarRE.LDT.Polynomial params => g u = a), Gx.outcome g) * B) *
              T) *
          S.R (P₂ * P₁ a))) =
      ∑ g : MIPStarRE.LDT.Polynomial params,
        S.ev (S.L ((Gx.outcome g * B) * T) * S.R (P₂ * P₁ (g u))) := by
  refine (Finset.sum_congr rfl fun a _ => ?_).trans
    (Finset.sum_fiberwise Finset.univ (fun g : MIPStarRE.LDT.Polynomial params => g u)
      fun g => S.ev (S.L ((Gx.outcome g * B) * T) * S.R (P₂ * P₁ (g u))))
  rw [Finset.sum_mul, Finset.sum_mul, ← S.leftTensor_finset_sum, Finset.sum_mul,
    S.ev_finset_sum]
  exact Finset.sum_congr rfl fun g hg => by rw [(Finset.mem_filter.mp hg).2]

/-- Pointwise expansion of the swapped paper defect after writing the first point as `(u,x)`.

The statement keeps point measurements in the local `evaluatedSlicePointMeas`
notation; the final reindexing lemma rewrites those to `strategy.pointMeasurement`
when matching `gCommStabilityTwoRawScalarDefect`. -/
lemma evaluatedSlicePhaseFivePaperSwappedDefect_appendPoint_expansion
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (x : Fq params) (u : Point params) (vy : Point params.next) :
    evaluatedSlicePhaseFivePaperSwappedDefect params strategy family G
        (appendPoint params u x, vy) =
      ∑ g : MIPStarRE.LDT.Polynomial params, ∑ b : Fq params,
        strategy.state.ev
          (strategy.state.L
              ((G x).outcome g *
                (evaluatedPointFamily params family vy).outcome b *
                (1 - (G x).total)) *
            strategy.state.R
              (((evaluatedSlicePointMeas params strategy vy).outcome b) *
                ((evaluatedSlicePointMeas params strategy
                    (appendPoint params u x)).outcome (g u)))) := by
  rw [Finset.sum_comm]
  unfold evaluatedSlicePhaseFivePaperSwappedDefect
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [evaluatedSliceFirstFactor, evaluatedSliceSecondFactor,
    MIPStarRE.LDT.pointHeight_appendPoint,
    evaluatedPointFamily_appendPoint_outcome params family G hG x u]
  exact phaseFivePaper_fiber_sum_ev params strategy.state u _ _ _ (G x)
    fun a => (evaluatedSlicePointMeas params strategy (appendPoint params u x)).outcome a

/-- Exact reindexing of the swapped paper defect to the raw scalar stability defect.

The proof decomposes the **first** evaluated-slice coordinate
`q.1 = appendPoint params u x`, because the defect reads
`pointHeight params q.1` and the first-coordinate point outcome
`evaluatedSlicePointMeas params strategy q.1`. There is no `gamma` parameter in
this reindexing lemma: the only `gamma` loss in phase five is the separate
right-register point-measurement swap. -/
lemma evaluatedSlice_phaseFivePaper_reindex_to_raw_defect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hG : ∀ x, G x = (family.meas x).toSubMeas) :
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedSlicePhaseFivePaperSwappedDefect params strategy family G) =
      avgOver (uniformDistribution (Fq params))
        (gCommStabilityTwoRawScalarDefect params strategy family G) := by
  let D := evaluatedSlicePhaseFivePaperSwappedDefect params strategy family G
  calc avgOver (uniformDistribution (EvaluatedSliceQuestion params)) D
      = avgOver (uniformDistribution (Point params.next)) (fun ux =>
          avgOver (uniformDistribution (Point params.next)) (fun vy => D (ux, vy))) :=
        avgOver_uniform_prod fun ux vy => D (ux, vy)
    _ = avgOver (uniformDistribution (Fq params)) (fun x =>
          avgOver (uniformDistribution (Point params)) (fun u =>
            avgOver (uniformDistribution (Point params.next)) (fun vy =>
              D (appendPoint params u x, vy)))) :=
        MIPStarRE.LDT.CommutativityPoints.avgOver_uniform_pointNext_decompose params _
    _ = avgOver (uniformDistribution (Fq params)) (fun x =>
          avgOver (uniformDistribution (Point params.next)) (fun vy =>
            avgOver (uniformDistribution (Point params)) (fun u =>
              D (appendPoint params u x, vy)))) :=
        avgOver_congr _ _ _ fun x => avgOver_uniform_comm fun u vy => D (appendPoint params u x, vy)
    _ = avgOver (uniformDistribution (Fq params))
          (gCommStabilityTwoRawScalarDefect params strategy family G) :=
        avgOver_congr _ _ _ fun x => avgOver_congr _ _ _ fun vy => avgOver_congr _ _ _ fun u =>
          evaluatedSlicePhaseFivePaperSwappedDefect_appendPoint_expansion
            params strategy family G hG x u vy

end MIPRE.LIDT.Co.Commutativity

end
