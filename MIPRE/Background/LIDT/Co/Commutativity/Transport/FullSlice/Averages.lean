/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/Transport/FullSlice/Averages.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.EvaluatedSliceCommutation.Averages
public import MIPRE.Background.LIDT.Co.Commutativity.Scaffold.Products
public import MIPRE.Background.LIDT.Co.Commutativity.Transport.Pullback
public import MIPRE.Background.LIDT.Co.Preliminaries.PolynomialAgreement
public import MIPRE.Background.LIDT.MIPStarRE.LDT.Commutativity.Transport.FullSlice.Averages

@[expose] public section

/-!
# Full-slice averages and index equivalences

Zero-family definition, shared average-reindexing helpers, and averaged scalar and tensor
quantities for the full-slice outcome space: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/Transport/FullSlice/Averages.lean` in the
port of `planning/c6b-plan.md` (milestone M7, section "Port conventions").

The averages are real expectations `strategy.state.ev …` on the symmetric model of a strategy
`strategy : SymStrat params.next 𝔓 K`, the vendored `leftTensor (ι₂ := ι)` and
`rightTensor (ι₁ := ι)` being `strategy.state.L` and `strategy.state.R`. The tensor-form
averages are internal to the scalar/tensor comparison recorded upstream in
`docs/decisions/713-scalar-tensor-decision.md`; downstream code should use the scalar API.

`zeroFullSliceOpFamily` is generic over any type with a zero, so a dependant names the operator
type, `zeroFullSliceOpFamily (R := K →L[ℂ] K) params`, where the vendored text has
`(ι := ι)`. The two swap identities of `fullSliceCommutation_avg_swap_terms` are one private
reindexing helper applied twice, in place of the vendored product-average calculation. The
data-reindexing equivalences and the point-marginal lemma are classical and imported from the
vendored file, which this file imports alongside its mirrored imports.

## Not ported

- `xEvaluatedQuestionPointNextEquiv`: classical, imported.
- `avgOver_xEvaluatedQuestion_to_pointNext`: classical, imported.
- `evaluatedSliceQuestionYDataEquiv`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Commutativity

open MIPStarRE.LDT (Parameters FieldModel Point Fq avgOver avgOver_congr avgOver_uniform_equiv
  avgOver_uniform_comm avgOver_uniform_prod uniformDistribution)
open MIPStarRE.LDT.Commutativity (EvaluatedSliceQuestion EvaluatedSliceOutcome FullSliceQuestion
  FullSliceOutcome)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Reindexing by the swap of a pair question and of a pair outcome: if `f q (a, b)` is
`g (q.2, q.1) (b, a)`, then the averaged sums of `f` and `g` agree. -/
private theorem avg_pair_sum_eq_of_swap {α β : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] (f g : α × α → β × β → ℝ) (h : ∀ q ab, f q ab = g q.swap ab.swap) :
    avgOver (uniformDistribution (α × α)) (fun q => ∑ ab : β × β, f q ab) =
      avgOver (uniformDistribution (α × α)) (fun q => ∑ ab : β × β, g q ab) := by
  refine ((avgOver_congr _ _ _ fun q => ?_).trans
    (avgOver_uniform_equiv (Equiv.prodComm _ _) (fun q => ∑ ab : β × β, g q ab)).symm)
  simp_rw [h]
  exact Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun _ => rfl

/-- Swapping the full-slice question and outcome identifies the averaged
`BAB`/`ABA` terms and the averaged `BABA`/`ABAB` terms. -/
lemma fullSliceCommutation_avg_swap_terms
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓) :
    avgOver (uniformDistribution (FullSliceQuestion params))
        (fun q => ∑ gh : FullSliceOutcome params,
          fullSliceBABTerm params strategy family q gh) =
      avgOver (uniformDistribution (FullSliceQuestion params))
        (fun q => ∑ gh : FullSliceOutcome params,
          fullSliceABATerm params strategy family q gh) ∧
    avgOver (uniformDistribution (FullSliceQuestion params))
        (fun q => ∑ gh : FullSliceOutcome params,
          fullSliceBABATerm params strategy family q gh) =
      avgOver (uniformDistribution (FullSliceQuestion params))
        (fun q => ∑ gh : FullSliceOutcome params,
          fullSliceABABTerm params strategy family q gh) :=
  ⟨avg_pair_sum_eq_of_swap _ _ fun _ _ => rfl, avg_pair_sum_eq_of_swap _ _ fun _ _ => rfl⟩

/-- The zero operator family on the full-slice outcome space. -/
noncomputable def zeroFullSliceOpFamily {R : Type*} [Zero R]
    (params : Parameters) [FieldModel params.q] :
    OpFamily (FullSliceOutcome params) R where
  outcome := fun _ => 0
  total := 0

/-- Full-slice ABA scalar average: `E_{x,y} ∑_{g,h} ⟨ψ| G^x_g G^y_h G^x_g ⊗ I |ψ⟩`.

Full-polynomial analog of the evaluated `evaluatedSliceABATerm`; obtained from it by replacing
the evaluated outcomes `a,b` with polynomial outcomes `g,h` summed over `FullSliceOutcome`. -/
noncomputable def fullSliceABAAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓) : ℝ :=
  avgOver (uniformDistribution (FullSliceQuestion params))
    (fun xy =>
      ∑ gh : FullSliceOutcome params,
        strategy.state.ev
          (strategy.state.L
            ((family.meas xy.1).toSubMeas.outcome gh.1 *
              (family.meas xy.2).toSubMeas.outcome gh.2 *
              (family.meas xy.1).toSubMeas.outcome gh.1)))

/-- Full-slice ABAB scalar average:
`E_{x,y} ∑_{g,h} ⟨ψ| G^x_g G^y_h G^x_g G^y_h ⊗ I |ψ⟩`. -/
noncomputable def fullSliceABABAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓) : ℝ :=
  avgOver (uniformDistribution (FullSliceQuestion params))
    (fun xy =>
      ∑ gh : FullSliceOutcome params,
        strategy.state.ev
          (strategy.state.L
            ((family.meas xy.1).toSubMeas.outcome gh.1 *
              (family.meas xy.2).toSubMeas.outcome gh.2 *
              (family.meas xy.1).toSubMeas.outcome gh.1 *
              (family.meas xy.2).toSubMeas.outcome gh.2)))

/-- Evaluated-slice ABA scalar average:
`E_{u,v,x,y} ∑_{a,b} ⟨ψ| G^x_[g(u)=a] G^y_[h(v)=b] G^x_[g(u)=a] ⊗ I |ψ⟩`.

Averaged analog of `evaluatedSliceABATerm` over the evaluated-slice question. -/
noncomputable def evaluatedSliceABAAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓) : ℝ :=
  avgOver (uniformDistribution (EvaluatedSliceQuestion params))
    (fun q =>
      ∑ ab : EvaluatedSliceOutcome params,
        evaluatedSliceABATerm params strategy family q ab)

/-- Evaluated-slice ABAB scalar average:
`E_{u,v,x,y} ∑_{a,b} ⟨ψ| G^x_[g(u)=a] G^y_[h(v)=b] G^x_[g(u)=a] G^y_[h(v)=b] ⊗ I |ψ⟩`. -/
noncomputable def evaluatedSliceABABAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓) : ℝ :=
  avgOver (uniformDistribution (EvaluatedSliceQuestion params))
    (fun q =>
      ∑ ab : EvaluatedSliceOutcome params,
        evaluatedSliceABABTerm params strategy family q ab)

/-- Full-slice `BAB ⊗ A` tensor average (paper `eq:gcom4`, right-hand side):
`E_{x,y} ∑_{g,h} ⟨ψ| G^y_h G^x_g G^y_h ⊗ G^x_g |ψ⟩`.

This is the manifestly positive tensor-form partner of `fullSliceABAAvg` used by the
marginalization step: each summand factors as `V^* V` with `V = (G^x_g G^y_h) ⊗ √(G^x_g)`, so
the outer absolute value drops and the Schwartz–Zippel collision bound applies per outcome.
This tensor-form average is internal to the scalar API (upstream decision #713). -/
noncomputable def fullSliceBABAtensorAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓) : ℝ :=
  avgOver (uniformDistribution (FullSliceQuestion params))
    (fun xy =>
      ∑ gh : FullSliceOutcome params,
        strategy.state.ev
          (strategy.state.L
              ((family.meas xy.2).toSubMeas.outcome gh.2 *
                (family.meas xy.1).toSubMeas.outcome gh.1 *
                (family.meas xy.2).toSubMeas.outcome gh.2) *
            strategy.state.R ((family.meas xy.1).toSubMeas.outcome gh.1)))

/-- Full-slice `ABA ⊗ B` tensor average (y-side analogue):
`E_{x,y} ∑_{g,h} ⟨ψ| G^x_g G^y_h G^x_g ⊗ G^y_h |ψ⟩`.

Naming convention (consistent with the sibling `fullSliceBABAtensorAvg` for `BAB ⊗ A`): the
four-letter operator string `ABAB` decomposes as left register `ABA` followed by right register
`B`. This is *not* the same operator as the scalar `fullSliceABABAvg`, whose left register is
the full quartic `G^x_g G^y_h G^x_g G^y_h`; the `tensorAvg` suffix marks the tensor split.

The manifestly positive tensor-form partner of `fullSliceABABAvg`, reached from it by
`closenessOfIP` (moving the trailing `G^y_h` factor from the left register to the right). Each
summand factors as `V^* V` with `V = (G^y_h G^x_g) ⊗ √(G^y_h)`. Internal per upstream decision
#713.

The evaluated-side analogue is `evaluatedSliceABABtensorAvg` below. -/
noncomputable def fullSliceABABtensorAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓) : ℝ :=
  avgOver (uniformDistribution (FullSliceQuestion params))
    (fun xy =>
      ∑ gh : FullSliceOutcome params,
        strategy.state.ev
          (strategy.state.L
              ((family.meas xy.1).toSubMeas.outcome gh.1 *
                (family.meas xy.2).toSubMeas.outcome gh.2 *
                (family.meas xy.1).toSubMeas.outcome gh.1) *
            strategy.state.R ((family.meas xy.2).toSubMeas.outcome gh.2)))

/-- Evaluated-slice `ABA ⊗ B` tensor average (evaluated-side analogue of
`fullSliceABABtensorAvg`):
`E_{u,v,x,y} ∑_{a,b} ⟨ψ| G^x_[g(u)=a] G^y_[h(v)=b] G^x_[g(u)=a] ⊗ G^y_[h(v)=b] |ψ⟩`.

This is the second tensor-form endpoint of the paper's `commutativity-G.tex` (lines 356–360).
The scalar-to-tensor comparison `evaluatedSliceABAB_scalar_to_ABABtensor` reaches it by moving
the trailing `G^y_[h(v)=b]` factor from the left register to the right register.

The shared tensor endpoint is defined here so the evaluated-side transport lemmas can use the
same notation as the full-slice transport lemmas. -/
noncomputable def evaluatedSliceABABtensorAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓) : ℝ :=
  avgOver (uniformDistribution (EvaluatedSliceQuestion params))
    (fun q =>
      ∑ ab : EvaluatedSliceOutcome params,
        strategy.state.ev
          (strategy.state.L
              ((evaluatedSliceFirstFactor params family q).outcome ab.1 *
                (evaluatedSliceSecondFactor params family q).outcome ab.2 *
                (evaluatedSliceFirstFactor params family q).outcome ab.1) *
            strategy.state.R ((evaluatedSliceSecondFactor params family q).outcome ab.2)))

/-- X-evaluated `BAB ⊗ A` tensor average.

This is the intermediate obtained from `fullSliceBABAtensorAvg` after postprocessing only the
first/full-`x` polynomial outcome by a sampled point `u : Point params`; the second/`y`
polynomial outcome remains full. The x-side tensor marginalization lemma identifies its
difference from the full tensor average with `fullSliceBABAxCollisionFactored`. -/
noncomputable def xEvaluatedSliceBABAtensorAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓) : ℝ :=
  avgOver (uniformDistribution (FullSliceQuestion params))
    (fun xy =>
      avgOver (uniformDistribution (Point params))
        (fun u =>
          let A : SubMeas (Fq params) 𝔓 :=
            evaluateAt params u ((family.meas xy.1).toSubMeas)
          let B : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓 := (family.meas xy.2).toSubMeas
          ∑ a : Fq params, ∑ h : MIPStarRE.LDT.Polynomial params,
            strategy.state.ev
              (strategy.state.L (B.outcome h * A.outcome a * B.outcome h) *
                strategy.state.R (A.outcome a))))

/-- X-evaluated, y-full ABAB scalar average.

This is the scalar endpoint in the display from `eq:evaluate-gcom-at-points` to
`eq:don't-understand-the-numbering-system`: the `x` polynomial outcome has been postprocessed
at `u`, but the second `closenessOfIP` move has not yet transferred the trailing `G^y_h` to the
right register. -/
noncomputable def xEvaluatedFullSliceABABAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓) : ℝ :=
  avgOver (uniformDistribution (Point params × FullSliceQuestion params))
    (fun ux =>
      let A : SubMeas (Fq params) 𝔓 :=
        evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)
      let B : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓 := (family.meas ux.2.2).toSubMeas
      ∑ ah : Fq params × MIPStarRE.LDT.Polynomial params,
        strategy.state.ev
          (strategy.state.L
            (A.outcome ah.1 * B.outcome ah.2 * A.outcome ah.1 * B.outcome ah.2)))

/-- X-evaluated, y-full `ABA ⊗ B` tensor average.

This is the y-side intermediate in the paper's `eq:evaluate-gcom-at-points-part-dos`: the
first/`x` family has already been postprocessed at `u`, while the second/`y` family still
ranges over full polynomial outcomes. The y-side tensor marginalization lemma compares this to
`evaluatedSliceABABtensorAvg`. -/
noncomputable def xEvaluatedFullSliceABABtensorAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓) : ℝ :=
  avgOver (uniformDistribution (Point params × FullSliceQuestion params))
    (fun ux =>
      let A : SubMeas (Fq params) 𝔓 :=
        evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)
      let B : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓 := (family.meas ux.2.2).toSubMeas
      ∑ ah : Fq params × MIPStarRE.LDT.Polynomial params,
        strategy.state.ev
          (strategy.state.L (A.outcome ah.1 * B.outcome ah.2 * A.outcome ah.1) *
            strategy.state.R (B.outcome ah.2)))

/-- Reindex `xEvaluatedSliceBABAtensorAvg` into the mixed `(u,x,y)` data order. -/
lemma xEvaluatedSliceBABAtensorAvg_eq_xFullData
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓) :
    xEvaluatedSliceBABAtensorAvg params strategy family =
      avgOver (uniformDistribution (Point params × FullSliceQuestion params))
        (fun ux =>
          let A : SubMeas (Fq params) 𝔓 :=
            evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)
          let B : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓 := (family.meas ux.2.2).toSubMeas
          ∑ a : Fq params, ∑ h : MIPStarRE.LDT.Polynomial params,
            strategy.state.ev
              (strategy.state.L (B.outcome h * A.outcome a * B.outcome h) *
                strategy.state.R (A.outcome a))) :=
  let term : Point params → FullSliceQuestion params → ℝ := fun u xy =>
    let A : SubMeas (Fq params) 𝔓 := evaluateAt params u ((family.meas xy.1).toSubMeas)
    let B : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓 := (family.meas xy.2).toSubMeas
    ∑ a : Fq params, ∑ h : MIPStarRE.LDT.Polynomial params,
      strategy.state.ev
        (strategy.state.L (B.outcome h * A.outcome a * B.outcome h) *
          strategy.state.R (A.outcome a))
  (avgOver_uniform_comm (fun xy u => term u xy)).trans (avgOver_uniform_prod term).symm

end MIPRE.LIDT.Co.Commutativity

end
