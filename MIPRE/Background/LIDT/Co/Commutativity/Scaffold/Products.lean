/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/Scaffold/Products.lean, to the symmetric model of `planning/c6b-plan.md`; not a
vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.Scaffold.Symmetry

@[expose] public section

/-!
# Section 11 commutativity: product estimates

Basic product-style lemmas on projective submeasurement outcomes, the expansion of the two
scalar-stability defects, and the commutator-expansion terms reused throughout the Section 11
commutativity argument: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/Scaffold/Products.lean` in the port of
`planning/c6b-plan.md` (milestone M7, section "Port conventions").

The expansion terms are expectations `strategy.state.ev (strategy.state.L …)` on the symmetric
model of the strategy; the vendored `leftTensor (ι₂ := ι)` and `rightTensor (ι₁ := ι)` are
`strategy.state.L` and `strategy.state.R`, and `ᴴ` is `star`. `postprocess_proj_outcome` is
generic over any C*-algebra with its order.

The vendored proofs of the two stability expansions restate the Kronecker products in every
step and prove self-adjointness through `Matrix.PosSemidef`; here both are one application of
`stabilityDefect_ev_eq` (below), whose proof uses the keystone's `opTensor` algebra and the
self-adjointness of nonnegative elements.

## New here

`stabilityDefect_ev_eq`, the per-outcome identity
`ev((L(X T) R(√G) − L X R(√G))^* (L(X T) R(√G) − L X R(√G))) = ev(L((1 − T) X^* X (1 − T)) R G)`
for self-adjoint `T` and `0 ≤ G`, which the vendored file proves inline twice.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Commutativity

open MIPStarRE.LDT (Parameters FieldModel Point Fq truncatePoint pointHeight)
open MIPStarRE.LDT.Commutativity (EvaluatedSliceQuestion EvaluatedSliceOutcome FullSliceQuestion
  FullSliceOutcome StabilityOneOutcome StabilityTwoOutcome fullSliceQuestionOfEvaluatedSlice)
open MIPRE.LIDT.Co.CommutativityPoints (orderedProductOpFamily)

/-- Postprocessing a projective submeasurement preserves outcome projectivity. -/
lemma postprocess_proj_outcome
    {α β : Type*} [Fintype α] [Fintype β]
    {R : Type*} [CStarAlgebra R] [PartialOrder R] [StarOrderedRing R]
    (P : ProjSubMeas α R) (f : α → β) (b : β) :
    (postprocess P.toSubMeas f).outcome b * (postprocess P.toSubMeas f).outcome b =
      (postprocess P.toSubMeas f).outcome b :=
  ProjSubMeas.postprocess_outcome_proj P f b

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Evaluating a projective polynomial family at a point preserves outcome projectivity. -/
lemma evaluatedPointFamily_outcome_proj
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (u : Point params.next) (a : Fq params) :
    (evaluatedPointFamily params family u).outcome a *
        (evaluatedPointFamily params family u).outcome a =
      (evaluatedPointFamily params family u).outcome a :=
  postprocess_proj_outcome (family.meas (pointHeight params u))
    (fun g => g (truncatePoint params u)) a

/-- The positive square root of a submeasurement outcome squares back to that
outcome. -/
lemma sqrt_subMeas_outcome_mul_self
    {α : Type*} [Fintype α]
    (A : SubMeas α 𝔓) (a : α) :
    CFC.sqrt (A.outcome a) * CFC.sqrt (A.outcome a) = A.outcome a :=
  CFC.sqrt_mul_sqrt_self (A.outcome a) (A.outcome_pos a)

/-- The defect of a trailing self-adjoint factor `T`, weighted on the second factor by `√G`:
`ev((L(X T) R(√G) − L X R(√G))^* (…)) = ev(L((1 − T) X^* X (1 − T)) R G)`. -/
theorem stabilityDefect_ev_eq (S : SymModel 𝔓 K) (X T G : 𝔓) (hT : IsSelfAdjoint T)
    (hG : 0 ≤ G) :
    S.ev (star (S.L X * S.L T * S.R (CFC.sqrt G) - S.L X * S.R (CFC.sqrt G)) *
        (S.L X * S.L T * S.R (CFC.sqrt G) - S.L X * S.R (CFC.sqrt G))) =
      S.ev (S.L ((1 - T) * (star X * X) * (1 - T)) * S.R G) := by
  have hW : star (CFC.sqrt G) * CFC.sqrt G = G := by
    rw [(CFC.sqrt_nonneg G).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self G hG]
  have hX : star (X * (T - 1)) * (X * (T - 1)) = (1 - T) * (star X * X) * (1 - T) := by
    rw [star_mul, star_sub, star_one, hT.star_eq, ← neg_sub 1 T]
    simp only [neg_mul, mul_neg, neg_neg, mul_assoc]
  have hD : S.L X * S.L T * S.R (CFC.sqrt G) - S.L X * S.R (CFC.sqrt G) =
      S.opTensor (X * (T - 1)) (CFC.sqrt G) := by
    rw [S.leftTensor_mul_leftTensor, S.opTensor_sub_left, mul_sub, mul_one]
  rw [hD, S.conjTranspose_opTensor, S.opTensor_mul, hX, hW]

/-- Fixed-question expansion of the first scalar-stability `qSDDOp` term.

This is the pointwise algebra behind the paper's `G^y` insertion/removal step:
the left-register defect is sandwiched by `1 - G^y`, while the right-register
weight is the projective outcome `G^y_h`. -/
lemma commDataProcessedGStabilityOne_qSDDOp_expand
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (q : EvaluatedSliceQuestion params) :
    strategy.state.qSDDOp
      (commDataProcessedGStabilityOneLeft params strategy family G q)
      (commDataProcessedGStabilityOneRight params strategy family G q) =
      ∑ ah : StabilityOneOutcome params,
        strategy.state.ev
          (strategy.state.L
            ((1 - (G (pointHeight params q.2)).total) *
              (star ((evaluatedSliceSandwichRaw params strategy family q).outcome
                (ah.1, ah.2 (truncatePoint params q.2))) *
                (evaluatedSliceSandwichRaw params strategy family q).outcome
                  (ah.1, ah.2 (truncatePoint params q.2))) *
              (1 - (G (pointHeight params q.2)).total)) *
          strategy.state.R ((G (pointHeight params q.2)).outcome ah.2)) := by
  have hT : (fullSliceSecondFactor params family
      (fullSliceQuestionOfEvaluatedSlice params q)).total = (G (pointHeight params q.2)).total := by
    rw [hG]; rfl
  refine Finset.sum_congr rfl fun ah _ => ?_
  rw [commDataProcessedGStabilityOneLeft_outcome, commDataProcessedGStabilityOneRight_outcome,
    hT]
  exact stabilityDefect_ev_eq strategy.state _ _ _
    (IsSelfAdjoint.of_nonneg (G _).total_nonneg) ((G _).outcome_pos _)

/-- Fixed-question expansion of the second scalar-stability `qSDDOp` term: the
left-register defect is sandwiched by `1 - G^x`, while the right-register weight is the
projective outcome `G^x_g`. -/
lemma commDataProcessedGStabilityTwo_qSDDOp_expand
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (q : EvaluatedSliceQuestion params) :
    strategy.state.qSDDOp
      (commDataProcessedGStabilityTwoLeft params strategy family G q)
      (commDataProcessedGStabilityTwoRight params strategy family G q) =
      ∑ gb : StabilityTwoOutcome params,
        strategy.state.ev
          (strategy.state.L
            ((1 - (G (pointHeight params q.1)).total) *
              (star ((orderedProductOpFamily
                  (evaluatedSliceFirstFactor params family q)
                  (evaluatedSliceSecondFactor params family q)).outcome
                  (gb.1 (truncatePoint params q.1), gb.2)) *
                (orderedProductOpFamily
                  (evaluatedSliceFirstFactor params family q)
                  (evaluatedSliceSecondFactor params family q)).outcome
                  (gb.1 (truncatePoint params q.1), gb.2)) *
              (1 - (G (pointHeight params q.1)).total)) *
          strategy.state.R ((G (pointHeight params q.1)).outcome gb.1)) := by
  have hT : (fullSliceFirstFactor params family
      (fullSliceQuestionOfEvaluatedSlice params q)).total = (G (pointHeight params q.1)).total := by
    rw [hG]; rfl
  refine Finset.sum_congr rfl fun gb _ => ?_
  rw [commDataProcessedGStabilityTwoLeft_outcome, commDataProcessedGStabilityTwoRight_outcome,
    hT]
  exact stabilityDefect_ev_eq strategy.state _ _ _
    (IsSelfAdjoint.of_nonneg (G _).total_nonneg) ((G _).outcome_pos _)

/-- The `BAB` term in the evaluated-slice commutator expansion. -/
noncomputable def evaluatedSliceBABTerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (q : EvaluatedSliceQuestion params) (ab : EvaluatedSliceOutcome params) : ℝ :=
  let A := (evaluatedPointFamily params family q.1).outcome ab.1
  let B := (evaluatedPointFamily params family q.2).outcome ab.2
  strategy.state.ev <| strategy.state.L (B * A * B)

/-- The `ABA` term in the evaluated-slice commutator expansion. -/
noncomputable def evaluatedSliceABATerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (q : EvaluatedSliceQuestion params) (ab : EvaluatedSliceOutcome params) : ℝ :=
  let A := (evaluatedPointFamily params family q.1).outcome ab.1
  let B := (evaluatedPointFamily params family q.2).outcome ab.2
  strategy.state.ev <| strategy.state.L (A * B * A)

/-- The `BABA` term in the evaluated-slice commutator expansion. -/
noncomputable def evaluatedSliceBABATerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (q : EvaluatedSliceQuestion params) (ab : EvaluatedSliceOutcome params) : ℝ :=
  let A := (evaluatedPointFamily params family q.1).outcome ab.1
  let B := (evaluatedPointFamily params family q.2).outcome ab.2
  strategy.state.ev <| strategy.state.L (B * A * B * A)

/-- The `ABAB` term in the evaluated-slice commutator expansion. -/
noncomputable def evaluatedSliceABABTerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (q : EvaluatedSliceQuestion params) (ab : EvaluatedSliceOutcome params) : ℝ :=
  let A := (evaluatedPointFamily params family q.1).outcome ab.1
  let B := (evaluatedPointFamily params family q.2).outcome ab.2
  strategy.state.ev <| strategy.state.L (A * B * A * B)

/-- The first evaluated-slice factor viewed as a projective family. -/
noncomputable def evaluatedSliceFirstProj
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) :
    IdxProjSubMeas (EvaluatedSliceQuestion params) (Fq params) 𝔓 :=
  fun q =>
    { toSubMeas := evaluatedSliceFirstFactor params family q
      proj := evaluatedPointFamily_outcome_proj params family q.1 }

/-- The second evaluated-slice factor viewed as a projective family. -/
noncomputable def evaluatedSliceSecondProj
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) :
    IdxProjSubMeas (EvaluatedSliceQuestion params) (Fq params) 𝔓 :=
  fun q =>
    { toSubMeas := evaluatedSliceSecondFactor params family q
      proj := evaluatedPointFamily_outcome_proj params family q.2 }

/-- The first full-slice factor viewed as a projective family. -/
noncomputable def fullSliceFirstProj
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) :
    IdxProjSubMeas (FullSliceQuestion params) (MIPStarRE.LDT.Polynomial params) 𝔓 :=
  fun q => family.meas q.1

/-- The second full-slice factor viewed as a projective family. -/
noncomputable def fullSliceSecondProj
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) :
    IdxProjSubMeas (FullSliceQuestion params) (MIPStarRE.LDT.Polynomial params) 𝔓 :=
  fun q => family.meas q.2

/-- The `BAB` term in the full-slice commutator expansion. -/
noncomputable def fullSliceBABTerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (q : FullSliceQuestion params) (gh : FullSliceOutcome params) : ℝ :=
  let A := (fullSliceFirstFactor params family q).outcome gh.1
  let B := (fullSliceSecondFactor params family q).outcome gh.2
  strategy.state.ev <| strategy.state.L (B * A * B)

/-- The `ABA` term in the full-slice commutator expansion. -/
noncomputable def fullSliceABATerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (q : FullSliceQuestion params) (gh : FullSliceOutcome params) : ℝ :=
  let A := (fullSliceFirstFactor params family q).outcome gh.1
  let B := (fullSliceSecondFactor params family q).outcome gh.2
  strategy.state.ev <| strategy.state.L (A * B * A)

/-- The `BABA` term in the full-slice commutator expansion. -/
noncomputable def fullSliceBABATerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (q : FullSliceQuestion params) (gh : FullSliceOutcome params) : ℝ :=
  let A := (fullSliceFirstFactor params family q).outcome gh.1
  let B := (fullSliceSecondFactor params family q).outcome gh.2
  strategy.state.ev <| strategy.state.L (B * A * B * A)

/-- The `ABAB` term in the full-slice commutator expansion. -/
noncomputable def fullSliceABABTerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (q : FullSliceQuestion params) (gh : FullSliceOutcome params) : ℝ :=
  let A := (fullSliceFirstFactor params family q).outcome gh.1
  let B := (fullSliceSecondFactor params family q).outcome gh.2
  strategy.state.ev <| strategy.state.L (A * B * A * B)

end MIPRE.LIDT.Co.Commutativity

end
