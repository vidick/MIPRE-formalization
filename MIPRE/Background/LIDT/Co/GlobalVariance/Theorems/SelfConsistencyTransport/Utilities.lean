/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
GlobalVariance/Theorems/SelfConsistencyTransport/Utilities.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.GlobalVariance.Theorems.CollisionExpansion
public import MIPRE.Background.LIDT.MIPStarRE.LDT.GlobalVariance.Theorems.SelfConsistencyTransport.Utilities

@[expose] public section

/-!
# Sampling and operator-symmetry utilities

The counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/GlobalVariance/Theorems/SelfConsistencyTransport/Utilities.lean`
in the port of `planning/c6b-plan.md` (milestone M6, section "Port conventions"): support lemmas
for the good-strategy self-consistency transport of `lem:local-variance-of-points`.

* `ev_adjoint_sub_swap` — the squared distance is unchanged by swapping the two operators;
* `qSDDCore_optionUnit_some_le` — the selected `some ()` term of a two-outcome defect is at most
  the whole defect;
* `generalizeBReversePointwiseBound` — the reverse `lem:generalize-b` step at
  `expansion.tex:309`;
* `rightPolynomialWeightSqrt_contraction`, `rightPolynomialWeightSqrt_grouped_contraction` —
  `S.R ((G_g)^{1/2})` is a contraction, and so is the column of them over a fiber `g(u) = a`;
* `cabApproxDelta_sum_from_sdd` — `prop:cab-approx-delta` with the grouped multiplier, summed
  over polynomials with no cardinality loss.

A same-space lemma (`ev_adjoint_sub_swap`, `qSDDCore_optionUnit_some_le`) takes a vector state
`V : VecState K`. A lemma that places the weight `(G_g)^{1/2}` on the right factor takes the
model `S : SymModel 𝔓 K` as its explicit first argument, `rightTensor (ι₁ := ι) X` being `S.R X`;
`cabApproxDelta_sum_from_sdd` takes `S` where the vendored lemma takes its state `ψ`, and
evaluates on it. `generalizeBReversePointwiseBound` takes `V` where the vendored lemma takes
`ψbi`, as `Theorems/CollisionExpansion.lean` does.

The two marginal identities of the rerandomized hypercube-edge distribution are statements about
distributions alone; this file imports the vendored file for them.

## Not ported

- `avgOver_rerandomizeCoord_fst`: classical, imported.
- `avgOver_rerandomizeCoord_snd`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/expansion.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.GlobalVariance

open MIPStarRE.LDT (Parameters FieldModel Point Fq Distribution avgOver avgOver_congr avgOver_mono
  avgOver_sum)
open MIPStarRE.LDT.GlobalVariance (axisParallelLineQuestionDistribution generalizeBError)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The squared distance `ev((Y - X)† (Y - X))` is symmetric in `X` and `Y`. -/
theorem ev_adjoint_sub_swap (V : VecState K) (X Y : K →L[ℂ] K) :
    V.ev (star (Y - X) * (Y - X)) = V.ev (star (X - Y) * (X - Y)) := by
  rw [← neg_sub X Y, star_neg, neg_mul_neg]

/-- The selected `some ()` contribution is bounded by the full `Option Unit`
summed squared-distance core.

This extracts the common monotonicity step used when a two-outcome
postprocessed event is passed to `cabApproxDelta`: the singleton selected
outcome is one summand of the full `Option Unit` sum defining `qSDDCore`. -/
theorem qSDDCore_optionUnit_some_le {α : Type*}
    (V : VecState K) (𝒟 : Distribution α)
    (A B : α → Option Unit → K →L[ℂ] K) :
    avgOver 𝒟
        (fun x =>
          V.qSDDCore
            (fun _ : Unit => A x (some ()))
            (fun _ : Unit => B x (some ()))) ≤
      avgOver 𝒟 (fun x => V.qSDDCore (A x) (B x)) :=
  avgOver_mono _ _ _ fun x =>
    (Fintype.sum_unique _).trans_le
      (Finset.single_le_sum (fun a _ => V.ev_adjoint_self_nonneg (A x a - B x a))
        (Finset.mem_univ (some ())))

/-- The reverse `lem:generalize-b` step used at `references/ldt-paper/expansion.tex`, line 309.

The paper first moves from the evaluated line event to the exact restriction (line 308), then
uses the same estimate in the reverse direction at the second sampled point (line 309). The
squared-distance expression is unchanged by swapping the two endpoints, because
`(Y - X) = -(X - Y)`. -/
theorem generalizeBReversePointwiseBound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (V : VecState K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hgen : GeneralizeBStatement params strategy V G)
    (g : MIPStarRE.LDT.Polynomial params) :
    avgOver (axisParallelLineQuestionDistribution params)
      (fun qu =>
        let D := weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu -
          weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
        V.ev (star D * D)) ≤ generalizeBError params :=
  (avgOver_congr _ _ _ fun qu =>
    ev_adjoint_sub_swap V (weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu)
      (weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu)).trans_le
    (hgen.pointwiseNormBound g)

/-- The right placement of the square-root polynomial weight is a contraction.

The square of `(G_g)^{1/2}` is the submeasurement outcome `G_g`, and every
outcome of a submeasurement is bounded by the identity. -/
theorem rightPolynomialWeightSqrt_contraction
    (S : SymModel 𝔓 K)
    (params : Parameters)
    [FieldModel params.q]
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) (g : MIPStarRE.LDT.Polynomial params) :
    star (S.R (polynomialWeightSqrtOperator params G g)) *
        S.R (polynomialWeightSqrtOperator params G g) ≤ 1 := by
  rw [S.rightTensor_conjTranspose, S.rightTensor_mul_rightTensor,
    polynomialWeightSqrtOperator_conjTranspose, polynomialWeightSqrtOperator_mul_self]
  exact S.rightTensor_le_one (G.outcome_le_one g)

/-- Grouped-by-evaluation-value submeasurement contraction for `(G_g)^{1/2}`.

For a fixed point `u` and a field element `a`, sum over all polynomials `g`
with `g(u) = a` of `S.R ((G_g)^{1/2})† S.R ((G_g)^{1/2})`.
The contraction `∑_{g : g(u)=a} G_g ≤ I` follows from the submeasurement
inequality `G.total ≤ I`. This is the key algebraic input that allows the
`cabApproxDelta` multiplier family in `cabApproxDelta_sum_from_sdd` and the
sum-form `2ε` endpoints to group polynomials by their evaluation value without
incurring a cardinality factor. -/
theorem rightPolynomialWeightSqrt_grouped_contraction
    (S : SymModel 𝔓 K)
    (params : Parameters)
    [FieldModel params.q]
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (u : Point params) (a : Fq params) :
    ∑ g : MIPStarRE.LDT.Polynomial params,
        star (if a = g u then S.R (polynomialWeightSqrtOperator params G g) else 0) *
          (if a = g u then S.R (polynomialWeightSqrtOperator params G g) else 0) ≤ 1 := by
  classical
  have hterm : ∀ g : MIPStarRE.LDT.Polynomial params,
      star (if a = g u then S.R (polynomialWeightSqrtOperator params G g) else 0) *
          (if a = g u then S.R (polynomialWeightSqrtOperator params G g) else 0) =
        S.R (if a = g u then G.outcome g else 0) := fun g => by
    split_ifs
    · rw [S.rightTensor_conjTranspose, S.rightTensor_mul_rightTensor,
        polynomialWeightSqrtOperator_conjTranspose, polynomialWeightSqrtOperator_mul_self]
    · rw [star_zero, zero_mul, map_zero]
  rw [Finset.sum_congr rfl fun g _ => hterm g, S.rightTensor_finset_sum]
  refine S.rightTensor_le_one (le_trans ?_ G.total_le_one)
  rw [← G.sum_eq_total]
  exact Finset.sum_le_sum fun g _ => by
    split_ifs
    · exact le_rfl
    · exact G.outcome_pos g

/-- Shared polynomial-sum `cabApproxDelta` transport.

The argument keeps the answer space at `Fq params`, applies
`prop:cab-approx-delta` with multiplier
`if a = g(base s) then S.R ((G_g)^{1/2}) else 0`, and uses the grouped
contraction `rightPolynomialWeightSqrt_grouped_contraction`. The bridge
hypotheses identify the surviving fiber `a = g(base s)` with the weighted
left and right operators desired by the caller. -/
theorem cabApproxDelta_sum_from_sdd
    {Sample : Type*}
    (params : Parameters)
    [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (𝒟 : Distribution Sample)
    (base : Sample → Point params)
    (left right : Sample → Fq params → K →L[ℂ] K)
    (L R : Sample → MIPStarRE.LDT.Polynomial params → K →L[ℂ] K)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (η : ℝ)
    (hbase : avgOver 𝒟 (fun s => S.qSDDCore (left s) (right s)) ≤ η)
    (hleft : ∀ s g,
      S.R (polynomialWeightSqrtOperator params G g) * left s (g (base s)) = L s g)
    (hright : ∀ s g,
      S.R (polynomialWeightSqrtOperator params G g) * right s (g (base s)) = R s g) :
    (∑ g : MIPStarRE.LDT.Polynomial params,
      avgOver 𝒟 (fun s => S.ev (star (L s g - R s g) * (L s g - R s g)))) ≤ η := by
  classical
  let C : Sample → Fq params → MIPStarRE.LDT.Polynomial params → K →L[ℂ] K :=
    fun s a g => if a = g (base s) then S.R (polynomialWeightSqrtOperator params G g) else 0
  have hcab := Preliminaries.cabApproxDelta S.toVecState 𝒟 left right C η hbase
    fun s a => rightPolynomialWeightSqrt_grouped_contraction S params G (base s) a
  refine le_of_eq_of_le ?_ hcab
  rw [← avgOver_sum]
  refine avgOver_congr _ _ _ fun s => ?_
  simp only [VecState.qSDDCore]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.sum_eq_single (g (base s)) (fun a _ ha => by simp [C, ha, S.ev_zero])
    (fun h => absurd (Finset.mem_univ _) h)]
  simp only [C, ite_true, hleft, hright]

end MIPRE.LIDT.Co.GlobalVariance

end
