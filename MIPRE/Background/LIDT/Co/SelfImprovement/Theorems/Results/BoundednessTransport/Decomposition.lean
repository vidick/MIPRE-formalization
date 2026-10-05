/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
SelfImprovement/Theorems/Results/BoundednessTransport/Decomposition.lean, to the symmetric model
of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Basic.QuantumState
public import MIPStarRE.LDT.Basic.ParametersFiniteAnswers
public import MIPRE.Background.LIDT.Co.Basic.SubMeasurementFamilies
public import MIPRE.Background.LIDT.Co.Preliminaries.SelfConsistency.DataProcessing
public import MIPRE.Background.LIDT.Co.Preliminaries.Triangles.SimEq
public import MIPStarRE.LDT.SelfImprovement.Theorems.Thresholds.Final
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Statements
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.AddInUPointConsistency

@[expose] public section

/-!
# Boundedness transport decomposition identities

The algebraic reindexing and off-diagonal decompositions of the helper-agreement operator used in
the final-fields boundedness and point-consistency arguments of self-improvement: the counterpart
of the vendored `SelfImprovement/Theorems/Results/BoundednessTransport/Decomposition.lean`
(under `MIPRE/Background/LIDT/MIPStarRE/LDT/`) in the port of `planning/c6b-plan.md` (milestone
M10, section "Port conventions").

## Contents

- `helper_agreement_average_ev_eq_avg`, `helper_agreement_average_ev_eq_polynomial_sum`: scalar
  expansions of the averaged helper-agreement operator.
- `helperAgreementOperatorAtPoint_eq_sum_polynomial`: `∑_a A^u_a ⊗ H_{[h(u)=a]} = ∑_h A^u_{h(u)} ⊗
  H_h`.
- `helperAgreementOperatorAtPoint_off_diagonal_decomposition` and its scalar and averaged forms
  (`helperAgreementOperatorAtPoint_ev_slack_eq_off_diagonal_sum`,
  `helper_boundedness_slack_average_ev_eq_off_diagonal_avg`): `I ⊗ H.total` minus the agreement
  operator is the off-diagonal sum `∑_h ∑_{a ≠ h(u)} A^u_a ⊗ H_h`.

A strategy is a `SymStrat params 𝔓 K`; the point measurement and `H` are local (in `𝔓`), and the
agreement operators are joint operators `K →L[ℂ] K`. The vendored `opTensor A B` is
`strategy.state.opTensor A B`, `rightTensor (ι₁ := ι) X` is `strategy.state.R X` (the named
carrier argument dropped) and `ev strategy.state` is `strategy.state.ev`. The vendored entrywise
step `(evaluateAt params u H).outcome a = ∑_{h(u)=a} H_h` is `SubMeas.postprocess_outcome`, and
`I ⊗ H.total = ∑_h I ⊗ H_h` is the keystone's `opTensor_sum_right_univ` at `1`. No statement of
the vendored file carries a swap, density or normalization hypothesis, so no statement changed;
the file sets no option, the vendored file-wide `respectTransparency false` not being needed.

The imports mirror the vendored ones, with the Co keystone `Basic/QuantumState` in place of the
vendored `Basic/QuantumState`; the vendored `Basic/ParametersFiniteAnswers` is imported for
`polynomial_sum_fiberwise` and the finite-answer instances, and the vendored
`Thresholds/Final.lean` (classical) as in the vendored file.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/self_improvement.tex` lines 435 and 612--613
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.SelfImprovement

open MIPStarRE.LDT (Parameters FieldModel Point Fq avgOver uniformDistribution avgOver_congr
  avgOver_sub avgOver_uniform_const polynomial_sum_fiberwise)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Scalar expansion of the averaged helper-agreement operator.

The expectation of the averaged agreement operator is the average, over the
point question, of the scalar agreement between the point measurement and the
postprocessed polynomial family. -/
theorem helper_agreement_average_ev_eq_avg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (H : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    strategy.state.ev (helperAgreementAverageOperator params strategy H) =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ a : Fq params,
          strategy.state.ev
            (strategy.state.opTensor ((strategy.pointMeasurement u).outcome a)
              ((evaluateAt params u H).outcome a))) :=
  (strategy.state.ev_averageOperatorOverDistribution _ _).trans
    (avgOver_congr (uniformDistribution (Point params)) _ _ fun _ =>
      strategy.state.ev_sum _)

/-- Reindexing identity for the pointwise helper-agreement operator.

The fiberwise definition `H_{[h(u)=a]} := ∑_{h : h(u)=a} H_h` collapses the
`a`-summed expression `∑_a A^u_a ⊗ H_{[h(u)=a]}` to the polynomial-indexed sum
`∑_h A^u_{h(u)} ⊗ H_h`, by expanding the tensor product fiberwise and applying
`polynomial_sum_fiberwise` along `h ↦ h u`.

This is the first equality of the boundedness display in the proof of
`\ref{item:self-improvement-boundedness}` (`references/ldt-paper/self_improvement.tex` line 612).
It is a purely algebraic identity: no estimate, and no measurement structure beyond the
postprocess fiber decomposition built into `evaluateAt`. -/
theorem helperAgreementOperatorAtPoint_eq_sum_polynomial
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (H : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (u : Point params) :
    helperAgreementOperatorAtPoint params strategy H u =
      ∑ h : MIPStarRE.LDT.Polynomial params,
        strategy.state.opTensor ((strategy.pointMeasurement u).outcome (h u))
          (H.outcome h) := by
  rw [polynomial_sum_fiberwise params u]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [evaluateAt, SubMeas.postprocess_outcome, strategy.state.opTensor_sum_right_finset]
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [(Finset.mem_filter.1 hh).2]

/-- Reindexed expansion of the averaged helper-agreement operator.

Combining the pointwise reindexing identity
`helperAgreementOperatorAtPoint_eq_sum_polynomial` with
`helper_agreement_average_ev_eq_avg`, the scalar
`⟨ψ| E_u Σ_a A^u_a ⊗ H_{[h(u)=a]} |ψ⟩` equals the polynomial-indexed expectation
`E_u Σ_h ⟨ψ| A^u_{h(u)} ⊗ H_h |ψ⟩` from the second line of the boundedness
display in the proof of `\ref{item:self-improvement-boundedness}`
(`references/ldt-paper/self_improvement.tex` line 612). -/
theorem helper_agreement_average_ev_eq_polynomial_sum
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (H : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    strategy.state.ev (helperAgreementAverageOperator params strategy H) =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : MIPStarRE.LDT.Polynomial params,
          strategy.state.ev
            (strategy.state.opTensor ((strategy.pointMeasurement u).outcome (h u))
              (H.outcome h))) :=
  (strategy.state.ev_averageOperatorOverDistribution _ _).trans
    (avgOver_congr (uniformDistribution (Point params)) _ _ fun u =>
      (congrArg strategy.state.ev
        (helperAgreementOperatorAtPoint_eq_sum_polynomial params strategy H u)).trans
        (strategy.state.ev_sum _))

/-- Off-diagonal decomposition of the pointwise helper boundedness slack.

For each point `u`, the difference between the right-placed total
`I ⊗ H.total = ∑_h I ⊗ H_h` and the pointwise helper-agreement operator
`∑_a A^u_a ⊗ H_{[h(u)=a]}` equals the off-diagonal sum `∑_h ∑_{a ≠ h(u)} A^u_a ⊗ H_h`, by the
reindexing `helperAgreementOperatorAtPoint_eq_sum_polynomial`, `∑_a A^u_a = 1` (the point
measurement is a measurement) and the bilinearity of `opTensor`.

This is the operator-level form of the second algebraic identity in the
boundedness display in `\ref{item:self-improvement-boundedness}`
(`references/ldt-paper/self_improvement.tex` line 613). The averaged scalar form of the
off-diagonal sum on the right is the left side of `eq:explicit-bound-for-A-consistency`
(line 435), which the paper bounds by `4 √ζ_variance`. -/
theorem helperAgreementOperatorAtPoint_off_diagonal_decomposition
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (H : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (u : Point params) :
    strategy.state.R H.total -
        helperAgreementOperatorAtPoint params strategy H u =
      ∑ h : MIPStarRE.LDT.Polynomial params,
        ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
          strategy.state.opTensor ((strategy.pointMeasurement u).outcome a) (H.outcome h) := by
  classical
  have hrhs_total : strategy.state.R H.total =
      ∑ h : MIPStarRE.LDT.Polynomial params, strategy.state.opTensor (1 : 𝔓) (H.outcome h) := by
    rw [← strategy.state.opTensor_sum_right_univ, H.sum_eq_total]
    exact (one_mul _).symm.trans (congrArg (· * _) strategy.state.L.map_one.symm)
  rw [helperAgreementOperatorAtPoint_eq_sum_polynomial, hrhs_total, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun h _ => ?_
  have hsubst :
      (1 : 𝔓) - (strategy.pointMeasurement u).outcome (h u) =
        ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
          (strategy.pointMeasurement u).outcome a := by
    rw [← (strategy.pointMeasurement u).toMeasurement.sum_eq,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ (h u)), add_sub_cancel_left]
  rw [strategy.state.opTensor_sub_left, hsubst, strategy.state.opTensor_sum_left_finset]

/-- Scalar form of the pointwise off-diagonal decomposition.

For each evaluation point `u`, the scalar slack
`⟨ψ, I ⊗ H.total, ψ⟩ - ⟨ψ, helperAgreementOperatorAtPoint u, ψ⟩`
is the sum of the off-diagonal masses
`⟨ψ, A^u_a ⊗ H_h, ψ⟩` over the pairs with `a ≠ h(u)`. -/
theorem helperAgreementOperatorAtPoint_ev_slack_eq_off_diagonal_sum
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (H : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (u : Point params) :
    strategy.state.ev (strategy.state.R H.total) -
        strategy.state.ev (helperAgreementOperatorAtPoint params strategy H u) =
      ∑ h : MIPStarRE.LDT.Polynomial params,
        ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
          strategy.state.ev
            (strategy.state.opTensor ((strategy.pointMeasurement u).outcome a)
              (H.outcome h)) := by
  rw [← strategy.state.ev_sub, helperAgreementOperatorAtPoint_off_diagonal_decomposition,
    strategy.state.ev_sum]
  simp only [strategy.state.ev_finset_sum]

/-- Averaged scalar form of the off-diagonal decomposition.

The difference `⟨ψ, I ⊗ H.total, ψ⟩ - ⟨ψ, helperAgreementAverageOperator, ψ⟩` equals the
averaged off-diagonal scalar sum `E_u ∑_h ∑_{a ≠ h(u)} ⟨ψ, A^u_a ⊗ H_h, ψ⟩`, the left side of
`eq:explicit-bound-for-A-consistency` (`references/ldt-paper/self_improvement.tex` line 435),
by `helperAgreementOperatorAtPoint_ev_slack_eq_off_diagonal_sum` averaged over `u`. -/
theorem helper_boundedness_slack_average_ev_eq_off_diagonal_avg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (H : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    strategy.state.ev (strategy.state.R H.total) -
        strategy.state.ev (helperAgreementAverageOperator params strategy H) =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : MIPStarRE.LDT.Polynomial params,
          ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
            strategy.state.ev
              (strategy.state.opTensor ((strategy.pointMeasurement u).outcome a)
                (H.outcome h))) := by
  rw [helperAgreementAverageOperator, strategy.state.ev_averageOperatorOverDistribution,
    ← avgOver_uniform_const (α := Point params) (strategy.state.ev (strategy.state.R H.total)), ← avgOver_sub]
  exact avgOver_congr (uniformDistribution (Point params)) _ _ fun u =>
    helperAgreementOperatorAtPoint_ev_slack_eq_off_diagonal_sum params strategy H u

end MIPRE.LIDT.Co.SelfImprovement

end
