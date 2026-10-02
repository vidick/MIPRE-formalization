/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
ComparisonLemmas/LdSandwichLineOnePoint/Core.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.LdSandwichLineOnePoint.CauchySchwarz

@[expose] public section

/-!
# Section 12 pasting: line one-point transport — core theorems

The assembly of `lem:ld-sandwich-line-one-point`: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/ComparisonLemmas/LdSandwichLineOnePoint/Core.lean`
in the port of `planning/c6b-plan.md` (milestone M11, section "Port conventions").

A strategy is a `SymStrat params.next 𝔓 K` and the slice family an `IdxPolyFamily params 𝔓`;
the consistency statements are `ConsRel`s on `strategy.state`. The linear-defect bound of
`Co/.../LdSandwichLineOnePoint/CauchySchwarz.lean` reinstates the `max 0` of the bipartite
consistency error (`ldSandwichLineOnePoint_prefix_cauchySchwarz_transport`), the moved endpoint
of `PrefixMoved.lean` closes the nonzero-coordinate branch, and the endpoint of `Endpoint.lean`
the zero-coordinate branch. The vendored proofs bound the two failure probabilities by `1`
through `strategy.isNormalized`; here `S.bipartiteConsError_uniform_le_one` and
`Pasting.bipartiteSSCError_uniform_le_one` take no normalization argument. No statement carries
a swap or normalization hypothesis, the vendored statements having none.

## Not ported

Nothing: every vendored declaration has a counterpart of the same name.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Point AxisParallelTestSample uniformDistribution)
open MIPStarRE.LDT.Pasting (SandwichedLineQuestion commuteGHalfSandwichError
  ldSandwichLineOnePointError ldSandwichLineOnePoint_endpoint_comm_error_le
  ldSandwichLineOnePoint_endpoint_error_le)
open MIPRE.LIDT.Co (SymModel SymStrat IdxProjMeas IdxPolyFamily gamma_nonneg_of_isGood
  axisParallelPointAnswerFamily axisParallelLineAnswerFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The post-deletion analytic transport in `lem:ld-sandwich-line-one-point`.

The substantive paper gap is now the averaged linear defect bound
`ldSandwichLineOnePoint_prefix_linearDefect_average_cauchySchwarz_bound`; this
lemma is only the proved reduction that reinstates the `max 0` bipartite
consistency error using the measurement-valued right family. -/
theorem ldSandwichLineOnePoint_prefix_cauchySchwarz_transport
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ)
    {k i : ℕ} (hi : i < k) (hi0 : i ≠ 0)
    (facts : LdSandwichLineOnePointAdjointRawCoreBound params strategy family gamma zeta hi) :
    strategy.state.bipartiteConsError
      (uniformDistribution (SandwichedLineQuestion params k))
      (ldSandwichLineOnePointPrefixOriginalFamily params family hi)
      (ldSandwichLineOnePointRightFamily params strategy family k i)
      ≤
    strategy.state.bipartiteConsError
      (uniformDistribution (SandwichedLineQuestion params k))
      (ldSandwichLineOnePointPrefixMovedFamily params family hi)
      (ldSandwichLineOnePointRightFamily params strategy family k i) +
      2 * Real.sqrt (commuteGHalfSandwichError params gamma zeta (i + 1)) :=
  bipartiteConsError_le_of_linearDefect_average_bound strategy.state
    (uniformDistribution (SandwichedLineQuestion params k))
    (ldSandwichLineOnePointPrefixOriginalFamily params family hi)
    (ldSandwichLineOnePointPrefixMovedFamily params family hi)
    (ldSandwichLineOnePointRightFamily params strategy family k i)
    (2 * Real.sqrt (commuteGHalfSandwichError params gamma zeta (i + 1)))
    (ldSandwichLineOnePointRightFamily_total_eq_one params strategy family hi)
    (ldSandwichLineOnePoint_prefix_linearDefect_average_cauchySchwarz_bound
      params strategy family gamma zeta hi hi0 facts)

/-- Scalar residual for the nonzero-coordinate branch of
`lem:ld-sandwich-line-one-point`.

This is the match-mass lower-bound step after unfolding `ConsRel`: it bounds the
averaged off-diagonal defect for the prefix-marginalized one-point family.  The
helper consumes only the adjoint raw-core bound; endpoint identifications,
raw-family reindexing, exact tail deletion, and match-mass expansion are
proved directly in the local lemmas that use them. -/
theorem ldSandwichLineOnePoint_matchMass_lower_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma zeta : ℝ)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (hzeta_le : zeta ≤ 1)
    (family : IdxPolyFamily params 𝔓)
    {k i : ℕ} (hi : i < k) (hi0 : i ≠ 0)
    (facts : LdSandwichLineOnePointAdjointRawCoreBound params strategy family gamma zeta hi)
    (hmovedEndpoint :
      strategy.state.ConsRel
        (uniformDistribution (SandwichedLineQuestion params k))
        (ldSandwichLineOnePointPrefixMovedFamily params family hi)
        (ldSandwichLineOnePointRightFamily params strategy family k i)
        (zeta + Real.sqrt (8 * (params.m : ℝ) * min eps 1 + 4 * min delta 1))) :
    strategy.state.bipartiteConsError
      (uniformDistribution (SandwichedLineQuestion params k))
      (ldSandwichLineOnePointPrefixOriginalFamily params family hi)
      (ldSandwichLineOnePointRightFamily params strategy family k i)
      ≤ ldSandwichLineOnePointError params eps delta gamma zeta k :=
  ((ldSandwichLineOnePoint_prefix_cauchySchwarz_transport
      params strategy family gamma zeta hi hi0 facts).trans
    (add_le_add_left hmovedEndpoint.offDiagonalBound _)).trans
    (ldSandwichLineOnePoint_endpoint_comm_error_le
      params eps delta gamma zeta (Nat.succ_pos i) (Nat.succ_le_of_lt hi)
      heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg hzeta_le)

/-- Turn the scalar match-mass lower bound into the `ConsRel` needed by the
public line-one-point statement. -/
theorem ldSandwichLineOnePoint_nonzero_prefix_transport
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma zeta : ℝ)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (hzeta_le : zeta ≤ 1)
    (family : IdxPolyFamily params 𝔓)
    {k i : ℕ} (hi : i < k) (hi0 : i ≠ 0)
    (hcomm : ∀ j : ℕ, 2 ≤ j →
      CommuteGHalfSandwichStatement params strategy.state family
        gamma zeta j)
    (hmovedEndpoint :
      strategy.state.ConsRel
        (uniformDistribution (SandwichedLineQuestion params k))
        (ldSandwichLineOnePointPrefixMovedFamily params family hi)
        (ldSandwichLineOnePointRightFamily params strategy family k i)
        (zeta + Real.sqrt (8 * (params.m : ℝ) * min eps 1 + 4 * min delta 1))) :
    strategy.state.ConsRel
      (uniformDistribution (SandwichedLineQuestion params k))
      (ldSandwichLineOnePointLeftFamily params strategy family k i)
      (ldSandwichLineOnePointRightFamily params strategy family k i)
      (ldSandwichLineOnePointError params eps delta gamma zeta k) := by
  rw [ldSandwichLineOnePointLeftFamily_eq_prefixOriginal params strategy family hi]
  exact ⟨ldSandwichLineOnePoint_matchMass_lower_bound params strategy eps delta gamma zeta
    heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg hzeta_le family hi hi0
    ⟨ldSandwichLineOnePoint_adjointRawCommutation_qSDDCore_bound
      params strategy family gamma zeta hcomm hi hi0⟩
    hmovedEndpoint⟩

/-- Cauchy-Schwarz sandwich elimination for one-point consistency.

Given the half-sandwich commutation bound from `commuteGHalfSandwich`, performs
the Cauchy-Schwarz + measurement-completeness argument that converts the
sandwiched operator distance into a one-point consistency bound.

Paper reference: `lem:ld-sandwich-line-one-point` proof in
`ld-pasting.tex` lines 931-1036.

Steps:
1. Simplify by summing out indices `> i` using measurement completeness
2. Apply Cauchy-Schwarz with `commuteGHalfSandwich` to move `Ghat_1` left
3. Apply Cauchy-Schwarz again to move `Ghat_1` right
4. Eliminate `Ghat_<i` product using measurement completeness
5. Reduce to the single-slice bound `eq:ld-gbcon` -/
theorem ldSandwichLineOnePoint_core_of_axis_self
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma zeta : ℝ)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself : strategy.selfConsistencyFailureProbability ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_le : zeta ≤ 1)
    (family : IdxPolyFamily params 𝔓)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hcomm : ∀ j : ℕ, 2 ≤ j →
      CommuteGHalfSandwichStatement params strategy.state family
        gamma zeta j)
    (k i : ℕ) (hi : i < k) :
    strategy.state.ConsRel
      (uniformDistribution (SandwichedLineQuestion params k))
      (ldSandwichLineOnePointLeftFamily params strategy family k i)
      (ldSandwichLineOnePointRightFamily params strategy family k i)
      (ldSandwichLineOnePointError params eps delta gamma zeta k) := by
  have heps_nonneg : 0 ≤ eps :=
    (strategy.state.bipartiteConsError_nonneg
      (uniformDistribution (AxisParallelTestSample params.next))
      (axisParallelPointAnswerFamily strategy)
      (axisParallelLineAnswerFamily strategy)).trans haxis
  have hdelta_nonneg : 0 ≤ delta :=
    (strategy.state.bipartiteSSCError_nonneg
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)).trans hself
  have hzeta_nonneg : 0 ≤ zeta :=
    IdxPolyFamily.zeta_nonneg_of_consistentWithPoints strategy family hcons
  have haxis_small : strategy.axisParallelFailureProbability ≤ min eps 1 :=
    le_min haxis (strategy.state.bipartiteConsError_uniform_le_one
      (axisParallelPointAnswerFamily strategy) (axisParallelLineAnswerFamily strategy))
  have hself_small : strategy.selfConsistencyFailureProbability ≤ min delta 1 :=
    le_min hself (bipartiteSSCError_uniform_le_one strategy.state
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
  by_cases hi0 : i = 0
  · subst i
    have hend := ldSandwichLineOnePoint_endpoint_ldGbcon_lift_of_axis_self
      params strategy (min eps 1) (min delta 1) zeta haxis_small hself_small family hcons k 0 hi
    rw [← ldSandwichLineOnePointLeftFamily_zero_eq_endpoint params strategy family hi] at hend
    exact hend.mono
      (ldSandwichLineOnePoint_endpoint_error_le params eps delta gamma zeta k hi
        heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg hzeta_le)
  · /-
    Remaining branch: the paper's two Cauchy-Schwarz transports across the nonempty
    prefix `Ghat_<i`, followed by the same endpoint reduction used above.
    -/
    exact ldSandwichLineOnePoint_nonzero_prefix_transport
      params strategy eps delta gamma zeta
      heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg hzeta_le
      family hi hi0 hcomm
      (ldSandwichLineOnePointPrefixMoved_consRel_endpoint_of_axis_self
        params strategy (min eps 1) (min delta 1) zeta haxis_small hself_small family hcons hi)

/-- Internal form of `lem:ld-sandwich-line-one-point` after applying
`cor:G-hat-facts`.

**Source:** The proof in `references/ldt-paper/ld-pasting.tex:956-1074` uses
the half-sandwich commutation estimates obtained from `cor:G-hat-facts`.  The
paper-facing theorem `ldSandwichLineOnePoint` below derives those estimates
from the source hypotheses. -/
theorem ldSandwichLineOnePoint_ofGHatFacts_of_axis_self
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma zeta : ℝ)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself_good : strategy.selfConsistencyFailureProbability ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_le : zeta ≤ 1)
    (family : IdxPolyFamily params 𝔓)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hfacts : GHatFactsStatement params strategy.state family gamma zeta)
    (k i : ℕ)
    (hi : i < k) :
    LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i :=
  ⟨ldSandwichLineOnePoint_core_of_axis_self params strategy eps delta gamma zeta
    haxis hself_good hgamma_nonneg hzeta_le family hcons
    (fun j hj => commuteGHalfSandwich_ofGHatFacts params strategy.state family gamma zeta
      j hj hzeta_le hfacts) k i hi⟩

/-- Internal form of `lem:ld-sandwich-line-one-point` after applying
`cor:G-hat-facts`.

This source-facing statement retains the usual good-strategy hypothesis. -/
theorem ldSandwichLineOnePoint_ofGHatFacts
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma zeta : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (_hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (_hdq_le : params.d ≤ params.q)
    (family : IdxPolyFamily params 𝔓)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
    (_hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (hfacts : GHatFactsStatement params strategy.state family gamma zeta)
    (k i : ℕ)
    (hi : i < k) :
    LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i :=
  ldSandwichLineOnePoint_ofGHatFacts_of_axis_self params strategy eps delta gamma zeta
    hgood.axisParallelTest hgood.selfConsistencyTest
    (gamma_nonneg_of_isGood params.next strategy hgood) hzeta_le family hcons hfacts k i hi

/-- `lem:ld-sandwich-line-one-point`, source-facing form. -/
theorem ldSandwichLineOnePoint
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma zeta : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (family : IdxPolyFamily params 𝔓)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k i : ℕ)
    (hi : i < k) :
    LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i :=
  ldSandwichLineOnePoint_ofGHatFacts params strategy eps delta gamma zeta
    hgood hgamma_le hzeta_le hdq_le family hcons hself hbound
    (gHatFacts params strategy family eps delta gamma zeta
      (gamma_nonneg_of_isGood params.next strategy hgood) hgamma_le
      (IdxPolyFamily.zeta_nonneg_of_consistentWithPoints strategy family hcons) hzeta_le
      hdq_le hgood hcons hself hbound)
    k i hi

end MIPRE.LIDT.Co.Pasting

end
