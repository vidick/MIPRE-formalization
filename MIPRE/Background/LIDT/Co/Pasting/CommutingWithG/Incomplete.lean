/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
CommutingWithG/Incomplete.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored
file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.CommutingWithG.Complete

@[expose] public section

/-!
# Section 12 pasting: commuting-with-G incomplete part

Incomplete-part commuting-with-`G` bounds, `cor:commuting-with-G-incomplete`: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/CommutingWithG/Incomplete.lean` in the port of
`planning/c6b-plan.md` (milestone M11, section "Port conventions").

The vendored second bipartite state `ψbi : QuantumState (ι × ι)` is the symmetric model
`S : SymModel 𝔓 K`, in the vendored argument position, and a strategy is a
`SymStrat params.next 𝔓 K`; the slice family is an `IdxPolyFamily params 𝔓`.

Both bounds compare outcome differences: with `T = G^y` the complete part, the commutator of
`G^x_g` with `1 - T` is minus its commutator with `T`, and the commutator of `1 - G^x` with
`1 - G^y` is the commutator of `G^x` with `G^y`. The vendored proofs check these identities
entrywise on Kronecker products; here they are identities in `𝔓`, by `noncomm_ring`, placed by
`S.L` (`S.leftTensor_sub`).

## Not ported

Nothing: every declaration of the vendored file is ported here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel avgOver_congr uniformDistribution)
open MIPStarRE.LDT.Pasting (SlicePairQuestion commutingWithGIncompleteError)
open MIPRE.LIDT.Co (SymModel VecState SymStrat IdxPolyFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Internal form of `cor:commuting-with-G-incomplete` after applying
`cor:commuting-with-G-complete`.

**Source:** The proof in `references/ldt-paper/ld-pasting.tex:775-816`
uses `cor:commuting-with-G-complete` internally.  The paper-facing theorem
`commutingWithGIncomplete` below derives that complete-part commutation
statement from the source hypotheses rather than exposing it as a public
hypothesis. -/
theorem commutingWithGIncomplete_ofComplete
    (params : Parameters)
    [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ)
    (hcomm : CommutingWithGCompleteStatement params S family gamma zeta) :
    CommutingWithGIncompleteStatement params S family gamma zeta := by
  refine ⟨⟨le_of_eq_of_le ?_ hcomm.pointWithCompletePartCommutation.squaredDistanceBound⟩,
    ⟨le_of_eq_of_le ?_ hcomm.completePartCommutation.squaredDistanceBound⟩⟩
  · refine avgOver_congr _ _ _ fun q => Finset.sum_congr rfl fun g _ => ?_
    -- `G^x_g (1 - T) - (1 - T) G^x_g = -(G^x_g T - T G^x_g)`, `T = G^y`.
    set A := (family.meas q.1).outcome g
    set T := (family.meas q.2).total
    have hdiff : S.L (A * (1 - T)) - S.L ((1 - T) * A) = -(S.L (A * T) - S.L (T * A)) := by
      rw [S.leftTensor_sub, S.leftTensor_sub, ← map_neg S.L]
      congr 1
      noncomm_ring
    show S.ev (star (S.L (A * (1 - T)) - S.L ((1 - T) * A)) *
        (S.L (A * (1 - T)) - S.L ((1 - T) * A))) =
      S.ev (star (S.L (A * T) - S.L (T * A)) * (S.L (A * T) - S.L (T * A)))
    rw [hdiff, star_neg, neg_mul_neg]
  · refine avgOver_congr _ _ _ fun q => ?_
    unfold VecState.qSDDOp VecState.qSDDCore
    refine Finset.sum_congr rfl fun u _ => ?_
    -- `(1 - A)(1 - B) - (1 - B)(1 - A) = A B - B A`, `A = G^x`, `B = G^y`.
    set A := (family.meas q.1).total
    set B := (family.meas q.2).total
    have hdiff : S.L ((1 - A) * (1 - B)) - S.L ((1 - B) * (1 - A)) =
        S.L (A * B) - S.L (B * A) := by
      rw [S.leftTensor_sub, S.leftTensor_sub]
      congr 1
      noncomm_ring
    have hA : (completePartSubMeas params family q.1).outcome u = A := by
      rw [completePartSubMeas_outcome_unit, completePartSubMeas_total]
    show S.ev (star (S.L ((1 - A) * (1 - B)) - S.L ((1 - B) * (1 - A))) *
        (S.L ((1 - A) * (1 - B)) - S.L ((1 - B) * (1 - A)))) =
      S.ev (star (S.L ((completePartSubMeas params family q.1).outcome u * B) -
          S.L (B * (completePartSubMeas params family q.1).outcome u)) *
        (S.L ((completePartSubMeas params family q.1).outcome u * B) -
          S.L (B * (completePartSubMeas params family q.1).outcome u)))
    rw [hA, hdiff]

/-- `cor:commuting-with-G-incomplete`, source-facing form. -/
theorem commutingWithGIncomplete
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (eps delta gamma zeta : ℝ)
    (hgamma_nonneg : 0 ≤ gamma) (hgamma : gamma ≤ 1)
    (hzeta_nonneg : 0 ≤ zeta) (hzeta : zeta ≤ 1)
    (hd_le_q : params.d ≤ params.q)
    (hgood : strategy.IsGood eps delta gamma)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    CommutingWithGIncompleteStatement params strategy.state family gamma zeta :=
  commutingWithGIncomplete_ofComplete params strategy.state family gamma zeta
    (commutingWithGComplete params strategy family eps delta gamma zeta
      hgamma_nonneg hgamma hzeta_nonneg hzeta hd_le_q hgood hcons hself hbound)

end MIPRE.LIDT.Co.Pasting

end
