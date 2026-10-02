/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
ComparisonLemmas/CommuteGHalfSandwich/MoveChain/Core.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.CommuteGHalfSandwich.MoveChain.FlatChainStep

@[expose] public section

/-!
# Section 12 pasting: half-sandwich chain assembly

The move chain, the flat post-move chain and the move-back chain assembled into the
operator-family estimate used by `lem:commute-g-half-sandwich`: the counterpart of the vendored
file of the same path under `MIPRE/Background/LIDT/MIPStarRE/LDT/` in the port of
`planning/c6b-plan.md` (milestone M11, section "Port conventions").

`commuteGHalfSandwich_core params S family gamma zeta k hk hzeta_le hsc hcom` takes the symmetric
model `S : SymModel 𝔓 K` where the vendored `ψbi` was; the vendored lemma has no swap, density or
normalization hypothesis. The proof is the vendored one: the case `k = 2` is
`commuteGHalfSandwich_core_two`, and for `k = r + 2` the flat chain of
`commuteGHalfSandwich_flatChainStep` is composed in one call to `Preliminaries.sddOpRel_chain`,
its endpoints identified with the move source and the recursive target, and the result carried to
the half-sandwich by `commuteGHalfSandwich_split_succ_iff` and `commuteGHalfSandwich_split_iff`.
The final estimate of the chain error against `commuteGHalfSandwichError` is one `mul_le_mul`
from the classical sum `commuteGHalfSandwich_flatChainError_sum` and the chain length `3r + 1`,
where the vendored proof argues by `nlinarith`.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel PointTuple avgOver_nonneg uniformDistribution)
open MIPStarRE.LDT.Pasting (SliceQuestion SlicePairQuestion MoveQ gHatSelfConsistencyError
  gHatCommutationError commuteGHalfSandwichError commuteGHalfSandwich_flatChainLength
  commuteGHalfSandwich_flatChainError
  commuteGHalfSandwich_postMoveFlatLength_eq commuteGHalfSandwich_flatChainError_sum
  commuteGHalfSandwich_error_bound)
open MIPRE.LIDT.Co (SymModel IdxPolyFamily)
open MIPRE.LIDT.Co.CommutativityPoints (sddOpRel_congr_outcome)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ## Main theorem: `commuteGHalfSandwich_core`

The flat-chain construction and the final error envelope.
-/

/-- The staged move-commute-move chain for `commuteGHalfSandwich`.

Constructs the sequence of `3k - 4` intermediate bipartite operator families
joined by `3k - 5` elementary edges. These edges repeatedly move `Ĝ₁` through
the product `Ĝ₁ · Ĝ₂ · ⋯ · Ĝₖ` using self-consistency (move to right tensor,
error `2ζ`) and pairwise commutation (swap past neighbor, error `ν₃`), then
compose them in one call to `sddOpRel_chain`, avoiding the exponential loss from
recursive macro-chain composition.

Paper reference: `lem:commute-g-half-sandwich` computation in
`ld-pasting.tex` lines 881–914. -/
theorem commuteGHalfSandwich_core
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ) (k : ℕ) (hk : 2 ≤ k)
    (hzeta_le : zeta ≤ 1)
    (hsc : S.SDDRel
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily S params family)
      (gHatSelfConsistencyRightFamily S params family)
      (gHatSelfConsistencyError zeta))
    (hcom : S.SDDOpRel
      (uniformDistribution (SlicePairQuestion params))
      (gHatPairProductLeft S params family)
      (gHatPairProductRight S params family)
      (gHatCommutationError params gamma zeta)) :
    S.SDDOpRel
      (uniformDistribution (PointTuple params k))
      (gHatHalfSandwichLeft S params family k)
      (gHatHalfSandwichRight S params family k)
      (commuteGHalfSandwichError params gamma zeta k) := by
  obtain rfl | hk3 := hk.eq_or_lt
  · exact commuteGHalfSandwich_core_two params S family gamma zeta hcom
  obtain ⟨r, rfl⟩ : ∃ r, k = r + 2 := ⟨k - 2, by omega⟩
  have hzeta_nonneg : 0 ≤ zeta := by
    have h := (S.sddError_nonneg _ _ _).trans hsc.squaredDistanceBound
    simp only [gHatSelfConsistencyError] at h
    linarith
  have hν_nonneg : 0 ≤ gHatCommutationError params gamma zeta :=
    (avgOver_nonneg _ _ fun _ => Preliminaries.qSDDOp_nonneg S.toVecState _ _).trans
      hcom.squaredDistanceBound
  have hchain := Preliminaries.sddOpRel_chain S.toVecState
    (uniformDistribution (MoveQ params r)) (commuteGHalfSandwich_flatChainLength r)
    (commuteGHalfSandwich_flatChainFamily S params family r)
    (commuteGHalfSandwich_flatChainError params gamma zeta r)
    (commuteGHalfSandwich_flatChainStep params S family gamma zeta hsc hcom r)
  have hsplit := sddOpRel_congr_outcome S.toVecState _ _ _
    (commuteGHalfSandwich_moveSourceFamily S params family r)
    (commuteGHalfSandwich_recursiveTargetFamily S params family r) _
    (commuteGHalfSandwich_flatChainFamily_zero params S family r)
    (commuteGHalfSandwich_flatChainFamily_last params S family r) hchain
  have hpoint := (commuteGHalfSandwich_split_iff params S family (r + 1) _).2
    ((commuteGHalfSandwich_split_succ_iff params S family r _).2 hsplit)
  refine Preliminaries.sddOpRel_mono S.toVecState _ _ _ _ _ hpoint
    (le_trans ?_ (commuteGHalfSandwich_error_bound params gamma zeta (r + 2) hzeta_nonneg
      hzeta_le))
  have hlen : ((commuteGHalfSandwich_flatChainLength r : ℕ) : ℝ) = 3 * r + 1 := by
    rw [commuteGHalfSandwich_flatChainLength, commuteGHalfSandwich_postMoveFlatLength_eq]
    push_cast
    ring
  rw [hlen, commuteGHalfSandwich_flatChainError_sum]
  push_cast
  have hr : (0 : ℝ) ≤ r := r.cast_nonneg
  exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)

end MIPRE.LIDT.Co.Pasting

end
