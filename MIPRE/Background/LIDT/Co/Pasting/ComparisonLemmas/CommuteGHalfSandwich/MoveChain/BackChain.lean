/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
ComparisonLemmas/CommuteGHalfSandwich/MoveChain/BackChain.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.CommuteGHalfSandwich.MoveChain.Chain

@[expose] public section

/-!
# Section 12 pasting: half-sandwich move-back chain

The reverse part of the finite commutation chain used in `lem:commute-g-half-sandwich`: after the
initial move chain and the flat post-move comparison, these families bring the leading
completed-slice measurement back to the position required by the rotated half-sandwich endpoint.
The counterpart of the vendored file of the same path under `MIPRE/Background/LIDT/MIPStarRE/LDT/`
in the port of `planning/c6b-plan.md` (milestone M11, section "Port conventions").

The move-back family takes the symmetric model `S : SymModel 𝔓 K` as its first explicit argument,
as the placed families of `Setup/Definitions` and `MoveChain/Lifting` do:
`commuteGHalfSandwich_moveBackChainFamily S params family r i`. The lemmas take `S` second, after
`params`: `commuteGHalfSandwich_commute_to_moveBackChainFamily_zero params S family zeta hsc` where
the vendored `ψbi` was, and the three outcome identities, whose vendored versions have no state,
gain it there. No vendored lemma here has a swap, density or normalization hypothesis. The
swapped-front equivalences are classical and imported from the vendored `MoveChain/Lifting`.

The outcome identities hold by association and `S.rightTensor_mul_rightTensor` up to
definitional equality through the swapped-front equivalences, `Fin.cons` and `pointTupleTail`,
where the vendored proofs unfold by `simp`; at index `0` the move-back family is the second-slice
lift of the last move-chain family by definitional equality (`r - 0 = r`), so
`commuteGHalfSandwich_moveChainFamily_last` applies directly. The identity
`commuteGHalfSandwich_moveBackChainFamily_zero_eq_secondSliceLift_moveFamily` is declared before
`commuteGHalfSandwich_commute_to_moveBackChainFamily_zero`, the reverse of the vendored order, so
that the latter cites it rather than repeating its proof, as the vendored proof does.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel uniformDistribution)
open MIPStarRE.LDT.Pasting (SliceQuestion MoveQ MoveO gHatSelfConsistencyError
  moveTailSwappedFrontQuestionEquiv moveTailSwappedFrontOutcomeEquiv)
open MIPRE.LIDT.Co (SymModel IdxOpFamily IdxPolyFamily)
open MIPRE.LIDT.Co.CommutativityPoints (sddOpRel_reindex sddOpRel_congr_outcome)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ## Move-back chain -/

/-- Reverse the move-chain indexing so that the leading completed-slice factor
is moved back through the product. -/
noncomputable def commuteGHalfSandwich_moveBackChainFamily (S : SymModel 𝔓 K)
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (r : ℕ) :
    Fin (r + 1) → IdxOpFamily (MoveQ params (r + 1)) (MoveO params (r + 1)) (K →L[ℂ] K) :=
  fun i =>
    commuteGHalfSandwich_secondSliceLiftFamily S params family r
      ((commuteGHalfSandwich_moveChainFamily S params family r) ⟨r - i.1, by omega⟩)

/-- The second-slice lift of the `r`-move family is the move-step middle family, after exposing
the first tail coordinate and swapping the two distinguished slices. -/
theorem commuteGHalfSandwich_secondSliceLift_moveFamily_eq_swappedFrontMoveStepMid
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (r : ℕ)
    (q : MoveQ params (r + 1))
    (ogs : MoveO params (r + 1)) :
    (commuteGHalfSandwich_secondSliceLiftFamily S params family r
      (commuteGHalfSandwich_moveFamily S params family r) q).outcome ogs =
      (commuteGHalfSandwich_moveStepMidFamily S params family r
        ((moveTailSwappedFrontQuestionEquiv params r) q)).outcome
        ((moveTailSwappedFrontOutcomeEquiv params r) ogs) :=
  (mul_assoc _ _ _).symm.trans (congrArg (· * _) (mul_assoc _ _ _).symm)

/-- The `(r + 1)`-move commuted endpoint is the move-step target family, after exposing the first
tail coordinate and swapping the two distinguished slices. -/
theorem commuteGHalfSandwich_commute_eq_swappedFrontMoveStepTarget
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (r : ℕ)
    (q : MoveQ params (r + 1))
    (ogs : MoveO params (r + 1)) :
    (commuteGHalfSandwich_commuteFamily S params family (r + 1) q).outcome ogs =
      (commuteGHalfSandwich_moveStepTargetFamily S params family r
        ((moveTailSwappedFrontQuestionEquiv params r) q)).outcome
        ((moveTailSwappedFrontOutcomeEquiv params r) ogs) :=
  (congrArg (_ * ·) (S.rightTensor_mul_rightTensor _ _).symm).trans (mul_assoc _ _ _).symm

/-- The first family of the move-back chain is the second-slice lift of the `r`-move family. -/
theorem commuteGHalfSandwich_moveBackChainFamily_zero_eq_secondSliceLift_moveFamily
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (r : ℕ)
    (q : MoveQ params (r + 1))
    (ogs : MoveO params (r + 1)) :
    (commuteGHalfSandwich_moveBackChainFamily S params family r 0 q).outcome ogs =
      (commuteGHalfSandwich_secondSliceLiftFamily S params family r
        (commuteGHalfSandwich_moveFamily S params family r) q).outcome ogs :=
  congrArg (_ * ·) (commuteGHalfSandwich_moveChainFamily_last params S family r _ _)

/-- The commuted endpoint is close to the first family of the move-back chain, at the
self-consistency error. -/
theorem commuteGHalfSandwich_commute_to_moveBackChainFamily_zero
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (zeta : ℝ) {r : ℕ}
    (hsc : S.SDDRel
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily S params family)
      (gHatSelfConsistencyRightFamily S params family)
      (gHatSelfConsistencyError zeta)) :
    S.SDDOpRel
      (uniformDistribution (MoveQ params (r + 1)))
      (commuteGHalfSandwich_commuteFamily S params family (r + 1))
      ((commuteGHalfSandwich_moveBackChainFamily S params family r) 0)
      (gHatSelfConsistencyError zeta) := by
  have htargetMid := Preliminaries.sddOpRel_symm S.toVecState _ _ _ _
    (commuteGHalfSandwich_moveStepMid_toTarget params S family zeta r hsc)
  have hq := (sddOpRel_uniform_equiv (moveTailSwappedFrontQuestionEquiv params r).symm
    S.toVecState (commuteGHalfSandwich_moveStepTargetFamily S params family r)
    (commuteGHalfSandwich_moveStepMidFamily S params family r)
    (gHatSelfConsistencyError zeta)).1 htargetMid
  refine sddOpRel_congr_outcome S.toVecState _ _ _
    (commuteGHalfSandwich_commuteFamily S params family (r + 1))
    (commuteGHalfSandwich_moveBackChainFamily S params family r 0) _ ?_ ?_
    (sddOpRel_reindex (moveTailSwappedFrontOutcomeEquiv params r).symm S.toVecState
      _ _ _ _ hq)
  · exact fun q ogs =>
      (commuteGHalfSandwich_commute_eq_swappedFrontMoveStepTarget params S family r q ogs).symm
  · exact fun q ogs =>
      (commuteGHalfSandwich_secondSliceLift_moveFamily_eq_swappedFrontMoveStepMid params S
        family r q ogs).symm.trans
        (commuteGHalfSandwich_moveBackChainFamily_zero_eq_secondSliceLift_moveFamily params S
          family r q ogs).symm

end MIPRE.LIDT.Co.Pasting

end
