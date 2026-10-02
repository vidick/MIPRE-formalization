/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
ComparisonLemmas/CommuteGHalfSandwich/MoveChain/FlatChainStep.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.CommuteGHalfSandwich.MoveChain.FlatChain
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.CommuteGHalfSandwich.MoveChain.BackChain

@[expose] public section

/-!
# Section 12 pasting: half-sandwich flat-chain steps

The adjacent-edge estimates for the post-move and combined flat chains, the local inputs to the
final chain composition in the proof of `commuteGHalfSandwich_core`: the counterpart of the
vendored file of the same path under `MIPRE/Background/LIDT/MIPStarRE/LDT/` in the port of
`planning/c6b-plan.md` (milestone M11, section "Port conventions").

Both lemmas take the symmetric model `S : SymModel 𝔓 K` second, after `params`, where the vendored
`ψbi` was: `commuteGHalfSandwich_postMoveFlatStep params S family gamma zeta hsc hcom r i` and
`commuteGHalfSandwich_flatChainStep params S family gamma zeta hsc hcom r i`. Neither has a swap,
density or normalization hypothesis in the vendored file.

Where the vendored proofs compare outcomes by `simp` and transport each edge along
`sddOpRel_congr_outcome`, these rewrite the two families of the edge and its error to the
families of a step lemma, as equalities of families: the recursions unfold by `ite_eq_left`,
`ite_eq_right`, `dite_eq_left` and `dite_eq_right`, and an index whose value is not
definitionally that of the step lemma's index is moved by `Fin.ext`. Outcome identities remain at
the two edges whose families agree only outcome by outcome: the base edge of the post-move chain
(`commuteGHalfSandwich_commuteFamily_zero_eq_recursiveTarget`) and its edge into the move-back
chain (`commuteGHalfSandwich_postMoveFlatFamily_zero_active`,
`commuteGHalfSandwich_moveBackChainFamily_zero_eq_secondSliceLift_moveFamily`). The base edge of
the combined chain is the commutation step at `r = 0`, as the vendored
`commuteGHalfSandwich_postMoveFlatStep` at `0` is, with the move family and the move source
identified outcome by outcome.

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
open MIPStarRE.LDT.Pasting (SliceQuestion SlicePairQuestion MoveQ gHatSelfConsistencyError
  gHatCommutationError commuteGHalfSandwich_postMoveFlatLength
  commuteGHalfSandwich_postMoveFlatError commuteGHalfSandwich_flatChainLength
  commuteGHalfSandwich_flatChainError commuteGHalfSandwich_postMoveFlatLength_eq)
open MIPRE.LIDT.Co (SymModel IdxPolyFamily)
open MIPRE.LIDT.Co.CommutativityPoints (sddOpRel_congr_outcome)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ## Flat-chain step lemmas

`postMoveFlatStep` builds the edges within the post-move phase, and
`flatChainStep` stitches the move-chain prefix and the post-move suffix
into one combined chain.
-/

/-- Adjacent families of the post-move flat chain are at the error of the post-move error
sequence. -/
theorem commuteGHalfSandwich_postMoveFlatStep
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ)
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
    ∀ r (i : Fin (commuteGHalfSandwich_postMoveFlatLength r)),
      S.SDDOpRel
        (uniformDistribution (MoveQ params r))
        ((commuteGHalfSandwich_postMoveFlatFamily S params family r) i.castSucc)
        ((commuteGHalfSandwich_postMoveFlatFamily S params family r) i.succ)
        ((commuteGHalfSandwich_postMoveFlatError params gamma zeta r) i)
  | 0, i => by
      have hi : i.1 = 0 := Nat.lt_one_iff.mp i.2
      have hsrc : commuteGHalfSandwich_postMoveFlatFamily S params family 0 i.castSucc =
          commuteGHalfSandwich_moveFamily S params family 0 :=
        ite_eq_left hi
      have htgt : commuteGHalfSandwich_postMoveFlatFamily S params family 0 i.succ =
          commuteGHalfSandwich_recursiveTargetFamily S params family 0 :=
        ite_eq_right (Nat.succ_ne_zero _)
      rw [hsrc, htgt]
      exact sddOpRel_congr_outcome S.toVecState _ _ _ _ _ _ (fun _ _ => rfl)
        (commuteGHalfSandwich_commuteFamily_zero_eq_recursiveTarget params S family)
        (commuteGHalfSandwich_step_commute params S family gamma zeta 0 hcom)
  | r + 1, i => by
      by_cases hi0 : i.1 = 0
      · have hsrc : commuteGHalfSandwich_postMoveFlatFamily S params family (r + 1) i.castSucc =
            commuteGHalfSandwich_moveFamily S params family (r + 1) :=
          ite_eq_left hi0
        have htgt : commuteGHalfSandwich_postMoveFlatFamily S params family (r + 1) i.succ =
            commuteGHalfSandwich_commuteFamily S params family (r + 1) :=
          (ite_eq_right (Nat.succ_ne_zero _)).trans (ite_eq_left (by simp [hi0]))
        have herr : commuteGHalfSandwich_postMoveFlatError params gamma zeta (r + 1) i =
            gHatCommutationError params gamma zeta :=
          dite_eq_left hi0
        rw [hsrc, htgt, herr]
        exact commuteGHalfSandwich_step_commute params S family gamma zeta (r + 1) hcom
      by_cases hi1 : i.1 = 1
      · have hsrc : commuteGHalfSandwich_postMoveFlatFamily S params family (r + 1) i.castSucc =
            commuteGHalfSandwich_commuteFamily S params family (r + 1) :=
          (ite_eq_right hi0).trans (ite_eq_left hi1)
        have htgt : commuteGHalfSandwich_postMoveFlatFamily S params family (r + 1) i.succ =
            commuteGHalfSandwich_prefixSecondSliceLeftFamily S params family (r + 1)
              (commuteGHalfSandwich_splitSuccLiftFamily params r
                (commuteGHalfSandwich_postMoveFlatFamily S params family r 0)) :=
          (ite_eq_right (Nat.succ_ne_zero _)).trans ((ite_eq_right (by simp [hi1])).trans
            (congrArg (fun j => commuteGHalfSandwich_prefixSecondSliceLeftFamily S params family
              (r + 1) (commuteGHalfSandwich_splitSuccLiftFamily params r
                (commuteGHalfSandwich_postMoveFlatFamily S params family r j)))
              (Fin.ext (by simp [hi1]))))
        have herr : commuteGHalfSandwich_postMoveFlatError params gamma zeta (r + 1) i =
            gHatSelfConsistencyError zeta :=
          (dite_eq_right hi0).trans (dite_eq_left hi1)
        rw [hsrc, htgt, herr]
        refine sddOpRel_congr_outcome S.toVecState _ _ _ _ _ _ (fun _ _ => rfl) ?_
          (commuteGHalfSandwich_commute_to_moveBackChainFamily_zero params S family zeta hsc)
        exact fun q ogs =>
          (commuteGHalfSandwich_moveBackChainFamily_zero_eq_secondSliceLift_moveFamily params S
            family r q ogs).trans (congrArg (_ * ·)
              (commuteGHalfSandwich_postMoveFlatFamily_zero_active params S family r _ _).symm)
      · let j : Fin (commuteGHalfSandwich_postMoveFlatLength r) :=
          ⟨i.1 - 2, by
            have hi_lt : i.1 < commuteGHalfSandwich_postMoveFlatLength r + 2 := i.2
            omega⟩
        have hsrc : commuteGHalfSandwich_postMoveFlatFamily S params family (r + 1) i.castSucc =
            commuteGHalfSandwich_prefixSecondSliceLeftFamily S params family (r + 1)
              (commuteGHalfSandwich_splitSuccLiftFamily params r
                (commuteGHalfSandwich_postMoveFlatFamily S params family r j.castSucc)) :=
          (ite_eq_right hi0).trans (ite_eq_right hi1)
        have htgt : commuteGHalfSandwich_postMoveFlatFamily S params family (r + 1) i.succ =
            commuteGHalfSandwich_prefixSecondSliceLeftFamily S params family (r + 1)
              (commuteGHalfSandwich_splitSuccLiftFamily params r
                (commuteGHalfSandwich_postMoveFlatFamily S params family r j.succ)) :=
          (ite_eq_right (Nat.succ_ne_zero _)).trans
            ((ite_eq_right (by simp only [Fin.val_succ]; omega)).trans
            (congrArg (fun j => commuteGHalfSandwich_prefixSecondSliceLeftFamily S params family
              (r + 1) (commuteGHalfSandwich_splitSuccLiftFamily params r
                (commuteGHalfSandwich_postMoveFlatFamily S params family r j)))
              (Fin.ext (by simp only [Fin.val_succ, j]; omega))))
        have herr : commuteGHalfSandwich_postMoveFlatError params gamma zeta (r + 1) i =
            commuteGHalfSandwich_postMoveFlatError params gamma zeta r j :=
          (dite_eq_right hi0).trans (dite_eq_right hi1)
        rw [hsrc, htgt, herr]
        exact commuteGHalfSandwich_prefixSecondSliceLeftLift params S family (r + 1) _ _ _
          (commuteGHalfSandwich_splitSuccLift params S r _ _ _
            (commuteGHalfSandwich_postMoveFlatStep params S family gamma zeta hsc hcom r j))

/-- Adjacent families of the combined flat chain are at the error of the combined error
sequence. -/
theorem commuteGHalfSandwich_flatChainStep
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ)
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
    ∀ r (i : Fin (commuteGHalfSandwich_flatChainLength r)),
      S.SDDOpRel
        (uniformDistribution (MoveQ params r))
        ((commuteGHalfSandwich_flatChainFamily S params family r) i.castSucc)
        ((commuteGHalfSandwich_flatChainFamily S params family r) i.succ)
        ((commuteGHalfSandwich_flatChainError params gamma zeta r) i)
  | 0, i => by
      have hi : i.1 = 0 := Nat.lt_one_iff.mp i.2
      have hsrc : commuteGHalfSandwich_flatChainFamily S params family 0 i.castSucc =
          commuteGHalfSandwich_moveSourceFamily S params family 0 :=
        dite_eq_left (by simp [hi])
      have htgt : commuteGHalfSandwich_flatChainFamily S params family 0 i.succ =
          commuteGHalfSandwich_recursiveTargetFamily S params family 0 :=
        (dite_eq_right (by simp [hi])).trans (ite_eq_right (by simp [hi]))
      have herr : commuteGHalfSandwich_flatChainError params gamma zeta 0 i =
          gHatCommutationError params gamma zeta :=
        rfl
      rw [hsrc, htgt, herr]
      exact sddOpRel_congr_outcome S.toVecState _ _ _ _ _ _
        (fun _ _ => congrArg (_ * ·) (S.rightTensor_one.trans S.leftTensor_one.symm))
        (commuteGHalfSandwich_commuteFamily_zero_eq_recursiveTarget params S family)
        (commuteGHalfSandwich_step_commute params S family gamma zeta 0 hcom)
  | r + 1, i => by
      by_cases hi : i.1 < r + 1
      · let imove : Fin (r + 1) := ⟨i.1, hi⟩
        have hsrc : commuteGHalfSandwich_flatChainFamily S params family (r + 1) i.castSucc =
            commuteGHalfSandwich_moveChainFamily S params family (r + 1) imove.castSucc :=
          dite_eq_left (Nat.lt_succ_of_lt hi)
        have htgt : commuteGHalfSandwich_flatChainFamily S params family (r + 1) i.succ =
            commuteGHalfSandwich_moveChainFamily S params family (r + 1) imove.succ :=
          dite_eq_left (Nat.succ_lt_succ hi)
        have herr : commuteGHalfSandwich_flatChainError params gamma zeta (r + 1) i =
            gHatSelfConsistencyError zeta :=
          dite_eq_left hi
        rw [hsrc, htgt, herr]
        exact commuteGHalfSandwich_moveChain_step params S family zeta hsc (r + 1) imove
      by_cases hboundary : i.1 = r + 1
      · have hone : 1 < commuteGHalfSandwich_postMoveFlatLength (r + 1) + 1 := by
          rw [commuteGHalfSandwich_postMoveFlatLength_eq]
          omega
        have hone_active : commuteGHalfSandwich_postMoveFlatFamily S params family (r + 1)
              ⟨1, hone⟩ = commuteGHalfSandwich_commuteFamily S params family (r + 1) :=
          (ite_eq_right Nat.one_ne_zero).trans (ite_eq_left rfl)
        have hsrc : commuteGHalfSandwich_flatChainFamily S params family (r + 1) i.castSucc =
            commuteGHalfSandwich_moveFamily S params family (r + 1) :=
          (dite_eq_left (by simp [hboundary])).trans
            ((congrArg (commuteGHalfSandwich_moveChainFamily S params family (r + 1))
              (Fin.ext (by simp [hboundary]) : _ = Fin.last (r + 1))).trans
              (dite_eq_right (lt_irrefl (r + 1))))
        have htgt : commuteGHalfSandwich_flatChainFamily S params family (r + 1) i.succ =
            commuteGHalfSandwich_commuteFamily S params family (r + 1) :=
          (dite_eq_right (by simp [hboundary])).trans
            ((congrArg (commuteGHalfSandwich_postMoveFlatFamily S params family (r + 1))
              (Fin.ext (by simp [hboundary]) : _ = ⟨1, hone⟩)).trans hone_active)
        have herr : commuteGHalfSandwich_flatChainError params gamma zeta (r + 1) i =
            gHatCommutationError params gamma zeta :=
          (dite_eq_right hi).trans (dite_eq_left (by simp [hboundary]))
        rw [hsrc, htgt, herr]
        exact commuteGHalfSandwich_step_commute params S family gamma zeta (r + 1) hcom
      · let j : Fin (commuteGHalfSandwich_postMoveFlatLength (r + 1)) :=
          ⟨i.1 - (r + 1), by
            have hi_lt : i.1 < (r + 1) + commuteGHalfSandwich_postMoveFlatLength (r + 1) := i.2
            omega⟩
        have hsrc : commuteGHalfSandwich_flatChainFamily S params family (r + 1) i.castSucc =
            commuteGHalfSandwich_postMoveFlatFamily S params family (r + 1) j.castSucc :=
          dite_eq_right (by simp only [Fin.val_castSucc]; omega)
        have htgt : commuteGHalfSandwich_flatChainFamily S params family (r + 1) i.succ =
            commuteGHalfSandwich_postMoveFlatFamily S params family (r + 1) j.succ :=
          (dite_eq_right (by simp only [Fin.val_succ]; omega)).trans
            (congrArg (commuteGHalfSandwich_postMoveFlatFamily S params family (r + 1))
              (Fin.ext (by simp only [Fin.val_succ, j]; omega)))
        have herr : commuteGHalfSandwich_flatChainError params gamma zeta (r + 1) i =
            commuteGHalfSandwich_postMoveFlatError params gamma zeta (r + 1) j :=
          dite_eq_right hi
        rw [hsrc, htgt, herr]
        exact commuteGHalfSandwich_postMoveFlatStep params S family gamma zeta hsc hcom (r + 1) j

end MIPRE.LIDT.Co.Pasting

end
