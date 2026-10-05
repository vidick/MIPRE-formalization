/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
ComparisonLemmas/CommuteGHalfSandwich/MoveChain/FlatChain.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.CommuteGHalfSandwich.MoveChain.Chain
public import MIPStarRE.LDT.Pasting.ComparisonLemmas.CommuteGHalfSandwich.MoveChain.FlatChain

@[expose] public section

/-!
# Section 12 pasting: half-sandwich flat chain

The post-move and combined flat chains used after the distinguished completed-slice factor has
been moved to the right tensor register, alternating between pairwise commutation and
self-consistency steps: the counterpart of the vendored file of the same path under
`MIPRE/Background/LIDT/MIPStarRE/LDT/` in the port of `planning/c6b-plan.md` (milestone M11,
section "Port conventions").

The chain lengths, the error sequences and their sums are classical and imported from the
vendored file. The two families take the symmetric model `S : SymModel 𝔓 K` as their first
explicit argument, as the placed families of `Setup/Definitions` and `MoveChain/Lifting` do:
`commuteGHalfSandwich_postMoveFlatFamily S params family r i` and
`commuteGHalfSandwich_flatChainFamily S params family r i`. The outcome identities, whose vendored
versions have no state, take `S` second, after `params`, as
`commuteGHalfSandwich_moveChainFamily_zero` does. No vendored lemma here has a swap, density or
normalization hypothesis.

The recursions unfold by `ite_eq_left`, `ite_eq_right`, `dite_eq_left` and `dite_eq_right` (the
current names of the deprecated `if_pos`, `if_neg`, `dif_pos`, `dif_neg`), and the outcome
identities hold by `S.leftTensor_one`, `S.rightTensor_one`, `S.leftTensor_mul_leftTensor` and
association up to definitional equality, where the vendored proofs unfold by `simp`; the last
family of the post-move chain is reached by induction through
`commuteGHalfSandwich_prefixSecondSliceLeft_splitSuccLift_eq_secondSliceLift`, as in the vendored
proof, with the index `Fin.last` reached by definitional equality.

## Not ported

- `commuteGHalfSandwich_postMoveFlatLength`: classical, imported.
- `commuteGHalfSandwich_postMoveFlatError`: classical, imported.
- `commuteGHalfSandwich_postMoveFlatError_sum`: classical, imported.
- `commuteGHalfSandwich_flatChainLength`: classical, imported.
- `commuteGHalfSandwich_flatChainError`: classical, imported.
- `commuteGHalfSandwich_postMoveFlatLength_eq`: classical, imported.
- `commuteGHalfSandwich_flatChainError_sum`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel PointTuple)
open MIPStarRE.LDT.Pasting (GHatOutcome GHatTupleOutcome SliceQuestion MoveQ MoveO
  commuteGHalfSandwich_postMoveFlatLength commuteGHalfSandwich_flatChainLength
  commuteGHalfSandwich_postMoveFlatLength_eq)
open MIPRE.LIDT.Co (SymModel IdxOpFamily IdxPolyFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ## Post-move flat chain and flat-chain families -/

/-- Operator-family sequence for the post-move part of the flat chain. -/
noncomputable def commuteGHalfSandwich_postMoveFlatFamily (S : SymModel 𝔓 K)
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) :
    (r : ℕ) → Fin (commuteGHalfSandwich_postMoveFlatLength r + 1) →
      IdxOpFamily (MoveQ params r) (MoveO params r) (K →L[ℂ] K)
  | 0, i =>
      if i.1 = 0 then
        commuteGHalfSandwich_moveFamily S params family 0
      else
        commuteGHalfSandwich_recursiveTargetFamily S params family 0
  | r + 1, i =>
      if i.1 = 0 then
        commuteGHalfSandwich_moveFamily S params family (r + 1)
      else if i.1 = 1 then
        commuteGHalfSandwich_commuteFamily S params family (r + 1)
      else
        commuteGHalfSandwich_prefixSecondSliceLeftFamily S params family (r + 1)
          (commuteGHalfSandwich_splitSuccLiftFamily params r
            ((commuteGHalfSandwich_postMoveFlatFamily S params family r)
                ⟨i.1 - 2, by
                  have hi_lt : i.1 < commuteGHalfSandwich_postMoveFlatLength r + 3 := i.2
                  omega⟩))

/-- Operator-family sequence obtained by concatenating the move chain and the
post-move flat chain. -/
noncomputable def commuteGHalfSandwich_flatChainFamily (S : SymModel 𝔓 K)
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (r : ℕ) :
    Fin (commuteGHalfSandwich_flatChainLength r + 1) →
      IdxOpFamily (MoveQ params r) (MoveO params r) (K →L[ℂ] K) :=
  fun i =>
      if hi : i.1 < r + 1 then
        commuteGHalfSandwich_moveChainFamily S params family r ⟨i.1, hi⟩
      else
        commuteGHalfSandwich_postMoveFlatFamily S params family r
          ⟨i.1 - r, by
            have hi_lt : i.1 < r + commuteGHalfSandwich_postMoveFlatLength r + 1 := i.2
            omega⟩

/-- With no tail, the commuted endpoint is the recursive target. -/
theorem commuteGHalfSandwich_commuteFamily_zero_eq_recursiveTarget
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (q : SliceQuestion params × SliceQuestion params × PointTuple params 0)
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params 0) :
    (commuteGHalfSandwich_commuteFamily S params family 0 q).outcome ogs =
      (commuteGHalfSandwich_recursiveTargetFamily S params family 0 q).outcome ogs := by
  change S.L _ * S.L _ * S.R 1 = S.L _ * (S.L 1 * S.L _)
  rw [S.rightTensor_one, S.leftTensor_one, mul_one, one_mul]

/-- The second-slice lift of the `r`-step recursive target is the `(r + 1)`-step recursive
target. -/
theorem commuteGHalfSandwich_secondSliceLift_recursiveTarget
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (r : ℕ)
    (q : MoveQ params (r + 1))
    (ogs : MoveO params (r + 1)) :
    (commuteGHalfSandwich_secondSliceLiftFamily S params family r
      (commuteGHalfSandwich_recursiveTargetFamily S params family r) q).outcome ogs =
      (commuteGHalfSandwich_recursiveTargetFamily S params family (r + 1) q).outcome ogs :=
  congrArg (_ * ·)
    ((mul_assoc _ _ _).symm.trans (congrArg (· * _) (S.leftTensor_mul_leftTensor _ _)))

/-- The first family of the post-move flat chain is the move family. -/
theorem commuteGHalfSandwich_postMoveFlatFamily_zero_active
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓) :
    ∀ r q ogs,
      (commuteGHalfSandwich_postMoveFlatFamily S params family r 0 q).outcome ogs =
        (commuteGHalfSandwich_moveFamily S params family r q).outcome ogs
  | 0, q, ogs => by
      have h : commuteGHalfSandwich_postMoveFlatFamily S params family 0 0 =
          commuteGHalfSandwich_moveFamily S params family 0 :=
        ite_eq_left rfl
      rw [h]
  | r + 1, q, ogs => by
      have h : commuteGHalfSandwich_postMoveFlatFamily S params family (r + 1) 0 =
          commuteGHalfSandwich_moveFamily S params family (r + 1) :=
        ite_eq_left rfl
      rw [h]

/-- The second family of the post-move flat chain of length `r + 1` is the commuted endpoint. -/
theorem commuteGHalfSandwich_postMoveFlatFamily_one_active
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (r : ℕ)
    (q : MoveQ params (r + 1))
    (ogs : MoveO params (r + 1)) :
    (commuteGHalfSandwich_postMoveFlatFamily S params family (r + 1)
      ⟨1, by
        rw [commuteGHalfSandwich_postMoveFlatLength_eq]
        omega⟩ q).outcome ogs =
      (commuteGHalfSandwich_commuteFamily S params family (r + 1) q).outcome ogs := by
  have h : commuteGHalfSandwich_postMoveFlatFamily S params family (r + 1)
        ⟨1, by rw [commuteGHalfSandwich_postMoveFlatLength_eq]; omega⟩ =
      commuteGHalfSandwich_commuteFamily S params family (r + 1) :=
    (ite_eq_right Nat.one_ne_zero).trans (ite_eq_left rfl)
  rw [h]

/-- The last family of the post-move flat chain is the recursive target. -/
theorem commuteGHalfSandwich_postMoveFlatFamily_last_active
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓) :
    ∀ r q ogs,
      (commuteGHalfSandwich_postMoveFlatFamily S params family r
          (Fin.last (commuteGHalfSandwich_postMoveFlatLength r)) q).outcome ogs =
        (commuteGHalfSandwich_recursiveTargetFamily S params family r q).outcome ogs
  | 0, q, ogs => by
      have h : commuteGHalfSandwich_postMoveFlatFamily S params family 0
            (Fin.last (commuteGHalfSandwich_postMoveFlatLength 0)) =
          commuteGHalfSandwich_recursiveTargetFamily S params family 0 :=
        ite_eq_right Nat.one_ne_zero
      rw [h]
  | r + 1, q, ogs => by
      have h : commuteGHalfSandwich_postMoveFlatFamily S params family (r + 1)
            (Fin.last (commuteGHalfSandwich_postMoveFlatLength (r + 1))) =
          commuteGHalfSandwich_prefixSecondSliceLeftFamily S params family (r + 1)
            (commuteGHalfSandwich_splitSuccLiftFamily params r
              (commuteGHalfSandwich_postMoveFlatFamily S params family r
                (Fin.last (commuteGHalfSandwich_postMoveFlatLength r)))) :=
        (ite_eq_right (Nat.succ_ne_zero _)).trans
          (ite_eq_right fun h => Nat.succ_ne_zero _ (Nat.succ.inj h))
      rw [h]
      refine Eq.trans ?_
        ((commuteGHalfSandwich_prefixSecondSliceLeft_splitSuccLift_eq_secondSliceLift params S
          family r _ q ogs).trans
          (commuteGHalfSandwich_secondSliceLift_recursiveTarget params S family r q ogs))
      exact congrArg (_ * ·)
        (commuteGHalfSandwich_postMoveFlatFamily_last_active params S family r _ _)

/-- The first family of the flat chain is the move source. -/
theorem commuteGHalfSandwich_flatChainFamily_zero
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (r : ℕ) (q : MoveQ params r)
    (ogs : MoveO params r) :
    (commuteGHalfSandwich_flatChainFamily S params family r 0 q).outcome ogs =
      (commuteGHalfSandwich_moveSourceFamily S params family r q).outcome ogs := by
  have h : commuteGHalfSandwich_flatChainFamily S params family r 0 =
      commuteGHalfSandwich_moveChainFamily S params family r ⟨0, Nat.succ_pos r⟩ :=
    dite_eq_left (Nat.succ_pos r)
  rw [h]
  exact commuteGHalfSandwich_moveChainFamily_zero params S family r q ogs

/-- The last family of the flat chain is the recursive target. -/
theorem commuteGHalfSandwich_flatChainFamily_last
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (r : ℕ) (q : MoveQ params r)
    (ogs : MoveO params r) :
    (commuteGHalfSandwich_flatChainFamily S params family r
      (Fin.last (commuteGHalfSandwich_flatChainLength r)) q).outcome ogs =
      (commuteGHalfSandwich_recursiveTargetFamily S params family r q).outcome ogs := by
  have hnot : ¬ (commuteGHalfSandwich_flatChainLength r : ℕ) < r + 1 := by
    unfold commuteGHalfSandwich_flatChainLength
    rw [commuteGHalfSandwich_postMoveFlatLength_eq]
    omega
  have h : commuteGHalfSandwich_flatChainFamily S params family r
        (Fin.last (commuteGHalfSandwich_flatChainLength r)) =
      commuteGHalfSandwich_postMoveFlatFamily S params family r
        (Fin.last (commuteGHalfSandwich_postMoveFlatLength r)) :=
    (dite_eq_right hnot).trans
      (congrArg _ (Fin.ext (Nat.add_sub_cancel_left r _)))
  rw [h]
  exact commuteGHalfSandwich_postMoveFlatFamily_last_active params S family r q ogs

end MIPRE.LIDT.Co.Pasting

end
