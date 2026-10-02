/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
ComparisonLemmas/CommuteGHalfSandwich/MoveChain/Chain.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.CommuteGHalfSandwich.MoveChain.Lifting

@[expose] public section

/-!
# Section 12 pasting: half-sandwich move chain

The recursive sequence of operator families which moves a completed-slice factor through the
half-product, and its adjacent edges, each supplied by the self-consistency estimate for the
completed-slice family: the counterpart of the vendored file of the same path under
`MIPRE/Background/LIDT/MIPStarRE/LDT/` in the port of `planning/c6b-plan.md` (milestone M11,
section "Port conventions").

The chain family takes the symmetric model `S : SymModel 𝔓 K` as its first explicit argument, as
the placed families of `Setup/Definitions` and `MoveChain/Lifting` do:
`commuteGHalfSandwich_moveChainFamily S params family r i`. The lemmas take `S` second, after
`params`: `commuteGHalfSandwich_moveChainFamily_zero params S family`,
`commuteGHalfSandwich_moveChainFamily_last params S family`, whose vendored versions have no
state, gain it there, and `commuteGHalfSandwich_moveChain_step params S family zeta hsc` takes it
where the vendored `ψbi` was. No vendored lemma here has a swap, density or normalization
hypothesis.

The recursion unfolds by `dite_eq_left` and `dite_eq_right`, and the outcome identities hold by
`S.leftTensor_mul_leftTensor` and association up to definitional equality, where the vendored
proofs unfold by `simp`.

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
open MIPStarRE.LDT.Pasting (SliceQuestion MoveQ MoveO pointTupleTail gHatTupleOutcomeTail
  gHatSelfConsistencyError)
open MIPRE.LIDT.Co (SymModel IdxOpFamily IdxPolyFamily)
open MIPRE.LIDT.Co.CommutativityPoints (sddOpRel_congr_outcome)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ## Move chain: recursive family, step lemma -/

/-- The finite sequence of operator families which moves the distinguished
completed-slice factor across an `r`-tuple tail. -/
noncomputable def commuteGHalfSandwich_moveChainFamily (S : SymModel 𝔓 K)
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) :
    (r : ℕ) → Fin (r + 1) → IdxOpFamily (MoveQ params r) (MoveO params r) (K →L[ℂ] K)
  | 0, _ => commuteGHalfSandwich_moveSourceFamily S params family 0
  | r + 1, i =>
      if hi : i.1 < r + 1 then
        commuteGHalfSandwich_moveChainLiftFamily S params family r
          (commuteGHalfSandwich_moveChainFamily S params family r ⟨i.1, hi⟩)
      else
        commuteGHalfSandwich_moveFamily S params family (r + 1)

/-- The first family of the move chain is the move source. -/
theorem commuteGHalfSandwich_moveChainFamily_zero
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓) :
    ∀ r q ogs,
      (commuteGHalfSandwich_moveChainFamily S params family r 0 q).outcome ogs =
        (commuteGHalfSandwich_moveSourceFamily S params family r q).outcome ogs
  | 0, _, _ => rfl
  | r + 1, q, ogs => by
      have h : commuteGHalfSandwich_moveChainFamily S params family (r + 1) 0 =
          commuteGHalfSandwich_moveChainLiftFamily S params family r
            (commuteGHalfSandwich_moveChainFamily S params family r 0) :=
        dite_eq_left (Nat.succ_pos r)
      rw [h]
      change S.L _ * (commuteGHalfSandwich_moveChainFamily S params family r 0 _).outcome _ = _
      rw [commuteGHalfSandwich_moveChainFamily_zero params S family r]
      change S.L _ * (S.L _ * S.L _ * S.L _) = S.L _ * S.L _ * S.L (_ * _)
      rw [← S.leftTensor_mul_leftTensor]
      simp only [mul_assoc]

/-- The last family of the move chain is the move family. -/
theorem commuteGHalfSandwich_moveChainFamily_last
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓) :
    ∀ r q ogs,
      (commuteGHalfSandwich_moveChainFamily S params family r (Fin.last r) q).outcome ogs =
        (commuteGHalfSandwich_moveFamily S params family r q).outcome ogs
  | 0, _, _ => congrArg (_ * ·) (S.leftTensor_one.trans S.rightTensor_one.symm)
  | r + 1, q, ogs => by
      have h : commuteGHalfSandwich_moveChainFamily S params family (r + 1) (Fin.last (r + 1)) =
          commuteGHalfSandwich_moveFamily S params family (r + 1) :=
        dite_eq_right (lt_irrefl (r + 1))
      rw [h]

/-- Adjacent families of the move chain are at the self-consistency error. -/
theorem commuteGHalfSandwich_moveChain_step
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (zeta : ℝ)
    (hsc : S.SDDRel
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily S params family)
      (gHatSelfConsistencyRightFamily S params family)
      (gHatSelfConsistencyError zeta)) :
    ∀ r (i : Fin r),
      S.SDDOpRel
        (uniformDistribution (MoveQ params r))
        ((commuteGHalfSandwich_moveChainFamily S params family r) i.castSucc)
        ((commuteGHalfSandwich_moveChainFamily S params family r) i.succ)
        (gHatSelfConsistencyError zeta)
  | 0, i => i.elim0
  | r + 1, i => by
      by_cases hi : i.1 < r
      · let j : Fin r := ⟨i.1, hi⟩
        have hcast : commuteGHalfSandwich_moveChainFamily S params family (r + 1) i.castSucc =
            commuteGHalfSandwich_moveChainLiftFamily S params family r
              (commuteGHalfSandwich_moveChainFamily S params family r j.castSucc) :=
          dite_eq_left (Nat.lt_succ_of_lt hi)
        have hsucc : commuteGHalfSandwich_moveChainFamily S params family (r + 1) i.succ =
            commuteGHalfSandwich_moveChainLiftFamily S params family r
              (commuteGHalfSandwich_moveChainFamily S params family r j.succ) :=
          dite_eq_left (Nat.succ_lt_succ hi)
        rw [hcast, hsucc]
        exact commuteGHalfSandwich_moveChainLift params S family r _ _ _
          (commuteGHalfSandwich_moveChain_step params S family zeta hsc r j)
      · obtain rfl : i = Fin.last r := Fin.ext (by simp only [Fin.val_last]; omega)
        have hcast : commuteGHalfSandwich_moveChainFamily S params family (r + 1)
              (Fin.last r).castSucc =
            commuteGHalfSandwich_moveChainLiftFamily S params family r
              (commuteGHalfSandwich_moveChainFamily S params family r (Fin.last r)) :=
          dite_eq_left (Nat.lt_succ_self r)
        have hsucc : commuteGHalfSandwich_moveChainFamily S params family (r + 1)
              (Fin.last r).succ =
            commuteGHalfSandwich_moveFamily S params family (r + 1) :=
          dite_eq_right (lt_irrefl (r + 1))
        rw [hcast, hsucc]
        exact sddOpRel_congr_outcome S.toVecState _ _ _ _ _ _
          (fun q ogs => congrArg (_ * ·)
            (commuteGHalfSandwich_moveChainFamily_last params S family r _ _).symm)
          (fun _ _ => rfl)
          (commuteGHalfSandwich_moveChainLift_moveFamily_last params S family zeta r hsc)

end MIPRE.LIDT.Co.Pasting

end
