/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
ComparisonLemmas/CommuteGHalfSandwich/MoveChain/Base.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.CommuteGHalfSandwich.Setup.StepLemmas.Split
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.CommuteGHalfSandwich.Setup.StepLemmas.Move
public import MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.ComparisonLemmas.CommuteGHalfSandwich.MoveChain.Base

@[expose] public section

/-!
# Section 12 pasting: half-sandwich move-chain base

The first recursive target family of the finite commutation chain in
`lem:commute-g-half-sandwich`, and the equivalence between the split-successor comparison and the
first move-chain comparison: the counterpart of the vendored file of the same path under
`MIPRE/Background/LIDT/MIPStarRE/LDT/` in the port of `planning/c6b-plan.md` (milestone M11,
section "Port conventions").

The question and outcome types `MoveQ`, `MoveO`, `MoveTailQ` and `MoveTailO` are classical and
imported from the vendored file. The recursive target family takes the symmetric model
`S : SymModel 𝔓 K` as its first explicit argument, as the placed families of `Setup/Definitions`
do; callers write `commuteGHalfSandwich_recursiveTargetFamily strategy.state params family r`.
The lemmas take `S` second, after `params`: `commuteGHalfSandwich_recursiveTarget_eq_split params
S family r q ogs`, whose vendored version has no state, gains it there, as
`commuteGHalfSandwich_moveSource_eq_split` does, and `commuteGHalfSandwich_split_succ_iff params S
family r δ` takes it where the vendored `ψbi` was. No vendored lemma here has a swap, density or
normalization hypothesis.

`commuteGHalfSandwich_recursiveTarget_eq_split` holds by `S.leftTensor_mul_leftTensor` up to
definitional equality, where the vendored proof unfolds by `simp`; `split_succ_iff` rewrites with
`sddOpRel_uniform_equiv` and applies the Co `sddOpRel_reindex` and `sddOpRel_congr_outcome` in
each direction, as `commuteGHalfSandwich_split_iff` does.

## Not ported

- `MoveQ`: classical, imported.
- `MoveO`: classical, imported.
- `MoveTailQ`: classical, imported.
- `MoveTailO`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel PointTuple uniformDistribution)
open MIPStarRE.LDT.Pasting (GHatOutcome GHatTupleOutcome SliceQuestion MoveQ MoveO
  splitSuccQuestionEquiv splitSuccOutcomeEquiv)
open MIPRE.LIDT.Co (SymModel IdxOpFamily IdxPolyFamily)
open MIPRE.LIDT.Co.CommutativityPoints (sddOpRel_reindex sddOpRel_congr_outcome)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ## Recursive target family and the split-succ equivalence -/

/-- The recursive target family obtained after one distinguished factor has
been moved into the rotated half-product. -/
noncomputable def commuteGHalfSandwich_recursiveTargetFamily (S : SymModel 𝔓 K)
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (r : ℕ) :
    IdxOpFamily (MoveQ params r) (MoveO params r) (K →L[ℂ] K) :=
  fun q =>
    { outcome := fun ogs =>
        S.L ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          (headTailRotatedFamily S params family r (q.1, q.2.2)).outcome (ogs.1, ogs.2.2)
      total := 0 }

/-- The recursive target family is the rotated head-tail family of length `r + 1`, with the
second distinguished coordinate consed onto the tail. -/
theorem commuteGHalfSandwich_recursiveTarget_eq_split
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (r : ℕ)
    (q : MoveQ params r)
    (ogs : MoveO params r) :
    (commuteGHalfSandwich_recursiveTargetFamily S params family r q).outcome ogs =
      (headTailRotatedFamily S params family (r + 1) (q.1, Fin.cons q.2.1 q.2.2)).outcome
        (ogs.1, Fin.cons ogs.2.1 ogs.2.2) :=
  (mul_assoc _ _ _).symm.trans (congrArg (· * _) (S.leftTensor_mul_leftTensor _ _))

/-- The head-tail commutation relation on `(r + 1)`-tuples is equivalent to the first move-chain
comparison, between the move source and the recursive target. -/
theorem commuteGHalfSandwich_split_succ_iff
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (r : ℕ) (δ : ℝ) :
    S.SDDOpRel
      (uniformDistribution (SliceQuestion params × PointTuple params (r + 1)))
      (headTailOrderedFamily S params family (r + 1))
      (headTailRotatedFamily S params family (r + 1))
      δ ↔
    S.SDDOpRel
      (uniformDistribution (MoveQ params r))
      (commuteGHalfSandwich_moveSourceFamily S params family r)
      (commuteGHalfSandwich_recursiveTargetFamily S params family r)
      δ := by
  let e' := splitSuccOutcomeEquiv params r
  rw [sddOpRel_uniform_equiv (splitSuccQuestionEquiv params r) S.toVecState]
  constructor
  · intro h
    exact sddOpRel_congr_outcome S.toVecState _ _ _ _ _ δ
      (fun q ogs => (commuteGHalfSandwich_moveSource_eq_split params S family r q ogs).symm)
      (fun q ogs => (commuteGHalfSandwich_recursiveTarget_eq_split params S family r q ogs).symm)
      (sddOpRel_reindex e' S.toVecState _ _ _ δ h)
  · intro h
    exact sddOpRel_congr_outcome S.toVecState _ _ _ _ _ δ
      (fun q gs => (commuteGHalfSandwich_moveSource_eq_split params S family r q (e' gs)).trans
        (congrArg _ (e'.symm_apply_apply gs)))
      (fun q gs => (commuteGHalfSandwich_recursiveTarget_eq_split params S family r q
        (e' gs)).trans (congrArg _ (e'.symm_apply_apply gs)))
      (sddOpRel_reindex e'.symm S.toVecState _ _ _ δ h)

end MIPRE.LIDT.Co.Pasting

end
