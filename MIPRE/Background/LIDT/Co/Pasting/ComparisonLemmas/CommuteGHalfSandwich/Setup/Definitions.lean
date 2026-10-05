/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
ComparisonLemmas/CommuteGHalfSandwich/Setup/Definitions.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.CommutativityPoints.SharedHelpers.Core
public import MIPRE.Background.LIDT.Co.Preliminaries.CompletionTransfer
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.Common
public import MIPStarRE.LDT.Pasting.ComparisonLemmas.CommuteGHalfSandwich.Setup.Definitions

@[expose] public section

/-!
# Section 12 pasting: commute G half-sandwich setup — definitions

Operator definitions and family constructions for the half-sandwich commutation chain, with the
small helper lemmas used by the sum-bound and step-commutation submodules: the counterpart of
the vendored file of the same path under `MIPRE/Background/LIDT/MIPStarRE/LDT/` in the port of `planning/c6b-plan.md` (milestone M11, section "Port conventions").

The slice family is an `IdxPolyFamily params 𝔓`, and the reverse half-product is a local
operator in `𝔓` that reads no state. The placed families take the symmetric model
`S : SymModel 𝔓 K` as their first explicit argument, in place of the vendored named carriers
`(ι₁ := ι)`, `(ι₂ := ι)`, so their outcomes are products of `S.L (…)` and `S.R (…)`; callers write
`headTailOrderedFamily strategy.state params family r` where the vendored text was
`headTailOrderedFamily params family r`. The lemmas take the vendored state in its vendored
argument position: `S : SymModel 𝔓 K` where it carries placed families, and `V : VecState K`
in the same-space `sddOpRel_uniform_equiv` and `sddOpRel_uniform_fst`, to which callers pass
`strategy.state` or `S`. No vendored lemma here has a swap, density or normalization hypothesis.

The split lemmas hold by `S.leftTensor_mul_leftTensor` up to definitional equality, where the
vendored proofs unfold by `simp`; `gHatSelfConsistency_sddOpRel` and
`commuteGHalfSandwich_move_recursive_zero` hold by definitional equality and `S.leftTensor_one`,
`S.rightTensor_one`.

## Not ported

- `pointTupleConsEquiv`: classical, imported.
- `thirdSliceFrontEquiv`: classical, imported.
- `splitQuestionEquiv`: classical, imported.
- `prefixTripleOutcomeEquiv`: classical, imported.
- `pairTailOutcomeEquiv`: classical, imported.
- `splitSuccQuestionEquiv`: classical, imported.
- `splitSuccOutcomeEquiv`: classical, imported.
- `moveTailQuestionEquiv`: classical, imported.
- `moveTailOutcomeEquiv`: classical, imported.
- `firstSliceBackQuestionEquiv`: classical, imported.
- `firstSliceBackOutcomeEquiv`: classical, imported.
- `pointTupleOneEquiv`: classical, imported.
- `gHatTupleOutcomeOneEquiv`: classical, imported.
- `splitQuestionEquivOne`: classical, imported.
- `splitOutcomeEquivOne`: classical, imported.
- `thirdSliceFrontOutcomeEquiv`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel PointTuple Distribution avgOver avgOver_uniform_equiv
  avgOver_uniform_fst uniformDistribution)
open MIPStarRE.LDT.Pasting (GHatOutcome GHatTupleOutcome SliceQuestion SlicePairQuestion
  pointTupleTail gHatTupleOutcomeTail gHatTupleOutcomeConsEquiv' gHatSelfConsistencyError
  gHatCommutationError pointTupleConsEquiv)
open MIPRE.LIDT.Co (SymModel VecState IdxSubMeas OpFamily IdxOpFamily IdxPolyFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ### Sandwich-chain comparison lemmas

These lemmas capture the infrastructure needed for the `lem:commute-g-half-sandwich`
through `cor:h-a-consistency` chain in `ld-pasting.tex` §9.3.

The n-step `SDDOpRel` composition lemma (`sddOpRel_chain`) lives in
`MIPRE.LIDT.Co.Preliminaries` (`Co/Preliminaries/CompletionTransfer.lean`) alongside
`sddOpRel_triangle`, since it is a general-purpose result used by multiple chapters. -/

/-- Reverse-ordered half-product of completed-slice outcome operators,
`\widehat G^{x_k}_{g_k} \cdots \widehat G^{x_1}_{g_1}`. -/
noncomputable def gHatReverseHalfProductOutcomeOperator
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) :
    (k : ℕ) → PointTuple params k → GHatTupleOutcome params k → 𝔓
  | 0, _xs, _gs => 1
  | k + 1, xs, gs =>
      gHatReverseHalfProductOutcomeOperator params family k
          (pointTupleTail xs) (gHatTupleOutcomeTail gs) *
        ((gHatIdxMeas params family (xs 0)).toSubMeas).outcome (gs 0)

/-- Ordered head-tail family with the head completed-slice operator followed
by the remaining half-product on the left tensor register. -/
noncomputable def headTailOrderedFamily (S : SymModel 𝔓 K)
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (r : ℕ) :
    IdxOpFamily
      (SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatTupleOutcome params r)
      (K →L[ℂ] K) :=
  fun q =>
    { outcome := fun ogs =>
        S.L ((gHatIdxMeas params family q.1).outcome ogs.1) *
          S.L (gHatHalfProductOutcomeOperator params family r q.2 ogs.2)
      total :=
        S.L (gHatIdxMeas params family q.1).total *
          S.L (gHatHalfProductTotalOperator params family r q.2) }

/-- Rotated head-tail family with the tail half-product placed before the head
completed-slice operator. -/
noncomputable def headTailRotatedFamily (S : SymModel 𝔓 K)
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (r : ℕ) :
    IdxOpFamily
      (SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatTupleOutcome params r)
      (K →L[ℂ] K) :=
  fun q =>
    { outcome := fun ogs =>
        S.L (gHatHalfProductOutcomeOperator params family r q.2 ogs.2) *
          S.L ((gHatIdxMeas params family q.1).outcome ogs.1)
      total :=
        S.L (gHatHalfProductTotalOperator params family r q.2) *
          S.L (gHatIdxMeas params family q.1).total }

/-- Move-family endpoint with two distinguished left-register factors and the
reverse half-product on the right register. -/
noncomputable def commuteGHalfSandwich_moveFamily (S : SymModel 𝔓 K)
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (r : ℕ) :
    IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (K →L[ℂ] K) :=
  fun q =>
    { outcome := fun ogs =>
        S.L ((gHatIdxMeas params family q.1).outcome ogs.1) *
          S.L ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          S.R (gHatReverseHalfProductOutcomeOperator params family r q.2.2 ogs.2.2)
      total :=
        S.L (gHatIdxMeas params family q.1).total *
          S.L (gHatIdxMeas params family q.2.1).total *
          S.R (gHatHalfProductTotalOperator params family r q.2.2) }

/-- Commuted endpoint obtained by interchanging the two distinguished
left-register completed-slice factors. -/
noncomputable def commuteGHalfSandwich_commuteFamily (S : SymModel 𝔓 K)
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (r : ℕ) :
    IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (K →L[ℂ] K) :=
  fun q =>
    { outcome := fun ogs =>
        S.L ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          S.L ((gHatIdxMeas params family q.1).outcome ogs.1) *
          S.R (gHatReverseHalfProductOutcomeOperator params family r q.2.2 ogs.2.2)
      total :=
        S.L (gHatIdxMeas params family q.2.1).total *
          S.L (gHatIdxMeas params family q.1).total *
          S.R (gHatHalfProductTotalOperator params family r q.2.2) }

/-- The outcomes of the `(k + 1)`-fold half-sandwich are those of the ordered head-tail family,
after splitting off the first coordinate of the question and outcome tuples. -/
theorem gHatHalfSandwichLeft_split_outcome
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (k : ℕ)
    (xs : PointTuple params (k + 1))
    (gs : GHatTupleOutcome params (k + 1)) :
    (gHatHalfSandwichLeft S params family (k + 1) xs).outcome gs =
      (headTailOrderedFamily S params family k ((pointTupleConsEquiv params k) xs)).outcome
        ((gHatTupleOutcomeConsEquiv' params k) gs) :=
  (S.leftTensor_mul_leftTensor _ _).symm

/-- The total of the `(k + 1)`-fold half-sandwich is that of the ordered head-tail family. -/
theorem gHatHalfSandwichLeft_split_total
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (k : ℕ)
    (xs : PointTuple params (k + 1)) :
    (gHatHalfSandwichLeft S params family (k + 1) xs).total =
      (headTailOrderedFamily S params family k ((pointTupleConsEquiv params k) xs)).total :=
  (S.leftTensor_mul_leftTensor _ _).symm

/-- The outcomes of the rotated `(k + 1)`-fold half-sandwich are those of the rotated head-tail
family, after splitting off the first coordinate of the question and outcome tuples. -/
theorem gHatHalfSandwichRight_split_outcome
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (k : ℕ)
    (xs : PointTuple params (k + 1))
    (gs : GHatTupleOutcome params (k + 1)) :
    (gHatHalfSandwichRight S params family (k + 1) xs).outcome gs =
      (headTailRotatedFamily S params family k ((pointTupleConsEquiv params k) xs)).outcome
        ((gHatTupleOutcomeConsEquiv' params k) gs) :=
  (S.leftTensor_mul_leftTensor _ _).symm

/-- The total of the rotated `(k + 1)`-fold half-sandwich is that of the rotated head-tail
family. -/
theorem gHatHalfSandwichRight_split_total
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (k : ℕ)
    (xs : PointTuple params (k + 1)) :
    (gHatHalfSandwichRight S params family (k + 1) xs).total =
      (headTailRotatedFamily S params family k ((pointTupleConsEquiv params k) xs)).total :=
  (S.leftTensor_mul_leftTensor _ _).symm

/-- Under uniform questions, an operator-family distance relation is invariant under
reindexing the questions along an equivalence `e : α ≃ β`. -/
theorem sddOpRel_uniform_equiv
    {α β Outcome : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    [Fintype Outcome]
    (e : α ≃ β)
    (V : VecState K)
    (A B : IdxOpFamily α Outcome (K →L[ℂ] K))
    (δ : ℝ) :
    V.SDDOpRel (uniformDistribution α) A B δ ↔
      V.SDDOpRel (uniformDistribution β)
        (fun b => A (e.symm b))
        (fun b => B (e.symm b))
        δ := by
  have h := avgOver_uniform_equiv e (fun a => V.qSDDOp (A a) (B a))
  exact ⟨fun ⟨h'⟩ => ⟨h.symm.trans_le h'⟩, fun ⟨h'⟩ => ⟨h.trans_le h'⟩⟩

/-! ### Base cases and consistency lifts -/

/-- The self-consistency of the completed slices, as a relation between submeasurements, is the
same relation between the underlying operator families. -/
theorem gHatSelfConsistency_sddOpRel
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (zeta : ℝ)
    (hsc : S.SDDRel
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily S params family)
      (gHatSelfConsistencyRightFamily S params family)
      (gHatSelfConsistencyError zeta)) :
    S.SDDOpRel
      (uniformDistribution (SliceQuestion params))
      (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyLeftFamily S params family))
      (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyRightFamily S params family))
      (gHatSelfConsistencyError zeta) :=
  ⟨hsc.squaredDistanceBound⟩

/-- An operator-family distance relation over uniform questions `a` persists when an unused
uniform coordinate `b` is adjoined to the question. -/
theorem sddOpRel_uniform_fst
    {α β Outcome : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    [Fintype Outcome]
    (V : VecState K)
    (A B : IdxOpFamily α Outcome (K →L[ℂ] K))
    (δ : ℝ) :
    V.SDDOpRel (uniformDistribution α) A B δ →
      V.SDDOpRel (uniformDistribution (α × β))
        (fun ab => A ab.1)
        (fun ab => B ab.1)
        δ := fun ⟨h⟩ =>
  ⟨(avgOver_uniform_fst (β := β) fun a => V.qSDDOp (A a) (B a)).trans_le h⟩

/-- The commutation of completed-slice pairs, restated on the triple questions
`(x, y, xs)` of the move chain. -/
theorem gHatPairProduct_sddOpRel_triple
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ) (r : ℕ)
    (hcom : S.SDDOpRel
      (uniformDistribution (SlicePairQuestion params))
      (gHatPairProductLeft S params family)
      (gHatPairProductRight S params family)
      (gHatCommutationError params gamma zeta)) :
    S.SDDOpRel
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      (fun q => gHatPairProductLeft S params family (q.1, q.2.1))
      (fun q => gHatPairProductRight S params family (q.1, q.2.1))
      (gHatCommutationError params gamma zeta) :=
  (sddOpRel_uniform_equiv
    (Equiv.prodAssoc (SliceQuestion params) (SliceQuestion params) (PointTuple params r))
    S.toVecState
    (fun q => gHatPairProductLeft S params family q.1)
    (fun q => gHatPairProductRight S params family q.1)
    (gHatCommutationError params gamma zeta)).1
    (sddOpRel_uniform_fst (β := PointTuple params r) S.toVecState
      (gHatPairProductLeft S params family) (gHatPairProductRight S params family)
      (gHatCommutationError params gamma zeta) hcom)

/-! ### Move-step and source families -/

/-- Source family for a single move step: three distinguished completed-slice
operators and the tail half-product all lie on the left tensor register. -/
noncomputable def commuteGHalfSandwich_moveStepSourceFamily (S : SymModel 𝔓 K)
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (r : ℕ) :
    IdxOpFamily
      (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (K →L[ℂ] K) :=
  fun q =>
    { outcome := fun ogs =>
        S.L ((gHatIdxMeas params family q.1).outcome ogs.1) *
          S.L ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          S.L ((gHatIdxMeas params family q.2.2.1).outcome ogs.2.2.1) *
          S.L (gHatHalfProductOutcomeOperator params family r q.2.2.2 ogs.2.2.2)
      total :=
        S.L (gHatIdxMeas params family q.1).total *
          S.L (gHatIdxMeas params family q.2.1).total *
          S.L (gHatIdxMeas params family q.2.2.1).total *
          S.L (gHatHalfProductTotalOperator params family r q.2.2.2) }

/-- Target family for a single move step: the exposed tail coordinate and the
reverse tail half-product have been moved to the right tensor register. -/
noncomputable def commuteGHalfSandwich_moveStepTargetFamily (S : SymModel 𝔓 K)
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (r : ℕ) :
    IdxOpFamily
      (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (K →L[ℂ] K) :=
  fun q =>
    { outcome := fun ogs =>
        S.L ((gHatIdxMeas params family q.1).outcome ogs.1) *
          S.L ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          S.R (gHatReverseHalfProductOutcomeOperator params family r q.2.2.2 ogs.2.2.2) *
          S.R ((gHatIdxMeas params family q.2.2.1).outcome ogs.2.2.1)
      total :=
        S.L (gHatIdxMeas params family q.1).total *
          S.L (gHatIdxMeas params family q.2.1).total *
          S.R (gHatIdxMeas params family q.2.2.1).total *
          S.R (gHatHalfProductTotalOperator params family r q.2.2.2) }

/-- Intermediate family for a move step, after the third distinguished
completed-slice operator but before that operator is moved to the right. -/
noncomputable def commuteGHalfSandwich_moveStepMidFamily (S : SymModel 𝔓 K)
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (r : ℕ) :
    IdxOpFamily
      (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (K →L[ℂ] K) :=
  fun q =>
    { outcome := fun ogs =>
        S.L ((gHatIdxMeas params family q.1).outcome ogs.1) *
          S.L ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          S.L ((gHatIdxMeas params family q.2.2.1).outcome ogs.2.2.1) *
          S.R (gHatReverseHalfProductOutcomeOperator params family r q.2.2.2 ogs.2.2.2)
      total :=
        S.L (gHatIdxMeas params family q.1).total *
          S.L (gHatIdxMeas params family q.2.1).total *
          S.L (gHatIdxMeas params family q.2.2.1).total *
          S.R (gHatHalfProductTotalOperator params family r q.2.2.2) }

/-- Source endpoint of the move chain before the first tail coordinate has been
exposed. -/
noncomputable def commuteGHalfSandwich_moveSourceFamily (S : SymModel 𝔓 K)
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (r : ℕ) :
    IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (K →L[ℂ] K) :=
  fun q =>
    { outcome := fun ogs =>
        S.L ((gHatIdxMeas params family q.1).outcome ogs.1) *
          S.L ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          S.L (gHatHalfProductOutcomeOperator params family r q.2.2 ogs.2.2)
      total :=
        S.L (gHatIdxMeas params family q.1).total *
          S.L (gHatIdxMeas params family q.2.1).total *
          S.L (gHatHalfProductTotalOperator params family r q.2.2) }

/-! ### Move-source splitting lemmas -/

/-- The source endpoint of the move chain is the ordered head-tail family of length `r + 1`,
with the second distinguished coordinate consed onto the tail. -/
theorem commuteGHalfSandwich_moveSource_eq_split
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (r : ℕ)
    (q : SliceQuestion params × SliceQuestion params × PointTuple params r)
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) :
    (commuteGHalfSandwich_moveSourceFamily S params family r q).outcome ogs =
      (headTailOrderedFamily S params family (r + 1) (q.1, Fin.cons q.2.1 q.2.2)).outcome
        (ogs.1, Fin.cons ogs.2.1 ogs.2.2) :=
  (mul_assoc _ _ _).trans (congrArg (_ * ·) (S.leftTensor_mul_leftTensor _ _))

/-- At tail length `0` the move source and the move endpoint agree, so they are at distance
`0`. -/
theorem commuteGHalfSandwich_move_recursive_zero
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓) :
    S.SDDOpRel
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params 0))
      (commuteGHalfSandwich_moveSourceFamily S params family 0)
      (commuteGHalfSandwich_moveFamily S params family 0)
      0 := by
  refine ⟨le_of_eq ?_⟩
  have h : ∀ q ogs, (commuteGHalfSandwich_moveSourceFamily S params family 0 q).outcome ogs =
      (commuteGHalfSandwich_moveFamily S params family 0 q).outcome ogs := fun _ _ =>
    congrArg (_ * ·) (S.leftTensor_one.trans S.rightTensor_one.symm)
  simp only [VecState.sddErrorOp, VecState.qSDDOp, VecState.qSDDCore, h, sub_self, mul_zero,
    S.ev_zero, Finset.sum_const_zero]
  simp [avgOver]

end MIPRE.LIDT.Co.Pasting

end
