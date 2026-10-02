/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/Sandwich/
Switcheroo.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.Defs.Families
public import MIPRE.Background.LIDT.Co.CommutativityPoints.Defs
public import MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.Sandwich.Switcheroo

@[expose] public section

/-!
# Section 12 — Sandwich constructions: switcheroo families

Switcheroo, complete-part, and half-product operator families: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Sandwich/Switcheroo.lean` in the port of
`planning/c6b-plan.md` (milestone M11, section "Port conventions").

The slice family is an `IdxPolyFamily params 𝔓` and the auxiliary family `M` an
`IdxProjSubMeas (Fq params) Outcome 𝔓`, both in the local C*-algebra `𝔓` (the vendored `Op ι`).
The placed families take the symmetric model `S : SymModel 𝔓 K` as their first explicit
argument, in place of the vendored named carriers `(ιA := ι)`, `(ιB := ι)`, and place by
`S.leftPlacedSubMeas`, `S.rightPlacedSubMeas` and `OpFamily.leftPlacedOpFamily S`, so their
outcomes are `S.L (…)` and `S.R (…)` by `rfl`; callers write
`switcherooPointProductLeft strategy.state params family M` where the vendored text was
`switcherooPointProductLeft params family M`. The half-product operators read no state and are
local operators in `𝔓`.

## Not ported

- `gHatTupleOutcomeConsEquiv'`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Fq PointTuple)
open MIPStarRE.LDT.Pasting (GHatOutcome GHatTupleOutcome SliceQuestion SlicePairQuestion
  pointTupleTail gHatTupleOutcomeTail)
open MIPRE.LIDT.Co (SymModel SubMeas IdxSubMeas IdxProjSubMeas OpFamily IdxOpFamily
  IdxPolyFamily)
open MIPRE.LIDT.Co.CommutativityPoints (orderedProductOpFamily reversedProductOpFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Left tensor-placement for the auxiliary family `M^x_o`. -/
noncomputable def switcherooSelfConsistencyLeft (S : SymModel 𝔓 K) {Outcome : Type*}
    [Fintype Outcome] (params : Parameters) [FieldModel params.q]
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓) :
    IdxSubMeas (SliceQuestion params) Outcome (K →L[ℂ] K) :=
  fun x => S.leftPlacedSubMeas (M x).toSubMeas

/-- Right tensor-placement for the auxiliary family `M^x_o`. -/
noncomputable def switcherooSelfConsistencyRight (S : SymModel 𝔓 K) {Outcome : Type*}
    [Fintype Outcome] (params : Parameters) [FieldModel params.q]
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓) :
    IdxSubMeas (SliceQuestion params) Outcome (K →L[ℂ] K) :=
  fun x => S.rightPlacedSubMeas (M x).toSubMeas

/-- Concrete hypothesis family for `G^x_g M^y_o`. -/
noncomputable def switcherooPointProductLeft (S : SymModel 𝔓 K) {Outcome : Type*}
    [Fintype Outcome] (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (M : IdxProjSubMeas (Fq params) Outcome 𝔓) :
    IdxOpFamily (SlicePairQuestion params) (MIPStarRE.LDT.Polynomial params × Outcome)
      (K →L[ℂ] K) :=
  fun q => OpFamily.leftPlacedOpFamily S <|
    orderedProductOpFamily (family.meas q.1).toSubMeas (M q.2).toSubMeas

/-- Concrete hypothesis family for `M^y_o G^x_g` on the
`Polynomial params × Outcome` outcome type. -/
noncomputable def switcherooPointProductRight (S : SymModel 𝔓 K) {Outcome : Type*}
    [Fintype Outcome] (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (M : IdxProjSubMeas (Fq params) Outcome 𝔓) :
    IdxOpFamily (SlicePairQuestion params) (MIPStarRE.LDT.Polynomial params × Outcome)
      (K →L[ℂ] K) :=
  fun q => OpFamily.leftPlacedOpFamily S <|
    reversedProductOpFamily (family.meas q.1).toSubMeas (M q.2).toSubMeas

/-- Concrete aggregate family for `G^x M^y_o`. -/
noncomputable def switcherooAggregateLeft (S : SymModel 𝔓 K) {Outcome : Type*}
    [Fintype Outcome] (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (M : IdxProjSubMeas (Fq params) Outcome 𝔓) :
    IdxOpFamily (SlicePairQuestion params) Outcome (K →L[ℂ] K) :=
  fun q => OpFamily.leftPlacedOpFamily S <|
    multiplyByTotalOnLeft (completePartSubMeas params family q.1) (M q.2).toSubMeas

/-- Concrete aggregate family for `M^y_o G^x`. -/
noncomputable def switcherooAggregateRight (S : SymModel 𝔓 K) {Outcome : Type*}
    [Fintype Outcome] (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (M : IdxProjSubMeas (Fq params) Outcome 𝔓) :
    IdxOpFamily (SlicePairQuestion params) Outcome (K →L[ℂ] K) :=
  fun q => OpFamily.leftPlacedOpFamily S <|
    multiplyByTotalOnRight (M q.2).toSubMeas (completePartSubMeas params family q.1)

/-- Concrete family for `G^x_g G^y`. -/
noncomputable def completePartPointProductLeft (S : SymModel 𝔓 K) (params : Parameters)
    [FieldModel params.q] (family : IdxPolyFamily params 𝔓) :
    IdxOpFamily (SlicePairQuestion params) (MIPStarRE.LDT.Polynomial params) (K →L[ℂ] K) :=
  fun q => OpFamily.leftPlacedOpFamily S <|
    multiplyByTotalOnRight (family.meas q.1).toSubMeas (completePartSubMeas params family q.2)

/-- Concrete family for `G^y G^x_g`. -/
noncomputable def completePartPointProductRight (S : SymModel 𝔓 K) (params : Parameters)
    [FieldModel params.q] (family : IdxPolyFamily params 𝔓) :
    IdxOpFamily (SlicePairQuestion params) (MIPStarRE.LDT.Polynomial params) (K →L[ℂ] K) :=
  fun q => OpFamily.leftPlacedOpFamily S <|
    multiplyByTotalOnLeft (completePartSubMeas params family q.2) (family.meas q.1).toSubMeas

/-- Concrete family for `G^x G^y`. -/
noncomputable def completePartTotalProductLeft (S : SymModel 𝔓 K) (params : Parameters)
    [FieldModel params.q] (family : IdxPolyFamily params 𝔓) :
    IdxOpFamily (SlicePairQuestion params) Unit (K →L[ℂ] K) :=
  fun q => OpFamily.leftPlacedOpFamily S <|
    multiplyByTotalOnRight (completePartSubMeas params family q.1)
      (completePartSubMeas params family q.2)

/-- Concrete family for `G^y G^x`. -/
noncomputable def completePartTotalProductRight (S : SymModel 𝔓 K) (params : Parameters)
    [FieldModel params.q] (family : IdxPolyFamily params 𝔓) :
    IdxOpFamily (SlicePairQuestion params) Unit (K →L[ℂ] K) :=
  fun q => OpFamily.leftPlacedOpFamily S <|
    multiplyByTotalOnLeft (completePartSubMeas params family q.2)
      (completePartSubMeas params family q.1)

/-- Concrete family for `G^x_g G^y_⊥`. -/
noncomputable def incompletePartPointProductLeft (S : SymModel 𝔓 K) (params : Parameters)
    [FieldModel params.q] (family : IdxPolyFamily params 𝔓) :
    IdxOpFamily (SlicePairQuestion params) (MIPStarRE.LDT.Polynomial params) (K →L[ℂ] K) :=
  fun q => OpFamily.leftPlacedOpFamily S <|
    multiplyByTotalOnRight (family.meas q.1).toSubMeas (incompletePartSubMeas params family q.2)

/-- Concrete family for `G^y_⊥ G^x_g`. -/
noncomputable def incompletePartPointProductRight (S : SymModel 𝔓 K) (params : Parameters)
    [FieldModel params.q] (family : IdxPolyFamily params 𝔓) :
    IdxOpFamily (SlicePairQuestion params) (MIPStarRE.LDT.Polynomial params) (K →L[ℂ] K) :=
  fun q => OpFamily.leftPlacedOpFamily S <|
    multiplyByTotalOnLeft (incompletePartSubMeas params family q.2) (family.meas q.1).toSubMeas

/-- Concrete family for `G^x_⊥ G^y_⊥`. -/
noncomputable def incompletePartTotalProductLeft (S : SymModel 𝔓 K) (params : Parameters)
    [FieldModel params.q] (family : IdxPolyFamily params 𝔓) :
    IdxOpFamily (SlicePairQuestion params) Unit (K →L[ℂ] K) :=
  fun q => OpFamily.leftPlacedOpFamily S <|
    multiplyByTotalOnRight (incompletePartSubMeas params family q.1)
      (incompletePartSubMeas params family q.2)

/-- Concrete family for `G^y_⊥ G^x_⊥`. -/
noncomputable def incompletePartTotalProductRight (S : SymModel 𝔓 K) (params : Parameters)
    [FieldModel params.q] (family : IdxPolyFamily params 𝔓) :
    IdxOpFamily (SlicePairQuestion params) Unit (K →L[ℂ] K) :=
  fun q => OpFamily.leftPlacedOpFamily S <|
    multiplyByTotalOnLeft (incompletePartSubMeas params family q.2)
      (incompletePartSubMeas params family q.1)

/-- Left tensor-placement for `\widehat G^x_g`. -/
noncomputable def gHatSelfConsistencyLeftFamily (S : SymModel 𝔓 K) (params : Parameters)
    [FieldModel params.q] (family : IdxPolyFamily params 𝔓) :
    IdxSubMeas (SliceQuestion params) (GHatOutcome params) (K →L[ℂ] K) :=
  fun x => S.leftPlacedSubMeas (gHatIdxMeas params family x).toSubMeas

/-- Right tensor-placement for `\widehat G^x_g`. -/
noncomputable def gHatSelfConsistencyRightFamily (S : SymModel 𝔓 K) (params : Parameters)
    [FieldModel params.q] (family : IdxPolyFamily params 𝔓) :
    IdxSubMeas (SliceQuestion params) (GHatOutcome params) (K →L[ℂ] K) :=
  fun x => S.rightPlacedSubMeas (gHatIdxMeas params family x).toSubMeas

/-- Concrete family for the pairwise product `\widehat G^x_g \widehat G^y_h`. -/
noncomputable def gHatPairProductLeft (S : SymModel 𝔓 K) (params : Parameters)
    [FieldModel params.q] (family : IdxPolyFamily params 𝔓) :
    IdxOpFamily (SlicePairQuestion params) (GHatOutcome params × GHatOutcome params)
      (K →L[ℂ] K) :=
  fun q => OpFamily.leftPlacedOpFamily S <|
    orderedProductOpFamily (gHatIdxMeas params family q.1).toSubMeas
      (gHatIdxMeas params family q.2).toSubMeas

/-- Concrete family for the reversed pairwise product `\widehat G^y_h \widehat G^x_g`. -/
noncomputable def gHatPairProductRight (S : SymModel 𝔓 K) (params : Parameters)
    [FieldModel params.q] (family : IdxPolyFamily params 𝔓) :
    IdxOpFamily (SlicePairQuestion params) (GHatOutcome params × GHatOutcome params)
      (K →L[ℂ] K) :=
  fun q => OpFamily.leftPlacedOpFamily S <|
    reversedProductOpFamily (gHatIdxMeas params family q.1).toSubMeas
      (gHatIdxMeas params family q.2).toSubMeas

/-- The ordered half-product `\widehat G^{x_1}_{g_1} \cdots \widehat G^{x_k}_{g_k}`. -/
noncomputable def gHatHalfProductOutcomeOperator (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) :
    (k : ℕ) → PointTuple params k → GHatTupleOutcome params k → 𝔓
  | 0, _xs, _gs => 1
  | k + 1, xs, gs =>
      (gHatIdxMeas params family (xs 0)).outcome (gs 0) *
        gHatHalfProductOutcomeOperator params family k (pointTupleTail xs)
          (gHatTupleOutcomeTail gs)

/-- The total half-product
`\sum_{g_1,\dots,g_k} \widehat G^{x_1}_{g_1} \cdots \widehat G^{x_k}_{g_k}`. -/
noncomputable def gHatHalfProductTotalOperator (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) :
    (k : ℕ) → PointTuple params k → 𝔓
  | 0, _xs => 1
  | k + 1, xs =>
      (gHatIdxMeas params family (xs 0)).total *
        gHatHalfProductTotalOperator params family k (pointTupleTail xs)

/-- The cyclically rotated half-product
`\widehat G^{x_2}_{g_2} \cdots \widehat G^{x_k}_{g_k} \widehat G^{x_1}_{g_1}`. -/
noncomputable def gHatRotatedHalfProductOutcomeOperator (params : Parameters)
    [FieldModel params.q] (family : IdxPolyFamily params 𝔓) :
    (k : ℕ) → PointTuple params k → GHatTupleOutcome params k → 𝔓
  | 0, _xs, _gs => 1
  | k + 1, xs, gs =>
      gHatHalfProductOutcomeOperator params family k (pointTupleTail xs)
          (gHatTupleOutcomeTail gs) *
        (gHatIdxMeas params family (xs 0)).outcome (gs 0)

/-- The total cyclically rotated half-product. -/
noncomputable def gHatRotatedHalfProductTotalOperator (params : Parameters)
    [FieldModel params.q] (family : IdxPolyFamily params 𝔓) :
    (k : ℕ) → PointTuple params k → 𝔓
  | 0, _xs => 1
  | k + 1, xs =>
      gHatHalfProductTotalOperator params family k (pointTupleTail xs) *
        (gHatIdxMeas params family (xs 0)).total

/-- The total operator of the ordered half-product is always the identity. -/
theorem gHatHalfProductTotalOperator_eq_one (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) :
    ∀ k (xs : PointTuple params k), gHatHalfProductTotalOperator params family k xs = 1
  | 0, _xs => rfl
  | k + 1, xs => by
      rw [gHatHalfProductTotalOperator,
        gHatHalfProductTotalOperator_eq_one params family k (pointTupleTail xs), mul_one]
      rfl

/-- Summing the ordered half-product over all completed outcomes gives its total operator. -/
theorem gHatHalfProduct_sum_eq_total (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) :
    ∀ k (xs : PointTuple params k),
      (∑ gs : GHatTupleOutcome params k,
        gHatHalfProductOutcomeOperator params family k xs gs) =
          gHatHalfProductTotalOperator params family k xs
  | 0, _xs => by
      rw [Fintype.sum_unique]
      rfl
  | k + 1, xs => by
      have htail : ∀ g (gs : GHatTupleOutcome params k),
          gHatTupleOutcomeTail
            ((Fin.consEquiv fun _ : Fin (k + 1) => GHatOutcome params) (g, gs)) = gs :=
        fun _ _ => rfl
      rw [← (Fin.consEquiv fun _ : Fin (k + 1) => GHatOutcome params).sum_comp,
        Fintype.sum_prod_type]
      simp only [gHatHalfProductOutcomeOperator, gHatHalfProductTotalOperator, htail,
        Fin.consEquiv_apply, Fin.cons_zero, ← Finset.mul_sum]
      rw [← Finset.sum_mul, (gHatIdxMeas params family (xs 0)).sum_eq_total]
      congr 2
      exact gHatHalfProduct_sum_eq_total params family k (pointTupleTail xs)

end MIPRE.LIDT.Co.Pasting

end
