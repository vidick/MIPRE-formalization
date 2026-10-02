/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Basic/
OpFamily.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Basic.SubMeasurementFamilies

@[expose] public section

/-!
# Raw operator families for the low individual degree test

This file introduces the notion of an indexed family of operators used in the paper
without positivity or boundedness requirements. These are used for `≈_δ`
chains whose intermediate objects are arbitrary operator families rather than
honest submeasurements: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/OpFamily.lean` in the port of
`planning/c6b-plan.md` (milestone M0, section "Port conventions").

The vendored families have their operators in the matrix algebra `Op ι`. Here a raw family
has its operators in an arbitrary type `R`, with no structure at all (the postprocessing asks
for an additive monoid to sum fibres in): local families take `R = 𝔓`, joint ones
`R = K →L[ℂ] K`. A family is placed on a tensor factor by `OpFamily.map` along `S.L` or `S.R`,
so `(A.leftPlacedOpFamily S).outcome a = S.L (A.outcome a)` holds by `rfl`; the placements take
the symmetric model `S` as their first explicit argument, in place of the vendored named
carriers `(ιB := ιB)`, as `SubMeas.liftLeft` does in `Co/Basic/SubMeasurementFamilies.lean`.

## New here

`OpFamily.map` (the image of a family under a map of operator types) and its projections
`map_outcome`, `map_total`, and `SubMeas.toOpFamily_map` (forgetting commutes with `map`).

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/self_improvement.tex`
- `references/ldt-paper/commutativity-points.tex`
- `references/ldt-paper/commutativity-G.tex`
- `references/ldt-paper/ld-pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co

/-- A raw operator family: outcome operators indexed by `α`, without positivity or bound
requirements. This matches the paper's use of arbitrary operator families in
`≈_δ` chains. -/
structure OpFamily (α : Type*) (R : Type*) where
  outcome : α → R
  total : R

/-- Indexed raw operator family (question → outcome → operator). -/
def IdxOpFamily (Question Outcome : Type*) (R : Type*) :=
  Question → OpFamily Outcome R

namespace SubMeas

/-- Forget the positivity and boundedness structure of a submeasurement. -/
def toOpFamily {α : Type*} {R : Type*} [Fintype α] [Ring R] [StarRing R] [PartialOrder R]
    (A : SubMeas α R) : OpFamily α R where
  outcome := A.outcome
  total := A.total

end SubMeas

/-- A submeasurement is a raw operator family. -/
instance {α : Type*} {R : Type*} [Fintype α] [Ring R] [StarRing R] [PartialOrder R] :
    Coe (SubMeas α R) (OpFamily α R) where
  coe := SubMeas.toOpFamily

namespace IdxSubMeas

/-- Forget the positivity and boundedness structure of an indexed submeasurement family. -/
def toIdxOpFamily {Question Outcome : Type*} {R : Type*}
    [Fintype Outcome] [Ring R] [StarRing R] [PartialOrder R]
    (A : IdxSubMeas Question Outcome R) :
    IdxOpFamily Question Outcome R :=
  fun q => (A q).toOpFamily

end IdxSubMeas

namespace OpFamily

/-- The image of a raw operator family under a map of operator types, applied to every
outcome operator and to the total. -/
def map {α : Type*} {R T : Type*} (f : R → T) (A : OpFamily α R) : OpFamily α T where
  outcome a := f (A.outcome a)
  total := f A.total

/-- The outcome operators of the image are the images of the outcome operators. -/
@[simp] theorem map_outcome {α : Type*} {R T : Type*} (f : R → T) (A : OpFamily α R) (a : α) :
    (A.map f).outcome a = f (A.outcome a) :=
  rfl

/-- The total of the image is the image of the total. -/
@[simp] theorem map_total {α : Type*} {R T : Type*} (f : R → T) (A : OpFamily α R) :
    (A.map f).total = f A.total :=
  rfl

section Placement

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Place a raw operator family on the first tensor factor: each operator `A_a` becomes
`S.L A_a` (the vendored `A_a ⊗ 1`). -/
def leftPlacedOpFamily {α : Type*} (S : SymModel 𝔓 K) (A : OpFamily α 𝔓) :
    OpFamily α (K →L[ℂ] K) :=
  A.map S.L

/-- Place a raw operator family on the second tensor factor: each operator `A_a` becomes
`S.R A_a` (the vendored `1 ⊗ A_a`). -/
noncomputable def rightPlacedOpFamily {α : Type*} (S : SymModel 𝔓 K) (A : OpFamily α 𝔓) :
    OpFamily α (K →L[ℂ] K) :=
  A.map S.R

end Placement

/-- Post-process the outcomes of a raw operator family. -/
noncomputable def postprocess {α β : Type*} {R : Type*}
    [Fintype α] [Fintype β] [AddCommMonoid R]
    (A : OpFamily α R) (f : α → β) :
    OpFamily β R :=
  open Classical in
    { outcome := fun b =>
        ∑ a ∈ Finset.univ.filter (fun a => f a = b), A.outcome a
      total := A.total }

end OpFamily

/-- Forgetting the submeasurement structure commutes with taking the image under a
`⋆`-homomorphism. -/
@[simp] theorem SubMeas.toOpFamily_map {α : Type*} [Fintype α]
    {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [PartialOrder R] [StarOrderedRing R]
    {T : Type*} [Ring T] [StarRing T] [Algebra ℂ T] [PartialOrder T] [StarOrderedRing T]
    (f : R →⋆ₐ[ℂ] T) (A : SubMeas α R) :
    (A.map f).toOpFamily = A.toOpFamily.map f :=
  rfl

namespace IdxOpFamily

/-- Lift an indexed raw operator family to the first tensor factor. -/
def liftLeft {Question Outcome : Type*}
    {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (S : SymModel 𝔓 K) (A : IdxOpFamily Question Outcome 𝔓) :
    IdxOpFamily Question Outcome (K →L[ℂ] K) :=
  fun q => (A q).leftPlacedOpFamily S

end IdxOpFamily

end MIPRE.LIDT.Co

end
