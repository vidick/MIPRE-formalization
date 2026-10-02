/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Bridge.Measurement
public import MIPRE.Background.LIDT.Co.Test.StrategyCore

@[expose] public section

/-!
# Bridge, part 3, over models: measurements

The model counterpart of the repository's matrix bridge
`MIPRE/Background/LIDT/Bridge/Measurement.lean` (not a vendored file; it serves the tensor
instance and stays), in the port of `planning/c6b-plan.md` (milestone M14, unit M14-0).

A projective strategy for our game in a bipartite model carries one projective measurement per
question, `P : Question F m → POVMIn (Answer F m d) R` with `hP : ∀ x, IsPVMIn (P x).op`, in a
star-ordered `⋆`-ring `R` (one of the two algebras of the model). The ported two-space strategy
container `MIPRE.LIDT.Co.ProjStrat` (`Co/Test/StrategyCore.lean`) wants instead

* point measurements with outcomes in the coded field,
* a measurement for *every* presentation `(base, direction)` of an axis-parallel line, with
  outcomes the polynomials of degree `≤ d` in the parameter of that presentation, covariant under
  rebasing the presentation (`AxisParallelMeasurementReparamInvariant`),
* and likewise for diagonal lines.

They are built as in the matrix bridge, from the strategy's measurements at the *canonical* line
questions: the measurement at a presentation `ℓ` is the coarse-graining of the measurement at the
canonical question of `ℓ` along the map sending an answer `g` (a polynomial in the canonical
parameter `s`) to the polynomial `t ↦ g(b + c·t)` in the parameter `t` of `ℓ`. Covariance follows
from the composition law `affine_comp_shift`, through the classical lemmas `axisAnswer_reparamAt`,
`axisCanon_rebaseAt`, `axisBase_rebaseAt` and their diagonal analogues.

**The coarse-graining.** The port's `ProjMeas.postprocess` (`Co/Basic/SubMeasurementFamilies.lean`)
asks for a C⋆-algebra, since it derives the orthogonality of the outcomes of a projective
measurement from positivity. The algebras of a bipartite model in `MIPRE.LIDT.Simul.SoundIn` are
only star-ordered `⋆`-rings, so here the coarse-graining is `postprocessMeas P hP x φ`: the port's
`postprocess` of the submeasurement `toProjMeas P hP x`, made projective by `IsPVMIn.coarse`, which
uses the orthogonality that `IsPVMIn` records. In a C⋆-algebra it is `ProjMeas.postprocess`, by
`rfl` (`postprocessMeas_eq_postprocess`).

**Reused by import.** Every classical declaration of the matrix bridge, which does not mention a
measurement, is imported, not restated: the canonical-line lemmas `Line.*` (namespace
`MIPRE.LIDT.Line`), `affine` and `affine_comp_shift`, the answer readings `axisPolyOf`,
`diagPolyOf`, `axisAnswer`, `diagAnswer` with their `*_reparamAt` and `*_zeroCoord` lemmas, the
canonical presentations `axisCanon`, `axisBase`, `diagCanon`, `diagData` with their `*_rebaseAt`
lemmas, and `codedValue`. Those this file uses are named through an explicit
`open MIPRE.LIDT.Bridge (…)` list, which names none of the declarations redeclared here.

## Not ported

The declarations of the matrix bridge that mention a measurement are redeclared here, under their
names, for an IsPVMIn family in a star-ordered `⋆`-ring: `toProjMeas`, `toProjMeas_outcome`,
`toProjMeas_total`, `postprocess_outcome_congr` (stated for the port's `postprocess` of any
submeasurement), `axisMeas`, `axisMeas_invariant`, `diagMeas`, `diagMeas_invariant` and
`pointMeas`. Nothing of the matrix bridge is left out; its classical half is imported, as above.

## New here

- `postprocessMeas`, `postprocessMeas_toSubMeas`, `postprocessMeas_outcome`,
  `postprocessMeas_eq_postprocess`: the coarse-graining of an IsPVMIn family, above.
-/

open MIPStarRE.LDT (Fq AxisParallelLine DiagonalLine AxisLinePolynomial DiagonalLinePolynomial
  zeroCoord)
open MIPRE.LIDT.Bridge (lidtParams enc dec decP axisPolyOf diagPolyOf axisAnswer
  diagAnswer axisAnswer_reparamAt diagAnswer_reparamAt axisCanon axisBase axisCanon_rebaseAt
  axisBase_rebaseAt diagCanon diagData diagCanon_rebaseAt diagData_rebaseAt codedValue)

noncomputable section

namespace MIPRE.LIDT.Co.Bridge

/-! ## From projective families to the port's measurements -/

section Generic

variable {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
  {X A : Type*} [Fintype A]

/-- The measurement for the question `x` of a projective family `P` in `R`, as a projective
measurement of the port (`ProjMeas.ofIsPVMIn`). -/
def toProjMeas (P : X → POVMIn A R) (hP : ∀ x, IsPVMIn (P x).op) (x : X) : ProjMeas A R :=
  ProjMeas.ofIsPVMIn (P x).op (hP x)

/-- The outcomes of `toProjMeas P hP x` are those of `P x`. -/
@[simp] theorem toProjMeas_outcome (P : X → POVMIn A R) (hP : ∀ x, IsPVMIn (P x).op) (x : X)
    (a : A) : (toProjMeas P hP x).outcome a = (P x).op a := rfl

/-- The total operator of `toProjMeas P hP x` is `1`. -/
@[simp] theorem toProjMeas_total (P : X → POVMIn A R) (hP : ∀ x, IsPVMIn (P x).op) (x : X) :
    (toProjMeas P hP x).total = 1 := rfl

/-- The coarse-graining of `toProjMeas P hP x` along `φ`: the port's `postprocess` of its
submeasurement, projective by `IsPVMIn.coarse`. In a C⋆-algebra it is `ProjMeas.postprocess`
(`postprocessMeas_eq_postprocess`). -/
def postprocessMeas (P : X → POVMIn A R) (hP : ∀ x, IsPVMIn (P x).op) (x : X) {B : Type*}
    [Fintype B] (φ : A → B) : ProjMeas B R where
  toMeasurement :=
    { toSubMeas := postprocess (toProjMeas P hP x).toSubMeas φ
      total_eq_one := rfl }
  proj b := by
    classical
    change (postprocess (toProjMeas P hP x).toSubMeas φ).outcome b *
      (postprocess (toProjMeas P hP x).toSubMeas φ).outcome b =
        (postprocess (toProjMeas P hP x).toSubMeas φ).outcome b
    rw [SubMeas.postprocess_outcome]
    exact ((hP x).coarse φ).idem b

/-- The submeasurement of `postprocessMeas P hP x φ` is the port's `postprocess`. -/
@[simp] theorem postprocessMeas_toSubMeas (P : X → POVMIn A R) (hP : ∀ x, IsPVMIn (P x).op)
    (x : X) {B : Type*} [Fintype B] (φ : A → B) :
    (postprocessMeas P hP x φ).toSubMeas = postprocess (toProjMeas P hP x).toSubMeas φ := rfl

/-- The outcome of `postprocessMeas P hP x φ` at `b` is the sum of `P x` over the fibre of `φ`. -/
theorem postprocessMeas_outcome (P : X → POVMIn A R)
    (hP : ∀ x, IsPVMIn (P x).op) (x : X) {B' : Type*} [Fintype B'] [DecidableEq B'] (φ : A → B')
    (b : B') :
    (postprocessMeas P hP x φ).outcome b = ∑ a ∈ Finset.univ.filter (fun a => φ a = b), (P x).op a :=
  SubMeas.postprocess_outcome _ φ b

/-- Two coarse-grainings of the same submeasurement agree on outcomes whose fibres agree. -/
theorem postprocess_outcome_congr {α β : Type*} [Fintype α] [Fintype β] (M : SubMeas α R)
    (φ φ' : α → β) (b b' : β) (h : ∀ a, φ' a = b' ↔ φ a = b) :
    (postprocess M φ').outcome b' = (postprocess M φ).outcome b := by
  classical
  simp only [SubMeas.postprocess_outcome]
  exact Finset.sum_congr (Finset.filter_congr fun a _ => h a) fun _ _ => rfl

end Generic

/-- In a C⋆-algebra, `postprocessMeas` is the port's `ProjMeas.postprocess`. -/
theorem postprocessMeas_eq_postprocess {R : Type*} [CStarAlgebra R] [PartialOrder R]
    [StarOrderedRing R] {X A : Type*} [Fintype A] (P : X → POVMIn A R)
    (hP : ∀ x, IsPVMIn (P x).op) (x : X) {B : Type*} [Fintype B] (φ : A → B) :
    postprocessMeas P hP x φ = (toProjMeas P hP x).postprocess φ := rfl

/-! ## Line and point measurement families -/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]
  {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]

/-- The axis-parallel line measurement family induced by a projective family `P`: at a
presentation `ℓ`, the measurement at the canonical line of `ℓ`, its answers read in the
parameter of `ℓ`. -/
def axisMeas (P : Question F m → POVMIn (Answer F m d) R) (hP : ∀ x, IsPVMIn (P x).op) :
    IdxProjMeas (AxisParallelLine (lidtParams F m d)) (AxisLinePolynomial (lidtParams F m d)) R :=
  fun ℓ => postprocessMeas P hP (.axisLine (axisCanon ℓ)) (axisAnswer (axisBase ℓ))

/-- The axis-parallel line measurement family induced by a projective family is covariant
under rebasing. -/
theorem axisMeas_invariant (P : Question F m → POVMIn (Answer F m d) R)
    (hP : ∀ x, IsPVMIn (P x).op) :
    AxisParallelMeasurementReparamInvariant (lidtParams F m d) (axisMeas P hP) := by
  intro ℓ t f
  change (postprocess _ _).outcome _ = (postprocess _ _).outcome _
  rw [axisCanon_rebaseAt, axisBase_rebaseAt]
  apply postprocess_outcome_congr
  intro a
  rw [← axisAnswer_reparamAt]
  exact (AxisLinePolynomial.reparamAtEquiv t).apply_eq_iff_eq

/-- The diagonal line measurement family induced by a projective family `P`: at a presentation
`ℓ`, the measurement at the canonical line of `ℓ`, its answers read in the parameter of `ℓ`
through the change of parameters `diagData ℓ`. -/
def diagMeas (P : Question F m → POVMIn (Answer F m d) R) (hP : ∀ x, IsPVMIn (P x).op) :
    IdxProjMeas (DiagonalLine (lidtParams F m d)) (DiagonalLinePolynomial (lidtParams F m d)) R :=
  fun ℓ => postprocessMeas P hP (.diagLine (diagCanon ℓ))
    (diagAnswer (diagData ℓ).1 (diagData ℓ).2)

/-- The diagonal line measurement family induced by a projective family is covariant under
rebasing. -/
theorem diagMeas_invariant (P : Question F m → POVMIn (Answer F m d) R)
    (hP : ∀ x, IsPVMIn (P x).op) :
    DiagonalMeasurementReparamInvariant (lidtParams F m d) (diagMeas P hP) := by
  intro ℓ t f
  change (postprocess _ _).outcome _ = (postprocess _ _).outcome _
  rw [diagCanon_rebaseAt, diagData_rebaseAt]
  apply postprocess_outcome_congr
  intro a
  rw [← diagAnswer_reparamAt]
  exact (DiagonalLinePolynomial.reparamAtEquiv t).apply_eq_iff_eq

/-- The point measurement family induced by a projective family `P`: at a coded point `u`, the
measurement at the point question `decP u`, its answers read as coded values. -/
def pointMeas (P : Question F m → POVMIn (Answer F m d) R) (hP : ∀ x, IsPVMIn (P x).op) :
    IdxProjMeas (MIPStarRE.LDT.Point (lidtParams F m d)) (Fq (lidtParams F m d)) R :=
  fun u => postprocessMeas P hP (.point (decP u)) codedValue

end MIPRE.LIDT.Co.Bridge

end

end
