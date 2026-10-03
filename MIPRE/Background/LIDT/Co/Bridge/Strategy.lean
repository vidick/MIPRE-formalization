/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Bridge.Measurement

@[expose] public section

/-!
# Bridge, part 4, over models: strategies

The model counterpart of the repository's matrix bridge `MIPRE/Background/LIDT/Bridge/Strategy.lean`
(not a vendored file; it serves the tensor instance and stays), in the port of
`planning/c6b-plan.md` (milestone M14, unit M14-0).

A projective strategy for our game in a bipartite model `M : MIPRE.BipartiteModel 𝒞 𝒜 ℬ`
(`S : M.ProjStrat (lidtGame F m d)`, `MIPRE/Foundations/ModelStrategy.lean`) is packaged as the
port's two-space projective strategy `MIPRE.LIDT.Co.ProjStrat (lidtParams F m d) 𝒞 𝒜 ℬ`
(`Co/Test/StrategyCore.lean`): the state is `M` itself, normalized by `S.ψ_unit`, and the six
measurement families are those of `Co/Bridge/Measurement.lean` for `S.PA` in `𝒜` and `S.PB` in
`ℬ`, with their four covariance fields. The `rfl` and coarse-graining equations at the end are
the ones the value bridge reads the strategy through: point measurements as coded values of the
point answers, and line measurements evaluated at the coded parameter `0` as the canonical line
answers evaluated at the base point.

## Not ported

Of the matrix bridge, `nonempty_of_unit`, its `Nonempty (Fin S.dA × Fin S.dB)` instance,
`pureState` and `ev_toProjStrat` are not carried over: they turn the state vector of a
tensor-product strategy into a MIPStarRE density matrix, while the port's strategy takes the
bipartite model `M` and its unit vector as they are. `toProjStrat` is `toCoProjStrat` here, and
the equations `pointMeasA_eq`, `pointMeasB_eq`, `axisMeasA_zero_eq`, `axisMeasB_zero_eq` and
`diagMeas_zero_eq` of the matrix `Bridge/Value.lean` are stated here, under their names, for
`toCoProjStrat`.
-/

universe u

open MIPStarRE.LDT (Fq DiagonalLine zeroCoord)
open MIPRE.LIDT.Bridge (lidtParams enc decP axisPolyOf diagPolyOf axisAnswer_zeroCoord
  diagAnswer_zeroCoord diagData codedValue)

noncomputable section

namespace MIPRE.LIDT.Co.Bridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]
  {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜]
  [PartialOrder 𝒜] [StarOrderedRing 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder ℬ]
  [StarOrderedRing ℬ] {M : MIPRE.BipartiteModel.{u} 𝒞 𝒜 ℬ}

/-- The port's two-space projective strategy induced by a projective strategy for our game in
the bipartite model `M`: the state is `M`, and the measurement families are the point, axis-line
and diagonal-line families of `S.PA` and `S.PB`. -/
def toCoProjStrat (S : M.ProjStrat (lidtGame F m d)) : ProjStrat (lidtParams F m d) 𝒞 𝒜 ℬ where
  state := M
  isNormalized := S.ψ_unit
  pointMeasurementA := pointMeas S.PA S.projA
  axisParallelMeasurementA := axisMeas S.PA S.projA
  axisParallelReparamInvariantA := axisMeas_invariant S.PA S.projA
  diagonalMeasurementA := diagMeas S.PA S.projA
  diagonalReparamInvariantA := diagMeas_invariant S.PA S.projA
  pointMeasurementB := pointMeas S.PB S.projB
  axisParallelMeasurementB := axisMeas S.PB S.projB
  axisParallelReparamInvariantB := axisMeas_invariant S.PB S.projB
  diagonalMeasurementB := diagMeas S.PB S.projB
  diagonalReparamInvariantB := diagMeas_invariant S.PB S.projB

/-- The state of the induced strategy is the model. -/
@[simp] theorem toCoProjStrat_state (S : M.ProjStrat (lidtGame F m d)) :
    (toCoProjStrat S).state = M := rfl

/-- The point measurement of player B at a coded point, in coarse-grained form. -/
theorem pointMeasB_eq (S : M.ProjStrat (lidtGame F m d))
    (u : MIPStarRE.LDT.Point (lidtParams F m d)) :
    ((toCoProjStrat S).pointMeasurementB u).toSubMeas =
      postprocess (toProjMeas S.PB S.projB (.point (decP u))).toSubMeas codedValue := rfl

/-- The point measurement of player A at a coded point, in coarse-grained form. -/
theorem pointMeasA_eq (S : M.ProjStrat (lidtGame F m d))
    (u : MIPStarRE.LDT.Point (lidtParams F m d)) :
    ((toCoProjStrat S).pointMeasurementA u).toSubMeas =
      postprocess (toProjMeas S.PA S.projA (.point (decP u))).toSubMeas codedValue := rfl

/-- The axis-parallel line measurement of player A evaluated at the coded parameter `0`, in
coarse-grained form: the canonical line answer evaluated at the base point. -/
theorem axisMeasA_zero_eq (S : M.ProjStrat (lidtGame F m d))
    (u : MIPStarRE.LDT.Point (lidtParams F m d)) (i : Fin m) :
    postprocess ((toCoProjStrat S).axisParallelMeasurementA ⟨u, i⟩).toSubMeas (· zeroCoord) =
      postprocess
        (toProjMeas S.PA S.projA (.axisLine (Line.through (decP u) (Pi.single i 1)))).toSubMeas
        fun a => enc ((axisPolyOf a).eval (decP u i)) := by
  change postprocess (postprocess _ _) _ = _
  rw [SubMeas.postprocess_comp]
  simp only [axisAnswer_zeroCoord]
  rfl

/-- The axis-parallel line measurement of player B evaluated at the coded parameter `0`, in
coarse-grained form. -/
theorem axisMeasB_zero_eq (S : M.ProjStrat (lidtGame F m d))
    (u : MIPStarRE.LDT.Point (lidtParams F m d)) (i : Fin m) :
    postprocess ((toCoProjStrat S).axisParallelMeasurementB ⟨u, i⟩).toSubMeas (· zeroCoord) =
      postprocess
        (toProjMeas S.PB S.projB (.axisLine (Line.through (decP u) (Pi.single i 1)))).toSubMeas
        fun a => enc ((axisPolyOf a).eval (decP u i)) := by
  change postprocess (postprocess _ _) _ = _
  rw [SubMeas.postprocess_comp]
  simp only [axisAnswer_zeroCoord]
  rfl

/-- The diagonal line measurement of a projective family evaluated at the coded parameter `0`,
in coarse-grained form: the canonical line answer is read at the parameter of the base point. -/
theorem diagMeas_zero_eq {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    (P : Question F m → POVMIn (Answer F m d) R)
    (hP : ∀ x, IsPVMIn (P x).op) (ℓ : DiagonalLine (lidtParams F m d)) :
    postprocess (diagMeas P hP ℓ).toSubMeas (· zeroCoord) =
      postprocess
        (toProjMeas P hP (.diagLine (Line.through (decP ℓ.base) (decP ℓ.direction)))).toSubMeas
        fun a => enc ((diagPolyOf a).eval
          ((Line.through (decP ℓ.base) (decP ℓ.direction)).param (decP ℓ.base))) := by
  change postprocess (postprocess _ _) _ = _
  rw [SubMeas.postprocess_comp]
  simp only [diagAnswer_zeroCoord]
  have : (diagData ℓ).1 =
      (Line.through (decP ℓ.base) (decP ℓ.direction)).param (decP ℓ.base) := by
    rw [Line.param_through]
    unfold diagData
    split_ifs <;> rfl
  rw [this]
  rfl

end MIPRE.LIDT.Co.Bridge

end

end
