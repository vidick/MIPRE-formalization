/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.LIDT.Bridge.Measurement

/-!
# Bridge, part 4: strategies

A tensor-product strategy for our game (`TensorProductStrategy (lidtGame F m d)`) is
packaged as a MIPStarRE two-space projective strategy (`ProjStrat`): the state vector
becomes a pure state (MIPStarRE's density matrices carry the normalization
`τ(ρ) = 1` for the normalized trace, so the density is `dim · |ψ⟩⟨ψ|`), and the
measurement families are those of `MIPRE.Background.LIDT.Bridge.Measurement`.
-/

open MIPStarRE.LDT (ProjStrat QuantumState PureState ev)
open Matrix

noncomputable section

namespace MIPRE.LIDT.Bridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]

/-- The index type of a unit vector is nonempty. -/
theorem nonempty_of_unit {ι : Type*} [Fintype ι] (ψ : ι → ℂ) (h : star ψ ⬝ᵥ ψ = 1) :
    Nonempty ι := by
  by_contra hne
  rw [not_nonempty_iff] at hne
  have : star ψ ⬝ᵥ ψ = 0 := by simp [dotProduct]
  exact zero_ne_one (this.symm.trans h)

instance (S : TensorProductStrategy (lidtGame F m d)) : Nonempty (Fin S.dA × Fin S.dB) :=
  nonempty_of_unit S.ψ S.ψ_unit

/-- The shared state of a strategy, as a MIPStarRE pure state. -/
def pureState (S : TensorProductStrategy (lidtGame F m d)) : PureState (Fin S.dA × Fin S.dB) :=
  ⟨S.ψ, S.ψ_unit⟩

/-- The MIPStarRE two-space projective strategy induced by a strategy for our game. -/
def toProjStrat (S : TensorProductStrategy (lidtGame F m d)) :
    ProjStrat (lidtParams F m d) (Fin S.dA) (Fin S.dB) where
  state := (pureState S : QuantumState _)
  isNormalized := (pureState S).toQuantumState_isNormalized
  pointMeasurementA := pointMeas S.PA
  axisParallelMeasurementA := axisMeas S.PA
  axisParallelReparamInvariantA := axisMeas_invariant S.PA
  diagonalMeasurementA := diagMeas S.PA
  diagonalReparamInvariantA := diagMeas_invariant S.PA
  pointMeasurementB := pointMeas S.PB
  axisParallelMeasurementB := axisMeas S.PB
  axisParallelReparamInvariantB := axisMeas_invariant S.PB
  diagonalMeasurementB := diagMeas S.PB
  diagonalReparamInvariantB := diagMeas_invariant S.PB

/-- Expectation values in the induced strategy are the Born-rule expectations of `S.ψ`. -/
theorem ev_toProjStrat (S : TensorProductStrategy (lidtGame F m d))
    (X : Matrix (Fin S.dA × Fin S.dB) (Fin S.dA × Fin S.dB) ℂ) :
    ev (toProjStrat S).state X = (star S.ψ ⬝ᵥ (X *ᵥ S.ψ)).re :=
  (pureState S).ev_eq_re_inner X

end MIPRE.LIDT.Bridge

end
