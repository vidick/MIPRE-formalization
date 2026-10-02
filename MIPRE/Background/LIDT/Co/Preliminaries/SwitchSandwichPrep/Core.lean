/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122),
MIPStarRE/LDT/Preliminaries/SwitchSandwichPrep/Core.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Preliminaries.ConsistencyBridges
public import MIPRE.Background.LIDT.MIPStarRE.LDT.Preliminaries.SwitchSandwichPrep.Core

@[expose] public section

/-!
# Switch-sandwich preparation: diagonal masses and bounded operators

Bridge lemmas for `prop:switch-sandwich`: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/SwitchSandwichPrep/Core.lean` in the port of
`planning/c6b-plan.md` (milestone M3, section "Port conventions").

The diagonal-mass lemmas use a single state and joint operators, so they take a vector state
`V : VecState K` (a symmetric model is accepted through its coercion) and submeasurements in
`K →L[ℂ] K`. They drop the vendored normalization hypothesis `hψ : ψ.IsNormalized`, which is a
theorem of the vector state (`V.ev_one_of_isNormalized`). The projective and `OpBounded01`
lemmas do not mention the state, and are stated for any C*-algebra with its order (local
operators in `𝔓`, joint ones in `K →L[ℂ] K`), or for any ordered `⋆`-ring where the proof needs
no more; `opBounded01_hermitian` obtains `star B = B` from `IsSelfAdjoint.of_nonneg`, in place of
the vendored positive semidefiniteness of matrices. `leftTensor_opBounded01` takes the model
`S : SymModel 𝔓 K` as a new first explicit argument, as in `Co/Preliminaries/Defs.lean`.

## Not ported

- `weightedFinsetCauchySchwarz`: classical, imported.
- `weightedFinsetCauchySchwarz_on_selectedSupport`: classical, imported.
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Preliminaries

section VecState

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The diagonal mass of a sub-measurement is bounded by its total mass. -/
theorem subMeas_diagMass_le_mass
    {Outcome : Type*} [Fintype Outcome]
    (V : VecState K) (A : SubMeas Outcome (K →L[ℂ] K)) :
    ∑ a : Outcome, V.ev (A.outcome a * A.outcome a) ≤ V.ev A.total := by
  calc
    ∑ a : Outcome, V.ev (A.outcome a * A.outcome a)
      ≤ ∑ a : Outcome, V.ev (A.outcome a) :=
          Finset.sum_le_sum fun a _ =>
            V.ev_mono _ _ (sq_le_self (A.outcome_pos a) (A.outcome_le_one a))
    _ = V.ev A.total := by rw [← V.ev_sum A.outcome, A.sum_eq_total]

/-- The diagonal mass of a sub-measurement is at most `1` (the state is normalized). -/
theorem subMeas_diagMass_le_one
    {Outcome : Type*} [Fintype Outcome]
    (V : VecState K) (A : SubMeas Outcome (K →L[ℂ] K)) :
    ∑ a : Outcome, V.ev (A.outcome a * A.outcome a) ≤ 1 :=
  (subMeas_diagMass_le_mass V A).trans
    ((V.ev_mono _ _ A.total_le_one).trans_eq V.ev_one_of_isNormalized)

/-- Projective outcomes satisfy `P_a^2 = P_a`, so diagonal mass equals total mass. -/
theorem projSubMeas_diagMass_eq_mass
    {Outcome : Type*} [Fintype Outcome]
    (V : VecState K) (A : ProjSubMeas Outcome (K →L[ℂ] K)) :
    ∑ a : Outcome, V.ev (A.outcome a * A.outcome a) = V.ev A.total := by
  simp_rw [A.proj]
  rw [← V.ev_sum A.outcome, A.sum_eq_total]

end VecState

section CStar

variable {R : Type*} [CStarAlgebra R] [PartialOrder R] [StarOrderedRing R]

/-- Each projective outcome is absorbed by the total projector. -/
theorem projSubMeas_outcome_mul_total_eq_outcome
    {Outcome : Type*} [Fintype Outcome]
    (A : ProjSubMeas Outcome R) (a : Outcome) :
    A.outcome a * A.total = A.outcome a :=
  ProjSubMeas.outcome_mul_total_eq_outcome A a

/-- The total operator of a projective sub-measurement is itself a projector. -/
theorem projSubMeas_total_proj
    {Outcome : Type*} [Fintype Outcome]
    (A : ProjSubMeas Outcome R) :
    A.total * A.total = A.total :=
  ProjSubMeas.total_proj A

/-- Any `OpBounded01` operator satisfies `B * B ≤ 1`. -/
theorem opBounded01_sq_le_one {B : R} (hB : OpBounded01 B) : B * B ≤ 1 :=
  have hB_le_one : B ≤ 1 := sub_nonneg.mp hB.boundedByIdentity
  (sq_le_self hB.nonnegative hB_le_one).trans hB_le_one

end CStar

/-- Any `OpBounded01` operator is self-adjoint. -/
theorem opBounded01_hermitian
    {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    {B : R} (hB : OpBounded01 B) :
    star B = B :=
  (IsSelfAdjoint.of_nonneg hB.nonnegative).star_eq

/-- Left placement preserves the `0 ≤ B ≤ 1` bounds. -/
theorem leftTensor_opBounded01
    {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (S : SymModel 𝔓 K) {B : 𝔓} (hB : OpBounded01 B) :
    OpBounded01 (S.L B) where
  nonnegative := S.leftTensor_nonneg hB.nonnegative
  boundedByIdentity :=
    sub_nonneg.mpr (S.leftTensor_le_one (sub_nonneg.mp hB.boundedByIdentity))

end MIPRE.LIDT.Co.Preliminaries

end
