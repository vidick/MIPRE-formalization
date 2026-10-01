/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Test/
StrategyCore.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Test.Defs
public import MIPRE.Background.LIDT.MIPStarRE.LDT.Test.StrategyCore

@[expose] public section

/-!
# Section 3 — Strategy core

Base state-invariance and strategy structures for the low individual degree test: the
counterpart of `MIPRE/Background/LIDT/MIPStarRE/LDT/Test/StrategyCore.lean` in the port of
`planning/c6b-plan.md` (milestone M0, section "Port conventions").

The vendored file assumes the swap symmetry of a symmetric strategy: its `SymStrat` carries, beside
the state `ψ : QuantumState (ι × ι)`, a proof `permInvState` that the density matrix is fixed by
the swap `swapDensity` of the two tensor factors, the same fact again as `densityFixed`, and the
normalization `isNormalized`. Here the state is a symmetric model `state : SymModel 𝔓 K`
(`Co/Basic/QuantumState.lean`), and all three are theorems of it: the swap of the two factors is
the flip `S.flip`, which fixes the expectation (`S.ev_flip`), carries `S.L` to `S.R`
(`S.ev_L_eq_ev_R`, the vendored `PermInvState.swap_ev`), and `S.ev 1 = 1` holds by `S.Ψ_norm`.
So the ported `SymStrat` has the field `state` (the vendored text `strategy.state` is unchanged)
and the three measurement families, over the local C*-algebra `𝔓`; the symmetry lemmas of the
vendored file lose their hypothesis `hfix`.

The covariance predicates and the answer families are generic over the ordered `⋆`-ring `R` of
`Co/Basic/SubMeasurementCore.lean` (the vendored `Op ι`), with `[StarOrderedRing R]` where they
postprocess. The two-space `ProjStrat` keeps its two local algebras `𝒜`, `ℬ`; its state is a
bipartite model of the repository, `MIPRE.BipartiteModel 𝒞 𝒜 ℬ`
(`MIPRE/Foundations/BipartiteModel.lean`), and its field `isNormalized` is `‖state.ψ‖ = 1`,
since a bipartite model carries no normalization (`reports/c6b-paper-proofs.md`, §4.1).

The classical declarations of the vendored file (the test samples, `extendRestrictedDirection`,
`lastDirectionLine`, the `Fintype Role` instance) are not ported: this file imports the vendored
file and names them through an explicit `open MIPStarRE.LDT (…)` list.

## Not ported

- `swapDensity`: the swap of the two factors of `ι × ι`; replaced by the model's flip `S.flip`
  (`Co/Basic/QuantumState.lean`). Its algebraic lemmas are ported below with `S.flip` in place of
  `swapDensity`.
- `swapDensity_eq_reindex`: an entrywise matrix identity; `S.flip` is a `⋆`-algebra equivalence
  by construction.
- `normalizedTrace_swapDensity`: the model has no trace; its role is played by `S.ev_flip`.
- `PermInvState`: a hypothesis on the vendored state; both of its fields are theorems of every
  symmetric model, `S.ev_flip` (`density_swap`) and `S.ev_L_eq_ev_R` (`swap_ev`).
- `AxisParallelTestSample`: classical, imported.
- `extendRestrictedDirection`: classical, imported.
- `RestrictedDiagonalSample`: classical, imported.
- `restrictedDiagonalSampleNonempty`: classical, imported.
- `lastDirectionLine`: classical, imported.

The structure fields `permInvState` and `densityFixed` of the vendored `SymStrat` and
`AnswerSymStrat` are not fields here: they are theorems of `strategy.state`, `ev_flip` and
`ev_L_eq_ev_R` (and `S.ev_opTensor_swap_of_density_fixed` for the bipartite form).

## Ported elsewhere

`swapDensity_opTensor`, `ev_swapDensity_of_density_fixed` and
`ev_opTensor_swap_of_density_fixed` are `SymModel` theorems of `Co/Basic/QuantumState.lean`,
without the hypothesis `hfix`. The fields `isNormalized` of `SymStrat` and `AnswerSymStrat` are
the theorems `SymStrat.isNormalized` and `AnswerSymStrat.isNormalized` below.
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co

open MIPStarRE.LDT (Parameters FieldModel Point Fq zeroCoord addCoord Distribution
  uniformDistribution AxisParallelLine AxisLinePolynomial DiagonalLine DiagonalLinePolynomial
  DiagonalLineAnswer AxisParallelTestSample RestrictedDiagonalSample extendRestrictedDirection
  lastDirectionLine)

/-! ### The swap of the two factors -/

namespace SymModel

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (S : SymModel 𝔓 K)

/-- The flip is an involution (the vendored `swapDensity_swapDensity`). -/
theorem swapDensity_swapDensity (X : K →L[ℂ] K) : S.flip (S.flip X) = X :=
  S.flip_flip X

/-- The flip is additive (the vendored `swapDensity_add`). -/
theorem swapDensity_add (X Y : K →L[ℂ] K) : S.flip (X + Y) = S.flip X + S.flip Y :=
  S.flip.map_add' X Y

/-- The flip is complex-linear (the vendored `swapDensity_smul`). -/
theorem swapDensity_smul (c : ℂ) (X : K →L[ℂ] K) : S.flip (c • X) = c • S.flip X :=
  S.flip.map_smul' c X

/-- The flip preserves multiplication (the vendored `swapDensity_mul`). -/
theorem swapDensity_mul (X Y : K →L[ℂ] K) : S.flip (X * Y) = S.flip X * S.flip Y :=
  S.flip.map_mul' X Y

/-- The bipartite matching mass is symmetric. -/
theorem qBipartiteMatchMass_symm_of_density_fixed {Outcome : Type*} [Fintype Outcome]
    (A B : SubMeas Outcome 𝔓) :
    S.qBipartiteMatchMass A B = S.qBipartiteMatchMass B A :=
  Finset.sum_congr rfl fun a _ =>
    S.ev_opTensor_swap_of_density_fixed (A.outcome a) (B.outcome a)

/-- The bipartite consistency defect is symmetric. -/
theorem qBipartiteConsDefect_symm_of_density_fixed {Outcome : Type*} [Fintype Outcome]
    (A B : SubMeas Outcome 𝔓) :
    S.qBipartiteConsDefect A B = S.qBipartiteConsDefect B A := by
  simp only [qBipartiteConsDefect, S.qBipartiteMatchMass_symm_of_density_fixed A B,
    S.ev_opTensor_swap_of_density_fixed A.total B.total]

/-- The bipartite consistency relation is symmetric. -/
theorem consRel_symm_of_density_fixed {Question Outcome : Type*} [Fintype Outcome]
    (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome 𝔓)
    (δ : ℝ) :
    S.ConsRel 𝒟 A B δ → S.ConsRel 𝒟 B A δ := by
  intro ⟨h⟩
  refine ⟨le_of_eq_of_le ?_ h⟩
  unfold bipartiteConsError
  exact MIPStarRE.LDT.avgOver_congr 𝒟 _ _ fun q =>
    S.qBipartiteConsDefect_symm_of_density_fixed (B q) (A q)

end SymModel

/-! ### Covariance of the line measurements -/

section Covariance

variable {R : Type*} [Ring R] [StarRing R] [PartialOrder R]

/-- Direct outcome-level covariance for axis-parallel-line measurements.

Rebasing a line question by `t` and reparametrizing an outcome polynomial by
the same translation leaves the corresponding projector unchanged. -/
def AxisParallelMeasurementReparamInvariant (params : Parameters)
    [FieldModel params.q]
    (M : IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) R) : Prop :=
  ∀ (ℓ : AxisParallelLine params) (t : Fq params) (f : AxisLinePolynomial params),
    (M (ℓ.rebaseAt t)).outcome (AxisLinePolynomial.reparamAt f t) =
      (M ℓ).outcome f

/-- Direct outcome-level covariance for diagonal-line measurements.

Rebasing a line question by `t` and reparametrizing an outcome polynomial by
the same translation leaves the corresponding projector unchanged. -/
def DiagonalMeasurementReparamInvariant (params : Parameters)
    [FieldModel params.q]
    (M : IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) R) : Prop :=
  ∀ (ℓ : DiagonalLine params) (t : Fq params) (f : DiagonalLinePolynomial params),
    (M (ℓ.rebaseAt t)).outcome (DiagonalLinePolynomial.reparamAt f t) =
      (M ℓ).outcome f

/-- Reparametrization invariance for diagonal-line measurements: evaluating a
rebased line at `zeroCoord` agrees outcome-wise with evaluating the original
line at the rebasing parameter.

At the answer level, the geometric identity is
`DiagonalLinePolynomial.reparamAt_apply_zero`. This predicate is stronger: it
asserts that the *measurement family itself* is covariant under rebasing the
question index. -/
def DiagonalEvaluationReparamInvariant [StarOrderedRing R] (params : Parameters)
    [FieldModel params.q]
    (M : IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) R) : Prop :=
  ∀ (ℓ : DiagonalLine params) (t a : Fq params),
    (postprocess ((M (DiagonalLine.rebaseAt ℓ t)).toSubMeas) (· zeroCoord)).outcome a =
      (postprocess ((M ℓ).toSubMeas) (fun f => f t)).outcome a

/-- Reparametrization invariance for axis-parallel-line measurements: evaluating a
rebased line at `zeroCoord` agrees outcome-wise with evaluating the original
line at the rebasing parameter. -/
def AxisParallelEvaluationReparamInvariant [StarOrderedRing R] (params : Parameters)
    [FieldModel params.q]
    (M : IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) R) : Prop :=
  ∀ (ℓ : AxisParallelLine params) (t a : Fq params),
    (postprocess ((M (AxisParallelLine.rebaseAt ℓ t)).toSubMeas) (· zeroCoord)).outcome a =
      (postprocess ((M ℓ).toSubMeas) (fun f => f t)).outcome a

namespace AxisParallelLine

/-- Transport an axis-parallel-line measurement along rebasing of the line
question by translating its polynomial outcomes. -/
noncomputable def transportMeasurement {params : Parameters} [FieldModel params.q]
    (M : ProjMeas (AxisLinePolynomial params) R) (t : Fq params) :
    ProjMeas (AxisLinePolynomial params) R :=
  ProjMeas.transport (AxisLinePolynomial.reparamAtEquiv (params := params) t) M

/-- Evaluating a transported axis-line measurement at `zeroCoord` agrees with
reading the original measurement at the rebasing parameter. -/
theorem transportMeasurement_postprocess_zero [StarOrderedRing R]
    {params : Parameters} [FieldModel params.q]
    (M : ProjMeas (AxisLinePolynomial params) R) (t a : Fq params) :
    (postprocess (transportMeasurement (params := params) M t).toSubMeas
        (· zeroCoord)).outcome a =
      (postprocess M.toSubMeas (fun f => f t)).outcome a := by
  have h :=
    SubMeas.postprocess_transport
      (e := AxisLinePolynomial.reparamAtEquiv (params := params) t)
      (A := M.toSubMeas)
      (f := fun g : AxisLinePolynomial params => g zeroCoord)
  simpa [transportMeasurement, AxisLinePolynomial.reparamAtEquiv,
    AxisLinePolynomial.reparamAt_apply_zero, addCoord, zeroCoord] using
    congrArg (fun A => A.outcome a) h

end AxisParallelLine

namespace DiagonalLine

/-- Transport a diagonal-line measurement along rebasing of the line question by
translating its polynomial outcomes. -/
noncomputable def transportMeasurement {params : Parameters} [FieldModel params.q]
    (M : ProjMeas (DiagonalLinePolynomial params) R) (t : Fq params) :
    ProjMeas (DiagonalLinePolynomial params) R :=
  ProjMeas.transport (DiagonalLinePolynomial.reparamAtEquiv (params := params) t) M

/-- Evaluating a transported diagonal-line measurement at `zeroCoord` agrees with
reading the original measurement at the rebasing parameter. -/
theorem transportMeasurement_postprocess_zero [StarOrderedRing R]
    {params : Parameters} [FieldModel params.q]
    (M : ProjMeas (DiagonalLinePolynomial params) R) (t a : Fq params) :
    (postprocess (transportMeasurement (params := params) M t).toSubMeas
        (· zeroCoord)).outcome a =
      (postprocess M.toSubMeas (fun f => f t)).outcome a := by
  have h :=
    SubMeas.postprocess_transport
      (e := DiagonalLinePolynomial.reparamAtEquiv (params := params) t)
      (A := M.toSubMeas)
      (f := fun g : DiagonalLinePolynomial params => g zeroCoord)
  simpa [transportMeasurement, DiagonalLinePolynomial.reparamAtEquiv,
    DiagonalLinePolynomial.reparamAt_apply_zero, addCoord, zeroCoord] using
    congrArg (fun A => A.outcome a) h

end DiagonalLine

/-- Stronger rebasing compatibility for axis-parallel-line measurements: the
measurement indexed by the rebased line is equal to the transport of the
original measurement along the answer reparametrization equivalence. -/
def AxisParallelMeasurementTransportInvariant (params : Parameters)
    [FieldModel params.q]
    (M : IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) R) : Prop :=
  ∀ (ℓ : AxisParallelLine params) (t : Fq params),
    M (MIPStarRE.LDT.AxisParallelLine.rebaseAt ℓ t) =
      AxisParallelLine.transportMeasurement (params := params) (M ℓ) t

/-- Stronger rebasing compatibility for diagonal-line measurements: the
measurement indexed by the rebased line is equal to the transport of the
original measurement along the answer reparametrization equivalence. -/
def DiagonalMeasurementTransportInvariant (params : Parameters)
    [FieldModel params.q]
    (M : IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) R) : Prop :=
  ∀ (ℓ : DiagonalLine params) (t : Fq params),
    M (MIPStarRE.LDT.DiagonalLine.rebaseAt ℓ t) =
      DiagonalLine.transportMeasurement (params := params) (M ℓ) t

/-- Transport-level axis-parallel covariance implies direct outcome covariance. -/
theorem AxisParallelMeasurementTransportInvariant.toMeasurementReparamInvariant
    {params : Parameters} [FieldModel params.q]
    {M : IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) R}
    (hM : AxisParallelMeasurementTransportInvariant params M) :
    AxisParallelMeasurementReparamInvariant params M := by
  intro ℓ t f
  change (M (ℓ.rebaseAt t)).outcome
    (AxisLinePolynomial.reparamAtEquiv (params := params) t f) = (M ℓ).outcome f
  have h := congrArg (fun N => N.outcome
    (AxisLinePolynomial.reparamAtEquiv (params := params) t f)) (hM ℓ t)
  simpa only [AxisParallelLine.transportMeasurement, ProjMeas.transport,
    Measurement.transport, SubMeas.transport, Equiv.symm_apply_apply] using h

/-- Transport-level diagonal covariance implies direct outcome covariance. -/
theorem DiagonalMeasurementTransportInvariant.toMeasurementReparamInvariant
    {params : Parameters} [FieldModel params.q]
    {M : IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) R}
    (hM : DiagonalMeasurementTransportInvariant params M) :
    DiagonalMeasurementReparamInvariant params M := by
  intro ℓ t f
  change (M (ℓ.rebaseAt t)).outcome
    (DiagonalLinePolynomial.reparamAtEquiv (params := params) t f) = (M ℓ).outcome f
  have h := congrArg (fun N => N.outcome
    (DiagonalLinePolynomial.reparamAtEquiv (params := params) t f)) (hM ℓ t)
  simpa only [DiagonalLine.transportMeasurement, ProjMeas.transport,
    Measurement.transport, SubMeas.transport, Equiv.symm_apply_apply] using h

/-- Direct axis-parallel outcome covariance implies transport-level covariance. -/
theorem AxisParallelMeasurementReparamInvariant.toTransportInvariant
    {params : Parameters} [FieldModel params.q]
    {M : IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) R}
    (hM : AxisParallelMeasurementReparamInvariant params M) :
    AxisParallelMeasurementTransportInvariant params M := by
  intro ℓ t
  ext a : 1
  obtain ⟨f, rfl⟩ :=
    (AxisLinePolynomial.reparamAtEquiv (params := params) t).surjective a
  change (M (ℓ.rebaseAt t)).outcome (AxisLinePolynomial.reparamAt f t) = _
  rw [hM ℓ t f]
  simp [AxisParallelLine.transportMeasurement, ProjMeas.transport,
    Measurement.transport, SubMeas.transport]

/-- Direct diagonal outcome covariance implies transport-level covariance. -/
theorem DiagonalMeasurementReparamInvariant.toTransportInvariant
    {params : Parameters} [FieldModel params.q]
    {M : IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) R}
    (hM : DiagonalMeasurementReparamInvariant params M) :
    DiagonalMeasurementTransportInvariant params M := by
  intro ℓ t
  ext a : 1
  obtain ⟨f, rfl⟩ :=
    (DiagonalLinePolynomial.reparamAtEquiv (params := params) t).surjective a
  change (M (ℓ.rebaseAt t)).outcome (DiagonalLinePolynomial.reparamAt f t) = _
  rw [hM ℓ t f]
  simp [DiagonalLine.transportMeasurement, ProjMeas.transport,
    Measurement.transport, SubMeas.transport]

/-- Direct outcome covariance and transport-level covariance are equivalent for
axis-parallel-line projective measurements. -/
theorem axisParallelMeasurementReparamInvariant_iff_transportInvariant
    {params : Parameters} [FieldModel params.q]
    {M : IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) R} :
    AxisParallelMeasurementReparamInvariant params M ↔
      AxisParallelMeasurementTransportInvariant params M :=
  ⟨AxisParallelMeasurementReparamInvariant.toTransportInvariant,
    AxisParallelMeasurementTransportInvariant.toMeasurementReparamInvariant⟩

/-- Direct outcome covariance and transport-level covariance are equivalent for
diagonal-line projective measurements. -/
theorem diagonalMeasurementReparamInvariant_iff_transportInvariant
    {params : Parameters} [FieldModel params.q]
    {M : IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) R} :
    DiagonalMeasurementReparamInvariant params M ↔
      DiagonalMeasurementTransportInvariant params M :=
  ⟨DiagonalMeasurementReparamInvariant.toTransportInvariant,
    DiagonalMeasurementTransportInvariant.toMeasurementReparamInvariant⟩

/-- The stronger transport-level axis-parallel compatibility implies the older
outcome-level reparametrization invariant predicate. -/
theorem AxisParallelMeasurementTransportInvariant.toEvaluationReparamInvariant
    [StarOrderedRing R]
    {params : Parameters} [FieldModel params.q]
    {M : IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) R}
    (hM : AxisParallelMeasurementTransportInvariant params M) :
    AxisParallelEvaluationReparamInvariant params M := by
  intro ℓ t a
  rw [hM ℓ t]
  exact AxisParallelLine.transportMeasurement_postprocess_zero
    (params := params) (M := M ℓ) t a

/-- The stronger transport-level diagonal compatibility implies the older
outcome-level reparametrization invariant predicate. -/
theorem DiagonalMeasurementTransportInvariant.toEvaluationReparamInvariant
    [StarOrderedRing R]
    {params : Parameters} [FieldModel params.q]
    {M : IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) R}
    (hM : DiagonalMeasurementTransportInvariant params M) :
    DiagonalEvaluationReparamInvariant params M := by
  intro ℓ t a
  rw [hM ℓ t]
  exact DiagonalLine.transportMeasurement_postprocess_zero
    (params := params) (M := M ℓ) t a

end Covariance

/-! ### Covariant measurement families -/

/-- Axis-parallel line measurements bundled with the stronger transport-level
rebasing covariance. -/
structure AxisParallelCovariantMeasurement (params : Parameters)
    [FieldModel params.q] (R : Type*) [Ring R] [StarRing R] [PartialOrder R] where
  toIdxProjMeas :
    IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) R
  transportInvariant :
    AxisParallelMeasurementTransportInvariant params toIdxProjMeas

instance {params : Parameters} [FieldModel params.q] {R : Type*}
    [Ring R] [StarRing R] [PartialOrder R] :
    CoeFun (AxisParallelCovariantMeasurement params R)
      (fun _ => AxisParallelLine params → ProjMeas (AxisLinePolynomial params) R) where
  coe M := M.toIdxProjMeas

namespace AxisParallelCovariantMeasurement

/-- A covariant wrapper automatically satisfies the older evaluation-level
rebasing invariant. -/
theorem reparamInvariant {params : Parameters} [FieldModel params.q]
    {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    (M : AxisParallelCovariantMeasurement params R) :
    AxisParallelEvaluationReparamInvariant params M.toIdxProjMeas :=
  M.transportInvariant.toEvaluationReparamInvariant

end AxisParallelCovariantMeasurement

/-- Diagonal line measurements bundled with the stronger transport-level
rebasing covariance. -/
structure DiagonalCovariantMeasurement (params : Parameters)
    [FieldModel params.q] (R : Type*) [Ring R] [StarRing R] [PartialOrder R] where
  toIdxProjMeas :
    IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) R
  transportInvariant :
    DiagonalMeasurementTransportInvariant params toIdxProjMeas

instance {params : Parameters} [FieldModel params.q] {R : Type*}
    [Ring R] [StarRing R] [PartialOrder R] :
    CoeFun (DiagonalCovariantMeasurement params R)
      (fun _ => DiagonalLine params → ProjMeas (DiagonalLinePolynomial params) R) where
  coe M := M.toIdxProjMeas

namespace DiagonalCovariantMeasurement

/-- A covariant wrapper automatically satisfies the older evaluation-level
rebasing invariant. -/
theorem reparamInvariant {params : Parameters} [FieldModel params.q]
    {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    (M : DiagonalCovariantMeasurement params R) :
    DiagonalEvaluationReparamInvariant params M.toIdxProjMeas :=
  M.transportInvariant.toEvaluationReparamInvariant

end DiagonalCovariantMeasurement

/-- Transport covariance for diagonal-line measurements whose answers are the
paper-level line functions. -/
def DiagonalAnswerMeasurementTransportInvariant (params : Parameters)
    [FieldModel params.q] {R : Type*} [Ring R] [StarRing R] [PartialOrder R]
    (M : IdxProjMeas (DiagonalLine params) (DiagonalLineAnswer params) R) : Prop :=
  ∀ (ℓ : DiagonalLine params) (t : Fq params),
    M (MIPStarRE.LDT.DiagonalLine.rebaseAt ℓ t) =
      ProjMeas.transport (DiagonalLineAnswer.reparamAtEquiv t) (M ℓ)

/-- Diagonal-line measurements with paper-level function answers, bundled with
transport-level rebasing covariance.

This parallel API is intended for the paper-faithful restriction redesign: unlike
`DiagonalLinePolynomial`, the function-answer alphabet admits a total slice
append/restrict equivalence. -/
structure DiagonalAnswerCovariantMeasurement (params : Parameters)
    [FieldModel params.q] (R : Type*) [Ring R] [StarRing R] [PartialOrder R] where
  toIdxProjMeas :
    IdxProjMeas (DiagonalLine params) (DiagonalLineAnswer params) R
  transportInvariant :
    DiagonalAnswerMeasurementTransportInvariant params toIdxProjMeas

instance {params : Parameters} [FieldModel params.q] {R : Type*}
    [Ring R] [StarRing R] [PartialOrder R] :
    CoeFun (DiagonalAnswerCovariantMeasurement params R)
      (fun _ => DiagonalLine params → ProjMeas (DiagonalLineAnswer params) R) where
  coe M := M.toIdxProjMeas

/-! ### Symmetric strategies -/

/-- Paper-level symmetric strategy data whose diagonal-line answers are functions.

This parallel structure is the target shape for the restriction redesign in
Section 6: restricting an ambient diagonal line to a slice is total for function
answers, unlike the current degree-bounded `DiagonalLinePolynomial` alphabet.

The vendored fields `permInvState`, `densityFixed` and `isNormalized` are theorems of the
symmetric model `state` (see the module docstring). -/
structure AnswerSymStrat (params : Parameters) [FieldModel params.q]
    (𝔓 : Type*) [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
    (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] where
  state : SymModel 𝔓 K
  pointMeasurement : IdxProjMeas (Point params) (Fq params) 𝔓
  axisParallelMeasurement : AxisParallelCovariantMeasurement params 𝔓
  diagonalMeasurement : DiagonalAnswerCovariantMeasurement params 𝔓

/-- Paper-local symmetric strategy data.

The line-measurement fields are bundled as transport-covariant wrappers:
rebasing the question index is required to agree with transporting the
projective measurement along the corresponding answer reparametrization
equivalence. This is stronger than the older evaluation-level formulas
at `zeroCoord`, but those formulas remain available as derived lemmas via
`AxisParallelCovariantMeasurement.reparamInvariant` and
`DiagonalCovariantMeasurement.reparamInvariant`.

The state is a symmetric model (`Co/Basic/QuantumState.lean`): a unit vector `Ψ` in a Hilbert
space `K`, with the local algebra `𝔓` placed on the two factors by `state.L` and `state.R` and
exchanged by the flip `state.flip`, which fixes the state. So the swap symmetry and the
normalization that the vendored structure carries as the fields `permInvState`, `densityFixed`
and `isNormalized` are theorems here: `strategy.state.ev_L_eq_ev_R`, `strategy.state.ev_flip`
and `strategy.isNormalized`. -/
structure SymStrat (params : Parameters) [FieldModel params.q]
    (𝔓 : Type*) [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
    (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] where
  state : SymModel 𝔓 K  -- symmetric bipartite state on `K`
  pointMeasurement : IdxProjMeas (Point params) (Fq params) 𝔓
  axisParallelMeasurement : AxisParallelCovariantMeasurement params 𝔓
  diagonalMeasurement : DiagonalCovariantMeasurement params 𝔓

-- NOTE: no global `Inhabited` instance for `SymStrat`; constructing default
-- projective measurement families is non-canonical and requires additional
-- assumptions on outcome types.

section Families

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The state of a symmetric strategy is normalized (the vendored field
`SymStrat.isNormalized`, a theorem of the model). -/
theorem SymStrat.isNormalized {params : Parameters} [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K) : strategy.state.IsNormalized :=
  strategy.state.isNormalized

/-- The state of an answer-valued symmetric strategy is normalized (the vendored field
`AnswerSymStrat.isNormalized`, a theorem of the model). -/
theorem AnswerSymStrat.isNormalized {params : Parameters} [FieldModel params.q]
    (strategy : AnswerSymStrat params 𝔓 K) : strategy.state.IsNormalized :=
  strategy.state.isNormalized

/-- Sampled point answers in the axis-parallel lines test, obtained from a
point measurement. -/
noncomputable abbrev axisParallelPointAnswerFamilyOf
    {params : Parameters} [FieldModel params.q]
    {R : Type*} [Ring R] [StarRing R] [PartialOrder R]
    (pointMeasurement : IdxProjMeas (Point params) (Fq params) R) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) R :=
  fun s => (pointMeasurement s.1).toSubMeas

/-- Sampled line answers in the axis-parallel lines test, obtained from an
axis-parallel measurement and evaluated at the base point. -/
noncomputable abbrev axisParallelLineAnswerFamilyOf
    {params : Parameters} [FieldModel params.q]
    {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    (axisParallelMeasurement :
      AxisParallelLine params → ProjMeas (AxisLinePolynomial params) R) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) R :=
  fun s =>
    let ℓ : AxisParallelLine params :=
      { base := s.1, direction := s.2 }
    postprocess
      ((axisParallelMeasurement ℓ).toSubMeas)
      (· zeroCoord)

/-- Sampled point answers in the restricted diagonal test, obtained from a
point measurement. -/
noncomputable abbrev diagonalPointAnswerFamilyOf
    {params : Parameters} [FieldModel params.q]
    {R : Type*} [Ring R] [StarRing R] [PartialOrder R]
    (pointMeasurement : IdxProjMeas (Point params) (Fq params) R)
    (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) R :=
  fun s => (pointMeasurement s.1).toSubMeas

/-- Sampled diagonal-line answers in the restricted diagonal test, obtained from
a diagonal-line measurement and evaluated at the base point. -/
noncomputable abbrev diagonalLineAnswerFamilyOf
    {params : Parameters} [FieldModel params.q]
    {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    {Answer : Type*} [Fintype Answer]
    (diagonalMeasurement : DiagonalLine params → ProjMeas Answer R)
    (evalAtBase : Answer → Fq params)
    (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) R :=
  fun s =>
    let v := extendRestrictedDirection j s.2
    let ℓ : DiagonalLine params :=
      { base := s.1, direction := v }
    postprocess
      ((diagonalMeasurement ℓ).toSubMeas)
      evalAtBase

/-- Sampled point answers in the axis-parallel lines test.
The point player receives `u` (the base point) and answers with
their measurement at `u`. -/
noncomputable def axisParallelPointAnswerFamily
    {params : Parameters} [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K) :
    IdxSubMeas (AxisParallelTestSample params)
      (Fq params) 𝔓 :=
  axisParallelPointAnswerFamilyOf strategy.pointMeasurement

/-- Sampled line answers in the axis-parallel lines test,
evaluated at the base point `u`.
The line player receives `ℓ` and returns a polynomial `f`.
The verifier checks `f(u) = a`; since `u = ℓ.pointAt zeroCoord`,
we evaluate `f` at `zeroCoord`. -/
noncomputable def axisParallelLineAnswerFamily
    {params : Parameters} [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K) :
    IdxSubMeas (AxisParallelTestSample params)
      (Fq params) 𝔓 :=
  axisParallelLineAnswerFamilyOf strategy.axisParallelMeasurement

-- Paper: `not:conditioned-on-last-direction` writes `B^u` for the axis-parallel
-- line measurement conditioned on the last direction choice.
/-- The axis-parallel line measurement family restricted to the paper's
last-direction notation `u ↦ B^u`. -/
noncomputable def lastDirectionMeasurementFamily
    {params : Parameters} [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) :
    IdxProjMeas (Point params) (AxisLinePolynomial params.next) 𝔓 :=
  fun u => strategy.axisParallelMeasurement (lastDirectionLine params u)

/-- Sampled point answers in the `j`-restricted diagonal test.
The point player receives `u` and answers at `u`. -/
noncomputable def diagonalPointAnswerFamily
    {params : Parameters} [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j)
      (Fq params) 𝔓 :=
  diagonalPointAnswerFamilyOf strategy.pointMeasurement j

/-- Sampled diagonal-line answers in the `j`-restricted diagonal
test, evaluated at the base point `u`.
Since `u = ℓ.pointAt zeroCoord`, we evaluate `f` at
`zeroCoord`. -/
noncomputable def diagonalLineAnswerFamily
    {params : Parameters} [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j)
      (Fq params) 𝔓 :=
  diagonalLineAnswerFamilyOf strategy.diagonalMeasurement (· zeroCoord) j

namespace AnswerSymStrat

/-- Sampled point answers in the axis-parallel lines test for an answer-valued
symmetric strategy. -/
noncomputable def axisParallelPointAnswerFamily
    {params : Parameters} [FieldModel params.q]
    (strategy : AnswerSymStrat params 𝔓 K) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) 𝔓 :=
  axisParallelPointAnswerFamilyOf strategy.pointMeasurement

/-- Sampled line answers in the axis-parallel lines test for an answer-valued
symmetric strategy, evaluated at the base point. -/
noncomputable def axisParallelLineAnswerFamily
    {params : Parameters} [FieldModel params.q]
    (strategy : AnswerSymStrat params 𝔓 K) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) 𝔓 :=
  axisParallelLineAnswerFamilyOf strategy.axisParallelMeasurement

/-- Sampled point answers in the restricted diagonal test for an answer-valued
symmetric strategy. -/
noncomputable def diagonalPointAnswerFamily
    {params : Parameters} [FieldModel params.q]
    (strategy : AnswerSymStrat params 𝔓 K)
    (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) 𝔓 :=
  diagonalPointAnswerFamilyOf strategy.pointMeasurement j

/-- Sampled diagonal-line answers in the restricted diagonal test for an
answer-valued symmetric strategy, evaluated at the base point. -/
noncomputable def diagonalLineAnswerFamily
    {params : Parameters} [FieldModel params.q]
    (strategy : AnswerSymStrat params 𝔓 K)
    (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) 𝔓 :=
  diagonalLineAnswerFamilyOf strategy.diagonalMeasurement (· zeroCoord) j

/-- Axis-parallel failure surrogate for an answer-valued symmetric strategy. -/
noncomputable def axisParallelFailureProbability
    {params : Parameters} [FieldModel params.q]
    (strategy : AnswerSymStrat params 𝔓 K) : ℝ :=
  strategy.state.bipartiteConsError
    (uniformDistribution (AxisParallelTestSample params))
    (axisParallelPointAnswerFamily strategy)
    (axisParallelLineAnswerFamily strategy)

/-- Self-consistency failure surrogate for an answer-valued symmetric strategy. -/
noncomputable def selfConsistencyFailureProbability
    {params : Parameters} [FieldModel params.q]
    (strategy : AnswerSymStrat params 𝔓 K) : ℝ :=
  strategy.state.bipartiteSSCError
    (uniformDistribution (Point params))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)

/-- Diagonal-line failure surrogate for an answer-valued symmetric strategy. -/
noncomputable def diagonalFailureProbability
    {params : Parameters} [FieldModel params.q]
    (strategy : AnswerSymStrat params 𝔓 K) : ℝ :=
  (1 / (params.m : ℝ)) *
    ∑ j : Fin params.m,
      strategy.state.bipartiteConsError
        (uniformDistribution (RestrictedDiagonalSample params j))
        (diagonalPointAnswerFamily strategy j)
        (diagonalLineAnswerFamily strategy j)

/-- Goodness data for an answer-valued symmetric strategy. -/
structure IsGood {params : Parameters} [FieldModel params.q]
    (strategy : AnswerSymStrat params 𝔓 K)
    (eps delta gamma : ℝ) : Prop where
  /-- The axis-parallel test fails with probability at most `eps`. -/
  axisParallelTest : strategy.axisParallelFailureProbability ≤ eps
  /-- The self-consistency test fails with probability at most `delta`. -/
  selfConsistencyTest : strategy.selfConsistencyFailureProbability ≤ delta
  /-- The diagonal-line test fails with probability at most `gamma`. -/
  diagonalLineTest : strategy.diagonalFailureProbability ≤ gamma

end AnswerSymStrat

end Families

/-! ### Two-space projective strategies -/

universe u

/-- Paper-faithful two-space projective strategy data.

This matches the paper's `def:general-projective-strategy`
(`test_definition.tex`, lines 98--115): Alice's and Bob's measurements act on
separate local algebras `𝒜` and `ℬ`, and the state is a bipartite model of the repository
(`MIPRE.BipartiteModel 𝒞 𝒜 ℬ`, `MIPRE/Foundations/BipartiteModel.lean`), a vector state on a
Hilbert space on which `𝒜` and `ℬ` act by commuting representations, without a built-in swap
symmetry. This replaces the vendored state on the tensor product `ιA × ιB` of two matrix
carriers.

The `isNormalized` field records that the state is a unit vector (a bipartite model carries no
normalization).

The four covariance conditions express that the line-indexed projectors
descend from chosen affine parametrizations to geometric lines; transport and
zero-coordinate evaluation are equivalent consequences. -/
structure ProjStrat (params : Parameters) [FieldModel params.q]
    (𝒞 : Type*) [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞]
    (𝒜 : Type*) [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [PartialOrder 𝒜]
    (ℬ : Type*) [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder ℬ] where
  /-- The bipartite state: a vector state with commuting representations of `𝒜` and `ℬ`. -/
  state : MIPRE.BipartiteModel.{u} 𝒞 𝒜 ℬ
  /-- The state is a unit vector. -/
  isNormalized : ‖state.ψ‖ = 1
  /-- Alice's point-measurement family, in `𝒜`. -/
  pointMeasurementA : IdxProjMeas (Point params) (Fq params) 𝒜
  /-- Alice's axis-parallel-line measurement family, in `𝒜`. -/
  axisParallelMeasurementA :
    IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) 𝒜
  /-- Alice's axis-parallel measurement is covariant under line rebasing. -/
  axisParallelReparamInvariantA :
    AxisParallelMeasurementReparamInvariant params axisParallelMeasurementA
  /-- Alice's diagonal-line measurement family, in `𝒜`. -/
  diagonalMeasurementA :
    IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) 𝒜
  /-- Alice's diagonal measurement is covariant under line rebasing. -/
  diagonalReparamInvariantA :
    DiagonalMeasurementReparamInvariant params diagonalMeasurementA
  /-- Bob's point-measurement family, in `ℬ`. -/
  pointMeasurementB : IdxProjMeas (Point params) (Fq params) ℬ
  /-- Bob's axis-parallel-line measurement family, in `ℬ`. -/
  axisParallelMeasurementB :
    IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) ℬ
  /-- Bob's axis-parallel measurement is covariant under line rebasing. -/
  axisParallelReparamInvariantB :
    AxisParallelMeasurementReparamInvariant params axisParallelMeasurementB
  /-- Bob's diagonal-line measurement family, in `ℬ`. -/
  diagonalMeasurementB :
    IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) ℬ
  /-- Bob's diagonal measurement is covariant under line rebasing. -/
  diagonalReparamInvariantB :
    DiagonalMeasurementReparamInvariant params diagonalMeasurementB

end MIPRE.LIDT.Co

end
