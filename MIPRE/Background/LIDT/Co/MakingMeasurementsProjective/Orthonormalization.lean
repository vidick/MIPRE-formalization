/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122),
MIPStarRE/LDT/MakingMeasurementsProjective/Orthonormalization.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.MakingMeasurementsProjective.LocalityPreservingRepair
public import MIPRE.Background.LIDT.Co.MakingMeasurementsProjective.Orthonormalization.Completion
public import MIPRE.Background.LIDT.Co.Doubling.Orthonormalization
public import MIPRE.Background.Orthonormalization.DyadicOrtho
public import MIPRE.Background.LIDT.Co.Test.StrategyBiProj.Measurements
public import MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization.ErrorBounds

@[expose] public section

/-!
# Section 5 — Orthonormalization

The orthonormalization theorem `thm:orthonormalization` and the measurement-level lemma
`lem:orthonormalization-main-lemma`: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/Orthonormalization.lean` in the
port of `planning/c6b-plan.md` (milestone M8, section "Port conventions"). It holds the second and
third sites at which the port calls the orthonormalization tier T1, and the top-level theorem.

**Same-space theorems.** The state `ψ` is a symmetric model `S : SymModel 𝔓 K`, with every
measurement local in `𝔓`; `hperm : PermInvState ψ` and `hψ : ψ.IsNormalized` are dropped (the
swap symmetry and `S.ev 1 = 1` are theorems). Every theorem that reaches T1 takes
`hS : S.toBipartite.IsFinitePair` and `hA : NoAbelianProj S.toBipartite.opsA` right after `S`,
and `hζ : 0 < ζ` in place of `0 ≤ ζ`; `orthonormalizationCompletionRoute` and `orthonormalization`,
which had no `hζ`, gain `(hζ : 0 < ζ)` after `ζ`. The case `ζ = 0` does not follow from the strict
tier and is not needed (`planning/c6b-plan.md`, §5). `bipartiteSSCRel_self_of_measurement` and
`leftLiftedRoundedProjMeasStatement_to_local` call no tier and take no new hypothesis.
`orthonormalizationMainLemma` is narrowed from two carriers `ιA`, `ιB` to one, as milestone M3
narrowed `triangleSub_heterogeneous`. The vendored `A.liftLeft` is `A.map S.L`, and the unused
vendored `[DecidableEq Outcome]` of `leftLiftedRoundedProjMeasStatement_to_local` is dropped.

`orthonormalization` is Theorem G (`SymModel.orthonormalization_of_isFinitePair_sddRel`,
`Co/Doubling/Orthonormalization.lean`) in one line: the vendored completion chain is not run again.
Its in-core call (the vendored `SelfImprovementTop/Core.lean`, line 433, milestone M10) must supply
`0 < selfImprovementHelperError`, which holds when `1 ≤ params.d`, threaded from `SoundIn` by
milestone M14. `orthonormalizationCompletionRoute` keeps the vendored completion chain (the
completion `optionCompletion`, its `2ζ` bound `Completion.optionCompletion_bipartiteSSCRel`, the
repair `leftLiftedProjectivizationRepair` and the restriction
`Completion.qSDD_liftLeft_restrictSomeProjSubMeas_le`), with the weaker `120 ζ^{1/4}` envelope.

**Two-space theorems.** The two `…_heterogeneous` lemmas are stated over a dyadic pair
`M : MIPRE.BipartiteModel 𝒞 𝒜 ℬ` (`BipartiteModel.IsDyadicPair`), with `A` a measurement of the
first player's algebra and `B` of the second's, and call T5
(`povm_orthogonalization_dyadicPair`, `povm_orthogonalization_dyadicPairB`). Their vendored state
is on `ιA × ιB` and their only vendored callers are the two-space `ProjStrat` of
`Test/MainTheorem/SourceRoleRegister/Core.lean` (lines 507 and 547), which milestone M13 ports, so
a narrowing to one carrier would duplicate
`orthonormalizationMeasurement_of_consistency_from_projectivizationRepair`. This departs from the
narrowing rule, as the two-space defect of milestone M2 did (`Co/Test/StrategyBiProj/Measurements.lean`):
- the hypothesis is the two-space defect `bipartiteConsError M (uniformDistribution Unit) … ≤ ζ`
  (the port has no two-space `ConsRel`, "Same-space and bipartite quantities");
- the conclusion `∑ₐ ‖π(πA(Aₐ − Pₐ)) ψ‖² ≤ 100 ζ^{1/4}` (or with `ℬ`, `πB`, `B`) replaces the
  vendored `SDDRel` of the left (right) placements, which mentions a state on the product space.
The proof is the vendored Cauchy–Schwarz chain with `bornProb`
(`one_sub_two_mul_le_sum_norm_sq_πA`), then the tier at `ε = 3 min(ζ, 1)`
(`Doubling.one_sub_three_mul_min_lt`) and `27 min(ζ, 1) ≤ 100 ζ^{1/4}`
(`Doubling.twentySeven_mul_min_le_orthonormalizationError`). There is no `hψ`-free form: the
two-space model carries no normalization, so `hψ : ‖M.ψ‖ = 1` stays.

**The vendored files of `MakingMeasurementsProjective` that have no port**, since the pairing
script checks only ported files:
- `Defs.lean` (320 lines): its error functions (`orthonormalizationError`,
  `orthonormalizationCompletionRouteError`, `orthonormalizationMainLemmaError`,
  `consistencyToAlmostProjectiveError`, `spectralTruncationError`, `roundingToProjectiveError`) are
  classical and imported from the vendored file; the rest is matrix-only (`FiniteHilbertSpace`,
  `MatrixOperator`, `PositiveMatrixState`, `MatrixSubmeasurement`, `MatrixMeasurement`,
  `matrixExpectation`, `naimarkAuxProjector`, `oneMeasLiftedDensity`, `OneMeasNaimarkData`,
  `NaimarkData`), consumed only by the not-ported `MatrixRealization` and `SdpMatrixBridge`
  (replaced by milestone M5's Gram positivity and M9's summed form) and by M5's vendored imports
  of `ExpansionHypercubeGraph/{Defs/Core,Theorems/Foundations,Theorems/Matrix,Theorems/Results}`,
  whose matrix content M5 replaced by Gram positivity.
- `Orthonormalization/ErrorBounds.lean` (142 lines): wholly classical scalar bookkeeping, imported
  by this file, as milestone M3 imports `Polynomials.lean`.
- `NaimarkCore.lean` (404 lines): the matrix Naimark dilation; nothing outside
  `MakingMeasurementsProjective` names it, and the model route needs no dilation (T1
  orthonormalizes inside the algebra).
- `QXPLayer/{Core, QCompleteness, AlmostProjective, TruncationCombinatorics, RankReduction/LowRank,
  RankReduction/Sigma}.lean` (2,478 lines): the finite-dimensional `Q/X/X̂/P` route (rank
  reduction, finite-spectrum functional calculus, cardinality counts), replaced by T1
  (`povm_orthogonalization_finitePair` in the repair theorems of
  `Co/MakingMeasurementsProjective/LocalityPreservingRepair.lean`, T5 in the heterogeneous lemmas
  here, Theorem G in `orthonormalization`); no declaration of it is used outside
  `MakingMeasurementsProjective`.
- `QXPLayerIdentities/{LayerAlgebra, ProjectorApprox, RectangularSvd, PositiveGram/Rows,
  PositiveGram/Completion, PositiveGram/Sigma}.lean` (3,140 lines): matrix identities of the same
  route (rectangular SVD, coisometries, positive Gram completion), replaced by T1 as above. The
  vendored `ProjectivizationChain/Basic.lean`, imported for its classical names, keeps
  `ProjectorApprox` in the import closure; no port file names it.
- `SpectralTruncation/{Conversion, ProjectiveNonMeasurement}.lean` (914 lines): a step-function
  calculus legal only on finite spectrum, replaced by T1; its conclusion
  `SpectralTruncationStatement` is listed as not ported in `Co/MakingMeasurementsProjective/Statements.lean`.

## New here

- `one_sub_two_mul_le_sum_norm_sq_πA`: in a bipartite model with a unit state, a two-space
  consistency defect at most `ζ` between measurements `A` of `𝒜` and `B` of `ℬ` gives
  `1 − 2ζ ≤ ∑ₐ ‖π(πA(Aₐ)) ψ‖²`.
- `one_sub_two_mul_le_sum_norm_sq_πB`: the same for `B`, `1 − 2ζ ≤ ∑ₐ ‖π(πB(Bₐ)) ψ‖²`.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/orthonormalization.tex`, lines 67–76 and 282–310
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.MakingMeasurementsProjective

open MIPStarRE.LDT (avgOver uniformDistribution)
open MIPStarRE.LDT.MakingMeasurementsProjective (orthonormalizationError
  orthonormalizationMainLemmaError orthonormalizationCompletionRouteError
  consistencyToAlmostProjectiveError totalMass_sub_two_defect_le_diagA)
open MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization.ErrorBounds
  (orthonormalizationMainLemmaError_le_orthonormalizationError
  orthonormalizationMainLemmaError_two_mul_le_orthonormalizationError completionRouteError_bound)
open MIPRE.Orthonormalization (povm_orthogonalization_dyadicPair
  povm_orthogonalization_dyadicPairB)

/-- The average over the one-point distribution is the value at the point. -/
private theorem avgOver_unit (f : Unit → ℝ) : avgOver (uniformDistribution Unit) f = f () := by
  simp [avgOver, uniformDistribution]

/-! ### Same-space orthonormalization -/

section SameSpace

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- `lem:orthonormalization-main-lemma`: in a symmetric model whose bipartite reading is a finite
pair without abelian projections in its first player's operators, a measurement `A` of the local
algebra `ζ`-consistent with a measurement `B`, `ζ > 0`, is within
`orthonormalizationMainLemmaError ζ = 84 ζ^{1/4}` of a projective submeasurement, in the left
placements: consistency gives almost projectivity at `2ζ` (`consistencyToAlmostProjective`), and
the locality-preserving repair at the `2ζ` scale closes it.

Paper origin: `references/ldt-paper/orthonormalization.tex:282-310`. -/
theorem orthonormalizationMainLemma {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (hS : S.toBipartite.IsFinitePair) (hA : NoAbelianProj S.toBipartite.opsA)
    (A B : Measurement Outcome 𝔓) (ζ : ℝ) (hζ : 0 < ζ) :
    S.ConsRel (uniformDistribution Unit) (constSubMeasFamily A.toSubMeas)
        (constSubMeasFamily B.toSubMeas) ζ →
      ∃ P : ProjSubMeas Outcome 𝔓,
        S.SDDRel (uniformDistribution Unit)
          (constSubMeasFamily (S.leftPlacedSubMeas A.toSubMeas))
          (constSubMeasFamily (S.leftPlacedSubMeas P.toSubMeas))
          (orthonormalizationMainLemmaError ζ) := fun hCons =>
  leftPlacedProjectivizationRepair_of_sourceAlmostProjective_two_mul S hS hA A ζ hζ
    (consistencyToAlmostProjective S A B ζ hCons).sourceAlmostProjective

/-- For a complete measurement, bipartite strong self-consistency is bipartite consistency of `A`
with itself. -/
theorem bipartiteSSCRel_self_of_measurement {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (A : Measurement Outcome 𝔓) (ζ : ℝ) :
    S.BipartiteSSCRel (uniformDistribution Unit) (constSubMeasFamily A.toSubMeas) ζ →
      S.ConsRel (uniformDistribution Unit) (constSubMeasFamily A.toSubMeas)
        (constSubMeasFamily A.toSubMeas) ζ := by
  rintro ⟨h⟩
  refine ⟨le_of_eq_of_le ?_ h⟩
  simp only [SymModel.bipartiteConsError, SymModel.bipartiteSSCError, avgOver_unit,
    constSubMeasFamily, SymModel.qBipartiteSSCDefect, SymModel.qBipartiteConsDefect,
    SymModel.qBipartiteMatchMass, SymModel.opTensor, A.total_eq_one, map_one, mul_one]

/-- A rounded-projective witness for the left-lifted measurement, whose projective submeasurement
is a left lift, is a distance bound on the left lifts. -/
theorem leftLiftedRoundedProjMeasStatement_to_local {Outcome : Type*} [Fintype Outcome]
    {S : SymModel 𝔓 K} {A : Measurement Outcome 𝔓} {P : ProjSubMeas Outcome 𝔓} {ζ : ℝ}
    (h : RoundedProjMeasStatement S.toVecState (S.leftLiftedMeasurement A)
      (ProjSubMeas.liftLeft S P) ζ) :
    S.SDDRel (uniformDistribution Unit) (constSubMeasFamily (A.toSubMeas.map S.L))
      (constSubMeasFamily (P.toSubMeas.map S.L)) ζ :=
  h.closeness

/-- Measurement-level orthonormalization from a cross-consistency hypothesis: the analogue of
`orthonormalizationMainLemma` for the left lifts, with the paper's `84 ζ^{1/4}` weakened to the
public `100 ζ^{1/4}` envelope. -/
theorem orthonormalizationMeasurement_of_consistency {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (hS : S.toBipartite.IsFinitePair) (hA : NoAbelianProj S.toBipartite.opsA)
    (A B : Measurement Outcome 𝔓) (ζ : ℝ) (hζ : 0 < ζ) :
    S.ConsRel (uniformDistribution Unit) (constSubMeasFamily A.toSubMeas)
        (constSubMeasFamily B.toSubMeas) ζ →
      ∃ P : ProjSubMeas Outcome 𝔓,
        S.SDDRel (uniformDistribution Unit) (constSubMeasFamily (A.toSubMeas.map S.L))
          (constSubMeasFamily (P.toSubMeas.map S.L)) (orthonormalizationError ζ) := by
  intro hCons
  obtain ⟨P, ⟨hP⟩⟩ := orthonormalizationMainLemma S hS hA A B ζ hζ hCons
  exact ⟨P, ⟨hP.trans (orthonormalizationMainLemmaError_le_orthonormalizationError ζ hζ.le)⟩⟩

/-- Measurement-level orthonormalization for a complete measurement: the measurement-level
corollary of `lem:orthonormalization-main-lemma`, through the consistency of `A` with itself. -/
theorem orthonormalizationMeasurement {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (hS : S.toBipartite.IsFinitePair) (hA : NoAbelianProj S.toBipartite.opsA)
    (A : Measurement Outcome 𝔓) (ζ : ℝ) (hζ : 0 < ζ) :
    S.BipartiteSSCRel (uniformDistribution Unit) (constSubMeasFamily A.toSubMeas) ζ →
      ∃ P : ProjSubMeas Outcome 𝔓,
        S.SDDRel (uniformDistribution Unit) (constSubMeasFamily (A.toSubMeas.map S.L))
          (constSubMeasFamily (P.toSubMeas.map S.L)) (orthonormalizationError ζ) := fun hssc =>
  orthonormalizationMeasurement_of_consistency S hS hA A A ζ hζ
    (bipartiteSSCRel_self_of_measurement S A ζ hssc)

/-- Measurement-level orthonormalization from cross consistency, through the locality-preserving
repair at the `ζ` scale applied to the `2ζ`-almost-projective left lift
(`leftLiftedProjectivizationRepair`): `84 (2ζ)^{1/4} ≤ 100 ζ^{1/4}`. -/
theorem orthonormalizationMeasurement_of_consistency_from_projectivizationRepair
    {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (hS : S.toBipartite.IsFinitePair) (hA : NoAbelianProj S.toBipartite.opsA)
    (A B : Measurement Outcome 𝔓) (ζ : ℝ) (hζ : 0 < ζ) :
    S.ConsRel (uniformDistribution Unit) (constSubMeasFamily A.toSubMeas)
        (constSubMeasFamily B.toSubMeas) ζ →
      ∃ P : ProjSubMeas Outcome 𝔓,
        S.SDDRel (uniformDistribution Unit) (constSubMeasFamily (A.toSubMeas.map S.L))
          (constSubMeasFamily (P.toSubMeas.map S.L)) (orthonormalizationError ζ) := by
  intro hCons
  obtain ⟨P, hRounded⟩ := leftLiftedProjectivizationRepair S hS hA A
    (consistencyToAlmostProjectiveError ζ) (mul_pos two_pos hζ)
    (consistencyToAlmostProjective S A B ζ hCons).sourceAlmostProjective
  obtain ⟨hP⟩ := leftLiftedRoundedProjMeasStatement_to_local hRounded
  exact ⟨P, ⟨hP.trans
    (orthonormalizationMainLemmaError_two_mul_le_orthonormalizationError ζ hζ.le)⟩⟩

/-- Completion-route orthonormalization, with the weaker `orthonormalizationCompletionRouteError
ζ = 120 ζ^{1/4}` envelope: complete `A` by the outcome `none`
(`Completion.optionCompletion_bipartiteSSCRel`, at `2ζ`), apply the repair to the completed
measurement at `consistencyToAlmostProjectiveError (2ζ) = 4ζ`, and drop the outcome `none`
(`Completion.qSDD_liftLeft_restrictSomeProjSubMeas_le`). The source theorem, with the sharper
`100 ζ^{1/4}`, is `orthonormalization`. -/
theorem orthonormalizationCompletionRoute {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (hS : S.toBipartite.IsFinitePair) (hA : NoAbelianProj S.toBipartite.opsA)
    (A : SubMeas Outcome 𝔓) (ζ : ℝ) (hζ : 0 < ζ) :
    S.BipartiteSSCRel (uniformDistribution Unit) (constSubMeasFamily A) ζ →
      ∃ P : ProjSubMeas Outcome 𝔓,
        S.SDDRel (uniformDistribution Unit) (constSubMeasFamily (A.map S.L))
          (constSubMeasFamily (P.toSubMeas.map S.L)) (orthonormalizationCompletionRouteError ζ) := by
  intro hssc
  have hCons := bipartiteSSCRel_self_of_measurement S (optionCompletion A) (2 * ζ)
    (Orthonormalization.Completion.optionCompletion_bipartiteSSCRel S A ζ hssc)
  obtain ⟨P, hRounded⟩ := leftLiftedProjectivizationRepair S hS hA (optionCompletion A)
    (consistencyToAlmostProjectiveError (2 * ζ)) (mul_pos two_pos (mul_pos two_pos hζ))
    (consistencyToAlmostProjective S _ _ _ hCons).sourceAlmostProjective
  obtain ⟨hP⟩ := leftLiftedRoundedProjMeasStatement_to_local hRounded
  rw [VecState.sddError, avgOver_unit] at hP
  refine ⟨restrictSomeProjSubMeas P, ⟨?_⟩⟩
  rw [VecState.sddError, avgOver_unit]
  exact ((Orthonormalization.Completion.qSDD_liftLeft_restrictSomeProjSubMeas_le S A P).trans
    hP).trans (completionRouteError_bound ζ hζ.le)

/-- `thm:orthonormalization`: in a symmetric model whose bipartite reading is a finite pair
without abelian projections in its first player's operators, a submeasurement `A` of the local
algebra that is `ζ`-strongly self-consistent, `ζ > 0`, is within the paper's
`orthonormalizationError ζ = 100 ζ^{1/4}` of a projective submeasurement, in the left placements.

This is Theorem G (`SymModel.orthonormalization_of_isFinitePair_sddRel`). The in-core call of the
vendored `SelfImprovementTop/Core.lean` (line 433, milestone M10) must supply
`0 < selfImprovementHelperError`, which holds when `1 ≤ params.d`, threaded from `SoundIn` by
milestone M14.

Paper origin: `references/ldt-paper/orthonormalization.tex:67-76`. -/
theorem orthonormalization {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (hS : S.toBipartite.IsFinitePair) (hA : NoAbelianProj S.toBipartite.opsA)
    (A : SubMeas Outcome 𝔓) (ζ : ℝ) (hζ : 0 < ζ) :
    S.BipartiteSSCRel (uniformDistribution Unit) (constSubMeasFamily A) ζ →
      ∃ P : ProjSubMeas Outcome 𝔓,
        S.SDDRel (uniformDistribution Unit) (constSubMeasFamily (A.map S.L))
          (constSubMeasFamily (P.toSubMeas.map S.L)) (orthonormalizationError ζ) :=
  S.orthonormalization_of_isFinitePair_sddRel hS hA A hζ

end SameSpace

/-! ### Two-space orthonormalization in a dyadic pair -/

section TwoSpace

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]
  [PartialOrder ℬ] [StarOrderedRing ℬ] (M : MIPRE.BipartiteModel 𝒞 𝒜 ℬ)

/-- The common core of `one_sub_two_mul_le_sum_norm_sq_πA` and `…_πB`: the vendored
Cauchy–Schwarz chain (`overlap² ≤ diagA · diagB`, both masses at most `1`), with `bornProb` for
`ev (A ⊗ B)`. -/
private theorem one_sub_two_mul_le_sum_norm_sq {Outcome : Type*} [Fintype Outcome]
    (hψ : ‖M.ψ‖ = 1) (A : Measurement Outcome 𝒜) (B : Measurement Outcome ℬ) {ζ : ℝ}
    (h : qBipartiteConsDefect M A.toSubMeas B.toSubMeas ≤ ζ) :
    1 - 2 * ζ ≤ ∑ a, ‖M.π (M.πA (A.outcome a)) M.ψ‖ ^ 2 ∧
      1 - 2 * ζ ≤ ∑ a, ‖M.π (M.πB (B.outcome a)) M.ψ‖ ^ 2 := by
  set sA : Outcome → ℝ := fun a => ‖M.π (M.πA (A.outcome a)) M.ψ‖
  set sB : Outcome → ℝ := fun a => ‖M.π (M.πB (B.outcome a)) M.ψ‖
  set diagA := ∑ a, sA a ^ 2
  set diagB := ∑ a, sB a ^ 2
  set overlap := ∑ a, M.bornProb (A.outcome a) (B.outcome a)
  have hdiagA0 : 0 ≤ diagA := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hdiagB0 : 0 ≤ diagB := Finset.sum_nonneg fun _ _ => sq_nonneg _
  -- both diagonal masses are at most one
  have hdiagA1 : diagA ≤ 1 := M.sum_stateSqNorm_le_one hψ A.toPOVMIn
  have hdiagB1 : diagB ≤ 1 := M.swap.sum_stateSqNorm_le_one hψ B.toPOVMIn
  -- Cauchy–Schwarz for the overlap
  have hterm : ∀ a, M.bornProb (A.outcome a) (B.outcome a) ≤ sA a * sB a := fun a => by
    have hcs := M.abs_qform_πA_mul_πB_le' (A.outcome a) (B.outcome a)
    rw [A.outcome_hermitian a] at hcs
    exact (le_abs_self _).trans hcs
  have hoverlap0 : 0 ≤ overlap :=
    Finset.sum_nonneg fun a _ => M.bornProb_nonneg (A.outcome_pos a) (B.outcome_pos a)
  have hcs : overlap ≤ Real.sqrt diagA * Real.sqrt diagB :=
    (Finset.sum_le_sum fun a _ => hterm a).trans (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ sA sB)
  have hsq : overlap ^ 2 ≤ diagA * diagB := by
    calc overlap ^ 2 ≤ (Real.sqrt diagA * Real.sqrt diagB) ^ 2 :=
          pow_le_pow_left₀ hoverlap0 hcs 2
      _ = diagA * diagB := by rw [mul_pow, Real.sq_sqrt hdiagA0, Real.sq_sqrt hdiagB0]
  have hoverlap1 : overlap ≤ 1 :=
    hcs.trans ((mul_le_mul (Real.sqrt_le_one.2 hdiagA1) (Real.sqrt_le_one.2 hdiagB1)
      (Real.sqrt_nonneg _) zero_le_one).trans_eq (one_mul 1))
  -- the defect is `1 − overlap`
  have hdefect : qBipartiteConsDefect M A.toSubMeas B.toSubMeas = 1 - overlap := by
    have htot : M.bornProb A.total B.total = 1 := by
      rw [A.total_eq_one, B.total_eq_one, MIPRE.BipartiteModel.bornProb, map_one, map_one,
        mul_one, M.qform_one hψ]
    change max 0 (M.bornProb A.total B.total - overlap) = 1 - overlap
    rw [htot, max_eq_right (sub_nonneg.2 hoverlap1)]
  have hdefect0 := qBipartiteConsDefect_nonneg M A.toSubMeas B.toSubMeas
  have hA := totalMass_sub_two_defect_le_diagA hdiagA0 hdefect0 hdefect hsq hdiagB1
  have hB := totalMass_sub_two_defect_le_diagA hdiagB0 hdefect0 hdefect
    (by rwa [mul_comm]) hdiagA1
  exact ⟨by linarith, by linarith⟩

/-- **Consistency gives mass on the first player's side**: in a bipartite model with a unit
state, if the two-space consistency defect of measurements `A` of `𝒜` and `B` of `ℬ` is at most
`ζ`, then `1 − 2ζ ≤ ∑ₐ ‖π(πA(Aₐ)) ψ‖²`. -/
theorem one_sub_two_mul_le_sum_norm_sq_πA {Outcome : Type*} [Fintype Outcome]
    (hψ : ‖M.ψ‖ = 1) (A : Measurement Outcome 𝒜) (B : Measurement Outcome ℬ) {ζ : ℝ}
    (h : qBipartiteConsDefect M A.toSubMeas B.toSubMeas ≤ ζ) :
    1 - 2 * ζ ≤ ∑ a, ‖M.π (M.πA (A.outcome a)) M.ψ‖ ^ 2 :=
  (one_sub_two_mul_le_sum_norm_sq M hψ A B h).1

/-- **Consistency gives mass on the second player's side**: the counterpart of
`one_sub_two_mul_le_sum_norm_sq_πA` for `B`, `1 − 2ζ ≤ ∑ₐ ‖π(πB(Bₐ)) ψ‖²`. -/
theorem one_sub_two_mul_le_sum_norm_sq_πB {Outcome : Type*} [Fintype Outcome]
    (hψ : ‖M.ψ‖ = 1) (A : Measurement Outcome 𝒜) (B : Measurement Outcome ℬ) {ζ : ℝ}
    (h : qBipartiteConsDefect M A.toSubMeas B.toSubMeas ≤ ζ) :
    1 - 2 * ζ ≤ ∑ a, ‖M.π (M.πB (B.outcome a)) M.ψ‖ ^ 2 :=
  (one_sub_two_mul_le_sum_norm_sq M hψ A B h).2

/-- **Heterogeneous orthonormalization on the first player's side**: in a dyadic pair with a unit
state, if measurements `A` of `𝒜` and `B` of `ℬ` have two-space consistency defect at most
`ζ > 0`, then `A` is within `∑ₐ ‖π(πA(Aₐ − Pₐ)) ψ‖² ≤ 100 ζ^{1/4}` of a projective
submeasurement `P` of `𝒜`.

The two-space form of `lem:orthonormalization-main-lemma`, consumed by milestone M13
(`Test/MainTheorem/SourceRoleRegister`); it departs from the narrowing rule as the two-space
defect of milestone M2 did (module docstring). -/
theorem orthonormalizationMeasurement_of_consistency_from_projectivizationRepair_heterogeneous
    {Outcome : Type*} [Fintype Outcome]
    (hψ : ‖M.ψ‖ = 1) (hM : M.IsDyadicPair)
    (A : Measurement Outcome 𝒜) (B : Measurement Outcome ℬ) (ζ : ℝ) (hζ : 0 < ζ) :
    bipartiteConsError M (uniformDistribution Unit) (constSubMeasFamily A.toSubMeas)
        (constSubMeasFamily B.toSubMeas) ≤ ζ →
      ∃ P : ProjSubMeas Outcome 𝒜,
        ∑ a, ‖M.π (M.πA (A.outcome a - P.outcome a)) M.ψ‖ ^ 2 ≤ orthonormalizationError ζ := by
  intro hcons
  rw [bipartiteConsError, avgOver_unit] at hcons
  have hs := one_sub_two_mul_le_sum_norm_sq_πA M hψ A B hcons
  have hlt := Doubling.one_sub_three_mul_min_lt (by linarith)
    (Finset.sum_nonneg fun a _ => sq_nonneg ‖M.π (M.πA (A.outcome a)) M.ψ‖) hζ
  obtain ⟨Q, hQ, hQlt⟩ := povm_orthogonalization_dyadicPair M hM hψ A.toPOVMIn _ hlt
  have hQlt' : ∑ a, ‖M.π (M.πA (A.outcome a - Q a)) M.ψ‖ ^ 2 < 9 * (3 * min ζ 1) := hQlt
  have hmin := Doubling.twentySeven_mul_min_le_orthonormalizationError hζ.le
  exact ⟨⟨(ProjMeas.ofIsPVMIn Q hQ).toSubMeas, hQ.idem⟩, hQlt'.le.trans (by linarith)⟩

/-- **Heterogeneous orthonormalization on the second player's side**: the counterpart of
`orthonormalizationMeasurement_of_consistency_from_projectivizationRepair_heterogeneous` for `B`,
`∑ₐ ‖π(πB(Bₐ − Pₐ)) ψ‖² ≤ 100 ζ^{1/4}` for a projective submeasurement `P` of `ℬ`, through the
second player's form of the tier (`povm_orthogonalization_dyadicPairB`). -/
theorem orthonormalizationMeasurement_right_of_consistency_from_projectivizationRepair_heterogeneous
    {Outcome : Type*} [Fintype Outcome]
    (hψ : ‖M.ψ‖ = 1) (hM : M.IsDyadicPair)
    (A : Measurement Outcome 𝒜) (B : Measurement Outcome ℬ) (ζ : ℝ) (hζ : 0 < ζ) :
    bipartiteConsError M (uniformDistribution Unit) (constSubMeasFamily A.toSubMeas)
        (constSubMeasFamily B.toSubMeas) ≤ ζ →
      ∃ P : ProjSubMeas Outcome ℬ,
        ∑ a, ‖M.π (M.πB (B.outcome a - P.outcome a)) M.ψ‖ ^ 2 ≤ orthonormalizationError ζ := by
  intro hcons
  rw [bipartiteConsError, avgOver_unit] at hcons
  have hs := one_sub_two_mul_le_sum_norm_sq_πB M hψ A B hcons
  have hlt := Doubling.one_sub_three_mul_min_lt (by linarith)
    (Finset.sum_nonneg fun a _ => sq_nonneg ‖M.π (M.πB (B.outcome a)) M.ψ‖) hζ
  obtain ⟨Q, hQ, hQlt⟩ := povm_orthogonalization_dyadicPairB M hM hψ B.toPOVMIn _ hlt
  have hQlt' : ∑ a, ‖M.π (M.πB (B.outcome a - Q a)) M.ψ‖ ^ 2 < 9 * (3 * min ζ 1) := hQlt
  have hmin := Doubling.twentySeven_mul_min_le_orthonormalizationError hζ.le
  exact ⟨⟨(ProjMeas.ofIsPVMIn Q hQ).toSubMeas, hQ.idem⟩, hQlt'.le.trans (by linarith)⟩

end TwoSpace

end MIPRE.LIDT.Co.MakingMeasurementsProjective

end
