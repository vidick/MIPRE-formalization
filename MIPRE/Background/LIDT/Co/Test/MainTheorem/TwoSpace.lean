/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Test.StrategyBiProj.Measurements
public import MIPRE.Background.LIDT.Co.Preliminaries.Triangles.SimEq
public import MIPRE.Background.LIDT.Co.Preliminaries.ComparisonProjective
public import MIPRE.Background.LIDT.Co.Preliminaries.Completion
public import MIPRE.Foundations.FinitePairOrder

@[expose] public section

/-!
# The two-space calculus of the main theorem's tail

The tail of the vendored main theorem (`Test/MainTheorem/SourceRoleRegister/*` and
`Test/MainTheorem/MainFormal.lean` under `MIPRE/Background/LIDT/MIPStarRE/LDT/`) runs on the
strategy's own state, a state on `ιA × ιB` with Alice's measurements on `ιA` and Bob's on `ιB`. In
the port of `planning/c6b-plan.md` (milestone M13) that state is the strategy's bipartite model
`M : MIPRE.BipartiteModel 𝒞 𝒜 ℬ`, whose players' algebras `𝒜` and `ℬ` are abstract star-ordered
`⋆`-algebras, as in Co `ProjStrat` and in `MIPRE.LIDT.Simul.SoundIn`, not C⋆-algebras. This file
holds the two-space calculus the tail needs there. It has no vendored counterpart.

**Why it is needed.** The doubled model `D(M)` (`Co/Doubling/`) gives only role averages:
`Doubling.bipartiteConsError_model` says `bc_D(X, Y) = ½ (bc_M(X¹, Y²) + bc_M(Y¹, X²))`, so pulling a
one-sided relation back from `D(M)` costs a factor two, which breaks the vendored scalar cascade
into `mainFormalError`. Milestone M3 narrowed the vendored `_heterogeneous` lemmas of
`Preliminaries` to one carrier (`planning/c6b-plan.md`, "Departures in M3 and M5"); their
two-space forms are here, under their vendored names in the namespace `MIPRE.LIDT.Co.TwoSpace`.

**Vocabulary.**
* The placements `placeA M = π ∘ πA` and `placeB M = π ∘ πB` into `B(M.H)`, the vector state
  `vecState M hψ` of a unit `M.ψ`, and the placed submeasurements `leftPlacedSubMeas M A`,
  `rightPlacedSubMeas M B` and families `placeLeft M A`, `placeRight M B` (the vendored
  `leftPlacedSubMeas (ιB := ιB)` and `IdxSubMeas.placeLeft`). They are `SubMeas.map`, positivity
  transferring because a `⋆`-homomorphism between star-ordered rings is monotone.
* Consistency is M2's two-space defect `MIPRE.LIDT.Co.bipartiteConsError M 𝒟 A B`
  (`Co/Test/StrategyBiProj/Measurements.lean`): the vendored `ConsRel ψ 𝒟 A B δ` is written
  `bipartiteConsError M 𝒟 A B ≤ δ`, and no two-space `ConsRel` structure is defined
  (`planning/c6b-plan.md`, "Same-space and bipartite quantities"). Distances are the `VecState`
  relations of the port on `vecState M hψ`, with joint operators in `M.H →L[ℂ] M.H`.
* `bornProb_eq_ev`, `qBipartiteMatchMass_eq`, `qBipartiteConsDefect_eq` and
  `bipartiteConsError_eq` translate M2's defect into that vocabulary, and
  `qSDD_leftPlaced_eq_sum_norm_sq` (with its `πB` form) is the sum of norms with which M8's
  heterogeneous orthonormalizations conclude.

**Completion in an abstract algebra.** Co `Preliminaries.completeAtOutcome` is generic, but
`completeAtOutcomeProj` and `ProjMeas.isPVMIn` need a C⋆-algebra. In a finite pair the players'
algebras are `⋆`-isomorphic to the commutants of the other player's operators
(`IsFinitePair.equivA`, `equivB`, `MIPRE/Foundations/FinitePairOrder.lean`), which are
C⋆-algebras; `completeAtOutcomeProjA` and `completeAtOutcomeProjB` complete there and come back
along the inverse. Positivity transfers along any `⋆`-homomorphism of star-ordered rings, and
projectivity and the total are algebraic, so the order agreement of a finite pair is not used.
`ProjMeas.isPVMIn_of_isFinitePair` (in the namespace `MIPRE.LIDT.Co.ProjMeas`, for dot notation)
is the same transport for `ProjMeas.isPVMIn`.

## New here

Every declaration of this file is new; it has no vendored counterpart.
- `placeA`, `placeB`, `vecState`, `leftPlacedSubMeas`, `rightPlacedSubMeas`, `placeLeft`,
  `placeRight` and their `_apply`, `_outcome`, `_total` and `vecState_Ψ` lemmas: the placements.
- `bornProb_eq_ev`, `qBipartiteMatchMass_eq`, `qBipartiteConsDefect_eq`, `bipartiteConsError_eq`,
  `qSDD_leftPlaced_eq_sum_norm_sq`, `qSDD_rightPlaced_eq_sum_norm_sq`: the bridges.
- `bornProb_le_qform_πA`, `bornProb_le_qform_πB`, `qBipartiteConsDefect_le_one`,
  `bipartiteConsError_le_one_of_isProbability`, `bipartiteConsError_uniform_le_one`: positivity.
- `questionSDD_placeLeft_placeRight_le_two_questionConsistency`, `simeqToApprox_heterogeneous`,
  `two_questionConsistency_eq_questionSDD_of_projective`, `approxToSimeq_heterogeneous`: the
  comparison of consistency and distance.
- `consRel_of_matchGap`, `triangleSub_heterogeneous`, `triangleSub_right_heterogeneous`,
  `simeqTriangleInequality_heterogeneous`: the triangle inequalities.
- `qBipartiteMatchMass_postprocess_ge`, `qBipartiteConsDefect_postprocess_le`,
  `consRelDataProcessing_questionDependent`: data processing.
- `completeAtOutcomeProjA`, `completeAtOutcomeProjB`, their `_toMeasurement` and `_toSubMeas`
  equations, and `MIPRE.LIDT.Co.ProjMeas.isPVMIn_of_isFinitePair`, `…B`: completion.

## Not ported

Nothing: the file has no vendored counterpart.
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.TwoSpace

open MIPStarRE.LDT (Distribution avgOver avgOver_mono avgOver_add avgOver_zero avgOver_const_mul
  avgOver_congr avgOver_const_of_isProbability uniformDistribution
  uniformDistribution_isProbability)
open MIPStarRE.LDT.Preliminaries (avgOver_abs_le_sqrt_of_pointwise_nonneg)

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] (M : MIPRE.BipartiteModel 𝒞 𝒜 ℬ)

/-! ## Placements -/

/-- The first player's placement `a ↦ π (πA a)` into the operators of `M.H`. -/
noncomputable def placeA : 𝒜 →⋆ₐ[ℂ] (M.H →L[ℂ] M.H) := M.π.comp M.πA

/-- The second player's placement `b ↦ π (πB b)` into the operators of `M.H`. -/
noncomputable def placeB : ℬ →⋆ₐ[ℂ] (M.H →L[ℂ] M.H) := M.π.comp M.πB

/-- `placeA M a` is `π (πA a)`. -/
@[simp] theorem placeA_apply (a : 𝒜) : placeA M a = M.π (M.πA a) := rfl

/-- `placeB M b` is `π (πB b)`. -/
@[simp] theorem placeB_apply (b : ℬ) : placeB M b = M.π (M.πB b) := rfl

/-- The vector state of a unit state of `M`. -/
def vecState (hψ : ‖M.ψ‖ = 1) : VecState M.H := ⟨M.ψ, hψ⟩

/-- The vector of `vecState M hψ` is `M.ψ`. -/
@[simp] theorem vecState_Ψ (hψ : ‖M.ψ‖ = 1) : (vecState M hψ).Ψ = M.ψ := rfl

/-- The Born probability is the expectation of the product of the placements. -/
theorem bornProb_eq_ev (hψ : ‖M.ψ‖ = 1) (a : 𝒜) (b : ℬ) :
    M.bornProb a b = (vecState M hψ).ev (placeA M a * placeB M b) :=
  congrArg (MIPRE.Op.qform M.ψ) (map_mul M.π (M.πA a) (M.πB b))

section PlacedA

variable [PartialOrder 𝒜] [StarOrderedRing 𝒜]

/-- A submeasurement of the first player's algebra, placed on `M.H` (the vendored
`leftPlacedSubMeas (ιB := ιB)`). -/
noncomputable def leftPlacedSubMeas {α : Type*} [Fintype α] (A : SubMeas α 𝒜) :
    SubMeas α (M.H →L[ℂ] M.H) :=
  A.map (placeA M)

/-- The outcome operators of a left-placed submeasurement are placed. -/
@[simp] theorem leftPlacedSubMeas_outcome {α : Type*} [Fintype α] (A : SubMeas α 𝒜) (a : α) :
    (leftPlacedSubMeas M A).outcome a = M.π (M.πA (A.outcome a)) := rfl

/-- The total of a left-placed submeasurement is placed. -/
@[simp] theorem leftPlacedSubMeas_total {α : Type*} [Fintype α] (A : SubMeas α 𝒜) :
    (leftPlacedSubMeas M A).total = M.π (M.πA A.total) := rfl

/-- A family of submeasurements of the first player's algebra, placed on `M.H` (the vendored
`IdxSubMeas.placeLeft (ιB := ιB)`). -/
noncomputable def placeLeft {Question Outcome : Type*} [Fintype Outcome]
    (A : IdxSubMeas Question Outcome 𝒜) : IdxSubMeas Question Outcome (M.H →L[ℂ] M.H) :=
  fun q => leftPlacedSubMeas M (A q)

/-- The squared distance of two placed submeasurements of the first player is the sum of norms
`∑ₐ ‖π(πA(Aₐ − Pₐ)) ψ‖²` with which M8's heterogeneous orthonormalization concludes. -/
theorem qSDD_leftPlaced_eq_sum_norm_sq (hψ : ‖M.ψ‖ = 1) {Outcome : Type*} [Fintype Outcome]
    (A P : SubMeas Outcome 𝒜) :
    (vecState M hψ).qSDD (leftPlacedSubMeas M A) (leftPlacedSubMeas M P) =
      ∑ a, ‖M.π (M.πA (A.outcome a - P.outcome a)) M.ψ‖ ^ 2 :=
  (VecState.qSDDCore_eq_sum_snorm_sq _ _ _).trans <| Finset.sum_congr rfl fun a _ => by
    rw [map_sub M.πA, map_sub M.π]
    rfl

end PlacedA

section PlacedB

variable [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- A submeasurement of the second player's algebra, placed on `M.H` (the vendored
`rightPlacedSubMeas (ιA := ιA)`). -/
noncomputable def rightPlacedSubMeas {α : Type*} [Fintype α] (B : SubMeas α ℬ) :
    SubMeas α (M.H →L[ℂ] M.H) :=
  B.map (placeB M)

/-- The outcome operators of a right-placed submeasurement are placed. -/
@[simp] theorem rightPlacedSubMeas_outcome {α : Type*} [Fintype α] (B : SubMeas α ℬ) (a : α) :
    (rightPlacedSubMeas M B).outcome a = M.π (M.πB (B.outcome a)) := rfl

/-- The total of a right-placed submeasurement is placed. -/
@[simp] theorem rightPlacedSubMeas_total {α : Type*} [Fintype α] (B : SubMeas α ℬ) :
    (rightPlacedSubMeas M B).total = M.π (M.πB B.total) := rfl

/-- A family of submeasurements of the second player's algebra, placed on `M.H` (the vendored
`IdxSubMeas.placeRight (ιA := ιA)`). -/
noncomputable def placeRight {Question Outcome : Type*} [Fintype Outcome]
    (B : IdxSubMeas Question Outcome ℬ) : IdxSubMeas Question Outcome (M.H →L[ℂ] M.H) :=
  fun q => rightPlacedSubMeas M (B q)

/-- The squared distance of two placed submeasurements of the second player is
`∑ₐ ‖π(πB(Bₐ − Pₐ)) ψ‖²`. -/
theorem qSDD_rightPlaced_eq_sum_norm_sq (hψ : ‖M.ψ‖ = 1) {Outcome : Type*} [Fintype Outcome]
    (B P : SubMeas Outcome ℬ) :
    (vecState M hψ).qSDD (rightPlacedSubMeas M B) (rightPlacedSubMeas M P) =
      ∑ a, ‖M.π (M.πB (B.outcome a - P.outcome a)) M.ψ‖ ^ 2 :=
  (VecState.qSDDCore_eq_sum_snorm_sq _ _ _).trans <| Finset.sum_congr rfl fun a _ => by
    rw [map_sub M.πB, map_sub M.π]
    rfl

end PlacedB

section Ordered

variable [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ]

/-! ## Bridges to the two-space defect -/

section Bridges

variable (hψ : ‖M.ψ‖ = 1)

/-- M2's two-space matching mass is the matching mass of the placed submeasurements. -/
theorem qBipartiteMatchMass_eq {Outcome : Type*} [Fintype Outcome] (A : SubMeas Outcome 𝒜)
    (B : SubMeas Outcome ℬ) :
    qBipartiteMatchMass M A B =
      (vecState M hψ).qMatchMass (leftPlacedSubMeas M A) (rightPlacedSubMeas M B) :=
  Finset.sum_congr rfl fun _ _ => bornProb_eq_ev M hψ _ _

/-- M2's two-space consistency defect is the consistency defect of the placed
submeasurements. -/
theorem qBipartiteConsDefect_eq {Outcome : Type*} [Fintype Outcome] (A : SubMeas Outcome 𝒜)
    (B : SubMeas Outcome ℬ) :
    qBipartiteConsDefect M A B =
      (vecState M hψ).qConsDefect (leftPlacedSubMeas M A) (rightPlacedSubMeas M B) := by
  rw [qBipartiteConsDefect, bornProb_eq_ev M hψ, qBipartiteMatchMass_eq M hψ]
  rfl

/-- M2's averaged two-space defect is the averaged consistency defect of the placed families. -/
theorem bipartiteConsError_eq {Question Outcome : Type*} [Fintype Outcome]
    (𝒟 : Distribution Question) (A : IdxSubMeas Question Outcome 𝒜)
    (B : IdxSubMeas Question Outcome ℬ) :
    bipartiteConsError M 𝒟 A B = (vecState M hψ).consError 𝒟 (placeLeft M A) (placeRight M B) :=
  congrArg (avgOver 𝒟) (funext fun q => qBipartiteConsDefect_eq M hψ (A q) (B q))

end Bridges

/-! ## Positivity -/

/-- `⟨ψ, (x ⊗ y) ψ⟩ ≤ ⟨ψ, (x ⊗ 1) ψ⟩` for `0 ≤ x` and `y ≤ 1`: `x ⊗ (1 − y)` is a product of
commuting positive operators. -/
theorem bornProb_le_qform_πA {x : 𝒜} {y : ℬ} (hx : 0 ≤ x) (hy : y ≤ 1) :
    M.bornProb x y ≤ M.qform (M.πA x) := by
  have h := M.bornProb_nonneg hx (sub_nonneg.2 hy)
  rw [M.bornProb_sub_right] at h
  have h1 : M.bornProb x 1 = M.qform (M.πA x) := by
    rw [MIPRE.BipartiteModel.bornProb, map_one, mul_one]
  linarith

/-- `⟨ψ, (x ⊗ y) ψ⟩ ≤ ⟨ψ, (1 ⊗ y) ψ⟩` for `x ≤ 1` and `0 ≤ y` (`bornProb_le_qform_πA` for the
swapped model). -/
theorem bornProb_le_qform_πB {x : 𝒜} {y : ℬ} (hx : x ≤ 1) (hy : 0 ≤ y) :
    M.bornProb x y ≤ M.qform (M.πB y) := by
  rw [← M.bornProb_swap]
  exact bornProb_le_qform_πA M.swap hy hx

/-- A two-space consistency defect is at most `1` at a unit state. -/
theorem qBipartiteConsDefect_le_one (hψ : ‖M.ψ‖ = 1) {Outcome : Type*} [Fintype Outcome]
    (A : SubMeas Outcome 𝒜) (B : SubMeas Outcome ℬ) :
    qBipartiteConsDefect M A B ≤ 1 := by
  have hmatch : 0 ≤ qBipartiteMatchMass M A B :=
    Finset.sum_nonneg fun a _ => M.bornProb_nonneg (A.outcome_pos a) (B.outcome_pos a)
  have h1 := bornProb_le_qform_πA M A.total_nonneg B.total_le_one
  have h2 := bornProb_le_qform_πB M A.total_le_one (zero_le_one (α := ℬ))
  have h3 : M.bornProb A.total 1 = M.qform (M.πA A.total) := by
    rw [MIPRE.BipartiteModel.bornProb, map_one, mul_one]
  have h4 : M.qform (M.πB 1) = 1 := by rw [map_one, M.qform_one hψ]
  rw [qBipartiteConsDefect]
  exact max_le zero_le_one (by linarith)

/-- Under a probability question distribution, the averaged two-space defect is at most `1`. -/
theorem bipartiteConsError_le_one_of_isProbability (hψ : ‖M.ψ‖ = 1)
    {Question Outcome : Type*} [Fintype Outcome] (𝒟 : Distribution Question)
    (h𝒟 : 𝒟.IsProbability) (A : IdxSubMeas Question Outcome 𝒜)
    (B : IdxSubMeas Question Outcome ℬ) :
    bipartiteConsError M 𝒟 A B ≤ 1 :=
  (avgOver_mono 𝒟 _ (fun _ => 1) fun q => qBipartiteConsDefect_le_one M hψ (A q) (B q)).trans_eq
    (avgOver_const_of_isProbability 𝒟 h𝒟 1)

/-- Under the uniform question distribution, the averaged two-space defect is at most `1` (the
trivial branch of the main theorem). -/
theorem bipartiteConsError_uniform_le_one (hψ : ‖M.ψ‖ = 1) {Question Outcome : Type*}
    [Fintype Question] [DecidableEq Question] [Nonempty Question] [Fintype Outcome]
    (A : IdxSubMeas Question Outcome 𝒜) (B : IdxSubMeas Question Outcome ℬ) :
    bipartiteConsError M (uniformDistribution Question) A B ≤ 1 :=
  bipartiteConsError_le_one_of_isProbability M hψ _
    (uniformDistribution_isProbability Question) A B

/-! ## Consistency and distance -/

section Comparison

variable (hψ : ‖M.ψ‖ = 1)

/-- For measurements `A` of `𝒜` and `B` of `ℬ`, the squared distance of their placements is at
most twice their two-space consistency defect: the per-question core of
`simeqToApprox_heterogeneous`, which is `BipartiteModel.xSqNorm_sum_le_two_mul`. -/
theorem questionSDD_placeLeft_placeRight_le_two_questionConsistency {Outcome : Type*}
    [Fintype Outcome] (A : Measurement Outcome 𝒜) (B : Measurement Outcome ℬ) :
    (vecState M hψ).qSDD (leftPlacedSubMeas M A.toSubMeas) (rightPlacedSubMeas M B.toSubMeas) ≤
      2 * qBipartiteConsDefect M A.toSubMeas B.toSubMeas := by
  have h := M.xSqNorm_sum_le_two_mul hψ A.toPOVMIn B.toPOVMIn
  have hL : (vecState M hψ).qSDD (leftPlacedSubMeas M A.toSubMeas)
      (rightPlacedSubMeas M B.toSubMeas) =
        ∑ c, M.xSqNorm (A.toPOVMIn.op c) (B.toPOVMIn.op c) :=
    (VecState.qSDDCore_eq_sum_snorm_sq _ _ _).trans <| Finset.sum_congr rfl fun c _ => by
      show _ = MIPRE.Op.snorm M.ψ (M.π (M.πA (A.outcome c) - M.πB (B.outcome c))) ^ 2
      rw [map_sub M.π]
      rfl
  have hR : 1 - ∑ c, M.bornProb (A.toPOVMIn.op c) (B.toPOVMIn.op c) ≤
      qBipartiteConsDefect M A.toSubMeas B.toSubMeas := by
    have htot : M.bornProb A.total B.total = 1 := by
      rw [A.total_eq_one, B.total_eq_one, MIPRE.BipartiteModel.bornProb, map_one, map_one,
        mul_one, M.qform_one hψ]
    rw [qBipartiteConsDefect, htot]
    exact le_max_right _ _
  rw [hL]
  linarith

/-- Heterogeneous `prop:simeq-to-approx`: two-space consistency of measurements `A` of `𝒜` and
`B` of `ℬ` at `δ` gives the state-dependent distance `2δ` between their placements. -/
theorem simeqToApprox_heterogeneous {Question Outcome : Type*} [Fintype Outcome]
    (𝒟 : Distribution Question) (A : IdxMeas Question Outcome 𝒜)
    (B : IdxMeas Question Outcome ℬ) (δ : ℝ) :
    bipartiteConsError M 𝒟 (IdxMeas.toIdxSubMeas A) (IdxMeas.toIdxSubMeas B) ≤ δ →
      (vecState M hψ).SDDRel 𝒟 (placeLeft M (IdxMeas.toIdxSubMeas A))
        (placeRight M (IdxMeas.toIdxSubMeas B)) (2 * δ) := fun hcons =>
  ⟨calc avgOver 𝒟 (fun q => (vecState M hψ).qSDD (leftPlacedSubMeas M (A q).toSubMeas)
          (rightPlacedSubMeas M (B q).toSubMeas))
        ≤ avgOver 𝒟 (fun q => 2 * qBipartiteConsDefect M (A q).toSubMeas (B q).toSubMeas) :=
          avgOver_mono 𝒟 _ _ fun q =>
            questionSDD_placeLeft_placeRight_le_two_questionConsistency M hψ (A q) (B q)
      _ = 2 * bipartiteConsError M 𝒟 (IdxMeas.toIdxSubMeas A) (IdxMeas.toIdxSubMeas B) :=
          avgOver_const_mul 𝒟 2 _
      _ ≤ 2 * δ := mul_le_mul_of_nonneg_left hcons (by norm_num)⟩

/-- For projective measurements `A` of `𝒜` and `B` of `ℬ`, twice their two-space consistency
defect is the squared distance of their placements: the two placements commute and each is
idempotent, so `(Aₐ ⊗ 1 − 1 ⊗ Bₐ)² = Aₐ ⊗ 1 + 1 ⊗ Bₐ − 2 Aₐ ⊗ Bₐ`. Algebraic: no C⋆-structure
on `𝒜` or `ℬ` is used. -/
theorem two_questionConsistency_eq_questionSDD_of_projective {Outcome : Type*} [Fintype Outcome]
    (A : ProjMeas Outcome 𝒜) (B : ProjMeas Outcome ℬ) :
    2 * qBipartiteConsDefect M A.toSubMeas B.toSubMeas =
      (vecState M hψ).qSDD (leftPlacedSubMeas M A.toSubMeas)
        (rightPlacedSubMeas M B.toSubMeas) := by
  set V := vecState M hψ
  have hterm : ∀ a, V.ev (star (placeA M (A.outcome a) - placeB M (B.outcome a)) *
      (placeA M (A.outcome a) - placeB M (B.outcome a))) =
        V.ev (placeA M (A.outcome a)) + V.ev (placeB M (B.outcome a)) -
          2 * V.ev (placeA M (A.outcome a) * placeB M (B.outcome a)) := fun a => by
    have hX : star (placeA M (A.outcome a) - placeB M (B.outcome a)) =
        placeA M (A.outcome a) - placeB M (B.outcome a) :=
      (((IsSelfAdjoint.of_nonneg (A.outcome_pos a)).map (placeA M)).sub
        ((IsSelfAdjoint.of_nonneg (B.outcome_pos a)).map (placeB M))).star_eq
    have hc : placeB M (B.outcome a) * placeA M (A.outcome a) =
        placeA M (A.outcome a) * placeB M (B.outcome a) :=
      ((M.commute (A.outcome a) (B.outcome a)).map M.π).eq.symm
    have hA : placeA M (A.outcome a) * placeA M (A.outcome a) = placeA M (A.outcome a) := by
      rw [← map_mul, A.proj]
    have hB : placeB M (B.outcome a) * placeB M (B.outcome a) = placeB M (B.outcome a) := by
      rw [← map_mul, B.proj]
    rw [hX, sub_mul, mul_sub, mul_sub, hc, hA, hB, V.ev_sub, V.ev_sub, V.ev_sub]
    ring
  have hL : ∑ a, V.ev (placeA M (A.outcome a)) = V.ev 1 := by
    rw [← V.ev_sum, ← map_sum, A.sum_eq_total, A.total_eq_one, map_one]
  have hR : ∑ a, V.ev (placeB M (B.outcome a)) = V.ev 1 := by
    rw [← V.ev_sum, ← map_sum, B.sum_eq_total, B.total_eq_one, map_one]
  set match' := ∑ a, V.ev (placeA M (A.outcome a) * placeB M (B.outcome a))
  have hSDD : V.qSDD (leftPlacedSubMeas M A.toSubMeas) (rightPlacedSubMeas M B.toSubMeas) =
      2 * (V.ev 1 - match') := by
    show ∑ a, V.ev (star (placeA M (A.outcome a) - placeB M (B.outcome a)) *
        (placeA M (A.outcome a) - placeB M (B.outcome a))) = _
    simp only [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hL, hR]
    ring
  have hgap : 0 ≤ V.ev 1 - match' := by
    have := V.qSDD_nonneg (leftPlacedSubMeas M A.toSubMeas) (rightPlacedSubMeas M B.toSubMeas)
    linarith
  have htot : M.bornProb A.total B.total = V.ev 1 := by
    rw [A.total_eq_one, B.total_eq_one, bornProb_eq_ev M hψ, map_one, map_one, mul_one]
  have hmatch : qBipartiteMatchMass M A.toSubMeas B.toSubMeas = match' :=
    Finset.sum_congr rfl fun a _ => bornProb_eq_ev M hψ _ _
  rw [qBipartiteConsDefect, htot, hmatch, max_eq_right hgap, hSDD]

/-- Heterogeneous projective converse of `prop:simeq-to-approx`: for projective measurements
`A` of `𝒜` and `B` of `ℬ`, the state-dependent distance `2δ` between their placements gives
two-space consistency at `δ`. -/
theorem approxToSimeq_heterogeneous {Question Outcome : Type*} [Fintype Outcome]
    (𝒟 : Distribution Question) (A : IdxProjMeas Question Outcome 𝒜)
    (B : IdxProjMeas Question Outcome ℬ) (δ : ℝ) :
    (vecState M hψ).SDDRel 𝒟 (placeLeft M (IdxProjMeas.toIdxSubMeas A))
        (placeRight M (IdxProjMeas.toIdxSubMeas B)) (2 * δ) →
      bipartiteConsError M 𝒟 (IdxProjMeas.toIdxSubMeas A) (IdxProjMeas.toIdxSubMeas B) ≤ δ := by
  intro ⟨happrox⟩
  have h : 2 * bipartiteConsError M 𝒟 (IdxProjMeas.toIdxSubMeas A)
      (IdxProjMeas.toIdxSubMeas B) =
        (vecState M hψ).sddError 𝒟 (placeLeft M (IdxProjMeas.toIdxSubMeas A))
          (placeRight M (IdxProjMeas.toIdxSubMeas B)) := by
    rw [bipartiteConsError, ← avgOver_const_mul]
    exact avgOver_congr _ _ _ fun q =>
      two_questionConsistency_eq_questionSDD_of_projective M hψ (A q) (B q)
  linarith

end Comparison

/-! ## Triangle inequalities -/

omit [StarOrderedRing 𝒜] [StarOrderedRing ℬ] in
/-- The common substitution step of the two-space `triangleSub` family (Co
`Preliminaries.consRel_of_matchGap`): if `bipartiteConsError M 𝒟 A B ≤ δ`, the matching masses
of `(A, B)` and `(A', B')` differ by at most `√(s q)` at each question, and the total overlap of
`(A', B')` exceeds that of `(A, B)` by at most `e q`, then the defect of `(A', B')` is at most
`δ + √ε + η` for `𝔼 s ≤ ε` and `𝔼 e ≤ η`. -/
theorem consRel_of_matchGap {Question Outcome : Type*} [Fintype Outcome]
    (𝒟 : Distribution Question) (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A A' : IdxSubMeas Question Outcome 𝒜) (B B' : IdxSubMeas Question Outcome ℬ)
    (s e : Question → ℝ) (δ ε η : ℝ)
    (hAB : bipartiteConsError M 𝒟 A B ≤ δ)
    (hgap : ∀ q, |qBipartiteMatchMass M (A q) (B q) - qBipartiteMatchMass M (A' q) (B' q)| ≤
      Real.sqrt (s q))
    (hs : ∀ q, 0 ≤ s q) (hsε : avgOver 𝒟 s ≤ ε)
    (he : ∀ q, max 0 (M.bornProb (A' q).total (B' q).total -
      M.bornProb (A q).total (B q).total) ≤ e q)
    (heη : avgOver 𝒟 e ≤ η) :
    bipartiteConsError M 𝒟 A' B' ≤ δ + Real.sqrt ε + η := by
  set gap : Question → ℝ := fun q =>
    qBipartiteMatchMass M (A q) (B q) - qBipartiteMatchMass M (A' q) (B' q)
  have hpt : ∀ q, qBipartiteConsDefect M (A' q) (B' q) ≤
      qBipartiteConsDefect M (A q) (B q) + |gap q| + e q := fun q => by
    have he' := he q
    rw [qBipartiteConsDefect, qBipartiteConsDefect]
    exact max_le (add_nonneg (add_nonneg (le_max_left _ _) (abs_nonneg _))
      ((le_max_left _ _).trans he'))
      (by linarith [le_max_right 0 (M.bornProb (A q).total (B q).total -
        qBipartiteMatchMass M (A q) (B q)), le_abs_self (gap q), (le_max_right _ _).trans he'])
  refine (avgOver_mono 𝒟 _ _ hpt).trans ?_
  rw [avgOver_add, avgOver_add]
  exact add_le_add (add_le_add hAB
    ((avgOver_abs_le_sqrt_of_pointwise_nonneg 𝒟 h𝒟 gap s hgap hs).trans
      (Real.sqrt_le_sqrt hsε))) heη

/-- Heterogeneous left substitution (`prop:triangle-sub`): if measurements `A` of `𝒜` and a
submeasurement `C` of `ℬ` are consistent at `δ`, and the placements of `A` and of a measurement
`B` of `𝒜` are at state-dependent distance `ε`, then `B` and `C` are consistent at `δ + √ε`. -/
theorem triangleSub_heterogeneous (hψ : ‖M.ψ‖ = 1) {Question Outcome : Type*}
    [Fintype Outcome] (𝒟 : Distribution Question) (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : IdxMeas Question Outcome 𝒜) (C : IdxSubMeas Question Outcome ℬ) (δ ε : ℝ)
    (hAC : bipartiteConsError M 𝒟 (IdxMeas.toIdxSubMeas A) C ≤ δ)
    (hAB : (vecState M hψ).SDDRel 𝒟 (placeLeft M (IdxMeas.toIdxSubMeas A))
      (placeLeft M (IdxMeas.toIdxSubMeas B)) ε) :
    bipartiteConsError M 𝒟 (IdxMeas.toIdxSubMeas B) C ≤ δ + Real.sqrt ε :=
  (consRel_of_matchGap M 𝒟 h𝒟 (IdxMeas.toIdxSubMeas A) (IdxMeas.toIdxSubMeas B) C C
    (fun q => (vecState M hψ).qSDD (placeLeft M (IdxMeas.toIdxSubMeas A) q)
      (placeLeft M (IdxMeas.toIdxSubMeas B) q)) (fun _ => 0) δ ε 0 hAC
    (fun q => by
      rw [qBipartiteMatchMass_eq M hψ, qBipartiteMatchMass_eq M hψ]
      exact Preliminaries.question_easyApproxFromApproxDelta (vecState M hψ)
        (leftPlacedSubMeas M (A q).toSubMeas) (leftPlacedSubMeas M (B q).toSubMeas)
        (rightPlacedSubMeas M (C q)))
    (fun _ => VecState.qSDD_nonneg _ _ _) hAB.squaredDistanceBound
    (fun q => by
      show max 0 (M.bornProb (B q).total (C q).total - M.bornProb (A q).total (C q).total) ≤ 0
      rw [(A q).total_eq_one, (B q).total_eq_one, sub_self, max_self])
    (avgOver_zero 𝒟).le).trans_eq (add_zero _)

/-- Heterogeneous right substitution: if a submeasurement `A` of `𝒜` and a measurement `B` of
`ℬ` are consistent at `δ`, and the placements of `B` and of a measurement `D` of `ℬ` are at
state-dependent distance `ε`, then `A` and `D` are consistent at `δ + √ε`. -/
theorem triangleSub_right_heterogeneous (hψ : ‖M.ψ‖ = 1) {Question Outcome : Type*}
    [Fintype Outcome] (𝒟 : Distribution Question) (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A : IdxSubMeas Question Outcome 𝒜) (B D : IdxMeas Question Outcome ℬ) (δ ε : ℝ)
    (hAB : bipartiteConsError M 𝒟 A (IdxMeas.toIdxSubMeas B) ≤ δ)
    (hBD : (vecState M hψ).SDDRel 𝒟 (placeRight M (IdxMeas.toIdxSubMeas B))
      (placeRight M (IdxMeas.toIdxSubMeas D)) ε) :
    bipartiteConsError M 𝒟 A (IdxMeas.toIdxSubMeas D) ≤ δ + Real.sqrt ε :=
  (consRel_of_matchGap M 𝒟 h𝒟 A A (IdxMeas.toIdxSubMeas B) (IdxMeas.toIdxSubMeas D)
    (fun q => (vecState M hψ).qSDD (placeRight M (IdxMeas.toIdxSubMeas B) q)
      (placeRight M (IdxMeas.toIdxSubMeas D) q)) (fun _ => 0) δ ε 0 hAB
    (fun q => by
      rw [qBipartiteMatchMass_eq M hψ, qBipartiteMatchMass_eq M hψ]
      exact Preliminaries.right_match_gap_abs_le_sqrt_qSDD (vecState M hψ)
        (leftPlacedSubMeas M (A q)) (rightPlacedSubMeas M (B q).toSubMeas)
        (rightPlacedSubMeas M (D q).toSubMeas))
    (fun _ => VecState.qSDD_nonneg _ _ _) hBD.squaredDistanceBound
    (fun q => by
      show max 0 (M.bornProb (A q).total (D q).total - M.bornProb (A q).total (B q).total) ≤ 0
      rw [(D q).total_eq_one, (B q).total_eq_one, sub_self, max_self])
    (avgOver_zero 𝒟).le).trans_eq (add_zero _)

/-- Heterogeneous `prop:simeq-triangle-inequality`, with the vendored constant: for measurements
`A`, `C` of `𝒜` and `B`, `D` of `ℬ`, consistency of `(A, B)` at `ε`, of `(C, B)` at `δ` and of
`(C, D)` at `γ` gives consistency of `(A, D)` at `ε + 2√(δ + γ)`. As in Co
`Preliminaries.simeqTriangleInequality`: compare the placements of `B` and `D` through `C`, then
substitute on the right. -/
theorem simeqTriangleInequality_heterogeneous (hψ : ‖M.ψ‖ = 1) {Question Outcome : Type*}
    [Fintype Outcome] (𝒟 : Distribution Question) (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A C : IdxMeas Question Outcome 𝒜) (B D : IdxMeas Question Outcome ℬ) (ε δ γ : ℝ)
    (hAB : bipartiteConsError M 𝒟 (IdxMeas.toIdxSubMeas A) (IdxMeas.toIdxSubMeas B) ≤ ε)
    (hCB : bipartiteConsError M 𝒟 (IdxMeas.toIdxSubMeas C) (IdxMeas.toIdxSubMeas B) ≤ δ)
    (hCD : bipartiteConsError M 𝒟 (IdxMeas.toIdxSubMeas C) (IdxMeas.toIdxSubMeas D) ≤ γ) :
    bipartiteConsError M 𝒟 (IdxMeas.toIdxSubMeas A) (IdxMeas.toIdxSubMeas D) ≤
      ε + 2 * Real.sqrt (δ + γ) := by
  have hBD : (vecState M hψ).SDDRel 𝒟 (placeRight M (IdxMeas.toIdxSubMeas B))
      (placeRight M (IdxMeas.toIdxSubMeas D)) (4 * (δ + γ)) :=
    Preliminaries.stateDependentDistanceRel_mono (vecState M hψ) 𝒟 _ _ _ _ (by linarith)
      (Preliminaries.stateDependentDistanceRel_triangle (vecState M hψ) 𝒟 _
        (placeLeft M (IdxMeas.toIdxSubMeas C)) _ (2 * δ) (2 * γ)
        (Preliminaries.sddRel_symm (vecState M hψ) 𝒟 _ _ _
          (simeqToApprox_heterogeneous M hψ 𝒟 C B δ hCB))
        (simeqToApprox_heterogeneous M hψ 𝒟 C D γ hCD))
  have hsqrt : Real.sqrt (4 * (δ + γ)) = 2 * Real.sqrt (δ + γ) := by
    rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  exact (triangleSub_right_heterogeneous M hψ 𝒟 h𝒟 _ B D ε _ hAB hBD).trans_eq
    (by rw [hsqrt])

/-! ## Data processing -/

/-- Postprocessing two submeasurements, of `𝒜` and of `ℬ`, by the same readout map can only
increase their two-space matching mass: the new terms are the old ones plus Born probabilities
of positive elements within each fibre. -/
theorem qBipartiteMatchMass_postprocess_ge {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α 𝒜) (B : SubMeas α ℬ) (f : α → β) :
    qBipartiteMatchMass M A B ≤ qBipartiteMatchMass M (postprocess A f) (postprocess B f) := by
  classical
  show ∑ a, M.bornProb (A.outcome a) (B.outcome a) ≤
    ∑ b, M.bornProb ((postprocess A f).outcome b) ((postprocess B f).outcome b)
  rw [← Finset.sum_fiberwise Finset.univ f]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [SubMeas.postprocess_outcome, SubMeas.postprocess_outcome, M.bornProb_sum_left]
  refine Finset.sum_le_sum fun a ha => ?_
  rw [M.bornProb_sum_right]
  exact Finset.single_le_sum
    (fun a' _ => M.bornProb_nonneg (A.outcome_pos a) (B.outcome_pos a')) ha

/-- Postprocessing two submeasurements, of `𝒜` and of `ℬ`, by the same readout map can only
decrease their two-space consistency defect: the totals are kept. -/
theorem qBipartiteConsDefect_postprocess_le {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α 𝒜) (B : SubMeas α ℬ) (f : α → β) :
    qBipartiteConsDefect M (postprocess A f) (postprocess B f) ≤ qBipartiteConsDefect M A B :=
  max_le_max le_rfl (sub_le_sub_left (qBipartiteMatchMass_postprocess_ge M A B f) _)

/-- Question-dependent postprocessing preserves two-space consistency (the two-space form of Co
`Preliminaries.consRelDataProcessing_questionDependent`). -/
theorem consRelDataProcessing_questionDependent {Question α β : Type*} [Fintype α] [Fintype β]
    (𝒟 : Distribution Question) (A : IdxSubMeas Question α 𝒜) (B : IdxSubMeas Question α ℬ)
    (δ : ℝ) (f : Question → α → β) :
    bipartiteConsError M 𝒟 A B ≤ δ →
      bipartiteConsError M 𝒟 (fun q => postprocess (A q) (f q))
        (fun q => postprocess (B q) (f q)) ≤ δ := fun h =>
  (avgOver_mono 𝒟 _ _ fun q => qBipartiteConsDefect_postprocess_le M (A q) (B q) (f q)).trans h

end Ordered

/-! ## Completion in the players' algebras of a finite pair -/

section CompletionA

variable {M} [PartialOrder 𝒜] [StarOrderedRing 𝒜]

/-- Complete a projective submeasurement of the first player's algebra of a finite pair at a
distinguished outcome, to a projective measurement: Co `Preliminaries.completeAtOutcomeProj` in
the commutant `IsFinitePair.equivA` identifies `𝒜` with, a C⋆-algebra, carried back along the
inverse. -/
noncomputable def completeAtOutcomeProjA (hM : M.IsFinitePair) {Outcome : Type*}
    [Fintype Outcome] (P : ProjSubMeas Outcome 𝒜) (a0 : Outcome) : ProjMeas Outcome 𝒜 :=
  (Preliminaries.completeAtOutcomeProj (P.map hM.equivA.toStarAlgHom) a0).map
    hM.equivA.symm.toStarAlgHom

/-- The measurement of `completeAtOutcomeProjA hM P a0` is the canonical completion
`completeAtOutcome P.toSubMeas a0` in `𝒜`. -/
theorem completeAtOutcomeProjA_toMeasurement (hM : M.IsFinitePair) {Outcome : Type*}
    [Fintype Outcome] (P : ProjSubMeas Outcome 𝒜) (a0 : Outcome) :
    (completeAtOutcomeProjA hM P a0).toMeasurement =
      Preliminaries.completeAtOutcome P.toSubMeas a0 := by
  refine Measurement.ext fun a => ?_
  by_cases ha : a = a0
  · subst ha
    simp [completeAtOutcomeProjA, Preliminaries.completeAtOutcome]
  · simp [completeAtOutcomeProjA, Preliminaries.completeAtOutcome, ha]

/-- The submeasurement of `completeAtOutcomeProjA hM P a0` is that of `completeAtOutcome`. -/
theorem completeAtOutcomeProjA_toSubMeas (hM : M.IsFinitePair) {Outcome : Type*}
    [Fintype Outcome] (P : ProjSubMeas Outcome 𝒜) (a0 : Outcome) :
    (completeAtOutcomeProjA hM P a0).toSubMeas =
      (Preliminaries.completeAtOutcome P.toSubMeas a0).toSubMeas :=
  congrArg Measurement.toSubMeas (completeAtOutcomeProjA_toMeasurement hM P a0)

/-- **A projective measurement of the first player's algebra of a finite pair is a projective
measurement of the repository** (`MIPRE.IsPVMIn`): Co `ProjMeas.isPVMIn` in the commutant
`IsFinitePair.equivA` identifies `𝒜` with, pulled back along `isPVMIn_map_equiv_iff`. -/
theorem _root_.MIPRE.LIDT.Co.ProjMeas.isPVMIn_of_isFinitePair (hM : M.IsFinitePair)
    {Outcome : Type*} [Fintype Outcome] (Q : ProjMeas Outcome 𝒜) : IsPVMIn Q.outcome :=
  (isPVMIn_map_equiv_iff hM.equivA).1 (Q.map hM.equivA.toStarAlgHom).isPVMIn

end CompletionA

section CompletionB

variable {M} [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- Complete a projective submeasurement of the second player's algebra of a finite pair at a
distinguished outcome, through `IsFinitePair.equivB`. -/
noncomputable def completeAtOutcomeProjB (hM : M.IsFinitePair) {Outcome : Type*}
    [Fintype Outcome] (P : ProjSubMeas Outcome ℬ) (a0 : Outcome) : ProjMeas Outcome ℬ :=
  (Preliminaries.completeAtOutcomeProj (P.map hM.equivB.toStarAlgHom) a0).map
    hM.equivB.symm.toStarAlgHom

/-- The measurement of `completeAtOutcomeProjB hM P a0` is the canonical completion
`completeAtOutcome P.toSubMeas a0` in `ℬ`. -/
theorem completeAtOutcomeProjB_toMeasurement (hM : M.IsFinitePair) {Outcome : Type*}
    [Fintype Outcome] (P : ProjSubMeas Outcome ℬ) (a0 : Outcome) :
    (completeAtOutcomeProjB hM P a0).toMeasurement =
      Preliminaries.completeAtOutcome P.toSubMeas a0 := by
  refine Measurement.ext fun a => ?_
  by_cases ha : a = a0
  · subst ha
    simp [completeAtOutcomeProjB, Preliminaries.completeAtOutcome]
  · simp [completeAtOutcomeProjB, Preliminaries.completeAtOutcome, ha]

/-- The submeasurement of `completeAtOutcomeProjB hM P a0` is that of `completeAtOutcome`. -/
theorem completeAtOutcomeProjB_toSubMeas (hM : M.IsFinitePair) {Outcome : Type*}
    [Fintype Outcome] (P : ProjSubMeas Outcome ℬ) (a0 : Outcome) :
    (completeAtOutcomeProjB hM P a0).toSubMeas =
      (Preliminaries.completeAtOutcome P.toSubMeas a0).toSubMeas :=
  congrArg Measurement.toSubMeas (completeAtOutcomeProjB_toMeasurement hM P a0)

/-- **A projective measurement of the second player's algebra of a finite pair is a projective
measurement of the repository**, through `IsFinitePair.equivB`. -/
theorem _root_.MIPRE.LIDT.Co.ProjMeas.isPVMIn_of_isFinitePairB (hM : M.IsFinitePair)
    {Outcome : Type*} [Fintype Outcome] (Q : ProjMeas Outcome ℬ) : IsPVMIn Q.outcome :=
  (isPVMIn_map_equiv_iff hM.equivB).1 (Q.map hM.equivB.toStarAlgHom).isPVMIn

end CompletionB

end MIPRE.LIDT.Co.TwoSpace

end
