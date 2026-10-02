/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Doubling.Halving
public import MIPRE.Background.LIDT.Co.Test.StrategyBiProj.Measurements

@[expose] public section

/-!
# The symmetric strategy of a two-space strategy

Theorem D of `reports/c6b-paper-proofs.md`, §4 (Lemma 12; symmetrization placed after the bridge),
for the doubled model `Doubling.model hM hψ` of `Co/Doubling/Model.lean`. A two-space projective
strategy `strategy : ProjStrat params 𝒞 𝒜 ℬ` (`Co/Test/StrategyCore.lean`) whose state `M` is a
finite pair doubles to a symmetric strategy `Doubling.symmStrat strategy hM` of the doubled model,
whose every measurement family is the componentwise pairing of the first and the second player's,
and the failure probabilities of the doubled strategy are the role averages of the two-space
surrogate of `Co/Test/StrategyBiProj/Measurements.lean`:

* `symmStrat_axisParallel_eq_roleAverage`: `axis(S_D) = axisParallelRoleAverage(S)`;
* `symmStrat_selfConsistency_eq_pointAgreement`: `selfCons(S_D) = pointAgreement(S)`;
* `symmStrat_diagonal_eq_roleAverage`: `diag(S_D) = diagonalRoleAverage(S)`;
* `symmStrat_isGood_three_mul`: a strategy passing the test with error `ε` doubles to a
  `(3ε, 3ε, 3ε)`-good symmetric strategy, the constants of the vendored
  `roleRegisterSymmStrategy_is_good_three_mul`
  (`LDT/Test/StrategyBiProjRoleAverage/Final.lean`), which this replaces.

**The pairing.** `SubMeas.prod`, `Measurement.prod` and `ProjMeas.prod` pair two families with the
same outcomes into the product algebra, componentwise; `Doubling.pairProjMeas hM P Q` translates
the pairing of `P` in `𝒜` and `Q` in `ℬ` to the doubled local algebra `Loc M` along
`Doubling.equiv` (`Co/Doubling/FinitePair.lean`). Its components are `P` and `Q` again
(`subMeasA_pairProjMeas`, `subMeasB_pairProjMeas`). Covariance holds componentwise
(`pairAxisParallel_reparamInvariant`, `pairDiagonal_reparamInvariant`).

**The halving** (`bipartiteConsError_model`): the port's symmetric-model defect of two families of
the doubled model is the average of the two two-space defects of `M` at their components, the
`max 0` of the definitions being inactive on both sides (`qBipartiteConsDefect_model` of
`Co/Doubling/Halving.lean`). So a doubled defect at most `σ` bounds each role assignment by `2σ`
(`bipartiteConsError_components_le_two_mul`), the arithmetic of Theorem E (unsymmetrization at the
vendored cut), whose input, the point consistency of the ported `mainInduction`'s measurement, is
milestone M13's. For measurements the two-space defect is the inconsistency of `M`
(`bipartiteConsError_eq_inconsistency`), the form `MIPRE.LIDT.Simul.SoundIn` concludes with.
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co

open MIPStarRE.LDT (Parameters FieldModel Point Fq zeroCoord Distribution avgOver avgOver_add
  avgOver_const_mul avgOver_congr uniformDistribution AxisParallelLine AxisLinePolynomial
  DiagonalLine DiagonalLinePolynomial AxisParallelTestSample RestrictedDiagonalSample)
open MIPRE.OperatorMatrix

/-! ### Componentwise pairing -/

section Pair

variable {α : Type*} [Fintype α]
  {R : Type*} [Ring R] [StarRing R] [PartialOrder R]
  {T : Type*} [Ring T] [StarRing T] [PartialOrder T]

/-- **The componentwise pairing** `(A ⊠ B)_a = (A_a, B_a)` of two submeasurements with the same
outcomes, a submeasurement of the product algebra. -/
def SubMeas.prod (A : SubMeas α R) (B : SubMeas α T) : SubMeas α (R × T) where
  outcome a := (A.outcome a, B.outcome a)
  total := (A.total, B.total)
  outcome_pos a := Prod.mk_le_mk.2 ⟨A.outcome_pos a, B.outcome_pos a⟩
  sum_eq_total := Prod.ext (Prod.fst_sum.trans A.sum_eq_total)
    (Prod.snd_sum.trans B.sum_eq_total)
  total_le_one := Prod.mk_le_mk.2 ⟨A.total_le_one, B.total_le_one⟩

/-- The componentwise pairing of two measurements, a measurement of the product algebra. -/
def Measurement.prod (A : Measurement α R) (B : Measurement α T) : Measurement α (R × T) where
  toSubMeas := A.toSubMeas.prod B.toSubMeas
  total_eq_one := Prod.ext A.total_eq_one B.total_eq_one

/-- The componentwise pairing of two projective measurements, a projective measurement of the
product algebra. -/
def ProjMeas.prod (A : ProjMeas α R) (B : ProjMeas α T) : ProjMeas α (R × T) where
  toMeasurement := A.toMeasurement.prod B.toMeasurement
  proj a := Prod.ext (A.proj a) (B.proj a)

/-- The outcomes of a paired projective measurement are the pairs of outcomes. -/
@[simp] theorem ProjMeas.prod_outcome (A : ProjMeas α R) (B : ProjMeas α T) (a : α) :
    (A.prod B).outcome a = (A.outcome a, B.outcome a) :=
  rfl

end Pair

/-- Postprocessing commutes with the image under a `⋆`-homomorphism. -/
theorem SubMeas.map_postprocess {α β : Type*} [Fintype α] [Fintype β]
    {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [PartialOrder R] [StarOrderedRing R]
    {T : Type*} [Ring T] [StarRing T] [Algebra ℂ T] [PartialOrder T] [StarOrderedRing T]
    (g : R →⋆ₐ[ℂ] T) (A : SubMeas α R) (f : α → β) :
    (postprocess A f).map g = postprocess (A.map g) f :=
  SubMeas.ext (fun _ => map_sum g _ _) rfl

/-! ### The two-space defect of measurements is the inconsistency -/

section Inconsistency

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]
  [PartialOrder ℬ] [StarOrderedRing ℬ] {M : BipartiteModel 𝒞 𝒜 ℬ}

/-- **The two-space consistency error of two measurement families is the inconsistency** of `M`
(`MIPRE.BipartiteModel.inconsistency`), weighted by the question distribution: the form of the
consistency conclusions of `MIPRE.LIDT.Simul.SoundIn`. -/
theorem bipartiteConsError_eq_inconsistency {Question Outcome : Type*}
    [Fintype Question] [Fintype Outcome] [DecidableEq Outcome] (𝒟 : Distribution Question)
    (A : IdxMeas Question Outcome 𝒜) (B : IdxMeas Question Outcome ℬ) :
    bipartiteConsError M 𝒟 (IdxMeas.toIdxSubMeas A) (IdxMeas.toIdxSubMeas B) =
      M.inconsistency 𝒟.weight (fun q => (A q).toPOVMIn) (fun q => (B q).toPOVMIn) := by
  rw [bipartiteConsError, avgOver_eq_sum_weight]
  refine Finset.sum_congr rfl fun q _ => congrArg (𝒟.weight q * ·) ?_
  have htot : M.bornProb (A q).total (B q).total =
      ∑ a, ∑ b, M.bornProb ((A q).outcome a) ((B q).outcome b) := by
    rw [← (A q).sum_eq_total, ← (B q).sum_eq_total, M.bornProb_sum_left]
    exact Finset.sum_congr rfl fun a _ => M.bornProb_sum_right _ _ _
  change max 0 (M.bornProb (A q).total (B q).total -
    ∑ a, M.bornProb ((A q).outcome a) ((B q).outcome a)) = _
  rw [htot, Doubling.max_sum_sub_diag fun a b => M.bornProb_nonneg ((A q).outcome_pos a)
    ((B q).outcome_pos b)]
  rfl

end Inconsistency

namespace Doubling

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]
  [PartialOrder ℬ] [StarOrderedRing ℬ] {M : BipartiteModel 𝒞 𝒜 ℬ}
  (hM : M.IsFinitePair) (hψ : ‖M.ψ‖ = 1)

/-! ### The components of a submeasurement -/

/-- **The first components of a submeasurement of the doubled local algebra**, a submeasurement
of `𝒜` (the image under `compA`). -/
noncomputable def subMeasA {Outcome : Type*} [Fintype Outcome] (X : SubMeas Outcome (Loc M)) :
    SubMeas Outcome 𝒜 :=
  X.map (compA hM)

/-- **The second components of a submeasurement of the doubled local algebra**, a submeasurement
of `ℬ` (the image under `compB`). -/
noncomputable def subMeasB {Outcome : Type*} [Fintype Outcome] (X : SubMeas Outcome (Loc M)) :
    SubMeas Outcome ℬ :=
  X.map (compB hM)

omit [PartialOrder ℬ] [StarOrderedRing ℬ] in
/-- Taking first components commutes with postprocessing. -/
theorem subMeasA_postprocess {α β : Type*} [Fintype α] [Fintype β] (X : SubMeas α (Loc M))
    (f : α → β) : subMeasA hM (postprocess X f) = postprocess (subMeasA hM X) f :=
  SubMeas.map_postprocess _ _ _

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] in
/-- Taking second components commutes with postprocessing. -/
theorem subMeasB_postprocess {α β : Type*} [Fintype α] [Fintype β] (X : SubMeas α (Loc M))
    (f : α → β) : subMeasB hM (postprocess X f) = postprocess (subMeasB hM X) f :=
  SubMeas.map_postprocess _ _ _

/-! ### The halving of the bipartite defect -/

/-- **The bipartite defect halves** (Theorem C of `reports/c6b-paper-proofs.md`, §4), in the
vocabulary of the two-space defect: the symmetric-model defect of two submeasurements of the
doubled model is the average of the two-space defects of `M` at the components `X¹, Y²` and
`Y¹, X²`. -/
theorem qBipartiteConsDefect_model_eq {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (X Y : SubMeas Outcome (Loc M)) :
    (model hM hψ).qBipartiteConsDefect X Y =
      2⁻¹ * (qBipartiteConsDefect M (subMeasA hM X) (subMeasB hM Y) +
        qBipartiteConsDefect M (subMeasA hM Y) (subMeasB hM X)) :=
  qBipartiteConsDefect_model hM hψ X Y

/-- **The averaged bipartite defect halves**: the symmetric-model consistency error of two
families of the doubled model is the average of the two-space consistency errors of `M` at their
components. -/
theorem bipartiteConsError_model {Question Outcome : Type*} [Fintype Outcome]
    [DecidableEq Outcome] (𝒟 : Distribution Question) (X Y : IdxSubMeas Question Outcome (Loc M)) :
    (model hM hψ).bipartiteConsError 𝒟 X Y =
      2⁻¹ * (bipartiteConsError M 𝒟 (fun q => subMeasA hM (X q))
          (fun q => subMeasB hM (Y q)) +
        bipartiteConsError M 𝒟 (fun q => subMeasA hM (Y q))
          (fun q => subMeasB hM (X q))) := by
  rw [SymModel.bipartiteConsError, bipartiteConsError, bipartiteConsError, ← avgOver_add,
    ← avgOver_const_mul]
  exact avgOver_congr 𝒟 _ _ fun q => qBipartiteConsDefect_model_eq hM hψ (X q) (Y q)

/-- **Each role assignment costs at most twice the doubled defect** (the arithmetic of Theorem E
of `reports/c6b-paper-proofs.md`, §4, Lemma 13): if the doubled defect of two families is at most
`σ`, each of the two two-space defects of `M` at their components is at most `2σ`. -/
theorem bipartiteConsError_components_le_two_mul {Question Outcome : Type*} [Fintype Outcome]
    [DecidableEq Outcome] (𝒟 : Distribution Question) (X Y : IdxSubMeas Question Outcome (Loc M))
    {σ : ℝ} (h : (model hM hψ).bipartiteConsError 𝒟 X Y ≤ σ) :
    bipartiteConsError M 𝒟 (fun q => subMeasA hM (X q)) (fun q => subMeasB hM (Y q)) ≤ 2 * σ ∧
      bipartiteConsError M 𝒟 (fun q => subMeasA hM (Y q)) (fun q => subMeasB hM (X q)) ≤
        2 * σ := by
  rw [bipartiteConsError_model] at h
  have h1 := bipartiteConsError_nonneg M 𝒟 (fun q => subMeasA hM (X q))
    (fun q => subMeasB hM (Y q))
  have h2 := bipartiteConsError_nonneg M 𝒟 (fun q => subMeasA hM (Y q))
    (fun q => subMeasB hM (X q))
  constructor <;> linarith

/-! ### The paired measurements -/

section PairProjMeas

variable {α : Type*} [Fintype α]

/-- **The paired projective measurement in the doubled model**: the componentwise pairing of a
projective measurement `P` of `𝒜` and `Q` of `ℬ`, translated to the doubled local algebra
`Loc M` along `Doubling.equiv`. -/
noncomputable def pairProjMeas (P : ProjMeas α 𝒜) (Q : ProjMeas α ℬ) : ProjMeas α (Loc M) :=
  (P.prod Q).map (equiv hM).toStarAlgHom

/-- The outcomes of a paired projective measurement are the translated pairs of outcomes. -/
theorem pairProjMeas_outcome (P : ProjMeas α 𝒜) (Q : ProjMeas α ℬ) (a : α) :
    (pairProjMeas hM P Q).outcome a = equiv hM (P.outcome a, Q.outcome a) :=
  rfl

/-- The first components of a paired projective measurement are the first measurement. -/
@[simp] theorem subMeasA_pairProjMeas (P : ProjMeas α 𝒜) (Q : ProjMeas α ℬ) :
    subMeasA hM (pairProjMeas hM P Q).toSubMeas = P.toSubMeas :=
  SubMeas.ext (fun a => compA_equiv hM (P.outcome a, Q.outcome a))
    (compA_equiv hM (P.total, Q.total))

/-- The second components of a paired projective measurement are the second measurement. -/
@[simp] theorem subMeasB_pairProjMeas (P : ProjMeas α 𝒜) (Q : ProjMeas α ℬ) :
    subMeasB hM (pairProjMeas hM P Q).toSubMeas = Q.toSubMeas :=
  SubMeas.ext (fun a => compB_equiv hM (P.outcome a, Q.outcome a))
    (compB_equiv hM (P.total, Q.total))

end PairProjMeas

/-! ### Covariance, componentwise -/

section Covariance

variable {params : Parameters} [FieldModel params.q]

/-- **Covariance of the paired axis-parallel measurements**: if both players' axis-parallel
families are covariant under rebasing, so is their pairing. -/
theorem pairAxisParallel_reparamInvariant
    {A : IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) 𝒜}
    {B : IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) ℬ}
    (hA : AxisParallelMeasurementReparamInvariant params A)
    (hB : AxisParallelMeasurementReparamInvariant params B) :
    AxisParallelMeasurementReparamInvariant params (fun ℓ => pairProjMeas hM (A ℓ) (B ℓ)) :=
  fun ℓ t f => by
    rw [pairProjMeas_outcome, pairProjMeas_outcome, hA ℓ t f, hB ℓ t f]

/-- **Covariance of the paired diagonal measurements**: if both players' diagonal families are
covariant under rebasing, so is their pairing. -/
theorem pairDiagonal_reparamInvariant
    {A : IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) 𝒜}
    {B : IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) ℬ}
    (hA : DiagonalMeasurementReparamInvariant params A)
    (hB : DiagonalMeasurementReparamInvariant params B) :
    DiagonalMeasurementReparamInvariant params (fun ℓ => pairProjMeas hM (A ℓ) (B ℓ)) :=
  fun ℓ t f => by
    rw [pairProjMeas_outcome, pairProjMeas_outcome, hA ℓ t f, hB ℓ t f]

end Covariance

end Doubling

/-! ### The symmetric strategy -/

namespace Doubling

variable {params : Parameters} [FieldModel params.q]
  {𝒞 : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞]
  {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  {ℬ : Type*} [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
  (strategy : ProjStrat params 𝒞 𝒜 ℬ) (hM : strategy.state.IsFinitePair)

/-- **The symmetric strategy of a two-space strategy** (Theorem D of
`reports/c6b-paper-proofs.md`, §4): on the doubled model of the strategy's state, every family is
the componentwise pairing of the first and the second player's, and the line families are
covariant componentwise. This replaces the vendored role-register symmetrization
`ProjStrat.roleRegisterSymmStrategy`. -/
noncomputable def symmStrat :
    SymStrat params (Loc strategy.state) (Ampl (Fin 2) strategy.state.H) where
  state := model hM strategy.isNormalized
  pointMeasurement u :=
    pairProjMeas hM (strategy.pointMeasurementA u) (strategy.pointMeasurementB u)
  axisParallelMeasurement :=
    { toIdxProjMeas := fun ℓ => pairProjMeas hM (strategy.axisParallelMeasurementA ℓ)
        (strategy.axisParallelMeasurementB ℓ)
      transportInvariant := (pairAxisParallel_reparamInvariant hM
        strategy.axisParallelReparamInvariantA
        strategy.axisParallelReparamInvariantB).toTransportInvariant }
  diagonalMeasurement :=
    { toIdxProjMeas := fun ℓ => pairProjMeas hM (strategy.diagonalMeasurementA ℓ)
        (strategy.diagonalMeasurementB ℓ)
      transportInvariant := (pairDiagonal_reparamInvariant hM
        strategy.diagonalReparamInvariantA
        strategy.diagonalReparamInvariantB).toTransportInvariant }

/-- The state of the symmetric strategy is the doubled model. -/
@[simp] theorem symmStrat_state :
    (symmStrat strategy hM).state = model hM strategy.isNormalized :=
  rfl

/-- The point measurements of the symmetric strategy are the paired point measurements. -/
theorem symmStrat_pointMeasurement (u : Point params) :
    (symmStrat strategy hM).pointMeasurement u =
      pairProjMeas hM (strategy.pointMeasurementA u) (strategy.pointMeasurementB u) :=
  rfl

/-- The axis-parallel measurements of the symmetric strategy are the paired axis-parallel
measurements. -/
theorem symmStrat_axisParallelMeasurement (ℓ : AxisParallelLine params) :
    (symmStrat strategy hM).axisParallelMeasurement ℓ =
      pairProjMeas hM (strategy.axisParallelMeasurementA ℓ)
        (strategy.axisParallelMeasurementB ℓ) :=
  rfl

/-- The diagonal measurements of the symmetric strategy are the paired diagonal
measurements. -/
theorem symmStrat_diagonalMeasurement (ℓ : DiagonalLine params) :
    (symmStrat strategy hM).diagonalMeasurement ℓ =
      pairProjMeas hM (strategy.diagonalMeasurementA ℓ) (strategy.diagonalMeasurementB ℓ) :=
  rfl

/-! ### The failure probabilities are the role averages -/

/-- **The axis-parallel branch** (Theorem D): the axis-parallel failure probability of the
symmetric strategy is the two-space role average `axisParallelRoleAverage`. -/
theorem symmStrat_axisParallel_eq_roleAverage :
    (symmStrat strategy hM).axisParallelFailureProbability = strategy.axisParallelRoleAverage := by
  rw [SymStrat.axisParallelFailureProbability, symmStrat_state, bipartiteConsError_model,
    ProjStrat.axisParallelRoleAverage,
    ProjStrat.axisParallelLineLeftPointRightFailureProbability,
    ProjStrat.axisParallelPointLeftLineRightFailureProbability]
  have hpA : (fun s => subMeasA hM (axisParallelPointAnswerFamily (symmStrat strategy hM) s)) =
      ProjStrat.axisParallelPointAnswerFamilyA strategy :=
    funext fun s => subMeasA_pairProjMeas hM _ _
  have hpB : (fun s => subMeasB hM (axisParallelPointAnswerFamily (symmStrat strategy hM) s)) =
      ProjStrat.axisParallelPointAnswerFamilyB strategy :=
    funext fun s => subMeasB_pairProjMeas hM _ _
  have hlA : (fun s => subMeasA hM (axisParallelLineAnswerFamily (symmStrat strategy hM) s)) =
      ProjStrat.axisParallelLineAnswerFamilyA strategy :=
    funext fun s => (subMeasA_postprocess hM _ _).trans
      (congrArg (postprocess · _) (subMeasA_pairProjMeas hM _ _))
  have hlB : (fun s => subMeasB hM (axisParallelLineAnswerFamily (symmStrat strategy hM) s)) =
      ProjStrat.axisParallelLineAnswerFamilyB strategy :=
    funext fun s => (subMeasB_postprocess hM _ _).trans
      (congrArg (postprocess · _) (subMeasB_pairProjMeas hM _ _))
  rw [hpA, hpB, hlA, hlB]
  ring

/-- For a measurement (total `1`), the bipartite strong self-consistency defect of a symmetric
model is its bipartite consistency defect with itself. -/
theorem _root_.MIPRE.LIDT.Co.SymModel.qBipartiteSSCDefect_eq_qBipartiteConsDefect
    {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (S : SymModel 𝔓 K) {Outcome : Type*} [Fintype Outcome] (X : SubMeas Outcome 𝔓)
    (hX : X.total = 1) :
    S.qBipartiteSSCDefect X = S.qBipartiteConsDefect X X := by
  simp only [SymModel.qBipartiteSSCDefect, SymModel.qBipartiteConsDefect,
    SymModel.qBipartiteMatchMass, SymModel.opTensor, hX, map_one, one_mul]

/-- **The self-consistency branch** (Theorem D): the self-consistency failure probability of the
symmetric strategy is the two-space point agreement `pointAgreementFailureProbability`. -/
theorem symmStrat_selfConsistency_eq_pointAgreement :
    (symmStrat strategy hM).selfConsistencyFailureProbability =
      strategy.pointAgreementFailureProbability := by
  have h : (symmStrat strategy hM).state.bipartiteSSCError (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas (symmStrat strategy hM).pointMeasurement) =
      (symmStrat strategy hM).state.bipartiteConsError (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas (symmStrat strategy hM).pointMeasurement)
        (IdxProjMeas.toIdxSubMeas (symmStrat strategy hM).pointMeasurement) :=
    avgOver_congr _ _ _ fun u => SymModel.qBipartiteSSCDefect_eq_qBipartiteConsDefect _ _
      ((symmStrat strategy hM).pointMeasurement u).total_eq_one
  rw [SymStrat.selfConsistencyFailureProbability, h, symmStrat_state, bipartiteConsError_model,
    ProjStrat.pointAgreementFailureProbability]
  have hA :
      (fun u => subMeasA hM (IdxProjMeas.toIdxSubMeas (symmStrat strategy hM).pointMeasurement u)) =
        IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA :=
    funext fun u => subMeasA_pairProjMeas hM _ _
  have hB :
      (fun u => subMeasB hM (IdxProjMeas.toIdxSubMeas (symmStrat strategy hM).pointMeasurement u)) =
        IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB :=
    funext fun u => subMeasB_pairProjMeas hM _ _
  rw [hA, hB]
  ring

/-- **The diagonal branch** (Theorem D): the diagonal failure probability of the symmetric
strategy is the two-space role average `diagonalRoleAverage`. -/
theorem symmStrat_diagonal_eq_roleAverage :
    (symmStrat strategy hM).diagonalFailureProbability = strategy.diagonalRoleAverage := by
  have hj : ∀ j : Fin params.m,
      (symmStrat strategy hM).state.bipartiteConsError
          (uniformDistribution (RestrictedDiagonalSample params j))
          (diagonalPointAnswerFamily (symmStrat strategy hM) j)
          (diagonalLineAnswerFamily (symmStrat strategy hM) j) =
        2⁻¹ * (bipartiteConsError strategy.state
            (uniformDistribution (RestrictedDiagonalSample params j))
            (ProjStrat.diagonalPointAnswerFamilyA strategy j)
            (ProjStrat.diagonalLineAnswerFamilyB strategy j) +
          bipartiteConsError strategy.state
            (uniformDistribution (RestrictedDiagonalSample params j))
            (ProjStrat.diagonalLineAnswerFamilyA strategy j)
            (ProjStrat.diagonalPointAnswerFamilyB strategy j)) := fun j => by
    rw [symmStrat_state, bipartiteConsError_model]
    have hpA : (fun s => subMeasA hM (diagonalPointAnswerFamily (symmStrat strategy hM) j s)) =
        ProjStrat.diagonalPointAnswerFamilyA strategy j :=
      funext fun s => subMeasA_pairProjMeas hM _ _
    have hpB : (fun s => subMeasB hM (diagonalPointAnswerFamily (symmStrat strategy hM) j s)) =
        ProjStrat.diagonalPointAnswerFamilyB strategy j :=
      funext fun s => subMeasB_pairProjMeas hM _ _
    have hlA : (fun s => subMeasA hM (diagonalLineAnswerFamily (symmStrat strategy hM) j s)) =
        ProjStrat.diagonalLineAnswerFamilyA strategy j :=
      funext fun s => (subMeasA_postprocess hM _ _).trans
        (congrArg (postprocess · _) (subMeasA_pairProjMeas hM _ _))
    have hlB : (fun s => subMeasB hM (diagonalLineAnswerFamily (symmStrat strategy hM) j s)) =
        ProjStrat.diagonalLineAnswerFamilyB strategy j :=
      funext fun s => (subMeasB_postprocess hM _ _).trans
        (congrArg (postprocess · _) (subMeasB_pairProjMeas hM _ _))
    rw [hpA, hpB, hlA, hlB]
  rw [SymStrat.diagonalFailureProbability, Finset.sum_congr rfl fun j _ => hj j,
    ProjStrat.diagonalRoleAverage, ProjStrat.diagonalLineLeftPointRightFailureProbability,
    ProjStrat.diagonalPointLeftLineRightFailureProbability, ← Finset.mul_sum,
    Finset.sum_add_distrib]
  ring

/-- **Symmetrization after the bridge** (Theorem D of `reports/c6b-paper-proofs.md`, §4): a
two-space strategy on a finite pair passing the low-individual-degree test with error `ε` doubles
to a `(3ε, 3ε, 3ε)`-good symmetric strategy, the constants of the vendored
`roleRegisterSymmStrategy_is_good_three_mul`. -/
theorem symmStrat_isGood_three_mul {eps : ℝ} (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    (symmStrat strategy hM).IsGood (3 * eps) (3 * eps) (3 * eps) := by
  have hmain : (strategy.axisParallelRoleAverage + strategy.pointAgreementFailureProbability +
      strategy.diagonalRoleAverage) / 3 ≤ eps := by
    simpa only [ProjStrat.lowIndividualDegreeFailureProbability_eq_role_averages] using
      hpass.soundnessHypothesis
  obtain ⟨haxis, hpoint, hdiag⟩ := three_summand_bounds_of_average_le
    strategy.axisParallelRoleAverage_nonneg strategy.pointAgreementFailureProbability_nonneg
    strategy.diagonalRoleAverage_nonneg hmain
  exact ⟨(symmStrat_axisParallel_eq_roleAverage strategy hM).trans_le haxis,
    (symmStrat_selfConsistency_eq_pointAgreement strategy hM).trans_le hpoint,
    (symmStrat_diagonal_eq_roleAverage strategy hM).trans_le hdiag⟩

end Doubling

end MIPRE.LIDT.Co

end
