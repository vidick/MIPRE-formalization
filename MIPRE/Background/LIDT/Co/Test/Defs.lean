/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Test/Defs.lean,
to the symmetric model of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Basic.OpFamily
public import MIPRE.Background.LIDT.Co.Basic.DistributionAvg
public import MIPStarRE.LDT.Basic.ParametersFiniteAnswers
public import MIPRE.Foundations.ModelStrategy

@[expose] public section

/-!
# Section 3 — Definitions

Core definitions for the low individual degree test: evaluation families,
matching mass, consistency defect, and test-passing predicates. This is the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Test/Defs.lean` in the port of `planning/c6b-plan.md`
(milestone M0, section "Port conventions").

The evaluation families (`evaluateAt`, `polynomialEvaluationFamily`, ...) are generic over the
ordered `⋆`-ring `R` of `Co/Basic/SubMeasurementCore.lean`. The ev-level defects and relations
are used with dot notation on the state: the vendored `qSDD ψ A B` is `S.qSDD A B`,
`SDDRel ψ 𝒟 A B δ` is `S.SDDRel 𝒟 A B δ`.

* A **same-space** quantity (`qMatchMass`, `qConsDefect`, `qSDDCore`, `qSDD`, `qSDDOp`,
  `qSSCDefect`, `consError`, `sddError`, `sddErrorOp`, `sscError`, `subMeasMass`,
  `idxSubMeasMass`, `bndError`, `SDDRel`, `SDDOpRel`, `SSCRel`, `CompletenessAtLeast`,
  `BoundedByOperator`) uses only the state, so it is a `VecState` declaration
  (`Co/Basic/QuantumState.lean`), about joint operators in `K →L[ℂ] K`. It applies to any vector
  state, with no swap symmetry: the vendored uses with a state on one space, a reduced state or a
  state tensored with an ancilla (`MakingMeasurementsProjective`) port without building a
  symmetric model; and `S.qSDD A B` for `S : SymModel 𝔓 K` is `S.toVecState.qSDD A B`.
* A **bipartite** quantity (`qBipartiteMatchMass`, `qBipartiteConsDefect`, `bipartiteConsError`,
  `ConsRel`, `qBipartiteSSCDefect`, `bipartiteSSCError`, `BipartiteSSCRel`) places local
  families in `𝔓` on the two factors through `S.opTensor`, so it is a `SymModel` declaration.
  The two-space `ProjStrat` of `Co/Test/StrategyCore.lean` has no counterpart of these: see
  there.

As everywhere in the port, the normalization hypothesis `hψ : ψ.IsNormalized` of the vendored
bounds is dropped: `V.ev 1 = 1` is a theorem of every vector state.

## New here

Three bridges to the repository calculus, through `V.toStateModel` and `S.toBipartite`
(`Co/Basic/QuantumState.lean`):

* `VecState.qSDDCore_eq_sum_snorm_sq`: `qSDDCore` is `∑ₐ ‖(Aₐ - Bₐ) Ψ‖²`;
* `SymModel.bipartiteConsError_eq_inconsistency`: for measurements, the bipartite consistency
  error is `MIPRE.BipartiteModel.inconsistency` (`MIPRE/Foundations/ModelStrategy.lean`) of the
  model, weighted by the distribution; its per-question form, for sub-measurements, is
  `SymModel.qBipartiteConsDefect_eq_sum_ne`, the off-diagonal Born mass;
* `SymModel.sddError_liftLeft_liftRight_eq_xPovmDist`: for measurements, the squared distance of
  the left and right lifts is `MIPRE.BipartiteModel.xPovmDist`
  (`MIPRE/Foundations/CrossConsistency.lean`).

## Not ported

Every declaration of the vendored file has a counterpart here.
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co

open MIPStarRE.LDT (Parameters FieldModel Point Fq appendPoint truncatePoint pointHeight
  Distribution avgOver avgOver_zero avgOver_mono avgOver_nonneg avgOver_const_of_isProbability
  uniformDistribution uniformDistribution_isProbability)

section Evaluation

variable {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]

/-- Evaluate a polynomial-valued submeasurement at a point. -/
noncomputable def evaluateAt
    (params : Parameters) [FieldModel params.q] (u : Point params)
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) R) : SubMeas (Fq params) R :=
  postprocess G (fun g => g u)

/-- Evaluation after adjoining an unused coordinate agrees with evaluation before
adjoining that coordinate. -/
@[simp] theorem evaluateAt_postprocess_appendAtHeight_appendPoint
    (params : Parameters) [FieldModel params.q]
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) R)
    (x : Fq params) (u : Point params) (y : Fq params) :
    evaluateAt params.next (appendPoint params u y)
        (postprocess G (fun g => MIPStarRE.LDT.Polynomial.appendAtHeight params g x)) =
      evaluateAt params u G := by
  unfold evaluateAt
  rw [SubMeas.postprocess_comp]
  congr
  funext g
  exact MIPStarRE.LDT.Polynomial.appendAtHeight_apply_appendPoint params g x u y

/-- View a global polynomial submeasurement as a point-indexed answer family. -/
noncomputable def polynomialEvaluationFamily
    (params : Parameters) [FieldModel params.q]
    (G : SubMeas (MIPStarRE.LDT.Polynomial params) R) :
    IdxSubMeas (Point params) (Fq params) R :=
  fun u => evaluateAt params u G

/-- View a global polynomial measurement as a point-indexed answer measurement family.

The submeasurement-valued `polynomialEvaluationFamily` is the form used by most
consistency statements.  The heterogeneous triangle step in the final theorem
uses complete measurements, so this version keeps the same postprocessing while
retaining the total-mass proof. -/
noncomputable def polynomialEvaluationMeasurementFamily
    (params : Parameters) [FieldModel params.q]
    (G : Measurement (MIPStarRE.LDT.Polynomial params) R) :
    IdxMeas (Point params) (Fq params) R :=
  fun u =>
    { toSubMeas := evaluateAt params u G.toSubMeas
      total_eq_one := G.total_eq_one }

namespace Test

/-- Namespace-compatible form of `polynomialEvaluationMeasurementFamily`.

This name is used by the two-space final-theorem route, where the surrounding
theorems live in the `Test` namespace. -/
noncomputable abbrev polynomialEvaluationMeasurementFamily
    (params : Parameters) [FieldModel params.q]
    (G : Measurement (MIPStarRE.LDT.Polynomial params) R) :
    IdxMeas (Point params) (Fq params) R :=
  MIPRE.LIDT.Co.polynomialEvaluationMeasurementFamily params G

end Test

/-- Evaluate an indexed slice family at a point `(u, x)` in `F_q^{m+1}`. -/
noncomputable def evaluateFiberFamilyAtNextPoint
    (params : Parameters) [FieldModel params.q]
    (G : IdxSubMeas (Fq params) (MIPStarRE.LDT.Polynomial params) R) :
    IdxSubMeas (Point params.next) (Fq params) R :=
  fun u => evaluateAt params (truncatePoint params u) (G (pointHeight params u))

/-! ### Postprocessing preserves totals -/

/-- Postprocessing preserves the total operator. -/
theorem postprocess_total {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α R) (f : α → β) :
    (postprocess A f).total = A.total :=
  rfl

end Evaluation

/-- An average against a distribution, written over the whole question type. -/
theorem avgOver_eq_sum_weight {Question : Type*} [Fintype Question]
    (𝒟 : Distribution Question) (f : Question → ℝ) :
    avgOver 𝒟 f = ∑ q, 𝒟.weight q * f q :=
  (MIPStarRE.LDT.Distribution.sum_univ_eq_sum_support 𝒟 _ fun q hq => by
    rw [𝒟.outsideSupport q hq, zero_mul]).symm

namespace VecState

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (V : VecState K)

/-! ### Questionwise defects -/

/-- Questionwise matching mass `∑_a ⟨Ψ, A_a B_a Ψ⟩`, summed over outcomes. -/
noncomputable def qMatchMass {Outcome : Type*} [Fintype Outcome]
    (A B : SubMeas Outcome (K →L[ℂ] K)) : ℝ :=
  ∑ a, V.ev (A.outcome a * B.outcome a)

/-- Questionwise off-diagonal mass surrogate for consistency. -/
noncomputable def qConsDefect {Outcome : Type*} [Fintype Outcome]
    (A B : SubMeas Outcome (K →L[ℂ] K)) : ℝ :=
  let totalOverlap := V.ev (A.total * B.total)
  max 0 (totalOverlap - V.qMatchMass A B)

/-- Questionwise squared-distance defect. -/
noncomputable def qSDDCore {Outcome : Type*} [Fintype Outcome]
    (A B : Outcome → K →L[ℂ] K) : ℝ :=
  ∑ a, V.ev (star (A a - B a) * (A a - B a))

/-- Questionwise squared-distance defect. -/
noncomputable def qSDD {Outcome : Type*} [Fintype Outcome]
    (A B : SubMeas Outcome (K →L[ℂ] K)) : ℝ :=
  V.qSDDCore A.outcome B.outcome

/-- State-dependent distance for raw operator families.
Matches the paper's `≈_δ` for arbitrary operator families.
This keeps the raw-family API separate while sharing the same core formula as
`qSDD`. -/
noncomputable def qSDDOp {Outcome : Type*} [Fintype Outcome]
    (A B : OpFamily Outcome (K →L[ℂ] K)) : ℝ :=
  V.qSDDCore A.outcome B.outcome

/-- Questionwise strong self-consistency defect. -/
noncomputable def qSSCDefect {Outcome : Type*} [Fintype Outcome]
    (A : SubMeas Outcome (K →L[ℂ] K)) : ℝ :=
  let totalMass := V.ev A.total
  let diagonalMass := ∑ a, V.ev (A.outcome a * A.outcome a)
  max 0 (totalMass - diagonalMass)

/-! ### Averaged defects -/

/-- Averaged off-diagonal mass for consistency statements. -/
noncomputable def consError {Question Outcome : Type*} [Fintype Outcome]
    (𝒟 : Distribution Question) (A B : IdxSubMeas Question Outcome (K →L[ℂ] K)) : ℝ :=
  avgOver 𝒟 (fun q => V.qConsDefect (A q) (B q))

/-- Averaged squared distance for `≈_δ`. -/
noncomputable def sddError {Question Outcome : Type*} [Fintype Outcome]
    (𝒟 : Distribution Question) (A B : IdxSubMeas Question Outcome (K →L[ℂ] K)) : ℝ :=
  avgOver 𝒟 (fun q => V.qSDD (A q) (B q))

/-- Averaged squared distance for raw operator families. -/
noncomputable def sddErrorOp {Question Outcome : Type*} [Fintype Outcome]
    (𝒟 : Distribution Question) (A B : IdxOpFamily Question Outcome (K →L[ℂ] K)) : ℝ :=
  avgOver 𝒟 (fun q => V.qSDDOp (A q) (B q))

/-- Averaged defect in strong self-consistency. -/
noncomputable def sscError {Question Outcome : Type*} [Fintype Outcome]
    (𝒟 : Distribution Question) (A : IdxSubMeas Question Outcome (K →L[ℂ] K)) : ℝ :=
  avgOver 𝒟 (fun q => V.qSSCDefect (A q))

/-- Total mass of a submeasurement on the state, computed from the concrete total operator. -/
noncomputable def subMeasMass {Outcome : Type*} [Fintype Outcome]
    (A : SubMeas Outcome (K →L[ℂ] K)) : ℝ :=
  V.ev A.total

/-- Averaged total mass of an indexed submeasurement. -/
noncomputable def idxSubMeasMass {Question Outcome : Type*} [Fintype Outcome]
    (𝒟 : Distribution Question) (A : IdxSubMeas Question Outcome (K →L[ℂ] K)) : ℝ :=
  avgOver 𝒟 (fun q => V.subMeasMass (A q))

/-- Defect in domination by an operator witness, measured at the expectation-value level. -/
noncomputable def bndError {Outcome : Type*} [Fintype Outcome]
    (A : SubMeas Outcome (K →L[ℂ] K)) (Z : K →L[ℂ] K) : ℝ :=
  max 0 (V.subMeasMass A - V.ev Z)

/-! ### Relations -/

/-- State-dependent distance relation. -/
structure SDDRel {Question Outcome : Type*} [Fintype Outcome]
    (𝒟 : Distribution Question) (A B : IdxSubMeas Question Outcome (K →L[ℂ] K)) (δ : ℝ) :
    Prop where
  squaredDistanceBound : V.sddError 𝒟 A B ≤ δ

/-- State-dependent distance relation for raw operator families. -/
structure SDDOpRel {Question Outcome : Type*} [Fintype Outcome]
    (𝒟 : Distribution Question) (A B : IdxOpFamily Question Outcome (K →L[ℂ] K)) (δ : ℝ) :
    Prop where
  squaredDistanceBound : V.sddErrorOp 𝒟 A B ≤ δ

/-- Strong self-consistency relation. -/
structure SSCRel {Question Outcome : Type*} [Fintype Outcome]
    (𝒟 : Distribution Question) (A : IdxSubMeas Question Outcome (K →L[ℂ] K)) (δ : ℝ) :
    Prop where
  diagonalOverlapBound : V.sscError 𝒟 A ≤ δ

/-- Completeness statement for a submeasurement. -/
structure CompletenessAtLeast {Outcome : Type*} [Fintype Outcome]
    (A : SubMeas Outcome (K →L[ℂ] K)) (r : ℝ) : Prop where
  lowerBound : V.subMeasMass A ≥ r

/-- Boundedness statement witnessed by an operator. -/
structure BoundedByOperator {Outcome : Type*} [Fintype Outcome]
    (A : SubMeas Outcome (K →L[ℂ] K)) (Z : K →L[ℂ] K) (δ : ℝ) : Prop where
  witnessOpPSD : 0 ≤ Z
  upperBound : V.bndError A Z ≤ δ

/-! ### Nonnegativity lemmas for defect measures -/

/-- The squared-distance defect is nonneg since each summand is `⟨Ψ, M†M Ψ⟩ ≥ 0`. -/
theorem qSDD_nonneg {Outcome : Type*} [Fintype Outcome]
    (A B : SubMeas Outcome (K →L[ℂ] K)) :
    0 ≤ V.qSDD A B :=
  Finset.sum_nonneg fun _ _ => V.ev_adjoint_self_nonneg _

/-- The averaged squared-distance error is nonneg. -/
theorem sddError_nonneg {Question Outcome : Type*} [Fintype Outcome]
    (𝒟 : Distribution Question) (A B : IdxSubMeas Question Outcome (K →L[ℂ] K)) :
    0 ≤ V.sddError 𝒟 A B :=
  avgOver_nonneg 𝒟 _ fun _ => V.qSDD_nonneg _ _

/-! ### Self-distance -/

/-- The self-distance `qSDD A A` is zero. -/
theorem qSDD_self {Outcome : Type*} [Fintype Outcome] (A : SubMeas Outcome (K →L[ℂ] K)) :
    V.qSDD A A = 0 :=
  Finset.sum_eq_zero fun _ _ => by rw [sub_self, mul_zero, V.ev_zero]

/-- The averaged self-distance `sddError 𝒟 A A` is zero. -/
theorem sddError_self {Question Outcome : Type*} [Fintype Outcome]
    (𝒟 : Distribution Question) (A : IdxSubMeas Question Outcome (K →L[ℂ] K)) :
    V.sddError 𝒟 A A = 0 := by
  unfold sddError
  have : (fun q => V.qSDD (A q) (A q)) = fun _ => 0 :=
    funext fun q => V.qSDD_self (A q)
  rw [this]; exact avgOver_zero 𝒟

/- The naive monotonicity statement
`V.qConsDefect (postprocess A f) (postprocess B f) ≤ V.qConsDefect A B`
is false for arbitrary submeasurements: without opposite-side / commuting
hypotheses, the extra cross terms created by postprocessing need not be
nonnegative. The paper's data-processing proposition is therefore recorded in
the bipartite form `Preliminaries.simeqDataProcessing`, not as a generic fact
about `qConsDefect`. -/

/-! ### Bridges to the repository calculus -/

/-- **The squared-distance defect is a sum of squared state norms**:
`qSDDCore A B = ∑ₐ ‖(Aₐ - Bₐ) Ψ‖²`, each term being `V.toStateModel.snorm (Aₐ - Bₐ) ^ 2`
(`toStateModel_snorm`). -/
theorem qSDDCore_eq_sum_snorm_sq {Outcome : Type*} [Fintype Outcome]
    (A B : Outcome → K →L[ℂ] K) :
    V.qSDDCore A B = ∑ a, ‖(A a - B a) V.Ψ‖ ^ 2 :=
  Finset.sum_congr rfl fun a _ => V.ev_adjoint_self_eq_norm_sq (A a - B a)

end VecState

namespace SymModel

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (S : SymModel 𝔓 K)

/-! ### Bipartite defects -/

/-- Bipartite matching mass `∑_a ⟨Ψ, (A_a ⊗ B_a) Ψ⟩`, with `A` on the first factor and `B` on
the second (`S.opTensor`). -/
noncomputable def qBipartiteMatchMass {Outcome : Type*} [Fintype Outcome]
    (A B : SubMeas Outcome 𝔓) : ℝ :=
  ∑ a, S.ev (S.opTensor (A.outcome a) (B.outcome a))

/-- Bipartite questionwise consistency defect.

In the paper (Definition 4.8), the consistency of `A` on `H_A` and `B` on
`H_B` for a shared state `|ψ⟩ ∈ H_A ⊗ H_B` is:
  `E_x ∑_{a≠b} ⟨ψ| A^x_a ⊗ B^x_b |ψ⟩ ≤ δ`
which equals
  `max 0 (⟨ψ| A_total ⊗ B_total |ψ⟩ − ∑_a ⟨ψ| A_a ⊗ B_a |ψ⟩)`
(`qBipartiteConsDefect_eq_sum_ne`). -/
noncomputable def qBipartiteConsDefect {Outcome : Type*} [Fintype Outcome]
    (A B : SubMeas Outcome 𝔓) : ℝ :=
  let totalOverlap := S.ev (S.opTensor A.total B.total)
  max 0 (totalOverlap - S.qBipartiteMatchMass A B)

/-- Averaged bipartite off-diagonal mass for consistency statements. -/
noncomputable def bipartiteConsError {Question Outcome : Type*} [Fintype Outcome]
    (𝒟 : Distribution Question) (A B : IdxSubMeas Question Outcome 𝔓) : ℝ :=
  avgOver 𝒟 (fun q => S.qBipartiteConsDefect (A q) (B q))

/-- **Bridge lemma**: the bipartite consistency defect equals the same-space
`qConsDefect` applied to the left/right-placed submeasurements. -/
theorem qBipartiteConsDefect_eq_qConsDefect_placed {Outcome : Type*} [Fintype Outcome]
    (A B : SubMeas Outcome 𝔓) :
    S.qBipartiteConsDefect A B =
      S.qConsDefect (S.leftPlacedSubMeas A) (S.rightPlacedSubMeas B) :=
  rfl

/-- **Bridge lemma**: averaged bipartite consistency equals the same-space
`consError` applied to the left/right-placed families. -/
theorem bipartiteConsError_eq_consError_placed {Question Outcome : Type*} [Fintype Outcome]
    (𝒟 : Distribution Question) (A B : IdxSubMeas Question Outcome 𝔓) :
    S.bipartiteConsError 𝒟 A B =
      S.consError 𝒟
        (fun q => S.leftPlacedSubMeas (A q))
        (fun q => S.rightPlacedSubMeas (B q)) :=
  rfl

/-! ### Relations -/

/-- Consistency relation (bipartite, paper Definition 4.8).

Alice's submeasurement `A` acts on the first factor and Bob's submeasurement `B` on the
second. The relation encodes
  `E_{x ∼ D} ∑_{a≠b} ⟨ψ| A^x_a ⊗ B^x_b |ψ⟩ ≤ δ`. -/
structure ConsRel {Question Outcome : Type*} [Fintype Outcome]
    (𝒟 : Distribution Question) (A B : IdxSubMeas Question Outcome 𝔓) (δ : ℝ) : Prop where
  offDiagonalBound : S.bipartiteConsError 𝒟 A B ≤ δ

/-- Bipartite questionwise strong self-consistency defect.
This is the paper's SSC condition (Definition 4.3/4.4):
  `max 0 (∑ₐ ev (Aₐ ⊗ I) − ∑ₐ ev (Aₐ ⊗ Aₐ))`.
It measures the gap between the total mass on one register and the
diagonal cross-register overlap. -/
noncomputable def qBipartiteSSCDefect {Outcome : Type*} [Fintype Outcome]
    (A : SubMeas Outcome 𝔓) : ℝ :=
  let totalMass := S.ev (S.L A.total)
  let overlapMass := ∑ a, S.ev (S.opTensor (A.outcome a) (A.outcome a))
  max 0 (totalMass - overlapMass)

/-- Averaged bipartite SSC defect. -/
noncomputable def bipartiteSSCError {Question Outcome : Type*} [Fintype Outcome]
    (𝒟 : Distribution Question) (A : IdxSubMeas Question Outcome 𝔓) : ℝ :=
  avgOver 𝒟 (fun q => S.qBipartiteSSCDefect (A q))

/-- Bipartite strong self-consistency relation (paper's definition).
Uses the cross-register overlap `∑ₐ ev (Aₐ ⊗ Aₐ)` rather than
the local square `∑ₐ ev (Aₐ² ⊗ I)`. -/
structure BipartiteSSCRel {Question Outcome : Type*} [Fintype Outcome]
    (𝒟 : Distribution Question) (A : IdxSubMeas Question Outcome 𝔓) (δ : ℝ) : Prop where
  overlapBound : S.bipartiteSSCError 𝒟 A ≤ δ

/-! ### Nonnegativity lemmas for defect measures -/

/-- The bipartite consistency defect is nonneg by definition (`max 0 _`). -/
theorem qBipartiteConsDefect_nonneg {Outcome : Type*} [Fintype Outcome]
    (A B : SubMeas Outcome 𝔓) :
    0 ≤ S.qBipartiteConsDefect A B :=
  le_max_left 0 _

/-- The averaged bipartite consistency error is nonneg. -/
theorem bipartiteConsError_nonneg {Question Outcome : Type*} [Fintype Outcome]
    (𝒟 : Distribution Question) (A B : IdxSubMeas Question Outcome 𝔓) :
    0 ≤ S.bipartiteConsError 𝒟 A B :=
  avgOver_nonneg 𝒟 _ fun _ => S.qBipartiteConsDefect_nonneg _ _

/-- The bipartite matching mass is nonnegative because each summand is the
expectation of a positive tensor product. -/
theorem qBipartiteMatchMass_nonneg {Outcome : Type*} [Fintype Outcome]
    (A B : SubMeas Outcome 𝔓) :
    0 ≤ S.qBipartiteMatchMass A B :=
  Finset.sum_nonneg fun a _ =>
    S.ev_nonneg_of_psd _ (S.opTensor_nonneg (A.outcome_pos a) (B.outcome_pos a))

/-- A bipartite consistency defect is at most `1` (the state is normalized). -/
theorem qBipartiteConsDefect_le_one_of_isNormalized {Outcome : Type*} [Fintype Outcome]
    (A B : SubMeas Outcome 𝔓) :
    S.qBipartiteConsDefect A B ≤ 1 := by
  have hmatch_nonneg : 0 ≤ S.qBipartiteMatchMass A B := S.qBipartiteMatchMass_nonneg A B
  have htotal_le_one : S.ev (S.opTensor A.total B.total) ≤ 1 :=
    (S.ev_mono _ _ (S.opTensor_le_one A.total_nonneg A.total_le_one B.total_le_one)).trans_eq
      S.ev_one_of_isNormalized
  exact max_le zero_le_one (by linarith)

/-- Under a probability question distribution, the averaged bipartite consistency
error is bounded by `1`. -/
theorem bipartiteConsError_le_one_of_isProbability {Question Outcome : Type*} [Fintype Outcome]
    (𝒟 : Distribution Question) (h𝒟 : 𝒟.IsProbability)
    (A B : IdxSubMeas Question Outcome 𝔓) :
    S.bipartiteConsError 𝒟 A B ≤ 1 :=
  (avgOver_mono 𝒟 _ (fun _ => 1) fun q =>
    S.qBipartiteConsDefect_le_one_of_isNormalized (A q) (B q)).trans_eq
    (avgOver_const_of_isProbability 𝒟 h𝒟 1)

/-- Under the uniform question distribution, the averaged bipartite consistency
error is bounded by `1`. -/
theorem bipartiteConsError_uniform_le_one {Question Outcome : Type*}
    [Fintype Question] [DecidableEq Question] [Nonempty Question] [Fintype Outcome]
    (A B : IdxSubMeas Question Outcome 𝔓) :
    S.bipartiteConsError (uniformDistribution Question) A B ≤ 1 :=
  S.bipartiteConsError_le_one_of_isProbability _
    (uniformDistribution_isProbability Question) A B

/-- The bipartite strong self-consistency defect is nonneg by definition (`max 0 _`). -/
theorem qBipartiteSSCDefect_nonneg {Outcome : Type*} [Fintype Outcome]
    (A : SubMeas Outcome 𝔓) :
    0 ≤ S.qBipartiteSSCDefect A :=
  le_max_left 0 _

/-- The averaged bipartite strong self-consistency error is nonneg. -/
theorem bipartiteSSCError_nonneg {Question Outcome : Type*} [Fintype Outcome]
    (𝒟 : Distribution Question) (A : IdxSubMeas Question Outcome 𝔓) :
    0 ≤ S.bipartiteSSCError 𝒟 A :=
  avgOver_nonneg 𝒟 _ fun _ => S.qBipartiteSSCDefect_nonneg _

/-! ### Bridges to the repository calculus -/

/-- **The bipartite consistency defect is the off-diagonal Born mass**
`∑_{a ≠ b} ⟨Ψ, (A_a ⊗ B_b) Ψ⟩`, for any two sub-measurements: the `max 0` of the definition
is inactive, since the total overlap is the sum of all the Born weights. -/
theorem qBipartiteConsDefect_eq_sum_ne {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (A B : SubMeas Outcome 𝔓) :
    S.qBipartiteConsDefect A B =
      ∑ a, ∑ b, if a = b then 0 else S.toBipartite.bornProb (A.outcome a) (B.outcome b) := by
  set f : Outcome → Outcome → ℝ := fun a b => S.ev (S.L (A.outcome a) * S.R (B.outcome b))
  have hbp : ∀ a b, S.toBipartite.bornProb (A.outcome a) (B.outcome b) = f a b := fun _ _ => rfl
  have hf0 : ∀ a b, 0 ≤ f a b := fun a b =>
    S.ev_nonneg_of_psd _ (S.opTensor_nonneg (A.outcome_pos a) (B.outcome_pos b))
  have htot : S.ev (S.opTensor A.total B.total) = ∑ a, ∑ b, f a b := by
    rw [← A.sum_eq_total, ← B.sum_eq_total, SymModel.opTensor, map_sum, map_sum, Finset.sum_mul_sum,
      S.ev_sum]
    exact Finset.sum_congr rfl fun a _ => S.ev_sum _
  have hrow : ∀ a, ∑ b, f a b = f a a + ∑ b, if a = b then 0 else f a b := fun a => by
    rw [← Fintype.sum_ite_eq a (f a), ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => by split_ifs <;> simp
  have hoff : 0 ≤ ∑ a, ∑ b, if a = b then (0 : ℝ) else f a b :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by split_ifs; exacts [le_rfl, hf0 a b]
  simp only [hbp]
  show max 0 (S.ev (S.opTensor A.total B.total) - ∑ a, f a a) = _
  rw [htot, Finset.sum_congr rfl fun a _ => hrow a, Finset.sum_add_distrib, add_sub_cancel_left,
    max_eq_right hoff]

/-- **The bipartite consistency error of two measurement families is the inconsistency** of the
model (`MIPRE.BipartiteModel.inconsistency`), weighted by the question distribution. -/
theorem bipartiteConsError_eq_inconsistency {Question Outcome : Type*} [Fintype Question]
    [Fintype Outcome] [DecidableEq Outcome]
    (𝒟 : Distribution Question) (A B : IdxMeas Question Outcome 𝔓) :
    S.bipartiteConsError 𝒟 (IdxMeas.toIdxSubMeas A) (IdxMeas.toIdxSubMeas B) =
      S.toBipartite.inconsistency 𝒟.weight (fun q => (A q).toPOVMIn)
        (fun q => (B q).toPOVMIn) := by
  rw [bipartiteConsError, avgOver_eq_sum_weight]
  exact Finset.sum_congr rfl fun q _ =>
    congrArg (𝒟.weight q * ·) (S.qBipartiteConsDefect_eq_sum_ne (A q).toSubMeas (B q).toSubMeas)

/-- **The squared distance of the left and right lifts of two measurement families is the
cross-party distance** of the model (`MIPRE.BipartiteModel.xPovmDist`), weighted by the question
distribution: the vendored `A ⊗ I ≈_δ I ⊗ B` is the appendix's `A ⊗ Id ≃_δ Id ⊗ B`. -/
theorem sddError_liftLeft_liftRight_eq_xPovmDist {Question Outcome : Type*} [Fintype Question]
    [Fintype Outcome] (𝒟 : Distribution Question) (A B : IdxMeas Question Outcome 𝔓) :
    S.sddError 𝒟 (IdxSubMeas.liftLeft S (IdxMeas.toIdxSubMeas A))
        (IdxSubMeas.liftRight S (IdxMeas.toIdxSubMeas B)) =
      S.toBipartite.xPovmDist 𝒟.weight (fun q => (A q).toPOVMIn) (fun q => (B q).toPOVMIn) := by
  rw [VecState.sddError, avgOver_eq_sum_weight]
  exact Finset.sum_congr rfl fun q _ => congrArg (𝒟.weight q * ·)
    (S.qSDDCore_eq_sum_snorm_sq (fun a => S.L ((A q).outcome a))
      (fun a => S.R ((B q).outcome a)))

end SymModel

end MIPRE.LIDT.Co

end
