/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122),
MIPStarRE/LDT/Preliminaries/ComparisonCore.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Preliminaries.Defs
public import MIPRE.Background.LIDT.Co.Basic.MeasurementLift

@[expose] public section

/-!
# Preliminary comparison theorems: core layer

Core comparison lemmas and measurement-agreement translations for the
preliminaries chapter: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/ComparisonCore.lean` in the port of
`planning/c6b-plan.md` (milestone M0, section "Port conventions").

As in `Co/Preliminaries/Defs.lean`, the declarations live in `MIPRE.LIDT.Co.Preliminaries` and
take the symmetric model `S : SymModel 𝔓 K` as an ordinary explicit argument in place of the
vendored state `ψ` (`simeqToApprox S 𝒟 A B δ`); `ConsRel.mono` lives in the namespace of the
ported relation, `MIPRE.LIDT.Co.SymModel.ConsRel`, so that `h.mono hδ` works on
`h : S.ConsRel 𝒟 A B δ`. Local families have their operators in `𝔓`; the same-space statements
`questionSDD_le_two_questionConsistency` and `qSDDOp_symm` are about joint operators, in
`K →L[ℂ] K`, and take a vector state `S : VecState K` (`Co/Basic/QuantumState.lean`; a symmetric
model is accepted through its coercion); `conjTranspose_mul_mono` holds in any star-ordered ring.

The vendored proof of `simeqToApprox` lifts the two measurements to the joint space and applies
the same-space bound. Here its per-question core is the repository's cross-party bound
`MIPRE.BipartiteModel.xSqNorm_sum_le_two_mul` (`MIPRE/Foundations/CrossConsistency.lean`) on
`S.toBipartite`, through `VecState.qSDDCore_eq_sum_snorm_sq` of `Co/Test/Defs.lean`: this is
`questionSDD_liftLeft_liftRight_le_two_questionConsistency`. In the symmetric model the
"heterogeneous" placements `IdxSubMeas.placeLeft`, `placeRight` are the lifts, so the
heterogeneous statements follow from the same-space ones by `rfl`.

## New here

- `questionSDD_liftLeft_liftRight_le_two_questionConsistency`: for two measurements on the
  local algebra, the squared distance of their left and right lifts is at most twice their
  bipartite consistency defect (the per-question core of `simeqToApprox`).

## Not ported

Every declaration of the vendored file has a counterpart here.
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.SymModel.ConsRel

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Monotonicity of `ConsRel` in the allowed error parameter. -/
theorem mono {Question Outcome : Type*} [Fintype Outcome]
    {S : SymModel 𝔓 K} {𝒟 : MIPStarRE.LDT.Distribution Question}
    {A B : IdxSubMeas Question Outcome 𝔓} {δ δ' : ℝ} (hδ : δ ≤ δ') :
    S.ConsRel 𝒟 A B δ → S.ConsRel 𝒟 A B δ' :=
  fun h => ⟨h.offDiagonalBound.trans hδ⟩

end MIPRE.LIDT.Co.SymModel.ConsRel

namespace MIPRE.LIDT.Co.Preliminaries

open MIPStarRE.LDT (Distribution avgOver uniformDistribution avgOver_mono avgOver_const_mul
  avgOver_uniform_fst avgOver_uniform_equiv)

/-- `prop:post-processing-preserves`.

Postprocessing preserves the total operator, so it preserves both the
submeasurement and measurement conditions. -/
theorem postprocessPreservesMeasurements {α β : Type*}
    {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    [Fintype α] [Fintype β]
    (A : SubMeas α R) (f : α → β) :
    (postprocess A f).total = A.total :=
  postprocess_total A f

/-- Loewner-order monotonicity of the sandwich `Z* X Z`.
If `X ≤ Y` then `Z* X Z ≤ Z* Y Z`. -/
theorem conjTranspose_mul_mono
    {R : Type*} [NonUnitalSemiring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
    {X Y Z : R}
    (hXY : X ≤ Y) :
    star Z * X * Z ≤ star Z * Y * Z :=
  star_left_conjugate_le_conjugate hXY Z

section Model

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- `prop:simeq-for-measurements`. -/
theorem simeqForMeasurements {Question Outcome : Type*}
    [Fintype Outcome]
    (S : SymModel 𝔓 K) (𝒟 : Distribution Question)
    (A B : IdxMeas Question Outcome 𝔓) (δ : ℝ) :
    S.ConsRel 𝒟 (IdxMeas.toIdxSubMeas A) (IdxMeas.toIdxSubMeas B) δ ↔
      ConsAgreement S 𝒟 A B δ := by
  constructor
  · intro ⟨h⟩
    exact ⟨by unfold agreementProbability; linarith⟩
  · intro ⟨h⟩
    exact ⟨by unfold agreementProbability at h; linarith⟩

/-- Atomic mathematical fact: for a full measurement, the squared-distance defect
is at most `2 * qConsDefect`. -/
theorem questionSDD_le_two_questionConsistency {Outcome : Type*}
    [Fintype Outcome]
    (S : VecState K) (A B : Measurement Outcome (K →L[ℂ] K)) :
    S.qSDD A.toSubMeas B.toSubMeas ≤
      2 * S.qConsDefect A.toSubMeas B.toSubMeas := by
  have hsq (M : Measurement Outcome (K →L[ℂ] K)) :
      ∑ a, S.ev (M.outcome a * M.outcome a) ≤ 1 :=
    calc
      ∑ a, S.ev (M.outcome a * M.outcome a) ≤ ∑ a, S.ev (M.outcome a) :=
        Finset.sum_le_sum fun a _ =>
          S.ev_mono _ _ (sq_le_self (M.outcome_pos a) (M.outcome_le_one a))
      _ = 1 := by rw [← S.ev_sum, M.sum_eq, S.ev_one_of_isNormalized]
  have h_expand (a : Outcome) :
      S.ev (star (A.outcome a - B.outcome a) * (A.outcome a - B.outcome a)) =
        S.ev (A.outcome a * A.outcome a) + S.ev (B.outcome a * B.outcome a) -
          2 * S.ev (A.outcome a * B.outcome a) := by
    have hcomm := S.ev_mul_comm_of_psd _ _ (B.outcome_pos a) (A.outcome_pos a)
    rw [star_sub, A.outcome_hermitian, B.outcome_hermitian, sub_mul, mul_sub, mul_sub,
      S.ev_sub, S.ev_sub, S.ev_sub, hcomm]
    ring
  have hqSDD : S.qSDD A.toSubMeas B.toSubMeas =
      ∑ a, S.ev (A.outcome a * A.outcome a) + ∑ a, S.ev (B.outcome a * B.outcome a) -
        2 * S.qMatchMass A.toSubMeas B.toSubMeas := by
    rw [VecState.qSDD, VecState.qSDDCore, Finset.sum_congr rfl fun a _ => h_expand a,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, VecState.qMatchMass, Finset.mul_sum]
  have htot : S.ev (A.total * B.total) = 1 := by
    rw [A.total_eq_one, B.total_eq_one, mul_one, S.ev_one_of_isNormalized]
  have h0 := S.qSDD_nonneg A.toSubMeas B.toSubMeas
  have hA := hsq A
  have hB := hsq B
  show _ ≤ 2 * max 0 (S.ev (A.total * B.total) - S.qMatchMass A.toSubMeas B.toSubMeas)
  rw [htot, max_eq_right (by linarith)]
  linarith

/-- For two measurements on the local algebra, the squared distance of the left and right
lifts is at most twice their bipartite consistency defect: the per-question core of
`simeqToApprox`. It is the repository's `MIPRE.BipartiteModel.xSqNorm_sum_le_two_mul` on
`S.toBipartite`. -/
theorem questionSDD_liftLeft_liftRight_le_two_questionConsistency {Outcome : Type*}
    [Fintype Outcome]
    (S : SymModel 𝔓 K) (A B : Measurement Outcome 𝔓) :
    S.qSDD (A.toSubMeas.liftLeft S) (B.toSubMeas.liftRight S) ≤
      2 * S.qBipartiteConsDefect A.toSubMeas B.toSubMeas := by
  have h := S.toBipartite.xSqNorm_sum_le_two_mul S.toBipartite_ψ_norm A.toPOVMIn B.toPOVMIn
  have hL : S.qSDD (A.toSubMeas.liftLeft S) (B.toSubMeas.liftRight S) =
      ∑ c, S.toBipartite.xSqNorm (A.toPOVMIn.op c) (B.toPOVMIn.op c) :=
    S.qSDDCore_eq_sum_snorm_sq _ _
  have hR : 1 - ∑ c, S.toBipartite.bornProb (A.toPOVMIn.op c) (B.toPOVMIn.op c) ≤
      S.qBipartiteConsDefect A.toSubMeas B.toSubMeas := by
    have htot : S.ev (S.opTensor A.total B.total) = 1 := by
      rw [A.total_eq_one, B.total_eq_one, SymModel.opTensor, S.leftTensor_one,
        S.rightTensor_one, mul_one, S.ev_one_of_isNormalized]
    show _ ≤ max 0 (S.ev (S.opTensor A.total B.total) -
      S.qBipartiteMatchMass A.toSubMeas B.toSubMeas)
    rw [htot]
    exact le_max_right _ _
  rw [hL]
  linarith

/-- `prop:simeq-to-approx`. -/
theorem simeqToApprox {Question Outcome : Type*}
    [Fintype Outcome]
    (S : SymModel 𝔓 K) (𝒟 : Distribution Question)
    (A B : IdxMeas Question Outcome 𝔓) (δ : ℝ) :
    S.ConsRel 𝒟
        (IdxMeas.toIdxSubMeas A)
        (IdxMeas.toIdxSubMeas B) δ →
      BipartiteSDDRel S 𝒟
        (IdxMeas.toIdxSubMeas A)
        (IdxMeas.toIdxSubMeas B)
        (2 * δ) := by
  intro ⟨hcons⟩
  constructor
  calc
    S.sddError 𝒟 (IdxSubMeas.liftLeft S (IdxMeas.toIdxSubMeas A))
        (IdxSubMeas.liftRight S (IdxMeas.toIdxSubMeas B))
      ≤ avgOver 𝒟 (fun q =>
          2 * S.qBipartiteConsDefect (A q).toSubMeas (B q).toSubMeas) :=
        avgOver_mono 𝒟 _ _ fun q =>
          questionSDD_liftLeft_liftRight_le_two_questionConsistency S (A q) (B q)
    _ = 2 * S.bipartiteConsError 𝒟 (IdxMeas.toIdxSubMeas A) (IdxMeas.toIdxSubMeas B) :=
        avgOver_const_mul 𝒟 2 _
    _ ≤ 2 * δ := mul_le_mul_of_nonneg_left hcons (by norm_num)

/-- Heterogeneous form of `prop:simeq-to-approx`.

The paper's consistency relation is naturally bipartite: Alice's measurement acts on the first
factor and Bob's on the second. This theorem is the same calculation as `simeqToApprox`,
expressed with the placements `IdxSubMeas.placeLeft` and `IdxSubMeas.placeRight`, which in the
symmetric model are the lifts. -/
theorem simeqToApprox_heterogeneous {Question Outcome : Type*}
    [Fintype Outcome]
    (S : SymModel 𝔓 K) (𝒟 : Distribution Question)
    (A B : IdxMeas Question Outcome 𝔓)
    (δ : ℝ) :
    S.ConsRel 𝒟
        (IdxMeas.toIdxSubMeas A)
        (IdxMeas.toIdxSubMeas B) δ →
      S.SDDRel 𝒟
        (IdxSubMeas.placeLeft S (IdxMeas.toIdxSubMeas A))
        (IdxSubMeas.placeRight S (IdxMeas.toIdxSubMeas B))
        (2 * δ) :=
  fun h => ⟨(simeqToApprox S 𝒟 A B δ h).leftRightSquaredDistanceBound⟩

/-- The expectation of `X ⊗ Y` is nonnegative for positive `X` and `Y`. -/
theorem ev_leftTensor_mul_rightTensor_nonneg
    (S : SymModel 𝔓 K)
    {X Y : 𝔓}
    (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    0 ≤ S.ev (S.L X * S.R Y) :=
  S.ev_nonneg_of_psd _ (S.opTensor_nonneg hX hY)

/-- Postprocessing two opposite-side families by the same readout map can only increase their
matching mass: the new diagonal terms are the old ones plus nonnegative cross terms within each
fibre. -/
theorem qMatchMass_leftRight_postprocess_ge {α β : Type*}
    [Fintype α] [Fintype β]
    (S : SymModel 𝔓 K) (A B : SubMeas α 𝔓)
    (f : α → β) :
    S.qMatchMass
        (S.leftPlacedSubMeas (postprocess A f))
        (S.rightPlacedSubMeas (postprocess B f)) ≥
      S.qMatchMass
        (S.leftPlacedSubMeas A)
        (S.rightPlacedSubMeas B) := by
  classical
  show ∑ a, S.ev (S.L (A.outcome a) * S.R (B.outcome a)) ≤
    ∑ b, S.ev (S.L ((postprocess A f).outcome b) * S.R ((postprocess B f).outcome b))
  rw [← Finset.sum_fiberwise Finset.univ f]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [SubMeas.postprocess_outcome, SubMeas.postprocess_outcome, map_sum, map_sum,
    Finset.sum_mul_sum, S.ev_finset_sum]
  refine Finset.sum_le_sum fun a ha => ?_
  rw [S.ev_finset_sum]
  exact Finset.single_le_sum
    (fun a' _ => ev_leftTensor_mul_rightTensor_nonneg S (A.outcome_pos a) (B.outcome_pos a')) ha

/-- Postprocessing can only decrease the bipartite strong self-consistency
defect: the total mass is preserved while the diagonal overlap term can only
increase. -/
theorem qBipartiteSSCDefect_postprocess_le {α β : Type*}
    [Fintype α] [Fintype β]
    (S : SymModel 𝔓 K) (M : SubMeas α 𝔓) (f : α → β) :
    S.qBipartiteSSCDefect (postprocess M f) ≤ S.qBipartiteSSCDefect M :=
  max_le_max le_rfl (sub_le_sub_left (qMatchMass_leftRight_postprocess_ge S M M f) _)

/-- Postprocessing two opposite-side families by the same readout map can only decrease their
consistency defect: the total overlap is preserved and the matching mass can only increase. -/
theorem qConsDefect_leftRight_postprocess_le {α β : Type*}
    [Fintype α] [Fintype β]
    (S : SymModel 𝔓 K) (A B : SubMeas α 𝔓)
    (f : α → β) :
    S.qConsDefect
        (S.leftPlacedSubMeas (postprocess A f))
        (S.rightPlacedSubMeas (postprocess B f))
      ≤
    S.qConsDefect
        (S.leftPlacedSubMeas A)
        (S.rightPlacedSubMeas B) :=
  max_le_max le_rfl (sub_le_sub_left (qMatchMass_leftRight_postprocess_ge S A B f) _)

/-- Question-dependent postprocessing preserves bipartite consistency. -/
theorem consRelDataProcessing_questionDependent {Question α β : Type*}
    [Fintype α] [Fintype β]
    (S : SymModel 𝔓 K) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question α 𝔓) (δ : ℝ)
    (f : Question → α → β) :
    S.ConsRel 𝒟 A B δ →
      S.ConsRel 𝒟
        (fun q => postprocess (A q) (f q))
        (fun q => postprocess (B q) (f q)) δ :=
  fun ⟨hcons⟩ => ⟨(avgOver_mono 𝒟 _ _ fun q =>
    qConsDefect_leftRight_postprocess_le S (A q) (B q) (f q)).trans hcons⟩

/-- Heterogeneous form of `prop:simeq-data-processing`.

This is the paper-faithful opposite-side statement: the two families are first
placed on opposite tensor factors of a bipartite state, and only then
postprocessed. The generic same-side `qConsDefect` monotonicity statement is
false for arbitrary noncommuting submeasurements. -/
theorem simeqDataProcessing_heterogeneous {Question α β : Type*}
    [Fintype α] [Fintype β]
    (S : SymModel 𝔓 K) (𝒟 : Distribution Question)
    (A B : IdxMeas Question α 𝔓) (δ : ℝ)
    (f : α → β) :
    S.ConsRel 𝒟
      (IdxMeas.toIdxSubMeas A)
      (IdxMeas.toIdxSubMeas B) δ →
      S.ConsRel 𝒟
        (fun q => postprocess ((A q).toSubMeas) f)
        (fun q => postprocess ((B q).toSubMeas) f) δ :=
  consRelDataProcessing_questionDependent S 𝒟 _ _ δ fun _ => f

/-- `prop:simeq-data-processing`.

This is the source-labelled same-space statement.  The proof is the
heterogeneous opposite-side data-processing theorem specialized to equal local
spaces. -/
theorem simeqDataProcessing {Question α β : Type*}
    [Fintype α] [Fintype β]
    (S : SymModel 𝔓 K) (𝒟 : Distribution Question)
    (A B : IdxMeas Question α 𝔓) (δ : ℝ)
    (f : α → β) :
    S.ConsRel 𝒟
      (IdxMeas.toIdxSubMeas A)
      (IdxMeas.toIdxSubMeas B) δ →
      S.ConsRel 𝒟
        (fun q => postprocess ((A q).toSubMeas) f)
        (fun q => postprocess ((B q).toSubMeas) f) δ :=
  simeqDataProcessing_heterogeneous S 𝒟 A B δ f

/-- If a uniformly sampled consistency statement depends only on the first
coordinate of a product question, it lifts to the full product with the same
error. -/
theorem consRel_uniform_prod_fst
    {α β Outcome : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    [Fintype Outcome]
    (S : SymModel 𝔓 K)
    (A B : IdxSubMeas α Outcome 𝔓)
    (δ : ℝ)
    (hAB : S.ConsRel (uniformDistribution α) A B δ) :
    S.ConsRel (uniformDistribution (α × β))
      (fun ab => A ab.1)
      (fun ab => B ab.1)
      δ :=
  ⟨(avgOver_uniform_fst (α := α) (β := β)
    (fun a => S.qBipartiteConsDefect (A a) (B a))).trans_le hAB.offDiagonalBound⟩

/-- Reindexing a uniformly sampled consistency statement along an equivalence. -/
theorem consRel_uniform_equiv
    {α β Outcome : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    [Fintype Outcome]
    (e : α ≃ β)
    (S : SymModel 𝔓 K)
    (A B : IdxSubMeas α Outcome 𝔓)
    (δ : ℝ) :
    S.ConsRel (uniformDistribution α) A B δ ↔
      S.ConsRel (uniformDistribution β)
        (fun b => A (e.symm b))
        (fun b => B (e.symm b))
        δ := by
  have hEq : S.bipartiteConsError (uniformDistribution α) A B =
      S.bipartiteConsError (uniformDistribution β)
        (fun b => A (e.symm b)) (fun b => B (e.symm b)) :=
    avgOver_uniform_equiv e fun a => S.qBipartiteConsDefect (A a) (B a)
  exact ⟨fun ⟨h⟩ => ⟨hEq.symm.trans_le h⟩, fun ⟨h⟩ => ⟨hEq.trans_le h⟩⟩

/-- `qSDDOp` is symmetric: swapping the two operator families gives the same
squared-distance sum. -/
theorem qSDDOp_symm
    {Outcome : Type*} [Fintype Outcome]
    (S : VecState K) (A B : OpFamily Outcome (K →L[ℂ] K)) :
    S.qSDDOp A B = S.qSDDOp B A :=
  Finset.sum_congr rfl fun a _ => by
    rw [← neg_sub (B.outcome a), star_neg, neg_mul_neg]

end Model

end MIPRE.LIDT.Co.Preliminaries

end
