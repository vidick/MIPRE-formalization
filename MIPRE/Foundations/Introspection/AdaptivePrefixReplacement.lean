/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.AdaptivePrefixMixing
public import MIPRE.Foundations.Introspection.AdaptivePrefixMeasurement
public import MIPRE.Foundations.Introspection.AdaptivePrefixExtension
public import MIPRE.Foundations.Introspection.AdaptiveDilationTransport

@[expose] public section

/-! # Actual adaptive residual projectors after mixing

Every conditioned prefix uses its actual remaining coordinates. Naimark
produces projective residual measurements with the single ancilla alphabet
`A` and fixed state `a₀`. The original prefix and the next Z readout remain
explicit tensor factors, and the error is averaged with the actual CL law.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the residual measurements are
block matrices over the remaining register with entries in the auxiliary algebra, the dilation is
the Kraus–Halmos one against the fixed ancilla state `inl (a₀, 0)` of `DilationAncilla A K`, with
one `K` for every prefix (`exists_pvm_dilation_ge`), and the reassociation is `regExchange`.
-/

noncomputable section

namespace MIPRE

open Finset Matrix Classical

/-- **Fixed-state dilation with any large enough padding**: the dilation of
`exists_pvm_dilation` exists on `DilationAncilla A K` for every `K` beyond a threshold, so that
finitely many families, even in different rings, can share one ancilla. -/
theorem exists_pvm_dilation_ge {R : Type*} [Ring R] [StarRing R] [PartialOrder R]
    [StarOrderedRing R] {Y A : Type*} [Fintype Y] [Fintype A] [DecidableEq A]
    (Q : Y → POVMIn A R) (a₀ : A) :
    ∃ K₀ : ℕ, ∀ K, K₀ ≤ K → ∃ P : Y → A → Matrix (DilationAncilla A K) (DilationAncilla A K) R,
      (∀ y, IsPVMIn (P y)) ∧ ∀ y a, P y a (Sum.inl (a₀, 0)) (Sum.inl (a₀, 0)) = (Q y).op a := by
  choose k Z hZ using fun (p : Y × A) => exists_sum_star_mul_self ((Q p.1).op_nonneg p.2)
  refine ⟨Finset.univ.sup fun p : Y × A => k p, fun K hK => ?_⟩
  have hk p : k p ≤ K + 1 :=
    ((Finset.le_sup (f := fun p : Y × A => k p) (mem_univ p)).trans hK).trans (Nat.le_succ K)
  let z : Y → A × Fin (K + 1) → R := fun y q =>
    if h : q.2.val < k (y, q.1) then Z (y, q.1) ⟨q.2.val, h⟩ else 0
  have hrow y a : ∑ i : Fin (K + 1), star (z y (a, i)) * z y (a, i) = (Q y).op a := by
    rw [hZ (y, a)]
    exact sum_star_mul_self_pad (hk (y, a)) (Z (y, a))
  have hsum y : ∑ q, star (z y q) * z y q = 1 := by
    rw [Fintype.sum_prod_type]
    simp_rw [hrow y]
    exact (Q y).sum_op
  have hw y : Halmos.naimark (z y) (a₀, 0) * (Halmos.naimark (z y) (a₀, 0))ᴴ *
      Halmos.naimark (z y) (a₀, 0) = Halmos.naimark (z y) (a₀, 0) :=
    Halmos.naimark_mul_conjTranspose_mul' (hsum y) _
  have hcomp y a : (∑ c ∈ univ.filter (fun c : A × Fin (K + 1) => c.1 = a),
      Halmos.proj (Halmos.naimark (z y) (a₀, 0)) c) (Sum.inl (a₀, 0)) (Sum.inl (a₀, 0)) =
      (Q y).op a := by
    rw [Matrix.sum_apply]
    simp_rw [Halmos.proj_naimark_inl_inl' (hsum y)]
    rw [← hrow y a, Finset.sum_filter, Fintype.sum_prod_type]
    refine (Finset.sum_eq_single a (fun b _ hb => ?_) (fun h => absurd (mem_univ a) h)).trans ?_
    · exact Finset.sum_eq_zero fun i _ => ite_eq_right hb
    · exact Finset.sum_congr rfl fun i _ => ite_eq_left rfl
  exact ⟨fun y => fibSumIn (Halmos.proj (Halmos.naimark (z y) (a₀, 0))) Prod.fst, fun y =>
    isPVMIn_fibSumIn (Halmos.isPVMIn_proj (hw y)) Prod.fst, hcomp⟩

namespace Introspection

open Weyl
set_option linter.unusedSectionVars false

variable {ι F A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype A] [DecidableEq A] {ℓ : ℕ}
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [StarModule ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]
variable {T : Type*} [Fintype T] [DecidableEq T]

/-- Joint outcomes retain the actual prefix and the next factor's outcome. -/
abbrev AdaptiveStageAnswer (P : CL.CLFun F ι ℓ) (k : ℕ) (A : Type*) :=
  (y : ι → F) × ((Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A)

/-- The dilated residual measurements: for each prefix and new Z outcome, block matrices over the
ancilla whose entries are block matrices over the coordinates after the new factor. -/
abbrev AdaptiveDilationFamily (P : CL.CLFun F ι ℓ) (k : ℕ) (𝒜 T A : Type*) :=
  (y : ι → F) → (Fin (Fintype.card (P.factorOfPrefix k y)) → F) → A →
    Matrix T T (Matrix (↥(stageRemaining P k y \ P.factorOfPrefix k y) → F)
      (↥(stageRemaining P k y \ P.factorOfPrefix k y) → F) 𝒜)

variable [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜]

/-- The actual old joint PVM, with dependent local outcome spaces. -/
def adaptiveOldJointPOVM (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ) (k : ℕ)
    (M : (y : ι → F) → POVMIn ((Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A)
      (Matrix (stageRemaining P k y → F) (stageRemaining P k y → F) 𝒜)) :
    POVMIn (AdaptiveStageAnswer P k A) (Matrix (ι → F) (ι → F) 𝒜) :=
  prefixResidualPOVM P hP k M

theorem adaptiveOldJointPOVM_isPVM (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ) (k : ℕ)
    (M : (y : ι → F) → POVMIn ((Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A)
      (Matrix (stageRemaining P k y → F) (stageRemaining P k y → F) 𝒜))
    (hM : ∀ y, IsPVMIn (M y).op) :
    IsPVMIn (adaptiveOldJointPOVM P hP k M).op :=
  prefixResidualPOVM_isPVM P hP k M hM

/-- The next joint PVM on one ambient register, retaining both the old
prefix and the new Z factor explicitly. -/
def adaptiveReplacementJointOp (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (D : AdaptiveDilationFamily P k 𝒜 T A) (p : AdaptiveStageAnswer P k A) :
    Matrix (ι → F) (ι → F) (Matrix T T 𝒜) :=
  prefixResidualOp P k p.1 (reassociatedConditionalDilation (stageSplit P hP k p.1)
    (synOf wZ (coordinateLinear (CLChecks.stageLinear P k p.1))) (D p.1) p.2)

set_option maxHeartbeats 800000 in
theorem adaptiveReplacementJointOp_isPVM (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (D : AdaptiveDilationFamily P k 𝒜 T A) (hD : ∀ y z, IsPVMIn (D y z)) :
    IsPVMIn (adaptiveReplacementJointOp P hP k D) :=
  prefixResidual_isPVM P hP k
    (fun y => reassociatedConditionalDilation (stageSplit P hP k y)
      (synOf wZ (coordinateLinear (CLChecks.stageLinear P k y))) (D y))
    (fun y => reassociatedConditionalDilation_isPVM (stageSplit P hP k y)
      (synOf wZ (coordinateLinear (CLChecks.stageLinear P k y)))
      (isPVM_synOf isWeylFamily_wZ _) (D y) (hD y))

omit [StarModule ℂ 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜] in
theorem layerSwap_layerSwap {I : Type*} [Fintype I] [DecidableEq I]
    (X : Matrix I I (Matrix T T 𝒜)) :
    BipartiteModel.layerSwap (BipartiteModel.layerSwap (T := I) (α := T) X) = X := by
  ext i i' t t'
  rfl

/-- The same actual joint PVM, in the extension ordering used by the
replacement-strategy constructor. -/
def adaptiveReplacementPOVM (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (D : AdaptiveDilationFamily P k 𝒜 T A) (hD : ∀ y z, IsPVMIn (D y z)) :
    POVMIn (AdaptiveStageAnswer P k A) (Matrix T T (Matrix (ι → F) (ι → F) 𝒜)) :=
  ((adaptiveReplacementJointOp_isPVM P hP k D hD).pushforward
    (f := BipartiteModel.layerSwap (T := ι → F) (α := T))
    BipartiteModel.layerSwap_one).toPOVMIn

theorem adaptiveReplacementPOVM_op (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (D : AdaptiveDilationFamily P k 𝒜 T A) (hD : ∀ y z, IsPVMIn (D y z))
    (p : AdaptiveStageAnswer P k A) :
    (adaptiveReplacementPOVM P hP k D hD).op p =
      BipartiteModel.layerSwap (T := ι → F) (α := T) (adaptiveReplacementJointOp P hP k D p) :=
  rfl

theorem adaptiveReplacementPOVM_isPVM (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (D : AdaptiveDilationFamily P k 𝒜 T A) (hD : ∀ y z, IsPVMIn (D y z)) :
    IsPVMIn (adaptiveReplacementPOVM P hP k D hD).op :=
  (adaptiveReplacementJointOp_isPVM P hP k D hD).pushforward
    (f := BipartiteModel.layerSwap (T := ι → F) (α := T)) BipartiteModel.layerSwap_one

variable [PartialOrder ℬ] [StarOrderedRing ℬ] [StarModule ℂ ℬ] [StarProper ℬ]
  (Ξ : BipartiteModel 𝒞 𝒜 ℬ)

/-- The local weighted dilation error is the squared error of the actual
global replacement PVM. No number-of-prefixes loss is introduced. -/
theorem adaptiveReplacement_distance (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (t₀ : T)
    (M : (y : ι → F) → POVMIn ((Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A)
      (Matrix (stageRemaining P k y → F) (stageRemaining P k y → F) 𝒜))
    (D : AdaptiveDilationFamily P k 𝒜 T A) (hD : ∀ y z, IsPVMIn (D y z)) {δ : ℝ}
    (hd : (∑ y, prefixWeight P k y * ∑ p,
      ((Ξ.reg (stageRemaining P k y → F)).expandA t₀).stateSqNorm
        ((diagonal fun _ => (M y).op p) - transportedConditionalDilation (stageSplit P hP k y)
          (synOf wZ (coordinateLinear (CLChecks.stageLinear P k y))) (D y) p)) ≤ δ) :
    (∑ p, ((Ξ.reg (ι → F)).expandA t₀).stateSqNorm
      ((diagonal fun _ => (adaptiveOldJointPOVM P hP k M).op p) -
        (adaptiveReplacementPOVM P hP k D hD).op p)) ≤ δ := by
  have he (y : ι → F) (p : (Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A) :
      ((Ξ.reg (ι → F)).expandA t₀).stateSqNorm
        ((diagonal fun _ => (adaptiveOldJointPOVM P hP k M).op ⟨y, p⟩) -
          (adaptiveReplacementPOVM P hP k D hD).op ⟨y, p⟩) =
      prefixWeight P k y * ((Ξ.reg (stageRemaining P k y → F)).expandA t₀).stateSqNorm
        ((diagonal fun _ => (M y).op p) - transportedConditionalDilation (stageSplit P hP k y)
          (synOf wZ (coordinateLinear (CLChecks.stageLinear P k y))) (D y) p) := by
    rw [adaptiveReplacementPOVM_op, adaptiveOldJointPOVM, prefixResidualPOVM_op,
      ← stateSqNorm_reassociated_extVecA Ξ t₀, map_sub, layerSwap_layerSwap]
    change ((Ξ.expandA t₀).reg (ι → F)).stateSqNorm
      (registeredExtendOp (prefixResidualOp P k y ((M y).op p)) -
        adaptiveReplacementJointOp P hP k D ⟨y, p⟩) = _
    rw [← prefixResidualOp_extend P k y ((M y).op p), adaptiveReplacementJointOp,
      prefixResidual_distance (Ξ.expandA t₀) P hP, reassociatedConditionalDilation,
      registeredExtendOp, ← map_sub, stateSqNorm_reassociated_extVecA]
  rw [Fintype.sum_sigma]
  simp_rw [he]
  simpa only [Finset.mul_sum] using hd

/-- The one shared answer ancilla suffices although the remaining coordinate
space and the next factor dimension depend on the prefix. -/
theorem exists_adaptive_prefix_dilation (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (hΞ : ‖Ξ.ψ‖ = 1) (a₀ : A)
    (M : (y : ι → F) → POVMIn ((Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A)
      (Matrix (stageRemaining P k y → F) (stageRemaining P k y → F) 𝒜))
    (hM : ∀ y, IsPVMIn (M y).op)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmarg : prefixStageMarginalError P hP k Ξ (fun y => (M y).op) ≤ ε)
    (hZ : prefixStageCommutatorError P hP k Ξ (fun y => (M y).op)
      (fun _ => wZ) (fun _ => LinearMap.id) ≤ ε)
    (hX : prefixStageCommutatorError P hP k Ξ (fun y => (M y).op)
      (fun _ => wX) (fun y => CL.lperp (coordinateLinear (CLChecks.stageLinear P k y))) ≤ ε) :
    ∃ K : ℕ, ∃ D : AdaptiveDilationFamily P k 𝒜 (DilationAncilla A K) A,
      (∀ y z, IsPVMIn (D y z)) ∧
      (∑ y, prefixWeight P k y * ∑ p,
        ((Ξ.reg (stageRemaining P k y → F)).expandA
            (Sum.inl (a₀, 0) : DilationAncilla A K)).stateSqNorm
          ((diagonal fun _ => (M y).op p) - transportedConditionalDilation (stageSplit P hP k y)
            (synOf wZ (coordinateLinear (CLChecks.stageLinear P k y))) (D y) p)) ≤
        2*Real.sqrt (56*Real.sqrt ε) := by
  obtain ⟨Q, hQ⟩ := exists_adaptive_prefix_mixing P hP k Ξ hΞ M hM hε0 hε1 hmarg hZ hX
  choose K₀ hK₀ using fun y => exists_pvm_dilation_ge (Q y) a₀
  let K := Finset.univ.sup K₀
  have hlocal y := hK₀ y K (Finset.le_sup (f := K₀) (mem_univ y))
  choose D hD hk using hlocal
  refine ⟨K, D, hD, ?_⟩
  let err y := ∑ p, (Ξ.reg (stageRemaining P k y → F)).stateSqNorm
    ((M y).op p - regSplitHom (stageSplit P hP k y)
      (smulKron ((Q y p.1).op p.2)
        (synOf wZ (coordinateLinear (CLChecks.stageLinear P k y)) p.1)))
  have herr y : 0 ≤ err y := Finset.sum_nonneg fun _ _ => BipartiteModel.stateSqNorm_nonneg _ _
  have havg : ∑ y, prefixWeight P k y * err y ≤ 56*Real.sqrt ε := by
    simpa only [prefixResidual_distance Ξ P hP, Finset.mul_sum, err] using hQ
  have hpoint y := dilated_pvm_distance (Ξ.reg (stageRemaining P k y → F))
    (by rw [BipartiteModel.norm_reg_ψ, hΞ]) (Sum.inl (a₀, 0) : DilationAncilla A K)
    (fun p => (M y).op p)
    (fun p => regSplitHom (stageSplit P hP k y)
      (smulKron ((Q y p.1).op p.2)
        (synOf wZ (coordinateLinear (CLChecks.stageLinear P k y)) p.1)))
    (transportedConditionalDilation (stageSplit P hP k y)
      (synOf wZ (coordinateLinear (CLChecks.stageLinear P k y))) (D y))
    (hM y) (transportedConditionalDilation_isPVM _ _ (isPVM_synOf isWeylFamily_wZ _) _ (hD y))
    (transportedConditionalDilation_compress _ _ _ _ (fun z a => (Q y z).op a) (hk y))
    (δ := err y) le_rfl
  calc
    _ ≤ ∑ y, prefixWeight P k y * (2*Real.sqrt (err y)) :=
      Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hpoint y) (prefixWeight_nonneg P k y)
    _ = 2*∑ y, prefixWeight P k y * Real.sqrt (err y) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ ≤ 2*Real.sqrt (56*Real.sqrt ε) := mul_le_mul_of_nonneg_left
      ((sum_weighted_sqrt_le (prefixWeight P k) err (prefixWeight_nonneg P k)
        (sum_prefixWeight P k) herr).trans (Real.sqrt_le_sqrt havg)) (by norm_num)

end Introspection

end MIPRE
end

end
