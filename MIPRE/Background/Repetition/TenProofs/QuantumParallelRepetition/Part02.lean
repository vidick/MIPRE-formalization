/-
Copyright (c) 2026 the openai/ten-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/openai/ten-proofs (commit 94bc0feb, 2026-08-01) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: QuantumParallelRepetition.lean
-/
import Mathlib
import MIPRE.Background.Repetition.TenProofs.QuantumParallelRepetition.Part01

-- Part 2 of 8 of upstream's single module `QuantumParallelRepetition.lean`: its lines
-- 8996-17933, cut between top-level `noncomputable section` blocks by
-- scripts/vendor-repetition.py (the Palomar registry caps a Lean file at 10,000 lines).
-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace QuantumParallelRepetition

open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset


noncomputable section

open scoped BigOperators Kronecker ComplexOrder MatrixOrder

theorem dSVMixedProjectorSuccessLoss_le_square
    {d : Type*} [Fintype d] [DecidableEq d]
    (P R : Matrix d d ℂ)
    (hcomplement : (1 - P).PosSemidef)
    (hR : R.PosSemidef)
    (hPP : P * P = P) (hRR : R * R = R) :
    (Matrix.trace P).re - (Matrix.trace (P * R)).re ≤
      (Matrix.trace ((P - R) * (P - R))).re := by
  have remainder := trace_mul_posSemidef_nonneg hcomplement hR
  have square :
      (Matrix.trace ((P - R) * (P - R))).re =
        (Matrix.trace P).re + (Matrix.trace R).re -
          2 * (Matrix.trace (P * R)).re := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      hPP, hRR, Matrix.trace_sub, Matrix.trace_sub,
      Matrix.trace_sub, Matrix.trace_mul_comm R P]
    simp [Complex.sub_re]
    ring
  have rest :
      0 ≤ (Matrix.trace R).re - (Matrix.trace (P * R)).re := by
    simpa [Matrix.sub_mul, Matrix.trace_sub] using remainder
  rw [square]
  linarith

theorem dSVWeightedMixedProjectorSuccessLoss_le_square
    {κ d : Type*} [Fintype κ] [Fintype d]
    [DecidableEq d]
    (w : κ → ℝ) (nonnegative : ∀ k, 0 ≤ w k)
    (P R : κ → Matrix d d ℂ)
    (hcomplement : ∀ k, (1 - P k).PosSemidef)
    (hR : ∀ k, (R k).PosSemidef)
    (hPP : ∀ k, P k * P k = P k)
    (hRR : ∀ k, R k * R k = R k) :
    (∑ k : κ, w k * (Matrix.trace (P k)).re) -
        (∑ k : κ, w k * (Matrix.trace (P k * R k)).re) ≤
      ∑ k : κ, w k *
        (Matrix.trace ((P k - R k) * (P k - R k))).re := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro k _
  rw [← mul_sub]
  exact mul_le_mul_of_nonneg_left
    (dSVMixedProjectorSuccessLoss_le_square
      (P k) (R k) (hcomplement k) (hR k) (hPP k) (hRR k))
    (nonnegative k)

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

def dSVGlobalProjectorBinaryPOVM
    {κ d : Type*} [Fintype κ] [Fintype d]
    [DecidableEq κ] [DecidableEq d]
    (P : κ → Matrix d d ℂ)
    (positive : ∀ k, (P k).PosSemidef)
    (complement : ∀ k, (1 - P k).PosSemidef) :
    POVM Bool (Σ _ : κ, d) where
  effect b := Matrix.blockDiagonal' fun k =>
    if b then P k else 1 - P k
  positive b := by
    apply posSemidef_blockDiagonal'
    intro k
    cases b
    · exact complement k
    · exact positive k
  complete := by
    classical
    rw [Fintype.sum_bool]
    ext ⟨k, i⟩ ⟨l, j⟩
    by_cases same : k = l
    · subst l
      simp [Matrix.blockDiagonal'_apply, Matrix.one_apply,
        Matrix.sub_apply]
    · simp [Matrix.blockDiagonal'_apply, same]

theorem dSVGlobalProjectorBinaryPOVM_projective
    {κ d : Type*} [Fintype κ] [Fintype d]
    [DecidableEq κ] [DecidableEq d]
    (P : κ → Matrix d d ℂ)
    (positive : ∀ k, (P k).PosSemidef)
    (complement : ∀ k, (1 - P k).PosSemidef)
    (projective : ∀ k, P k * P k = P k)
    (b : Bool) :
    (dSVGlobalProjectorBinaryPOVM
      P positive complement).effect b *
      (dSVGlobalProjectorBinaryPOVM
        P positive complement).effect b =
      (dSVGlobalProjectorBinaryPOVM
        P positive complement).effect b := by
  change
    Matrix.blockDiagonal' (fun k => if b then P k else 1 - P k) *
      Matrix.blockDiagonal' (fun k => if b then P k else 1 - P k) =
      Matrix.blockDiagonal' (fun k => if b then P k else 1 - P k)
  rw [← Matrix.blockDiagonal'_mul]
  apply congrArg (fun A : κ → Matrix d d ℂ => Matrix.blockDiagonal' A)
  funext k
  cases b
  · simp [Matrix.mul_sub, Matrix.sub_mul, projective k]
  · exact projective k

theorem dSVActualGlobalMixedBornSuccess_eq
    {κ d : Type*} [Fintype κ] [Fintype d]
    [DecidableEq κ] [DecidableEq d]
    (τ : κ → ℝ) (k₀ : κ) (i₀ : d) (nonzero : τ k₀ ≠ 0)
    (P R : κ → Matrix d d ℂ)
    (hP : ∀ k, (P k).PosSemidef)
    (hPc : ∀ k, (1 - P k).PosSemidef)
    (hR : ∀ k, (R k).PosSemidef)
    (hRc : ∀ k, (1 - R k).PosSemidef)
    (hPP : ∀ k, P k * P k = P k)
    (hRR : ∀ k, R k * R k = R k) :
    binaryJointSuccessProbability
      (pureDensityMatrix
        (sharedThresholdResource (d := d) τ)
        (sharedThresholdResource_norm τ k₀ i₀ nonzero))
      (dSVGlobalProjectorBinaryPOVM P hP hPc)
      (transposePOVM
        (dSVGlobalProjectorBinaryPOVM R hR hRc)) =
      (∑ k : κ, τ k ^ 2 * (Matrix.trace (P k * R k)).re) /
        ((Fintype.card d : ℝ) * ∑ k : κ, τ k ^ 2) := by
  let A := dSVGlobalProjectorBinaryPOVM P hP hPc
  let B := transposePOVM
    (dSVGlobalProjectorBinaryPOVM R hR hRc)
  let z := sharedThresholdResource (d := d) τ
  have hz : ‖z‖ = 1 :=
    sharedThresholdResource_norm τ k₀ i₀ nonzero
  have hA : ∀ b : Bool, A.effect b * A.effect b = A.effect b :=
    dSVGlobalProjectorBinaryPOVM_projective
      P hP hPc hPP
  have hB : ∀ b : Bool, B.effect b * B.effect b = B.effect b :=
    transposePOVM_projective
      (dSVGlobalProjectorBinaryPOVM R hR hRc)
      (dSVGlobalProjectorBinaryPOVM_projective
        R hR hRc hRR)
  change binaryJointSuccessProbability
    (pureDensityMatrix z hz) A B = _
  unfold binaryJointSuccessProbability
    binaryBornProbability
  rw [← coherentBinaryJointOutcome_norm_sq
    A B hA hB z hz true true]
  change
    ‖toLp 2
      ((Matrix.blockDiagonal' P ⊗ₖ
        (Matrix.blockDiagonal' R).transpose).mulVec
          (ofLp (sharedThresholdResource (d := d) τ)))‖ ^ 2 = _
  exact sharedThresholdResource_block_action_norm_sq
    τ P R hP hR hPP hRR

end

noncomputable section

open scoped BigOperators

def dSVRationalSoftPass (t x : ℝ) : ℝ :=
  x / (x + t)

theorem dSVRationalSoftPass_mem_unit
    {t x : ℝ} (positive : 0 < t) (nonnegative : 0 ≤ x) :
    0 ≤ dSVRationalSoftPass t x ∧
      dSVRationalSoftPass t x ≤ 1 := by
  unfold dSVRationalSoftPass
  have denominator : 0 < x + t := by linarith
  constructor
  · exact div_nonneg nonnegative denominator.le
  · apply (div_le_iff₀ denominator).mpr
    linarith

theorem dSVRationalSoftPass_sub
    {t a b : ℝ} (positive : 0 < t)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    dSVRationalSoftPass t a -
        dSVRationalSoftPass t b =
      t * (a - b) / ((a + t) * (b + t)) := by
  unfold dSVRationalSoftPass
  have da : a + t ≠ 0 := by linarith
  have db : b + t ≠ 0 := by linarith
  field_simp
  ring

theorem dSVRationalSoftPass_lipschitz
    {t a b : ℝ} (positive : 0 < t)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |dSVRationalSoftPass t a -
        dSVRationalSoftPass t b| ≤ |a - b| / t := by
  have denominator : 0 < (a + t) * (b + t) :=
    mul_pos (by linarith) (by linarith)
  rw [dSVRationalSoftPass_sub positive ha hb,
    abs_div, abs_mul, abs_of_pos positive, abs_of_pos denominator]
  apply (div_le_iff₀ denominator).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ positive).mpr
  have wide : t ^ 2 ≤ (a + t) * (b + t) := by
    nlinarith [mul_nonneg ha hb]
  nlinarith [mul_le_mul_of_nonneg_left wide (abs_nonneg (a - b))]

end

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
set_option maxRecDepth 3072

theorem dSVAdaptiveSoft_sqrt_sub_sq_le_abs
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 ≤ |a - b| := by
  have sa : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  have sb : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
  have square_a : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have square_b : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  rcases le_total a b with ordered | ordered
  · rw [abs_of_nonpos (sub_nonpos.mpr ordered)]
    have roots := Real.sqrt_le_sqrt ordered
    nlinarith [mul_nonneg sa (sub_nonneg.mpr roots)]
  · rw [abs_of_nonneg (sub_nonneg.mpr ordered)]
    have roots := Real.sqrt_le_sqrt ordered
    nlinarith [mul_nonneg sb (sub_nonneg.mpr roots)]

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

def dSVSoftBobLeftReducedDensity
    {d : ℕ} (ζ : BipartiteUnitVector d) :
    Matrix (Fin d) (Fin d) ℂ :=
  targetCoefficientMatrix ζ *
    (targetCoefficientMatrix ζ).conjTranspose

theorem dSVSoftBobLeftReducedDensity_posSemidef
    {d : ℕ} (ζ : BipartiteUnitVector d) :
    (dSVSoftBobLeftReducedDensity ζ).PosSemidef := by
  exact Matrix.posSemidef_self_mul_conjTranspose
    (targetCoefficientMatrix ζ)

theorem dSVSoftBobLeftReducedDensity_trace
    {d : ℕ} (ζ : BipartiteUnitVector d) :
    Matrix.trace (dSVSoftBobLeftReducedDensity ζ) = 1 := by
  unfold dSVSoftBobLeftReducedDensity
  calc
    Matrix.trace
        (targetCoefficientMatrix ζ *
          (targetCoefficientMatrix ζ).conjTranspose) =
        Matrix.trace
          ((targetCoefficientMatrix ζ).conjTranspose *
            targetCoefficientMatrix ζ) :=
      Matrix.trace_mul_comm _ _
    _ = 1 := targetReducedDensity_trace ζ

def dSVOriginalComputationalReindexedUnitary
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {D : ℕ} (e : ι ≃ Fin D)
    (U : Matrix.unitaryGroup ι ℂ) :
    Matrix.unitaryGroup (Fin D) ℂ := by
  classical
  let M : Matrix ι ι ℂ := U.val
  refine ⟨(Matrix.reindex e e) M, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff']
  have compatible :
      star ((Matrix.reindex e e) M) =
        (Matrix.reindex e e) (star M) := by
    ext i j
    simp [Matrix.star_eq_conjTranspose,
      Matrix.reindex_apply, Matrix.conjTranspose_apply]
  rw [compatible]
  change (Matrix.reindexRingEquiv ℂ e) (star M) *
    (Matrix.reindexRingEquiv ℂ e) M = 1
  rw [← (Matrix.reindexRingEquiv ℂ e).map_mul,
    (Matrix.mem_unitaryGroup_iff').mp U.property]
  exact (Matrix.reindexRingEquiv ℂ e).map_one

end

noncomputable section

open scoped BigOperators ComplexOrder

def dSVHeterogeneousRealPrefix
    (continuation : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∏ i ∈ Finset.range k, continuation i

theorem dSVHeterogeneousRealPrefix_succ
    (continuation : ℕ → ℝ) (k : ℕ) :
    dSVHeterogeneousRealPrefix continuation (k + 1) =
      dSVHeterogeneousRealPrefix continuation k *
        continuation k := by
  simp [dSVHeterogeneousRealPrefix,
    Finset.prod_range_succ]

theorem dSVHeterogeneousRealStopping_escape_identity
    (continuation : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N,
      dSVHeterogeneousRealPrefix continuation k *
        (1 - continuation k)) =
      1 - dSVHeterogeneousRealPrefix continuation N := by
  induction N with
  | zero =>
      simp [dSVHeterogeneousRealPrefix]
  | succ N ih =>
      simp only [Finset.sum_range_succ,
        dSVHeterogeneousRealPrefix_succ]
      linear_combination ih

theorem dSVHeterogeneousRealPrefix_nonneg
    (continuation : ℕ → ℝ)
    (nonnegative : ∀ k, 0 ≤ continuation k) (k : ℕ) :
    0 ≤ dSVHeterogeneousRealPrefix continuation k := by
  unfold dSVHeterogeneousRealPrefix
  exact Finset.prod_nonneg (fun i _ => nonnegative i)

theorem dSVHeterogeneousRealStopping_escape_budget
    (continuation escape : ℕ → ℝ)
    (continuation_nonnegative : ∀ k, 0 ≤ continuation k)
    (escape_bound : ∀ k, continuation k + escape k ≤ 1)
    (N : ℕ) :
    (∑ k ∈ Finset.range N,
      dSVHeterogeneousRealPrefix continuation k * escape k)
      ≤ 1 := by
  have each (k : ℕ) :
      dSVHeterogeneousRealPrefix continuation k * escape k ≤
        dSVHeterogeneousRealPrefix continuation k *
          (1 - continuation k) := by
    apply mul_le_mul_of_nonneg_left
    · linarith [escape_bound k]
    · exact dSVHeterogeneousRealPrefix_nonneg
        continuation continuation_nonnegative k
  calc
    (∑ k ∈ Finset.range N,
      dSVHeterogeneousRealPrefix continuation k * escape k)
        ≤ ∑ k ∈ Finset.range N,
          dSVHeterogeneousRealPrefix continuation k *
            (1 - continuation k) := by
              exact Finset.sum_le_sum (fun k _ => each k)
    _ = 1 - dSVHeterogeneousRealPrefix continuation N :=
      dSVHeterogeneousRealStopping_escape_identity
        continuation N
    _ ≤ 1 := by
      have := dSVHeterogeneousRealPrefix_nonneg
        continuation continuation_nonnegative N
      linarith

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

abbrev DSVUniformDensityThresholdLocalIndex
    (N d : ℕ) :=
  Σ _ : Fin N, Fin d

def dSVUniformDensityThresholdSharedState
    (N d : ℕ) :
    EuclideanSpace ℂ
      (DSVUniformDensityThresholdLocalIndex N d ×
        DSVUniformDensityThresholdLocalIndex N d) :=
  sharedThresholdResource (d := Fin d)
    (fun _ : Fin N => (1 : ℝ))

theorem dSVUniformDensityThresholdRaw_norm_sq
    (N d : ℕ) :
    ‖sharedThresholdResourceRaw (d := Fin d)
      (fun _ : Fin N => (1 : ℝ))‖ ^ 2 =
      (d : ℝ) * (N : ℝ) := by
  simpa using sharedThresholdResourceRaw_norm_sq
    (d := Fin d) (fun _ : Fin N => (1 : ℝ))

theorem dSVUniformDensityThresholdSharedState_norm
    {N d : ℕ} (grid : 0 < N) (dimension : 0 < d) :
    ‖dSVUniformDensityThresholdSharedState N d‖ = 1 := by
  exact sharedThresholdResource_norm
    (fun _ : Fin N => (1 : ℝ))
    ⟨0, grid⟩ ⟨0, dimension⟩ (by norm_num)

theorem dSVUniformDensityThresholdSharedState_mismatchedFlag
    (N d : ℕ) (k l : Fin N) (i j : Fin d)
    (different : k ≠ l) :
    dSVUniformDensityThresholdSharedState N d
      (⟨k, i⟩, ⟨l, j⟩) = 0 := by
  simp [dSVUniformDensityThresholdSharedState,
    sharedThresholdResource,
    sharedThresholdResourceRaw, different]

theorem dSVUniformDensityThresholdSharedState_mismatchedWork
    (N d : ℕ) (k l : Fin N) (i j : Fin d)
    (different : i ≠ j) :
    dSVUniformDensityThresholdSharedState N d
      (⟨k, i⟩, ⟨l, j⟩) = 0 := by
  simp [dSVUniformDensityThresholdSharedState,
    sharedThresholdResource,
    sharedThresholdResourceRaw, different]

def dSVUniformDensityThresholdSharedDensity
    {N d : ℕ} (grid : 0 < N) (dimension : 0 < d) :
    DensityMatrix
      (DSVUniformDensityThresholdLocalIndex N d ×
        DSVUniformDensityThresholdLocalIndex N d) :=
  pureDensityMatrix
    (dSVUniformDensityThresholdSharedState N d)
    (dSVUniformDensityThresholdSharedState_norm
      grid dimension)

theorem dSVUniformDensityThresholdShared_mixedBorn_eq
    {N d : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (P R : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hP : ∀ k, (P k).PosSemidef)
    (hPc : ∀ k, (1 - P k).PosSemidef)
    (hR : ∀ k, (R k).PosSemidef)
    (hRc : ∀ k, (1 - R k).PosSemidef)
    (hPP : ∀ k, P k * P k = P k)
    (hRR : ∀ k, R k * R k = R k) :
    binaryJointSuccessProbability
      (dSVUniformDensityThresholdSharedDensity
        grid dimension)
      (dSVGlobalProjectorBinaryPOVM P hP hPc)
      (transposePOVM
        (dSVGlobalProjectorBinaryPOVM R hR hRc)) =
      (∑ k : Fin N, (Matrix.trace (P k * R k)).re) /
        ((d : ℝ) * (N : ℝ)) := by
  simpa [dSVUniformDensityThresholdSharedDensity,
    dSVUniformDensityThresholdSharedState] using
    dSVActualGlobalMixedBornSuccess_eq
      (fun _ : Fin N => (1 : ℝ))
      ⟨0, grid⟩ ⟨0, dimension⟩ (by norm_num)
      P R hP hPc hR hRc hPP hRR

theorem dSVUniformDensityThresholdShared_diagonalBorn_eq
    {N d : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (P : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hP : ∀ k, (P k).PosSemidef)
    (hPc : ∀ k, (1 - P k).PosSemidef)
    (hPP : ∀ k, P k * P k = P k) :
    binaryJointSuccessProbability
      (dSVUniformDensityThresholdSharedDensity
        grid dimension)
      (dSVGlobalProjectorBinaryPOVM P hP hPc)
      (transposePOVM
        (dSVGlobalProjectorBinaryPOVM P hP hPc)) =
      (∑ k : Fin N, (Matrix.trace (P k)).re) /
        ((d : ℝ) * (N : ℝ)) := by
  rw [dSVUniformDensityThresholdShared_mixedBorn_eq
    grid dimension P P hP hPc hP hPc hPP hPP]
  simp_rw [hPP]

abbrev DSVUniformDensityIndependentHistoryLocalIndex
    (L N d : ℕ) :=
  Fin L → DSVUniformDensityThresholdLocalIndex N d

def dSVUniformDensityIndependentHistoryPairReindex
    (L N d : ℕ) :
    EuclideanSpace ℂ
      (Fin L →
        (DSVUniformDensityThresholdLocalIndex N d ×
          DSVUniformDensityThresholdLocalIndex N d)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ
        (DSVUniformDensityIndependentHistoryLocalIndex
            L N d ×
          DSVUniformDensityIndependentHistoryLocalIndex
            L N d) := by
  classical
  exact LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    bilateralWorkPairEquiv.symm

def dSVUniformDensityIndependentSharedState
    (L N d : ℕ) :
    EuclideanSpace ℂ
      (DSVUniformDensityIndependentHistoryLocalIndex L N d ×
        DSVUniformDensityIndependentHistoryLocalIndex L N d) :=
  dSVUniformDensityIndependentHistoryPairReindex L N d
    (finiteTensorVector
      (fun _ : Fin L =>
        dSVUniformDensityThresholdSharedState N d))

theorem dSVUniformDensityIndependentSharedState_apply
    (L N d : ℕ)
    (alice bob :
      DSVUniformDensityIndependentHistoryLocalIndex L N d) :
    dSVUniformDensityIndependentSharedState L N d
        (alice, bob) =
      ∏ j : Fin L,
        dSVUniformDensityThresholdSharedState N d
          (alice j, bob j) := by
  simp [dSVUniformDensityIndependentSharedState,
    dSVUniformDensityIndependentHistoryPairReindex,
    LinearIsometryEquiv.piLpCongrLeft_apply,
    finiteTensorVector,
    bilateralWorkPairEquiv]

theorem dSVUniformDensityIndependentSharedState_norm
    (L : ℕ) {N d : ℕ}
    (grid : 0 < N) (dimension : 0 < d) :
    ‖dSVUniformDensityIndependentSharedState L N d‖ = 1 := by
  unfold dSVUniformDensityIndependentSharedState
  rw [LinearIsometryEquiv.norm_map]
  exact finiteTensorVector_norm
    (fun _ : Fin L =>
      dSVUniformDensityThresholdSharedState N d)
    (fun _ =>
      dSVUniformDensityThresholdSharedState_norm
        grid dimension)

end

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
set_option maxRecDepth 3072

def dSVUniformDensitySpectralAtomDiscrepancy
    {d : ℕ} (ξ ζ : BipartiteUnitVector d) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d,
    |targetCanonicalSchmidtCoefficient ξ i ^ 2 -
      targetCanonicalSchmidtCoefficient ζ j ^ 2| *
      spectralAtomOverlap
        (targetReducedDensity ξ)
        (targetReducedDensity ζ)
        (targetReducedDensity_posSemidef ξ)
        (targetReducedDensity_posSemidef ζ) i j

def dSVUniformDensitySchmidtSumMass
    {d : ℕ} (ξ ζ : BipartiteUnitVector d) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d,
    (targetCanonicalSchmidtCoefficient ξ i +
      targetCanonicalSchmidtCoefficient ζ j) ^ 2 *
      spectralAtomOverlap
        (targetReducedDensity ξ)
        (targetReducedDensity ζ)
        (targetReducedDensity_posSemidef ξ)
        (targetReducedDensity_posSemidef ζ) i j

theorem dSVUniformDensitySchmidtSumMass_le_four
    {d : ℕ} (ξ ζ : BipartiteUnitVector d) :
    dSVUniformDensitySchmidtSumMass ξ ζ ≤ 4 := by
  let F := targetReducedDensity ξ
  let G := targetReducedDensity ζ
  let hF : F.PosSemidef := targetReducedDensity_posSemidef ξ
  let hG : G.PosSemidef := targetReducedDensity_posSemidef ζ
  let σ := targetCanonicalSchmidtCoefficient ξ
  let μ := targetCanonicalSchmidtCoefficient ζ
  let overlap := spectralAtomOverlap F G hF hG
  have left :
      (∑ i : Fin d, ∑ j : Fin d,
        σ i ^ 2 * overlap i j) = 1 := by
    calc
      _ = ∑ i : Fin d, σ i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.mul_sum,
          spectralAtomOverlap_sum_right F G hF hG i]
        simp
      _ = 1 := targetCanonicalSchmidtCoefficient_sq_sum ξ
  have right :
      (∑ i : Fin d, ∑ j : Fin d,
        μ j ^ 2 * overlap i j) = 1 := by
    rw [Finset.sum_comm]
    calc
      (∑ j : Fin d, ∑ i : Fin d,
        μ j ^ 2 * overlap i j) =
          ∑ j : Fin d, μ j ^ 2 := by
            apply Finset.sum_congr rfl
            intro j _
            rw [← Finset.mul_sum,
              spectralAtomOverlap_sum_left F G hF hG j]
            simp
      _ = 1 := targetCanonicalSchmidtCoefficient_sq_sum ζ
  have cross :
      (∑ i : Fin d, ∑ j : Fin d,
        σ i * μ j * overlap i j) ≤ 1 := by
    exact spectralAtomOverlap_schmidtMass_le_one
      F G hF hG (targetReducedDensity_trace ξ)
      (targetReducedDensity_trace ζ)
  have split :
      dSVUniformDensitySchmidtSumMass ξ ζ =
        (∑ i : Fin d, ∑ j : Fin d,
          σ i ^ 2 * overlap i j) +
        (∑ i : Fin d, ∑ j : Fin d,
          μ j ^ 2 * overlap i j) +
        2 * (∑ i : Fin d, ∑ j : Fin d,
          σ i * μ j * overlap i j) := by
    unfold dSVUniformDensitySchmidtSumMass
    change
      (∑ i : Fin d, ∑ j : Fin d,
        (σ i + μ j) ^ 2 * overlap i j) = _
    simp_rw [Finset.mul_sum]
    simp_rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [split, left, right]
  nlinarith

theorem dSVUniformDensitySpectralAtomDiscrepancy_le
    {d : ℕ} (ξ ζ : BipartiteUnitVector d) :
    dSVUniformDensitySpectralAtomDiscrepancy ξ ζ ≤
      2 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ := by
  let F := targetReducedDensity ξ
  let G := targetReducedDensity ζ
  let hF : F.PosSemidef := targetReducedDensity_posSemidef ξ
  let hG : G.PosSemidef := targetReducedDensity_posSemidef ζ
  let σ := targetCanonicalSchmidtCoefficient ξ
  let μ := targetCanonicalSchmidtCoefficient ζ
  let weight : Fin d × Fin d → ℝ := fun ij =>
    spectralAtomOverlap F G hF hG ij.1 ij.2
  let f : Fin d × Fin d → ℝ := fun ij =>
    |σ ij.1 - μ ij.2|
  let g : Fin d × Fin d → ℝ := fun ij =>
    σ ij.1 + μ ij.2
  have hweight : ∀ ij, 0 ≤ weight ij := fun ij =>
    spectralAtomOverlap_nonneg F G hF hG ij.1 ij.2
  have cauchy := weighted_real_cauchy weight f g hweight
  have exact_l1 :
      (∑ ij : Fin d × Fin d, weight ij * f ij * g ij) =
        dSVUniformDensitySpectralAtomDiscrepancy ξ ζ := by
    rw [Fintype.sum_prod_type]
    unfold dSVUniformDensitySpectralAtomDiscrepancy
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have sum_nonnegative : 0 ≤ σ i + μ j :=
      add_nonneg
        (targetCanonicalSchmidtCoefficient_nonneg ξ i)
        (targetCanonicalSchmidtCoefficient_nonneg ζ j)
    have factor : σ i ^ 2 - μ j ^ 2 =
        (σ i - μ j) * (σ i + μ j) := by ring
    rw [factor, abs_mul, abs_of_nonneg sum_nonnegative]
    dsimp [weight, f, g, F, G, hF, hG, σ, μ]
    ring
  have exact_energy :
      (∑ ij : Fin d × Fin d, weight ij * f ij ^ 2) =
        targetCanonicalSpectralEnergy ξ ζ := by
    rw [Fintype.sum_prod_type]
    unfold targetCanonicalSpectralEnergy
    dsimp [weight, f, F, G, hF, hG, σ, μ,
      targetCanonicalSchmidtCoefficient]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [sq_abs]
    ring
  have exact_mass :
      (∑ ij : Fin d × Fin d, weight ij * g ij ^ 2) =
        dSVUniformDensitySchmidtSumMass ξ ζ := by
    rw [Fintype.sum_prod_type]
    unfold dSVUniformDensitySchmidtSumMass
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp [weight, g, F, G, hF, hG, σ, μ]
    ring
  rw [exact_l1, exact_energy, exact_mass] at cauchy
  have target_energy := targetCanonicalSpectralEnergy_le ξ ζ
  have sum_mass := dSVUniformDensitySchmidtSumMass_le_four ξ ζ
  have first :
      Real.sqrt (targetCanonicalSpectralEnergy ξ ζ) ≤
        Real.sqrt 2 * ‖ξ.val - ζ.val‖ := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have square_two : Real.sqrt (2 : ℝ) ^ 2 = 2 :=
        Real.sq_sqrt (by norm_num)
      nlinarith [sq_nonneg ‖ξ.val - ζ.val‖]
  have second :
      Real.sqrt (dSVUniformDensitySchmidtSumMass ξ ζ) ≤ 2 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · nlinarith
  calc
    _ ≤ Real.sqrt (targetCanonicalSpectralEnergy ξ ζ) *
        Real.sqrt (dSVUniformDensitySchmidtSumMass ξ ζ) :=
      cauchy
    _ ≤ (Real.sqrt 2 * ‖ξ.val - ζ.val‖) * 2 :=
      mul_le_mul first second
        (Real.sqrt_nonneg _) (by positivity)
    _ = 2 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ := by ring

end

noncomputable section

open scoped BigOperators

namespace ClassicalSampling

variable {α : Type*} [Fintype α] [DecidableEq α]

def markedFirst (rank : α ≃ Fin (Fintype.card α))
    (marked : Finset α) (nonempty : marked.Nonempty)
    (permutation : Equiv.Perm α) : α :=
  permutation.symm
    (rank.symm
      ((marked.image (fun a => rank (permutation a))).min'
        (nonempty.image (fun a => rank (permutation a)))))

omit [DecidableEq α] in

theorem markedFirst_mem (rank : α ≃ Fin (Fintype.card α))
    (marked : Finset α) (nonempty : marked.Nonempty)
    (permutation : Equiv.Perm α) :
    markedFirst rank marked nonempty permutation ∈ marked := by
  have hmin := (marked.image (fun a => rank (permutation a))).min'_mem
    (nonempty.image (fun a => rank (permutation a)))
  obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hmin
  simpa [markedFirst, ← heq] using ha

omit [DecidableEq α] in

theorem markedFirst_rank (rank : α ≃ Fin (Fintype.card α))
    (marked : Finset α) (nonempty : marked.Nonempty)
    (permutation : Equiv.Perm α) :
    rank (permutation (markedFirst rank marked nonempty permutation)) =
      (marked.image (fun a => rank (permutation a))).min'
        (nonempty.image (fun a => rank (permutation a))) := by
  simp [markedFirst]

omit [DecidableEq α] in

theorem markedFirst_rank_le (rank : α ≃ Fin (Fintype.card α))
    (marked : Finset α) (nonempty : marked.Nonempty)
    (permutation : Equiv.Perm α) {a : α} (ha : a ∈ marked) :
    rank (permutation (markedFirst rank marked nonempty permutation)) ≤
      rank (permutation a) := by
  rw [markedFirst_rank]
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)

omit [DecidableEq α] in

theorem markedFirst_eq_of_mem_of_rank_le
    (rank : α ≃ Fin (Fintype.card α))
    (marked : Finset α) (nonempty : marked.Nonempty)
    (permutation : Equiv.Perm α) {a : α} (ha : a ∈ marked)
    (hle : ∀ b ∈ marked, rank (permutation a) ≤ rank (permutation b)) :
    markedFirst rank marked nonempty permutation = a := by
  apply permutation.injective
  apply rank.injective
  exact le_antisymm
    (markedFirst_rank_le rank marked nonempty permutation ha)
    (hle _ (markedFirst_mem rank marked nonempty permutation))

omit [DecidableEq α] in

theorem markedFirst_subset_eq_of_mem
    (rank : α ≃ Fin (Fintype.card α))
    {small large : Finset α}
    (hsmall : small.Nonempty) (hlarge : large.Nonempty)
    (permutation : Equiv.Perm α)
    (hsub : small ⊆ large)
    (hmem : markedFirst rank large hlarge permutation ∈ small) :
    markedFirst rank small hsmall permutation =
      markedFirst rank large hlarge permutation := by
  apply markedFirst_eq_of_mem_of_rank_le rank small hsmall permutation hmem
  intro a ha
  exact markedFirst_rank_le rank large hlarge permutation (hsub ha)

theorem markedFirst_eq_iff_union_first_mem_inter
    (rank : α ≃ Fin (Fintype.card α))
    (left right : Finset α)
    (hleft : left.Nonempty) (hright : right.Nonempty)
    (permutation : Equiv.Perm α) :
    markedFirst rank left hleft permutation =
        markedFirst rank right hright permutation ↔
      markedFirst rank (left ∪ right) (hleft.mono Finset.subset_union_left)
          permutation ∈ left ∩ right := by
  let hunion : (left ∪ right).Nonempty :=
    hleft.mono Finset.subset_union_left
  constructor
  · intro hagree
    have hfirst :
        markedFirst rank (left ∪ right) hunion permutation =
          markedFirst rank left hleft permutation := by
      apply markedFirst_eq_of_mem_of_rank_le
        rank (left ∪ right) hunion permutation
      · exact Finset.mem_union_left right
          (markedFirst_mem rank left hleft permutation)
      · intro a ha
        rcases Finset.mem_union.mp ha with ha | ha
        · exact markedFirst_rank_le rank left hleft permutation ha
        · rw [hagree]
          exact markedFirst_rank_le rank right hright permutation ha
    apply Finset.mem_inter.mpr
    constructor
    · rw [hfirst]
      exact markedFirst_mem rank left hleft permutation
    · rw [hfirst, hagree]
      exact markedFirst_mem rank right hright permutation
  · intro hcommon
    have hleft' := markedFirst_subset_eq_of_mem
      rank hleft hunion permutation Finset.subset_union_left
      (Finset.mem_inter.mp hcommon).1
    have hright' := markedFirst_subset_eq_of_mem
      rank hright hunion permutation Finset.subset_union_right
      (Finset.mem_inter.mp hcommon).2
    exact hleft'.trans hright'.symm

theorem markedFirst_ne_iff_union_first_mem_symmDiff
    (rank : α ≃ Fin (Fintype.card α))
    (left right : Finset α)
    (hleft : left.Nonempty) (hright : right.Nonempty)
    (permutation : Equiv.Perm α) :
    markedFirst rank left hleft permutation ≠
        markedFirst rank right hright permutation ↔
      markedFirst rank (left ∪ right) (hleft.mono Finset.subset_union_left)
          permutation ∈ (left \ right) ∪ (right \ left) := by
  let hunion : (left ∪ right).Nonempty :=
    hleft.mono Finset.subset_union_left
  let a := markedFirst rank (left ∪ right) hunion permutation
  have ha : a ∈ left ∪ right :=
    markedFirst_mem rank (left ∪ right) hunion permutation
  have hagree := markedFirst_eq_iff_union_first_mem_inter
    rank left right hleft hright permutation
  change markedFirst rank left hleft permutation ≠
      markedFirst rank right hright permutation ↔
    a ∈ (left \ right) ∪ (right \ left)
  constructor
  · intro hne
    have hninter : a ∉ left ∩ right := by
      intro hinter
      exact hne (hagree.mpr hinter)
    rcases Finset.mem_union.mp ha with hla | hra
    · apply Finset.mem_union_left
      exact Finset.mem_sdiff.mpr
        ⟨hla, fun hright' => hninter (Finset.mem_inter.mpr ⟨hla, hright'⟩)⟩
    · apply Finset.mem_union_right
      exact Finset.mem_sdiff.mpr
        ⟨hra, fun hleft' => hninter (Finset.mem_inter.mpr ⟨hleft', hra⟩)⟩
  · intro hdiff heq
    have hinter : a ∈ left ∩ right := hagree.mp heq
    rcases Finset.mem_union.mp hdiff with hdiff | hdiff
    · exact (Finset.mem_sdiff.mp hdiff).2 (Finset.mem_inter.mp hinter).2
    · exact (Finset.mem_sdiff.mp hdiff).2 (Finset.mem_inter.mp hinter).1

omit [Fintype α] in

theorem swap_mem_iff_of_mem {marked : Finset α} {x y : α}
    (hx : x ∈ marked) (hy : y ∈ marked) (a : α) :
    Equiv.swap x y a ∈ marked ↔ a ∈ marked := by
  by_cases hax : a = x
  · subst a
    simp [hx, hy]
  · by_cases hay : a = y
    · subst a
      simp [hx, hy]
    · rw [Equiv.swap_apply_of_ne_of_ne hax hay]

theorem markedFirst_swap_trans
    (rank : α ≃ Fin (Fintype.card α))
    (marked : Finset α) (nonempty : marked.Nonempty)
    {x y : α} (hx : x ∈ marked) (hy : y ∈ marked)
    (permutation : Equiv.Perm α) :
    markedFirst rank marked nonempty ((Equiv.swap x y).trans permutation) =
      Equiv.swap x y (markedFirst rank marked nonempty permutation) := by
  apply markedFirst_eq_of_mem_of_rank_le
    rank marked nonempty ((Equiv.swap x y).trans permutation)
  · exact (swap_mem_iff_of_mem hx hy _).mpr
      (markedFirst_mem rank marked nonempty permutation)
  · intro a ha
    have hminimal := markedFirst_rank_le rank marked nonempty permutation
      ((swap_mem_iff_of_mem hx hy a).mpr ha)
    simpa [Equiv.trans_apply] using hminimal

def firstFiber (rank : α ≃ Fin (Fintype.card α))
    (marked : Finset α) (nonempty : marked.Nonempty)
    (a : α) : Finset (Equiv.Perm α) :=
  Finset.univ.filter fun permutation =>
    markedFirst rank marked nonempty permutation = a

theorem firstFiber_card_eq
    (rank : α ≃ Fin (Fintype.card α))
    (marked : Finset α) (nonempty : marked.Nonempty)
    {x y : α} (hx : x ∈ marked) (hy : y ∈ marked) :
    (firstFiber rank marked nonempty x).card =
      (firstFiber rank marked nonempty y).card := by
  classical
  refine Finset.card_bij'
    (fun permutation _ => (Equiv.swap x y).trans permutation)
    (fun permutation _ => (Equiv.swap x y).trans permutation)
    ?_ ?_ ?_ ?_
  · intro permutation hpermutation
    have hfirst : markedFirst rank marked nonempty permutation = x :=
      (Finset.mem_filter.mp hpermutation).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [markedFirst_swap_trans rank marked nonempty hx hy permutation,
      hfirst, Equiv.swap_apply_left]
  · intro permutation hpermutation
    have hfirst : markedFirst rank marked nonempty permutation = y :=
      (Finset.mem_filter.mp hpermutation).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [markedFirst_swap_trans rank marked nonempty hx hy permutation,
      hfirst, Equiv.swap_apply_right]
  · intro permutation _
    ext a
    simp [Equiv.trans_apply]
  · intro permutation _
    ext a
    simp [Equiv.trans_apply]

theorem markedFirst_event_card_mul
    (rank : α ≃ Fin (Fintype.card α))
    (marked : Finset α) (nonempty : marked.Nonempty)
    (event : Finset α) (hevent : event ⊆ marked) :
    (Finset.univ.filter fun permutation : Equiv.Perm α =>
        markedFirst rank marked nonempty permutation ∈ event).card *
        marked.card =
      event.card * Fintype.card (Equiv.Perm α) := by
  classical
  obtain ⟨base, hbase⟩ := nonempty
  have hevent_card :
      (Finset.univ.filter fun permutation : Equiv.Perm α =>
          markedFirst rank marked ⟨base, hbase⟩ permutation ∈ event).card =
        event.card * (firstFiber rank marked ⟨base, hbase⟩ base).card := by
    calc
      (Finset.univ.filter fun permutation : Equiv.Perm α =>
          markedFirst rank marked ⟨base, hbase⟩ permutation ∈ event).card =
          ∑ a ∈ event,
            (firstFiber rank marked ⟨base, hbase⟩ a).card := by
              symm
              simpa [firstFiber] using
                (Finset.sum_card_fiberwise_eq_card_filter
                  (Finset.univ : Finset (Equiv.Perm α)) event
                  (markedFirst rank marked ⟨base, hbase⟩))
      _ = event.card * (firstFiber rank marked ⟨base, hbase⟩ base).card :=
        Finset.sum_const_nat fun a ha =>
          firstFiber_card_eq rank marked ⟨base, hbase⟩ (hevent ha) hbase
  have htotal_card :
      Fintype.card (Equiv.Perm α) =
        marked.card * (firstFiber rank marked ⟨base, hbase⟩ base).card := by
    calc
      Fintype.card (Equiv.Perm α) =
          (Finset.univ : Finset (Equiv.Perm α)).card := by simp
      _ = ∑ a ∈ marked,
            (firstFiber rank marked ⟨base, hbase⟩ a).card := by
              simpa [firstFiber] using
                (Finset.card_eq_sum_card_fiberwise
                  (f := markedFirst rank marked ⟨base, hbase⟩)
                  (s := (Finset.univ : Finset (Equiv.Perm α)))
                  (t := marked)
                  (fun permutation _ =>
                    markedFirst_mem rank marked ⟨base, hbase⟩ permutation))
      _ = marked.card * (firstFiber rank marked ⟨base, hbase⟩ base).card :=
        Finset.sum_const_nat fun a ha =>
          firstFiber_card_eq rank marked ⟨base, hbase⟩ ha hbase
  change
    (Finset.univ.filter fun permutation : Equiv.Perm α =>
        markedFirst rank marked ⟨base, hbase⟩ permutation ∈ event).card *
        marked.card =
      event.card * Fintype.card (Equiv.Perm α)
  rw [hevent_card, htotal_card]
  ac_rfl

theorem sharedPermutation_disagreement_card_mul
    (rank : α ≃ Fin (Fintype.card α))
    (left right : Finset α)
    (hleft : left.Nonempty) (hright : right.Nonempty) :
    (Finset.univ.filter fun permutation : Equiv.Perm α =>
        markedFirst rank left hleft permutation ≠
          markedFirst rank right hright permutation).card *
        (left ∪ right).card =
      ((left \ right) ∪ (right \ left)).card *
        Fintype.card (Equiv.Perm α) := by
  classical
  let hunion : (left ∪ right).Nonempty :=
    hleft.mono Finset.subset_union_left
  have hsubset : (left \ right) ∪ (right \ left) ⊆ left ∪ right := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact Finset.mem_union_left right (Finset.mem_sdiff.mp ha).1
    · exact Finset.mem_union_right left (Finset.mem_sdiff.mp ha).1
  have hfilter :
      (Finset.univ.filter fun permutation : Equiv.Perm α =>
        markedFirst rank left hleft permutation ≠
          markedFirst rank right hright permutation) =
      (Finset.univ.filter fun permutation : Equiv.Perm α =>
        markedFirst rank (left ∪ right) hunion permutation ∈
          (left \ right) ∪ (right \ left)) := by
    ext permutation
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact markedFirst_ne_iff_union_first_mem_symmDiff
      rank left right hleft hright permutation
  rw [hfilter]
  exact markedFirst_event_card_mul rank (left ∪ right) hunion
    ((left \ right) ∪ (right \ left)) hsubset

def uniformPermutationProbability (event : Equiv.Perm α → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter fun permutation : Equiv.Perm α =>
      event permutation).card : ℝ) / Fintype.card (Equiv.Perm α)

theorem markedFirst_event_probability
    (rank : α ≃ Fin (Fintype.card α))
    (marked : Finset α) (nonempty : marked.Nonempty)
    (event : Finset α) (hevent : event ⊆ marked) :
    uniformPermutationProbability
      (fun permutation : Equiv.Perm α =>
        markedFirst rank marked nonempty permutation ∈ event) =
      (event.card : ℝ) / marked.card := by
  classical
  have hpermutation : 0 < (Fintype.card (Equiv.Perm α) : ℝ) := by
    exact_mod_cast
      (Fintype.card_pos_iff.mpr ⟨Equiv.refl α⟩ :
        0 < Fintype.card (Equiv.Perm α))
  have hmarked : 0 < (marked.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr nonempty : 0 < marked.card)
  unfold uniformPermutationProbability
  apply (div_eq_div_iff hpermutation.ne' hmarked.ne').mpr
  have hcount := markedFirst_event_card_mul
    rank marked nonempty event hevent
  have hreal :
      ((Finset.univ.filter fun permutation : Equiv.Perm α =>
        markedFirst rank marked nonempty permutation ∈ event).card : ℝ) *
          (marked.card : ℝ) =
        (event.card : ℝ) * (Fintype.card (Equiv.Perm α) : ℝ) := by
    exact_mod_cast hcount
  simpa only [] using hreal

theorem sharedPermutation_disagreement_probability
    (rank : α ≃ Fin (Fintype.card α))
    (left right : Finset α)
    (hleft : left.Nonempty) (hright : right.Nonempty) :
    uniformPermutationProbability
      (fun permutation : Equiv.Perm α =>
        markedFirst rank left hleft permutation ≠
          markedFirst rank right hright permutation) =
      (((left \ right) ∪ (right \ left)).card : ℝ) /
        (left ∪ right).card := by
  classical
  have hpermutation : 0 < (Fintype.card (Equiv.Perm α) : ℝ) := by
    exact_mod_cast
      (Fintype.card_pos_iff.mpr ⟨Equiv.refl α⟩ :
        0 < Fintype.card (Equiv.Perm α))
  have hunion : 0 < ((left ∪ right).card : ℝ) := by
    exact_mod_cast
      (Finset.card_pos.mpr
        (hleft.mono Finset.subset_union_left) :
        0 < (left ∪ right).card)
  unfold uniformPermutationProbability
  apply (div_eq_div_iff hpermutation.ne' hunion.ne').mpr
  exact_mod_cast
    sharedPermutation_disagreement_card_mul rank left right hleft hright

theorem sharedPermutation_disagreement_probability_le
    (rank : α ≃ Fin (Fintype.card α))
    (left right : Finset α)
    (hleft : left.Nonempty) (hright : right.Nonempty) :
    uniformPermutationProbability
      (fun permutation : Equiv.Perm α =>
        markedFirst rank left hleft permutation ≠
          markedFirst rank right hright permutation) ≤
      (((left \ right) ∪ (right \ left)).card : ℝ) / left.card := by
  rw [sharedPermutation_disagreement_probability
    rank left right hleft hright]
  apply div_le_div_of_nonneg_left
  · positivity
  · exact_mod_cast (Finset.card_pos.mpr hleft : 0 < left.card)
  · exact_mod_cast (Finset.card_le_card Finset.subset_union_left :
      left.card ≤ (left ∪ right).card)

def markedTotalVariation (left right : Finset α) : ℝ :=
  (((left \ right) ∪ (right \ left)).card : ℝ) /
    (2 * (left.card : ℝ))

theorem sharedPermutation_disagreement_probability_le_two_mul_tv
    (rank : α ≃ Fin (Fintype.card α))
    (left right : Finset α)
    (hleft : left.Nonempty) (hright : right.Nonempty)
    (_equal_card : left.card = right.card) :
    uniformPermutationProbability
      (fun permutation : Equiv.Perm α =>
        markedFirst rank left hleft permutation ≠
          markedFirst rank right hright permutation) ≤
      2 * markedTotalVariation left right := by
  calc
    uniformPermutationProbability
        (fun permutation : Equiv.Perm α =>
          markedFirst rank left hleft permutation ≠
            markedFirst rank right hright permutation) ≤
        (((left \ right) ∪ (right \ left)).card : ℝ) / left.card :=
      sharedPermutation_disagreement_probability_le
        rank left right hleft hright
    _ = 2 * markedTotalVariation left right := by
      unfold markedTotalVariation
      have hcard : (left.card : ℝ) ≠ 0 := by
        exact_mod_cast (Finset.card_ne_zero.mpr hleft)
      field_simp

section RationalMarks

variable {β : Type*} [Fintype β] [DecidableEq β]

def rationalMarked (denominator : ℕ) (numerator : β → ℕ) :
    Finset (β × Fin denominator) := by
  classical
  exact Finset.univ.filter fun point =>
    point.2.val < numerator point.1

theorem rationalMarked_fiber_card
    (denominator : ℕ) (numerator : β → ℕ) (letter : β) :
    ((rationalMarked denominator numerator).filter
      fun point => point.1 = letter).card =
        min denominator (numerator letter) := by
  classical
  calc
    ((rationalMarked denominator numerator).filter
      fun point => point.1 = letter).card =
        (Finset.univ.filter fun copy : Fin denominator =>
          copy.val < numerator letter).card := by
      refine Finset.card_bij'
        (fun point _ => point.2)
        (fun copy _ => (letter, copy))
        ?_ ?_ ?_ ?_
      · intro point hpoint
        have hpoint' :
            point.2.val < numerator point.1 ∧ point.1 = letter := by
          simpa [rationalMarked] using hpoint
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, by simpa [hpoint'.2] using hpoint'.1⟩
      · intro copy hcopy
        have hcopy' : copy.val < numerator letter :=
          (Finset.mem_filter.mp hcopy).2
        simp [rationalMarked, hcopy']
      · intro point hpoint
        have hletter : point.1 = letter :=
          (Finset.mem_filter.mp hpoint).2
        apply Prod.ext
        · exact hletter.symm
        · rfl
      · intro copy _
        rfl
    _ = min denominator (numerator letter) := by
      simpa using
        (Fin.card_filter_val_lt (n := denominator)
          (m := numerator letter))

omit [DecidableEq β] in

theorem rationalNumerator_le_denominator
    (denominator : ℕ) (numerator : β → ℕ)
    (normalized : (∑ letter, numerator letter) = denominator)
    (letter : β) : numerator letter ≤ denominator := by
  rw [← normalized]
  exact Finset.single_le_sum
    (fun a _ => Nat.zero_le (numerator a)) (Finset.mem_univ letter)

theorem rationalMarked_card
    (denominator : ℕ) (numerator : β → ℕ)
    (normalized : (∑ letter, numerator letter) = denominator) :
    (rationalMarked denominator numerator).card = denominator := by
  classical
  calc
    (rationalMarked denominator numerator).card =
        ∑ letter : β,
          ((rationalMarked denominator numerator).filter
            fun point => point.1 = letter).card := by
      simpa using
        (Finset.card_eq_sum_card_fiberwise
          (f := fun point : β × Fin denominator => point.1)
          (s := rationalMarked denominator numerator)
          (t := (Finset.univ : Finset β))
          (fun _ _ => Finset.mem_univ _))
    _ = ∑ letter : β, numerator letter := by
      apply Finset.sum_congr rfl
      intro letter _
      rw [rationalMarked_fiber_card]
      exact min_eq_right
        (rationalNumerator_le_denominator denominator numerator normalized letter)
    _ = denominator := normalized

theorem rationalMarked_nonempty
    (denominator : ℕ) (numerator : β → ℕ)
    (normalized : (∑ letter, numerator letter) = denominator)
    (positive : 0 < denominator) :
    (rationalMarked denominator numerator).Nonempty := by
  apply Finset.card_pos.mp
  rw [rationalMarked_card denominator numerator normalized]
  exact positive

theorem rationalMarked_letter_probability
    (denominator : ℕ) (numerator : β → ℕ)
    (normalized : (∑ letter, numerator letter) = denominator)
    (nonempty : (rationalMarked denominator numerator).Nonempty)
    (rank : (β × Fin denominator) ≃
      Fin (Fintype.card (β × Fin denominator)))
    (letter : β) :
    uniformPermutationProbability
      (fun permutation : Equiv.Perm (β × Fin denominator) =>
        (markedFirst rank (rationalMarked denominator numerator)
          nonempty permutation).1 = letter) =
      (numerator letter : ℝ) / denominator := by
  classical
  let marked := rationalMarked denominator numerator
  let event := marked.filter fun point => point.1 = letter
  have hsub : event ⊆ marked := Finset.filter_subset _ _
  calc
    uniformPermutationProbability
        (fun permutation : Equiv.Perm (β × Fin denominator) =>
          (markedFirst rank marked nonempty permutation).1 = letter) =
        uniformPermutationProbability
          (fun permutation : Equiv.Perm (β × Fin denominator) =>
            markedFirst rank marked nonempty permutation ∈ event) := by
      congr 1
      funext permutation
      apply propext
      simp [event, markedFirst_mem rank marked nonempty permutation]
    _ = (event.card : ℝ) / marked.card :=
      markedFirst_event_probability rank marked nonempty event hsub
    _ = (numerator letter : ℝ) / denominator := by
      change
        (((rationalMarked denominator numerator).filter
          fun point => point.1 = letter).card : ℝ) /
          (rationalMarked denominator numerator).card =
        (numerator letter : ℝ) / denominator
      rw [rationalMarked_fiber_card,
        min_eq_right
          (rationalNumerator_le_denominator
            denominator numerator normalized letter),
        rationalMarked_card denominator numerator normalized]

end RationalMarks

end ClassicalSampling

namespace Pinsker

theorem centered_log_lower_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    2 * (x - 1) / (x + 1) ≤ Real.log x := by
  have hden : 0 < x + 1 := by linarith
  let t : ℝ := (x - 1) / (x + 1)
  have ht0 : 0 ≤ t := by
    exact div_nonneg (sub_nonneg.mpr hx) hden.le
  have ht1 : t < 1 := by
    apply (div_lt_one hden).mpr
    linarith
  have hratio : (1 + t) / (1 - t) = x := by
    dsimp [t]
    field_simp
    ring
  have hseries :
      t ≤ (1 / 2 : ℝ) * Real.log ((1 + t) / (1 - t)) := by
    simpa using (Real.sum_range_le_log_div ht0 ht1 1)
  rw [hratio] at hseries
  dsimp [t] at hseries
  calc
    2 * (x - 1) / (x + 1) = 2 * ((x - 1) / (x + 1)) := by ring
    _ ≤ Real.log x := by linarith

theorem centered_log_upper_of_le_one
    {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    Real.log x ≤ 2 * (x - 1) / (x + 1) := by
  have hinv : 1 ≤ (1 : ℝ) / x := by
    apply (le_div_iff₀ hx0).mpr
    simpa using hx1
  have h := centered_log_lower_of_one_le hinv
  have hratio :
      2 * ((1 : ℝ) / x - 1) / ((1 : ℝ) / x + 1) =
        -(2 * (x - 1) / (x + 1)) := by
    field_simp
    ring
  rw [hratio, Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hx0.ne',
    Real.log_one] at h
  linarith

def pinskerScalarGap (x : ℝ) : ℝ :=
  InformationTheory.klFun x - 3 * (x - 1) ^ 2 / (2 * (x + 2))

theorem hasDerivAt_pinskerScalarGap {x : ℝ} (hx : 0 < x) :
    HasDerivAt pinskerScalarGap
      (Real.log x - 3 * (x - 1) * (x + 5) / (2 * (x + 2) ^ 2)) x := by
  have hden : 2 * (x + 2) ≠ 0 := by positivity
  have hnumerator :=
    (((hasDerivAt_id x).sub_const 1).pow 2).const_mul 3
  have hdenominator :=
    ((hasDerivAt_id x).add_const 2).const_mul 2
  have hquotient := hnumerator.div hdenominator hden
  have hgap := (InformationTheory.hasDerivAt_klFun hx.ne').sub hquotient
  have hfunction :
      (InformationTheory.klFun -
        (fun y => 3 * ((fun z => id z - 1) ^ 2) y) /
          (fun y => 2 * (id y + 2))) = pinskerScalarGap := by
    funext y
    change
      InformationTheory.klFun y - 3 * (y - 1) ^ 2 / (2 * (y + 2)) =
        InformationTheory.klFun y - 3 * (y - 1) ^ 2 / (2 * (y + 2))
    rfl
  rw [hfunction] at hgap
  apply hgap.congr_deriv
  dsimp
  field_simp
  ring

theorem pinsker_rational_coefficient_le {x : ℝ} (hx : 0 < x) :
    3 * (x + 5) / (2 * (x + 2) ^ 2) ≤ 2 / (x + 1) := by
  have hleft : 0 < 2 * (x + 2) ^ 2 := by positivity
  have hright : 0 < x + 1 := by linarith
  apply (div_le_div_iff₀ hleft hright).mpr
  nlinarith [sq_nonneg (x - 1)]

theorem pinskerScalarGap_derivative_nonneg
    {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ Real.log x -
      3 * (x - 1) * (x + 5) / (2 * (x + 2) ^ 2) := by
  have hx0 : 0 < x := by linarith
  have hcoefficient := pinsker_rational_coefficient_le hx0
  have hscaled := mul_le_mul_of_nonneg_left
    hcoefficient (sub_nonneg.mpr hx)
  have hrational :
      3 * (x - 1) * (x + 5) / (2 * (x + 2) ^ 2) ≤
        2 * (x - 1) / (x + 1) := by
    calc
      3 * (x - 1) * (x + 5) / (2 * (x + 2) ^ 2) =
          (x - 1) * (3 * (x + 5) / (2 * (x + 2) ^ 2)) := by ring
      _ ≤ (x - 1) * (2 / (x + 1)) := hscaled
      _ = 2 * (x - 1) / (x + 1) := by ring
  have hlog := centered_log_lower_of_one_le hx
  linarith

theorem pinskerScalarGap_derivative_nonpos
    {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    Real.log x -
      3 * (x - 1) * (x + 5) / (2 * (x + 2) ^ 2) ≤ 0 := by
  have hcoefficient := pinsker_rational_coefficient_le hx0
  have hscaled := mul_le_mul_of_nonpos_left
    hcoefficient (sub_nonpos.mpr hx1)
  have hrational :
      2 * (x - 1) / (x + 1) ≤
        3 * (x - 1) * (x + 5) / (2 * (x + 2) ^ 2) := by
    calc
      2 * (x - 1) / (x + 1) = (x - 1) * (2 / (x + 1)) := by ring
      _ ≤ (x - 1) * (3 * (x + 5) / (2 * (x + 2) ^ 2)) := hscaled
      _ = 3 * (x - 1) * (x + 5) / (2 * (x + 2) ^ 2) := by ring
  have hlog := centered_log_upper_of_le_one hx0 hx1
  linarith

theorem pinskerScalarGap_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ pinskerScalarGap x := by
  by_cases hzero : x = 0
  · subst x
    norm_num [pinskerScalarGap, InformationTheory.klFun]
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hzero)
  by_cases hone : 1 ≤ x
  · let derivative : ℝ → ℝ := fun y =>
      Real.log y - 3 * (y - 1) * (y + 5) / (2 * (y + 2) ^ 2)
    have hcontinuous : ContinuousOn pinskerScalarGap (Set.Icc 1 x) := by
      intro y hy
      have hypos : 0 < y := by
        have hyone := (Set.mem_Icc.mp hy).1
        linarith
      exact (hasDerivAt_pinskerScalarGap hypos).continuousAt.continuousWithinAt
    have hmonotone : MonotoneOn pinskerScalarGap (Set.Icc 1 x) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg
        (f' := derivative) (convex_Icc 1 x) hcontinuous
      · intro y hy
        have hymem : y ∈ Set.Icc (1 : ℝ) x := interior_subset hy
        have hypos : 0 < y := by
          have hyone := (Set.mem_Icc.mp hymem).1
          linarith
        exact (hasDerivAt_pinskerScalarGap hypos).hasDerivWithinAt
      · intro y hy
        have hymem : y ∈ Set.Icc (1 : ℝ) x := interior_subset hy
        exact pinskerScalarGap_derivative_nonneg (Set.mem_Icc.mp hymem).1
    have hbound := hmonotone
      (show (1 : ℝ) ∈ Set.Icc 1 x from ⟨le_rfl, hone⟩)
      (show x ∈ Set.Icc (1 : ℝ) x from ⟨hone, le_rfl⟩) hone
    simpa [pinskerScalarGap, InformationTheory.klFun] using hbound
  · have hxone : x ≤ 1 := le_of_not_ge hone
    let derivative : ℝ → ℝ := fun y =>
      Real.log y - 3 * (y - 1) * (y + 5) / (2 * (y + 2) ^ 2)
    have hcontinuous : ContinuousOn pinskerScalarGap (Set.Icc x 1) := by
      intro y hy
      have hypos : 0 < y :=
        hxpos.trans_le (Set.mem_Icc.mp hy).1
      exact (hasDerivAt_pinskerScalarGap hypos).continuousAt.continuousWithinAt
    have hantitone : AntitoneOn pinskerScalarGap (Set.Icc x 1) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos
        (f' := derivative) (convex_Icc x 1) hcontinuous
      · intro y hy
        have hymem : y ∈ Set.Icc x (1 : ℝ) := interior_subset hy
        have hypos : 0 < y := hxpos.trans_le (Set.mem_Icc.mp hymem).1
        exact (hasDerivAt_pinskerScalarGap hypos).hasDerivWithinAt
      · intro y hy
        have hymem : y ∈ Set.Icc x (1 : ℝ) := interior_subset hy
        have hypos : 0 < y := hxpos.trans_le (Set.mem_Icc.mp hymem).1
        exact pinskerScalarGap_derivative_nonpos
          hypos (Set.mem_Icc.mp hymem).2
    have hbound := hantitone
      (show x ∈ Set.Icc x (1 : ℝ) from ⟨le_rfl, hxone⟩)
      (show (1 : ℝ) ∈ Set.Icc x 1 from ⟨hxone, le_rfl⟩) hxone
    simpa [pinskerScalarGap, InformationTheory.klFun] using hbound

theorem quadratic_le_klFun {x : ℝ} (hx : 0 ≤ x) :
    3 * (x - 1) ^ 2 / (2 * (x + 2)) ≤ InformationTheory.klFun x := by
  have h := pinskerScalarGap_nonneg hx
  dsimp [pinskerScalarGap] at h
  linarith

def finiteRelativeEntropy {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) : ℝ :=
  ∑ i, q i * InformationTheory.klFun (p i / q i)

def finiteTotalVariation {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) : ℝ :=
  (∑ i, |p i - q i|) / 2

theorem quadratic_density_le_weighted_kl
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    3 * (p - q) ^ 2 / (2 * (p + 2 * q)) ≤
      q * InformationTheory.klFun (p / q) := by
  have hscalar := quadratic_le_klFun (div_nonneg hp hq.le)
  have hweighted := mul_le_mul_of_nonneg_left hscalar hq.le
  calc
    3 * (p - q) ^ 2 / (2 * (p + 2 * q)) =
        q * (3 * (p / q - 1) ^ 2 / (2 * (p / q + 2))) := by
      field_simp [hq.ne']
    _ ≤ q * InformationTheory.klFun (p / q) := hweighted

theorem finiteRelativeEntropy_eq_log_sum
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ)
    (hq : ∀ i, 0 < q i)
    (hp_normalized : (∑ i, p i) = 1)
    (hq_normalized : (∑ i, q i) = 1) :
    finiteRelativeEntropy p q =
      ∑ i, p i * Real.log (p i / q i) := by
  unfold finiteRelativeEntropy
  calc
    (∑ i, q i * InformationTheory.klFun (p i / q i)) =
        ∑ i, (p i * Real.log (p i / q i) + q i - p i) := by
      apply Finset.sum_congr rfl
      intro i _
      unfold InformationTheory.klFun
      field_simp [(hq i).ne']
    _ = ∑ i, p i * Real.log (p i / q i) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        hp_normalized, hq_normalized]
      ring

theorem finite_pinsker
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hq : ∀ i, 0 < q i)
    (hp_normalized : (∑ i, p i) = 1)
    (hq_normalized : (∑ i, q i) = 1) :
    2 * (finiteTotalVariation p q) ^ 2 ≤ finiteRelativeEntropy p q := by
  classical
  let weight : ι → ℝ := fun i => (p i + 2 * q i) / 3
  have hweight : ∀ i, 0 < weight i := by
    intro i
    dsimp [weight]
    have hpi := hp i
    have hqi := hq i
    positivity
  have hweight_sum : (∑ i, weight i) = 1 := by
    dsimp [weight]
    calc
      (∑ i, (p i + 2 * q i) / 3) =
          ((∑ i, p i) + 2 * (∑ i, q i)) / 3 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = 1 := by rw [hp_normalized, hq_normalized]; norm_num
  have hcauchy :
      (∑ i, |p i - q i|) ^ 2 ≤
        ∑ i, |p i - q i| ^ 2 / weight i := by
    have h := Finset.sq_sum_div_le_sum_sq_div
      (Finset.univ : Finset ι)
      (fun i => |p i - q i|)
      (g := weight)
      (fun i _ => hweight i)
    simpa [hweight_sum] using h
  have hpoint : ∀ i,
      |p i - q i| ^ 2 / weight i ≤
        2 * (q i * InformationTheory.klFun (p i / q i)) := by
    intro i
    have hdensity := quadratic_density_le_weighted_kl (hp i) (hq i)
    calc
      |p i - q i| ^ 2 / weight i =
          2 * (3 * (p i - q i) ^ 2 /
            (2 * (p i + 2 * q i))) := by
        dsimp [weight]
        rw [sq_abs]
        have hden : p i + 2 * q i ≠ 0 := by
          have hpi := hp i
          have hqi := hq i
          positivity
        field_simp [hden]
      _ ≤ 2 * (q i * InformationTheory.klFun (p i / q i)) :=
        mul_le_mul_of_nonneg_left hdensity (by norm_num)
  have hsum :
      (∑ i, |p i - q i| ^ 2 / weight i) ≤
        2 * finiteRelativeEntropy p q := by
    calc
      (∑ i, |p i - q i| ^ 2 / weight i) ≤
          ∑ i, 2 * (q i * InformationTheory.klFun (p i / q i)) :=
        Finset.sum_le_sum fun i _ => hpoint i
      _ = 2 * finiteRelativeEntropy p q := by
        unfold finiteRelativeEntropy
        rw [Finset.mul_sum]
  have hmain :
      (∑ i, |p i - q i|) ^ 2 ≤ 2 * finiteRelativeEntropy p q :=
    hcauchy.trans hsum
  unfold finiteTotalVariation
  nlinarith

theorem sum_over_positive_reference_support
    {ι : Type*} [Fintype ι]
    (q f : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i)
    (hzero : ∀ i, q i = 0 → f i = 0) :
    (∑ i : {i : ι // 0 < q i}, f i) = ∑ i, f i := by
  classical
  calc
    (∑ i : {i : ι // 0 < q i}, f i) =
        ∑ i ∈ (Finset.univ.filter fun i : ι => 0 < q i), f i := by
      simpa using
        (Finset.sum_subtype_eq_sum_filter
          (s := (Finset.univ : Finset ι))
          (p := fun i : ι => 0 < q i) f)
    _ = ∑ i, f i := by
      apply Finset.sum_filter_of_ne
      intro i _ hfi
      have hqi : q i ≠ 0 := by
        intro hqi
        exact hfi (hzero i hqi)
      exact lt_of_le_of_ne (hq i) hqi.symm

theorem finite_pinsker_of_absolute_continuity
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hq : ∀ i, 0 ≤ q i)
    (absolute_continuity : ∀ i, q i = 0 → p i = 0)
    (hp_normalized : (∑ i, p i) = 1)
    (hq_normalized : (∑ i, q i) = 1) :
    2 * (finiteTotalVariation p q) ^ 2 ≤ finiteRelativeEntropy p q := by
  classical
  let p' : {i : ι // 0 < q i} → ℝ := fun i => p i
  let q' : {i : ι // 0 < q i} → ℝ := fun i => q i
  have hp'_nonnegative : ∀ i, 0 ≤ p' i := fun i => hp i
  have hq'_positive : ∀ i, 0 < q' i := fun i => i.property
  have hp'_normalized : (∑ i, p' i) = 1 := by
    change (∑ i : {i : ι // 0 < q i}, p i) = 1
    rw [sum_over_positive_reference_support q p hq absolute_continuity,
      hp_normalized]
  have hq'_normalized : (∑ i, q' i) = 1 := by
    change (∑ i : {i : ι // 0 < q i}, q i) = 1
    rw [sum_over_positive_reference_support q q hq (fun _ h => h),
      hq_normalized]
  have htv : finiteTotalVariation p' q' = finiteTotalVariation p q := by
    unfold finiteTotalVariation
    change
      (∑ i : {i : ι // 0 < q i}, |p i - q i|) / 2 =
        (∑ i, |p i - q i|) / 2
    rw [sum_over_positive_reference_support
      q (fun i => |p i - q i|) hq]
    intro i hqi
    simp [hqi, absolute_continuity i hqi]
  have hkl : finiteRelativeEntropy p' q' = finiteRelativeEntropy p q := by
    unfold finiteRelativeEntropy
    change
      (∑ i : {i : ι // 0 < q i},
        q i * InformationTheory.klFun (p i / q i)) =
      ∑ i, q i * InformationTheory.klFun (p i / q i)
    apply sum_over_positive_reference_support
      q (fun i => q i * InformationTheory.klFun (p i / q i)) hq
    intro i hqi
    simp [hqi]
  have h := finite_pinsker p' q'
    hp'_nonnegative hq'_positive hp'_normalized hq'_normalized
  rwa [htv, hkl] at h

theorem finiteRelativeEntropy_eq_log_sum_of_absolute_continuity
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i)
    (absolute_continuity : ∀ i, q i = 0 → p i = 0)
    (hp_normalized : (∑ i, p i) = 1)
    (hq_normalized : (∑ i, q i) = 1) :
    finiteRelativeEntropy p q =
      ∑ i, p i * Real.log (p i / q i) := by
  unfold finiteRelativeEntropy
  calc
    (∑ i, q i * InformationTheory.klFun (p i / q i)) =
        ∑ i, (p i * Real.log (p i / q i) + q i - p i) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hqi : q i = 0
      · simp [hqi, absolute_continuity i hqi]
      · unfold InformationTheory.klFun
        have hqpos : 0 < q i := lt_of_le_of_ne (hq i) (Ne.symm hqi)
        field_simp [hqpos.ne']
    _ = ∑ i, p i * Real.log (p i / q i) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        hp_normalized, hq_normalized]
      ring

theorem finite_pinsker_sqrt_of_absolute_continuity
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hq : ∀ i, 0 ≤ q i)
    (absolute_continuity : ∀ i, q i = 0 → p i = 0)
    (hp_normalized : (∑ i, p i) = 1)
    (hq_normalized : (∑ i, q i) = 1) :
    finiteTotalVariation p q ≤
      Real.sqrt (finiteRelativeEntropy p q / 2) := by
  apply Real.le_sqrt_of_sq_le
  have h := finite_pinsker_of_absolute_continuity
    p q hp hq absolute_continuity hp_normalized hq_normalized
  nlinarith

end Pinsker

namespace ClassicalInformation

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def distributionFloorNumerator (denominator : ℕ) (p : ι → ℝ) : ι → ℕ :=
  fun i => Nat.floor (p i * (denominator : ℝ))

def distributionFloorResidual (denominator : ℕ) (p : ι → ℝ) : ℕ :=
  denominator - ∑ i, distributionFloorNumerator denominator p i

def distributionRoundedNumerator
    (base : ι) (denominator : ℕ) (p : ι → ℝ) : ι → ℕ :=
  fun i => distributionFloorNumerator denominator p i +
    if i = base then distributionFloorResidual denominator p else 0

def distributionFloorProbability
    (denominator : ℕ) (p : ι → ℝ) : ι → ℝ :=
  fun i => (distributionFloorNumerator denominator p i : ℝ) / denominator

def distributionRoundedProbability
    (base : ι) (denominator : ℕ) (p : ι → ℝ) : ι → ℝ :=
  fun i =>
    (distributionRoundedNumerator base denominator p i : ℝ) / denominator

omit [Fintype ι] [DecidableEq ι] in

theorem distributionFloorNumerator_cast_le
    (denominator : ℕ) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (i : ι) :
    (distributionFloorNumerator denominator p i : ℝ) ≤
      p i * denominator := by
  unfold distributionFloorNumerator
  exact Nat.floor_le (mul_nonneg (hp i) (Nat.cast_nonneg _))

omit [Fintype ι] [DecidableEq ι] in

theorem distributionFloorProbability_le
    (denominator : ℕ) (positive : 0 < denominator)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (i : ι) :
    distributionFloorProbability denominator p i ≤ p i := by
  have hden : 0 < (denominator : ℝ) := by exact_mod_cast positive
  unfold distributionFloorProbability
  apply (div_le_iff₀ hden).mpr
  exact distributionFloorNumerator_cast_le denominator p hp i

omit [Fintype ι] [DecidableEq ι] in

theorem distributionFloorProbability_error_lt
    (denominator : ℕ) (positive : 0 < denominator)
    (p : ι → ℝ) (i : ι) :
    p i - distributionFloorProbability denominator p i <
      (1 : ℝ) / denominator := by
  have hden : 0 < (denominator : ℝ) := by exact_mod_cast positive
  apply (lt_div_iff₀ hden).mpr
  have hupper := Nat.lt_floor_add_one (p i * (denominator : ℝ))
  unfold distributionFloorProbability distributionFloorNumerator
  calc
    (p i - (Nat.floor (p i * (denominator : ℝ)) : ℝ) /
        (denominator : ℝ)) * (denominator : ℝ) =
      p i * (denominator : ℝ) - Nat.floor (p i * (denominator : ℝ)) := by
        field_simp
    _ < 1 := by linarith

omit [DecidableEq ι] in

theorem distributionFloorNumerator_sum_le
    (denominator : ℕ) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (normalized : (∑ i, p i) = 1) :
    (∑ i, distributionFloorNumerator denominator p i) ≤ denominator := by
  have hreal :
      ((∑ i, distributionFloorNumerator denominator p i) : ℝ) ≤
        (denominator : ℝ) := by
    calc
      ((∑ i, distributionFloorNumerator denominator p i) : ℝ) =
          ∑ i, (distributionFloorNumerator denominator p i : ℝ) := by
        simp
      _ ≤ ∑ i, p i * (denominator : ℝ) :=
        Finset.sum_le_sum fun i _ =>
          distributionFloorNumerator_cast_le denominator p hp i
      _ = (denominator : ℝ) := by
        rw [← Finset.sum_mul, normalized]
        simp
  exact_mod_cast hreal

theorem distributionRoundedNumerator_sum
    (base : ι) (denominator : ℕ) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (normalized : (∑ i, p i) = 1) :
    (∑ i, distributionRoundedNumerator base denominator p i) =
      denominator := by
  have hfloor := distributionFloorNumerator_sum_le
    denominator p hp normalized
  unfold distributionRoundedNumerator
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  unfold distributionFloorResidual
  omega

omit [DecidableEq ι] in

theorem distributionFloorResidual_probability_eq_sum
    (denominator : ℕ) (positive : 0 < denominator)
    (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (normalized : (∑ i, p i) = 1) :
    (distributionFloorResidual denominator p : ℝ) / denominator =
      ∑ i, (p i - distributionFloorProbability denominator p i) := by
  have hfloor := distributionFloorNumerator_sum_le
    denominator p hp normalized
  have hden : (denominator : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt positive)
  unfold distributionFloorResidual distributionFloorProbability
  rw [Nat.cast_sub hfloor, Nat.cast_sum, Finset.sum_sub_distrib,
    normalized, ← Finset.sum_div]
  field_simp

theorem distributionRoundedProbability_eq_floor_add
    (base : ι) (denominator : ℕ) (p : ι → ℝ) (i : ι) :
    distributionRoundedProbability base denominator p i =
      distributionFloorProbability denominator p i +
        if i = base then
          (distributionFloorResidual denominator p : ℝ) / denominator
        else 0 := by
  by_cases hbase : i = base
  · simp [distributionRoundedProbability,
      distributionRoundedNumerator, distributionFloorProbability,
      hbase, Nat.cast_add]
    ring
  · simp [distributionRoundedProbability,
      distributionRoundedNumerator, distributionFloorProbability, hbase]

theorem distributionRoundedProbability_totalVariation_le
    (base : ι) (denominator : ℕ) (positive : 0 < denominator)
    (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (normalized : (∑ i, p i) = 1) :
    finiteTotalVariation p
        (distributionRoundedProbability base denominator p) ≤
      (Fintype.card ι : ℝ) / denominator := by
  have hden : 0 < (denominator : ℝ) := by exact_mod_cast positive
  have hres :
      0 ≤ (distributionFloorResidual denominator p : ℝ) / denominator :=
    div_nonneg (Nat.cast_nonneg _) hden.le
  have hpoint : ∀ i,
      |p i - distributionRoundedProbability base denominator p i| ≤
        (p i - distributionFloorProbability denominator p i) +
          if i = base then
            (distributionFloorResidual denominator p : ℝ) / denominator
          else 0 := by
    intro i
    have hdefect :
        0 ≤ p i - distributionFloorProbability denominator p i :=
      sub_nonneg.mpr
        (distributionFloorProbability_le denominator positive p hp i)
    have htriangle := abs_sub_le (p i)
      (distributionFloorProbability denominator p i)
      (distributionRoundedProbability base denominator p i)
    rw [abs_of_nonneg hdefect] at htriangle
    have hcorrection :
        |distributionFloorProbability denominator p i -
            distributionRoundedProbability base denominator p i| =
          if i = base then
            (distributionFloorResidual denominator p : ℝ) / denominator
          else 0 := by
      rw [distributionRoundedProbability_eq_floor_add]
      by_cases hbase : i = base
      · simp [hbase, abs_of_nonneg hres]
      · simp [hbase]
    rw [hcorrection] at htriangle
    exact htriangle
  have htv_defect :
      finiteTotalVariation p
          (distributionRoundedProbability base denominator p) ≤
        ∑ i, (p i - distributionFloorProbability denominator p i) := by
    calc
      finiteTotalVariation p
          (distributionRoundedProbability base denominator p) =
        (∑ i, |p i - distributionRoundedProbability
          base denominator p i|) / 2 := rfl
      _ ≤ (∑ i,
          ((p i - distributionFloorProbability denominator p i) +
            if i = base then
              (distributionFloorResidual denominator p : ℝ) / denominator
            else 0)) / 2 := by
        apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr
        exact Finset.sum_le_sum fun i _ => hpoint i
      _ = ∑ i, (p i - distributionFloorProbability denominator p i) := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        rw [distributionFloorResidual_probability_eq_sum
          denominator positive p hp normalized]
        ring
  calc
    finiteTotalVariation p
        (distributionRoundedProbability base denominator p) ≤
      ∑ i, (p i - distributionFloorProbability denominator p i) :=
        htv_defect
    _ ≤ ∑ _i : ι, (1 : ℝ) / denominator :=
      Finset.sum_le_sum fun i _ =>
        (distributionFloorProbability_error_lt denominator positive p i).le
    _ = (Fintype.card ι : ℝ) / denominator := by
      simp [div_eq_mul_inv]

omit [Fintype ι] [DecidableEq ι] in

theorem finite_log_sum_inequality
    (indices : Finset ι) (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hq : ∀ i, 0 ≤ q i)
    (absolute_continuity : ∀ i, q i = 0 → p i = 0)
    (positive_mass : 0 < ∑ i ∈ indices, q i) :
    (∑ i ∈ indices, q i) *
        InformationTheory.klFun
          ((∑ i ∈ indices, p i) / (∑ i ∈ indices, q i)) ≤
      ∑ i ∈ indices,
        q i * InformationTheory.klFun (p i / q i) := by
  let total : ℝ := ∑ i ∈ indices, q i
  have htotal : 0 < total := positive_mass
  have hnormalized :
      (∑ i ∈ indices, q i / total) = 1 := by
    rw [← Finset.sum_div]
    exact div_self htotal.ne'
  have hmean :
      (∑ i ∈ indices, (q i / total) * (p i / q i)) =
        (∑ i ∈ indices, p i) / total := by
    calc
      (∑ i ∈ indices, (q i / total) * (p i / q i)) =
          ∑ i ∈ indices, p i / total := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hqi : q i = 0
        · simp [hqi, absolute_continuity i hqi]
        · field_simp [hqi, htotal.ne']
      _ = (∑ i ∈ indices, p i) / total := by
        rw [Finset.sum_div]
  have hjensen :
      InformationTheory.klFun ((∑ i ∈ indices, p i) / total) ≤
        ∑ i ∈ indices,
          (q i / total) * InformationTheory.klFun (p i / q i) := by
    have h := InformationTheory.convexOn_klFun.map_sum_le
      (t := indices)
      (w := fun i => q i / total)
      (p := fun i => p i / q i)
      (fun i _ => div_nonneg (hq i) htotal.le)
      hnormalized
      (fun i _ => show p i / q i ∈ Set.Ici (0 : ℝ) from
        div_nonneg (hp i) (hq i))
    simpa only [smul_eq_mul, hmean] using h
  change
    total * InformationTheory.klFun
      ((∑ i ∈ indices, p i) / total) ≤
      ∑ i ∈ indices, q i * InformationTheory.klFun (p i / q i)
  calc
    total * InformationTheory.klFun
        ((∑ i ∈ indices, p i) / total) ≤
      total * (∑ i ∈ indices,
        (q i / total) * InformationTheory.klFun (p i / q i)) :=
      mul_le_mul_of_nonneg_left hjensen htotal.le
    _ = ∑ i ∈ indices,
        q i * InformationTheory.klFun (p i / q i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      field_simp [htotal.ne']

section CoarseGraining

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def groupedMass (map : ι → κ) (p : ι → ℝ) (j : κ) : ℝ :=
  ∑ i ∈ (Finset.univ.filter fun i => map i = j), p i

omit [DecidableEq ι] in

theorem finite_relative_entropy_data_processing
    (map : ι → κ) (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hq : ∀ i, 0 ≤ q i)
    (absolute_continuity : ∀ i, q i = 0 → p i = 0) :
    finiteRelativeEntropy (groupedMass map p) (groupedMass map q) ≤
      finiteRelativeEntropy p q := by
  change
    (∑ j : κ, groupedMass map q j *
      InformationTheory.klFun
        (groupedMass map p j / groupedMass map q j)) ≤
      ∑ i : ι, q i * InformationTheory.klFun (p i / q i)
  calc
    (∑ j : κ, groupedMass map q j *
        InformationTheory.klFun
          (groupedMass map p j / groupedMass map q j)) ≤
      ∑ j : κ,
        ∑ i ∈ (Finset.univ.filter fun i => map i = j),
          q i * InformationTheory.klFun (p i / q i) := by
        apply Finset.sum_le_sum
        intro j _
        let indices : Finset ι :=
          Finset.univ.filter fun i => map i = j
        change
          (∑ i ∈ indices, q i) *
              InformationTheory.klFun
                ((∑ i ∈ indices, p i) / (∑ i ∈ indices, q i)) ≤
            ∑ i ∈ indices,
              q i * InformationTheory.klFun (p i / q i)
        have hreference : 0 ≤ ∑ i ∈ indices, q i :=
          Finset.sum_nonneg (fun i _ => hq i)
        by_cases hzero : (∑ i ∈ indices, q i) = 0
        · rw [hzero, zero_mul]
          apply Finset.sum_nonneg
          intro i _
          exact mul_nonneg (hq i)
            (InformationTheory.klFun_nonneg
              (div_nonneg (hp i) (hq i)))
        · exact finite_log_sum_inequality indices p q hp hq
            absolute_continuity (lt_of_le_of_ne hreference (Ne.symm hzero))
    _ = ∑ i : ι,
        q i * InformationTheory.klFun (p i / q i) := by
      simpa only [] using
        (Finset.sum_fiberwise (Finset.univ : Finset ι) map
          (fun i => q i * InformationTheory.klFun (p i / q i)))

end CoarseGraining

section JointChainRule

variable {κ : Type*} [Fintype κ]

def jointFirstMarginal (joint : ι × κ → ℝ) : ι → ℝ :=
  fun i => ∑ j : κ, joint (i, j)

def jointConditional (joint : ι × κ → ℝ) (i : ι) : κ → ℝ :=
  fun j => joint (i, j) / jointFirstMarginal joint i

omit [Fintype ι] [DecidableEq ι] in

theorem jointFirstMarginal_nonneg
    (joint : ι × κ → ℝ)
    (nonnegative : ∀ point, 0 ≤ joint point) (i : ι) :
    0 ≤ jointFirstMarginal joint i := by
  exact Finset.sum_nonneg (fun j _ => nonnegative (i, j))

omit [DecidableEq ι] in

theorem jointFirstMarginal_sum (joint : ι × κ → ℝ) :
    (∑ i : ι, jointFirstMarginal joint i) =
      ∑ point : ι × κ, joint point := by
  exact (Fintype.sum_prod_type joint).symm

omit [Fintype ι] [DecidableEq ι] in

theorem jointFirstMarginal_absolute_continuity
    (p q : ι × κ → ℝ)
    (hq : ∀ point, 0 ≤ q point)
    (absolute_continuity : ∀ point, q point = 0 → p point = 0)
    (i : ι) :
    jointFirstMarginal q i = 0 → jointFirstMarginal p i = 0 := by
  intro hzero
  change (∑ j : κ, q (i, j)) = 0 at hzero
  have hcoordinates : ∀ j : κ, q (i, j) = 0 := by
    intro j
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => hq (i, j))).mp hzero j (Finset.mem_univ j)
  change (∑ j : κ, p (i, j)) = 0
  exact Finset.sum_eq_zero
    (fun j _ => absolute_continuity (i, j) (hcoordinates j))

omit [Fintype ι] [DecidableEq ι] in

theorem jointConditional_sum
    (joint : ι × κ → ℝ) (i : ι)
    (nonzero : jointFirstMarginal joint i ≠ 0) :
    (∑ j : κ, jointConditional joint i j) = 1 := by
  unfold jointConditional
  rw [← Finset.sum_div]
  exact div_self nonzero

omit [DecidableEq ι] in

theorem finite_relative_entropy_joint_chain_rule
    (p q : ι × κ → ℝ)
    (hp : ∀ point, 0 ≤ p point)
    (hq : ∀ point, 0 ≤ q point)
    (absolute_continuity : ∀ point, q point = 0 → p point = 0)
    (hp_normalized : (∑ point, p point) = 1)
    (hq_normalized : (∑ point, q point) = 1) :
    finiteRelativeEntropy p q =
      finiteRelativeEntropy (jointFirstMarginal p)
        (jointFirstMarginal q) +
      ∑ i : ι, jointFirstMarginal p i *
        finiteRelativeEntropy (jointConditional p i)
          (jointConditional q i) := by
  have hp_marginal : (∑ i : ι, jointFirstMarginal p i) = 1 :=
    (jointFirstMarginal_sum p).trans hp_normalized
  have hq_marginal : (∑ i : ι, jointFirstMarginal q i) = 1 :=
    (jointFirstMarginal_sum q).trans hq_normalized
  have h_marginal_absolute :
      ∀ i : ι, jointFirstMarginal q i = 0 →
        jointFirstMarginal p i = 0 :=
    jointFirstMarginal_absolute_continuity p q hq absolute_continuity
  have h_joint_log :
      finiteRelativeEntropy p q =
        ∑ point : ι × κ,
          p point * Real.log (p point / q point) :=
    finiteRelativeEntropy_eq_log_sum_of_absolute_continuity
      p q hq absolute_continuity hp_normalized hq_normalized
  have h_marginal_log :
      finiteRelativeEntropy (jointFirstMarginal p)
        (jointFirstMarginal q) =
        ∑ i : ι, jointFirstMarginal p i *
          Real.log (jointFirstMarginal p i /
            jointFirstMarginal q i) :=
    finiteRelativeEntropy_eq_log_sum_of_absolute_continuity
      (jointFirstMarginal p) (jointFirstMarginal q)
      (jointFirstMarginal_nonneg q hq)
      h_marginal_absolute hp_marginal hq_marginal
  calc
    finiteRelativeEntropy p q =
      ∑ point : ι × κ,
        p point * Real.log (p point / q point) := h_joint_log
    _ = ∑ i : ι, ∑ j : κ,
        p (i, j) * Real.log (p (i, j) / q (i, j)) :=
          Fintype.sum_prod_type _
    _ = ∑ i : ι,
        (jointFirstMarginal p i *
          Real.log (jointFirstMarginal p i /
            jointFirstMarginal q i) +
          jointFirstMarginal p i *
            finiteRelativeEntropy (jointConditional p i)
              (jointConditional q i)) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hpzero : jointFirstMarginal p i = 0
      · have hcoordinates : ∀ j : κ, p (i, j) = 0 := by
          intro j
          apply (Finset.sum_eq_zero_iff_of_nonneg
            (fun j _ => hp (i, j))).mp
              (show (∑ j : κ, p (i, j)) = 0 from hpzero)
              j (Finset.mem_univ j)
        simp [hpzero, hcoordinates]
      · have hqzero : jointFirstMarginal q i ≠ 0 := by
          intro hzero
          exact hpzero (h_marginal_absolute i hzero)
        have hconditional_absolute :
            ∀ j : κ, jointConditional q i j = 0 →
              jointConditional p i j = 0 := by
          intro j hzero
          change q (i, j) / jointFirstMarginal q i = 0 at hzero
          have hpoint : q (i, j) = 0 := by
            rcases (div_eq_zero_iff.mp hzero) with hpoint | hmarginal
            · exact hpoint
            · exact (hqzero hmarginal).elim
          simp [jointConditional, absolute_continuity (i, j) hpoint]
        have hconditional_log :
            finiteRelativeEntropy (jointConditional p i)
              (jointConditional q i) =
              ∑ j : κ,
                jointConditional p i j *
                  Real.log (jointConditional p i j /
                    jointConditional q i j) := by
          apply finiteRelativeEntropy_eq_log_sum_of_absolute_continuity
          · intro j
            exact div_nonneg (hq (i, j))
              (jointFirstMarginal_nonneg q hq i)
          · exact hconditional_absolute
          · exact jointConditional_sum p i hpzero
          · exact jointConditional_sum q i hqzero
        rw [hconditional_log]
        calc
          (∑ j : κ,
            p (i, j) * Real.log (p (i, j) / q (i, j))) =
            ∑ j : κ,
              (p (i, j) *
                Real.log (jointFirstMarginal p i /
                  jointFirstMarginal q i) +
                jointFirstMarginal p i *
                  (jointConditional p i j *
                    Real.log (jointConditional p i j /
                      jointConditional q i j))) := by
              apply Finset.sum_congr rfl
              intro j _
              by_cases hpj : p (i, j) = 0
              · simp [hpj, jointConditional]
              · have hqj : q (i, j) ≠ 0 := by
                  intro hzero
                  exact hpj (absolute_continuity (i, j) hzero)
                have hfactorization :
                    p (i, j) / q (i, j) =
                      (jointFirstMarginal p i /
                        jointFirstMarginal q i) *
                        (jointConditional p i j /
                          jointConditional q i j) := by
                  unfold jointConditional
                  field_simp [hpzero, hqzero, hqj]
                have hfirst :
                    jointFirstMarginal p i /
                      jointFirstMarginal q i ≠ 0 :=
                  div_ne_zero hpzero hqzero
                have hsecond :
                    jointConditional p i j /
                      jointConditional q i j ≠ 0 := by
                  unfold jointConditional
                  exact div_ne_zero
                    (div_ne_zero hpj hpzero)
                    (div_ne_zero hqj hqzero)
                rw [hfactorization, Real.log_mul hfirst hsecond]
                unfold jointConditional
                field_simp [hpzero]
          _ = jointFirstMarginal p i *
              Real.log (jointFirstMarginal p i /
                jointFirstMarginal q i) +
              jointFirstMarginal p i *
                (∑ j : κ,
                  jointConditional p i j *
                    Real.log (jointConditional p i j /
                      jointConditional q i j)) := by
                rw [Finset.sum_add_distrib, ← Finset.sum_mul,
                  ← Finset.mul_sum]
                rfl
    _ = (∑ i : ι,
          jointFirstMarginal p i *
            Real.log (jointFirstMarginal p i /
              jointFirstMarginal q i)) +
        ∑ i : ι, jointFirstMarginal p i *
          finiteRelativeEntropy (jointConditional p i)
            (jointConditional q i) := by
      rw [Finset.sum_add_distrib]
    _ = finiteRelativeEntropy (jointFirstMarginal p)
          (jointFirstMarginal q) +
        ∑ i : ι, jointFirstMarginal p i *
          finiteRelativeEntropy (jointConditional p i)
            (jointConditional q i) := by
      rw [h_marginal_log]

end JointChainRule

section SharedPermutationSampling

def rationalPermutationOutput
    (denominator : ℕ) (numerator : ι → ℕ)
    (nonempty : (rationalMarked denominator numerator).Nonempty)
    (permutation : Equiv.Perm (ι × Fin denominator)) : ι :=
  (markedFirst (Fintype.equivFin (ι × Fin denominator))
    (rationalMarked denominator numerator) nonempty permutation).1

theorem rationalPermutationOutput_probability
    (denominator : ℕ) (numerator : ι → ℕ)
    (normalized : (∑ i, numerator i) = denominator)
    (nonempty : (rationalMarked denominator numerator).Nonempty)
    (letter : ι) :
    uniformPermutationProbability
        (fun permutation : Equiv.Perm (ι × Fin denominator) =>
          rationalPermutationOutput denominator numerator
            nonempty permutation = letter) =
      (numerator letter : ℝ) / denominator := by
  exact rationalMarked_letter_probability denominator numerator normalized
    nonempty (Fintype.equivFin (ι × Fin denominator)) letter

theorem rationalMarked_inter
    (denominator : ℕ) (left right : ι → ℕ) :
    rationalMarked denominator left ∩ rationalMarked denominator right =
      rationalMarked denominator (fun i => min (left i) (right i)) := by
  ext point
  simp [rationalMarked]

theorem rationalMarked_inter_card
    (denominator : ℕ) (left right : ι → ℕ)
    (hleft : (∑ i, left i) = denominator)
    (_hright : (∑ i, right i) = denominator) :
    (rationalMarked denominator left ∩
      rationalMarked denominator right).card =
        ∑ i : ι, min (left i) (right i) := by
  rw [rationalMarked_inter]
  calc
    (rationalMarked denominator
        (fun i => min (left i) (right i))).card =
      ∑ i : ι,
        ((rationalMarked denominator
          (fun i => min (left i) (right i))).filter
            fun point => point.1 = i).card := by
      simpa using
        (Finset.card_eq_sum_card_fiberwise
          (f := fun point : ι × Fin denominator => point.1)
          (s := rationalMarked denominator
            (fun i => min (left i) (right i)))
          (t := (Finset.univ : Finset ι))
          (fun _ _ => Finset.mem_univ _))
    _ = ∑ i : ι, min (left i) (right i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [rationalMarked_fiber_card, min_eq_right]
      exact (min_le_left (left i) (right i)).trans
        (rationalNumerator_le_denominator
          denominator left hleft i)

theorem rationalMarked_markedTotalVariation_eq
    (denominator : ℕ) (positive : 0 < denominator)
    (left right : ι → ℕ)
    (hleft : (∑ i, left i) = denominator)
    (hright : (∑ i, right i) = denominator) :
    markedTotalVariation
        (rationalMarked denominator left)
        (rationalMarked denominator right) =
      finiteTotalVariation
        (fun i => (left i : ℝ) / denominator)
        (fun i => (right i : ℝ) / denominator) := by
  let L := rationalMarked denominator left
  let R := rationalMarked denominator right
  have hL : L.card = denominator :=
    rationalMarked_card denominator left hleft
  have hR : R.card = denominator :=
    rationalMarked_card denominator right hright
  have hI :
      ((L ∩ R).card : ℝ) =
        ∑ i : ι, (min (left i) (right i) : ℝ) := by
    change
      (((rationalMarked denominator left ∩
        rationalMarked denominator right).card : ℕ) : ℝ) =
        ∑ i : ι, (min (left i) (right i) : ℝ)
    rw [rationalMarked_inter_card denominator left right hleft hright,
      Nat.cast_sum]
    simp only [Nat.cast_min]
  have hdisjoint : Disjoint (L \ R) (R \ L) := by
    apply Finset.disjoint_left.mpr
    intro point hpoint_left hpoint_right
    exact (Finset.mem_sdiff.mp hpoint_left).2
      (Finset.mem_sdiff.mp hpoint_right).1
  have hunion :
      (((L \ R) ∪ (R \ L)).card : ℝ) =
        ((L \ R).card : ℝ) + ((R \ L).card : ℝ) := by
    exact_mod_cast (Finset.card_union_of_disjoint hdisjoint)
  have hleft_difference :
      ((L \ R).card : ℝ) + ((L ∩ R).card : ℝ) =
        (L.card : ℝ) := by
    exact_mod_cast (Finset.card_sdiff_add_card_inter L R)
  have hright_difference :
      ((R \ L).card : ℝ) + ((L ∩ R).card : ℝ) =
        (R.card : ℝ) := by
    have h := Finset.card_sdiff_add_card_inter R L
    rw [Finset.inter_comm R L] at h
    exact_mod_cast h
  have hsymmetric :
      (((L \ R) ∪ (R \ L)).card : ℝ) =
        (denominator : ℝ) + denominator -
          2 * ∑ i : ι, (min (left i) (right i) : ℝ) := by
    have hLreal : (L.card : ℝ) = denominator := by exact_mod_cast hL
    have hRreal : (R.card : ℝ) = denominator := by exact_mod_cast hR
    linarith
  have hpointwise : ∀ i : ι,
      |(left i : ℝ) / denominator -
        (right i : ℝ) / denominator| =
        ((left i : ℝ) + right i -
          2 * (min (left i) (right i) : ℝ)) / denominator := by
    intro i
    rw [← sub_div, abs_div]
    have hdenominator_abs : |(denominator : ℝ)| = denominator :=
      abs_of_nonneg (Nat.cast_nonneg denominator)
    rw [hdenominator_abs]
    by_cases horder : left i ≤ right i
    · have hreal : (left i : ℝ) ≤ right i := by
        exact_mod_cast horder
      rw [min_eq_left hreal, abs_of_nonpos (sub_nonpos.mpr hreal)]
      ring
    · have horder' : right i ≤ left i :=
        (Nat.le_of_lt (Nat.lt_of_not_ge horder))
      have hreal : (right i : ℝ) ≤ left i := by
        exact_mod_cast horder'
      rw [min_eq_right hreal, abs_of_nonneg (sub_nonneg.mpr hreal)]
      ring
  have hleft_real : (∑ i : ι, (left i : ℝ)) = denominator := by
    exact_mod_cast hleft
  have hright_real : (∑ i : ι, (right i : ℝ)) = denominator := by
    exact_mod_cast hright
  have hdenominator : (denominator : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt positive)
  change
    (((L \ R) ∪ (R \ L)).card : ℝ) /
        (2 * (L.card : ℝ)) =
      (∑ i : ι,
        |(left i : ℝ) / denominator -
          (right i : ℝ) / denominator|) / 2
  rw [hsymmetric, hL]
  simp_rw [hpointwise]
  rw [← Finset.sum_div, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum,
    hleft_real, hright_real]
  field_simp [hdenominator]

theorem uniformPermutationProbability_mono
    {α : Type*} [Fintype α] [DecidableEq α]
    (small large : Equiv.Perm α → Prop)
    (hinclusion : ∀ permutation, small permutation → large permutation) :
    uniformPermutationProbability small ≤
      uniformPermutationProbability large := by
  classical
  unfold uniformPermutationProbability
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Finset.card_le_card (show
      (Finset.univ.filter fun permutation : Equiv.Perm α =>
        small permutation) ⊆
      (Finset.univ.filter fun permutation : Equiv.Perm α =>
        large permutation) from by
        intro permutation hpermutation
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hinclusion permutation
            (Finset.mem_filter.mp hpermutation).2⟩)
  · exact_mod_cast (Nat.zero_le (Fintype.card (Equiv.Perm α)))

theorem rationalPermutationOutput_disagreement_le_two_mul_tv
    (denominator : ℕ) (left right : ι → ℕ)
    (hleft : (∑ i, left i) = denominator)
    (hright : (∑ i, right i) = denominator)
    (nonempty_left : (rationalMarked denominator left).Nonempty)
    (nonempty_right : (rationalMarked denominator right).Nonempty) :
    uniformPermutationProbability
        (fun permutation : Equiv.Perm (ι × Fin denominator) =>
          rationalPermutationOutput denominator left
            nonempty_left permutation ≠
          rationalPermutationOutput denominator right
            nonempty_right permutation) ≤
      2 * markedTotalVariation
        (rationalMarked denominator left)
        (rationalMarked denominator right) := by
  let rank := Fintype.equivFin (ι × Fin denominator)
  calc
    uniformPermutationProbability
        (fun permutation : Equiv.Perm (ι × Fin denominator) =>
          rationalPermutationOutput denominator left
            nonempty_left permutation ≠
          rationalPermutationOutput denominator right
            nonempty_right permutation) ≤
      uniformPermutationProbability
        (fun permutation : Equiv.Perm (ι × Fin denominator) =>
          markedFirst rank (rationalMarked denominator left)
            nonempty_left permutation ≠
          markedFirst rank (rationalMarked denominator right)
            nonempty_right permutation) := by
        apply uniformPermutationProbability_mono
        intro permutation hdifferent hequal
        apply hdifferent
        exact congrArg Prod.fst hequal
    _ ≤ 2 * markedTotalVariation
        (rationalMarked denominator left)
        (rationalMarked denominator right) := by
      apply sharedPermutation_disagreement_probability_le_two_mul_tv
      calc
        (rationalMarked denominator left).card = denominator :=
          rationalMarked_card denominator left hleft
        _ = (rationalMarked denominator right).card :=
          (rationalMarked_card denominator right hright).symm

theorem rationalPermutationOutput_disagreement_le_two_mul_finiteTotalVariation
    (denominator : ℕ) (positive : 0 < denominator)
    (left right : ι → ℕ)
    (hleft : (∑ i, left i) = denominator)
    (hright : (∑ i, right i) = denominator)
    (nonempty_left : (rationalMarked denominator left).Nonempty)
    (nonempty_right : (rationalMarked denominator right).Nonempty) :
    uniformPermutationProbability
        (fun permutation : Equiv.Perm (ι × Fin denominator) =>
          rationalPermutationOutput denominator left
            nonempty_left permutation ≠
          rationalPermutationOutput denominator right
            nonempty_right permutation) ≤
      2 * finiteTotalVariation
        (fun i => (left i : ℝ) / denominator)
        (fun i => (right i : ℝ) / denominator) := by
  calc
    uniformPermutationProbability
        (fun permutation : Equiv.Perm (ι × Fin denominator) =>
          rationalPermutationOutput denominator left
            nonempty_left permutation ≠
          rationalPermutationOutput denominator right
            nonempty_right permutation) ≤
      2 * markedTotalVariation
        (rationalMarked denominator left)
        (rationalMarked denominator right) :=
          rationalPermutationOutput_disagreement_le_two_mul_tv
            denominator left right hleft hright
            nonempty_left nonempty_right
    _ = 2 * finiteTotalVariation
        (fun i => (left i : ℝ) / denominator)
        (fun i => (right i : ℝ) / denominator) := by
      rw [rationalMarked_markedTotalVariation_eq
        denominator positive left right hleft hright]

end SharedPermutationSampling

end ClassicalInformation

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
set_option maxRecDepth 3072

def dSVUniformLeftDensityConjugateSwapVector
    {d : ℕ} (z : EuclideanSpace ℂ (Fin d × Fin d)) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  toLp 2 (fun ij : Fin d × Fin d => star (z (ij.2, ij.1)))

theorem dSVUniformLeftDensityConjugateSwapVector_norm
    {d : ℕ} (z : EuclideanSpace ℂ (Fin d × Fin d)) :
    ‖dSVUniformLeftDensityConjugateSwapVector z‖ = ‖z‖ := by
  have squares :
      ‖dSVUniformLeftDensityConjugateSwapVector z‖ ^ 2 =
        ‖z‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Fintype.sum_prod_type, Fintype.sum_prod_type]
    change
      (∑ i : Fin d, ∑ j : Fin d,
        ‖star (z (j, i))‖ ^ 2) =
        ∑ i : Fin d, ∑ j : Fin d, ‖z (i, j)‖ ^ 2
    simp_rw [norm_star]
    rw [Finset.sum_comm]
  nlinarith [norm_nonneg
    (dSVUniformLeftDensityConjugateSwapVector z),
    norm_nonneg z]

theorem dSVUniformLeftDensityConjugateSwapVector_distance
    {d : ℕ} (z w : EuclideanSpace ℂ (Fin d × Fin d)) :
    ‖dSVUniformLeftDensityConjugateSwapVector z -
        dSVUniformLeftDensityConjugateSwapVector w‖ =
      ‖z - w‖ := by
  have difference :
      dSVUniformLeftDensityConjugateSwapVector z -
        dSVUniformLeftDensityConjugateSwapVector w =
      dSVUniformLeftDensityConjugateSwapVector (z - w) := by
    ext ij
    change star (z (ij.2, ij.1)) - star (w (ij.2, ij.1)) =
      star ((z - w) (ij.2, ij.1))
    simp
  rw [difference,
    dSVUniformLeftDensityConjugateSwapVector_norm]

def dSVUniformLeftDensityConjugateSwap
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    BipartiteUnitVector d :=
  ⟨dSVUniformLeftDensityConjugateSwapVector ξ.val,
    (dSVUniformLeftDensityConjugateSwapVector_norm ξ.val).trans
      ξ.property⟩

theorem dSVUniformLeftDensityConjugateSwap_coefficient
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    targetCoefficientMatrix
        (dSVUniformLeftDensityConjugateSwap ξ) =
      (targetCoefficientMatrix ξ).conjTranspose := by
  ext b a
  rfl

theorem dSVUniformLeftDensityConjugateSwap_density
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    targetReducedDensity
        (dSVUniformLeftDensityConjugateSwap ξ) =
      dSVSoftBobLeftReducedDensity ξ := by
  unfold targetReducedDensity
    dSVSoftBobLeftReducedDensity
  rw [dSVUniformLeftDensityConjugateSwap_coefficient,
    Matrix.conjTranspose_conjTranspose]

theorem dSVUniformLeftDensityConjugateSwap_distance
    {d : ℕ} (ξ ζ : BipartiteUnitVector d) :
    ‖(dSVUniformLeftDensityConjugateSwap ξ).val -
        (dSVUniformLeftDensityConjugateSwap ζ).val‖ =
      ‖ξ.val - ζ.val‖ :=
  dSVUniformLeftDensityConjugateSwapVector_distance
    ξ.val ζ.val

def dSVUniformLeftDensitySchmidtCoefficient
    {d : ℕ} (ξ : BipartiteUnitVector d)
    (i : Fin d) : ℝ :=
  Real.sqrt
    ((dSVSoftBobLeftReducedDensity_posSemidef ξ).isHermitian.eigenvalues i)

def dSVUniformLeftDensitySpectralAtomDiscrepancy
    {d : ℕ} (ξ ζ : BipartiteUnitVector d) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d,
    |dSVUniformLeftDensitySchmidtCoefficient ξ i ^ 2 -
      dSVUniformLeftDensitySchmidtCoefficient ζ j ^ 2| *
      spectralAtomOverlap
        (dSVSoftBobLeftReducedDensity ξ)
        (dSVSoftBobLeftReducedDensity ζ)
        (dSVSoftBobLeftReducedDensity_posSemidef ξ)
        (dSVSoftBobLeftReducedDensity_posSemidef ζ) i j

theorem dSVUniformLeftDensitySpectralAtomDiscrepancy_eq_swap
    {d : ℕ} (ξ ζ : BipartiteUnitVector d) :
    dSVUniformLeftDensitySpectralAtomDiscrepancy ξ ζ =
      dSVUniformDensitySpectralAtomDiscrepancy
        (dSVUniformLeftDensityConjugateSwap ξ)
        (dSVUniformLeftDensityConjugateSwap ζ) := by
  unfold dSVUniformLeftDensitySpectralAtomDiscrepancy
    dSVUniformDensitySpectralAtomDiscrepancy
    dSVUniformLeftDensitySchmidtCoefficient
    targetCanonicalSchmidtCoefficient
  simp only [dSVUniformLeftDensityConjugateSwap_density]

theorem dSVUniformLeftDensitySpectralAtomDiscrepancy_le
    {d : ℕ} (ξ ζ : BipartiteUnitVector d) :
    dSVUniformLeftDensitySpectralAtomDiscrepancy ξ ζ ≤
      2 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ := by
  rw [dSVUniformLeftDensitySpectralAtomDiscrepancy_eq_swap]
  have bound := dSVUniformDensitySpectralAtomDiscrepancy_le
    (dSVUniformLeftDensityConjugateSwap ξ)
    (dSVUniformLeftDensityConjugateSwap ζ)
  rwa [dSVUniformLeftDensityConjugateSwap_distance] at bound

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

def dSVUniformDensityThresholdGrid
    (N : ℕ) (k : Fin N) : ℝ :=
  finiteUniformThresholdGrid
    (1 / (N : ℝ)) (1 + 1 / (N : ℝ)) N k

theorem dSVUniformDensityThresholdGrid_apply
    {N : ℕ} (positive : 0 < N) (k : Fin N) :
    dSVUniformDensityThresholdGrid N k =
      ((k.val : ℝ) + 1) / (N : ℝ) := by
  have nonzero : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt positive)
  unfold dSVUniformDensityThresholdGrid
    finiteUniformThresholdGrid
  field_simp
  ring

def dSVUniformDensityThresholdWeight
    (N : ℕ) (_k : Fin N) : ℝ :=
  1 / (N : ℝ)

theorem dSVUniformDensityThresholdWeight_nonneg
    (N : ℕ) (k : Fin N) :
    0 ≤ dSVUniformDensityThresholdWeight N k := by
  unfold dSVUniformDensityThresholdWeight
  positivity

def dSVUniformDensityGridPrefix
    (N : ℕ) (density : ℝ) : ℝ :=
  ∑ k : Fin N,
    dSVUniformDensityThresholdWeight N k *
      if dSVUniformDensityThresholdGrid N k ≤ density
      then 1 else 0

theorem dSVUniformDensityGridPrefix_eq_count
    (N : ℕ) (density : ℝ) :
    dSVUniformDensityGridPrefix N density =
      ((Finset.univ.filter fun k : Fin N =>
        dSVUniformDensityThresholdGrid N k ≤ density).card : ℝ) /
        (N : ℝ) := by
  classical
  unfold dSVUniformDensityGridPrefix
    dSVUniformDensityThresholdWeight
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  simp [div_eq_mul_inv, mul_comm]

def dSVUniformDensityThresholdMismatch
    (N : ℕ) (alice bob : ℝ) : ℝ :=
  ∑ k : Fin N,
    dSVUniformDensityThresholdWeight N k *
      if ((dSVUniformDensityThresholdGrid N k ≤ alice) ↔
        (dSVUniformDensityThresholdGrid N k ≤ bob))
      then 0 else 1

theorem dSVUniformDensityThresholdMismatch_indicator_le_crossing
    {N : ℕ} (k : Fin N) (alice bob : ℝ) :
    (if ((dSVUniformDensityThresholdGrid N k ≤ alice) ↔
        (dSVUniformDensityThresholdGrid N k ≤ bob))
      then (0 : ℝ) else 1) ≤
      if min alice bob ≤ dSVUniformDensityThresholdGrid N k ∧
        dSVUniformDensityThresholdGrid N k ≤ max alice bob
      then 1 else 0 := by
  classical
  by_cases left : dSVUniformDensityThresholdGrid N k ≤ alice
  · by_cases right : dSVUniformDensityThresholdGrid N k ≤ bob
    · simp only [left, right, iff_self, ↓reduceIte]
      split <;> norm_num
    · have lower : bob < dSVUniformDensityThresholdGrid N k :=
        lt_of_not_ge right
      have interval :
          min alice bob ≤ dSVUniformDensityThresholdGrid N k ∧
            dSVUniformDensityThresholdGrid N k ≤ max alice bob :=
        ⟨(min_le_right alice bob).trans lower.le,
          left.trans (le_max_left alice bob)⟩
      simp [left, right, interval]
  · by_cases right : dSVUniformDensityThresholdGrid N k ≤ bob
    · have lower : alice < dSVUniformDensityThresholdGrid N k :=
        lt_of_not_ge left
      have interval :
          min alice bob ≤ dSVUniformDensityThresholdGrid N k ∧
            dSVUniformDensityThresholdGrid N k ≤ max alice bob :=
        ⟨(min_le_left alice bob).trans lower.le,
          right.trans (le_max_right alice bob)⟩
      simp [left, right, interval]
    · simp [left, right]

theorem dSVUniformDensityThresholdMismatch_le
    {N : ℕ} (positive : 0 < N) (alice bob : ℝ) :
    dSVUniformDensityThresholdMismatch N alice bob ≤
      |alice - bob| + 1 / (N : ℝ) := by
  classical
  have window :
      (1 / (N : ℝ)) < 1 + 1 / (N : ℝ) := by linarith
  calc
    dSVUniformDensityThresholdMismatch N alice bob ≤
      finiteUniformThresholdCrossing
        (1 / (N : ℝ)) (1 + 1 / (N : ℝ)) alice bob N := by
      unfold dSVUniformDensityThresholdMismatch
        finiteUniformThresholdCrossing
      calc
        (∑ k : Fin N,
          dSVUniformDensityThresholdWeight N k *
            if ((dSVUniformDensityThresholdGrid N k ≤ alice) ↔
              (dSVUniformDensityThresholdGrid N k ≤ bob))
            then 0 else 1) ≤
          ∑ k : Fin N,
            dSVUniformDensityThresholdWeight N k *
              if min alice bob ≤
                  dSVUniformDensityThresholdGrid N k ∧
                dSVUniformDensityThresholdGrid N k ≤ max alice bob
              then 1 else 0 := by
            apply Finset.sum_le_sum
            intro k _
            exact mul_le_mul_of_nonneg_left
              (dSVUniformDensityThresholdMismatch_indicator_le_crossing
                k alice bob)
              (dSVUniformDensityThresholdWeight_nonneg N k)
        _ = _ := by
          unfold dSVUniformDensityThresholdWeight
            dSVUniformDensityThresholdGrid
          simp_rw [mul_ite, mul_one, mul_zero]
          rw [← Finset.sum_filter]
          simp [div_eq_mul_inv, mul_comm]
    _ ≤ |alice - bob| /
        ((1 + 1 / (N : ℝ)) - (1 / (N : ℝ))) +
          1 / (N : ℝ) :=
      finiteUniformThresholdCrossing_le
        window alice bob N positive
    _ = |alice - bob| + 1 / (N : ℝ) := by
      ring

theorem dSVUniformDensityThresholdGrid_count_eq_floor
    {N : ℕ} (positive : 0 < N)
    (density : ℝ) (nonnegative : 0 ≤ density) (bounded : density ≤ 1) :
    (Finset.univ.filter fun k : Fin N =>
      dSVUniformDensityThresholdGrid N k ≤ density).card =
        Nat.floor (density * (N : ℝ)) := by
  classical
  have gridpositive : (0 : ℝ) < N := by exact_mod_cast positive
  have densitypositive : 0 ≤ density * (N : ℝ) :=
    mul_nonneg nonnegative gridpositive.le
  have floor_bound : Nat.floor (density * (N : ℝ)) ≤ N := by
    have product : density * (N : ℝ) ≤ (N : ℝ) := by
      nlinarith
    have floor := Nat.floor_mono product
    simpa using floor
  have same :
      (Finset.univ.filter fun k : Fin N =>
        dSVUniformDensityThresholdGrid N k ≤ density) =
      (Finset.univ.filter fun k : Fin N =>
        k.val < Nat.floor (density * (N : ℝ))) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [dSVUniformDensityThresholdGrid_apply positive,
      div_le_iff₀ gridpositive]
    constructor
    · intro threshold
      have cast : ((k.val + 1 : ℕ) : ℝ) ≤ density * (N : ℝ) := by
        simpa using threshold
      have below := (Nat.le_floor_iff densitypositive).2 cast
      omega
    · intro below
      have integer : k.val + 1 ≤ Nat.floor (density * (N : ℝ)) := by
        omega
      have cast := (Nat.le_floor_iff densitypositive).1 integer
      simpa using cast
  rw [same, Fin.card_filter_val_lt, min_eq_right floor_bound]

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option maxRecDepth 4096

theorem dSVUniformDensityBinarySpectral_false_eq_complement
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (bin : d → Bool) :
    (spectralPartitionPOVM F hF bin).effect false =
      1 - (spectralPartitionPOVM F hF bin).effect true := by
  have complete := (spectralPartitionPOVM F hF bin).complete
  rw [Fintype.sum_bool] at complete
  rw [add_comm] at complete
  exact eq_sub_of_add_eq complete

end

noncomputable section

open scoped BigOperators Kronecker ComplexOrder MatrixOrder

theorem dSVUniformDensitySchmidtVector_sub
    {d : ℕ} (σ τ : Fin d → ℝ)
    (U V : Matrix.unitaryGroup (Fin d) ℂ) :
    schmidtVector σ U V -
        schmidtVector τ U V =
      schmidtVector (fun i => σ i - τ i) U V := by
  unfold schmidtVector
  rw [← localUnitaryAction_sub]
  congr 1
  ext ⟨i, j⟩
  by_cases equal : i = j
  · subst j
    simp [diagonalSchmidtState]
  · simp [diagonalSchmidtState, equal]

theorem dSVUniformDensity_normalize_sub_self_norm
    {d : ℕ} (v : EuclideanSpace ℂ (Fin d × Fin d))
    (nonzero : v ≠ 0) :
    ‖NormedSpace.normalize v - v‖ = |1 - ‖v‖| := by
  have positive : 0 < ‖v‖ := norm_pos_iff.mpr nonzero
  calc
    ‖NormedSpace.normalize v - v‖ =
        ‖((‖v‖⁻¹ - 1 : ℝ) • v)‖ := by
          unfold NormedSpace.normalize
          congr 1
          rw [sub_smul, one_smul]
    _ = |‖v‖⁻¹ - 1| * ‖v‖ := by
          rw [norm_smul, Real.norm_eq_abs]
    _ = |(‖v‖⁻¹ - 1) * ‖v‖| := by
          rw [abs_mul, abs_of_nonneg (norm_nonneg v)]
    _ = |1 - ‖v‖| := by
          congr 1
          field_simp [positive.ne']

end

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] Classical.propDecidable

def normalizeOrDefault (fallback z : E) : E :=
  if z = 0 then fallback else NormedSpace.normalize z

theorem normalizeOrDefault_norm
    (fallback z : E) (hfallback : ‖fallback‖ = 1) :
    ‖normalizeOrDefault fallback z‖ = 1 := by
  classical
  by_cases hz : z = 0
  · simp [normalizeOrDefault, hz, hfallback]
  · simp [normalizeOrDefault, hz, NormedSpace.norm_normalize hz]

theorem normalizeOrDefault_sub_le
    (fallback u v : E)
    (hfallback : ‖fallback‖ = 1)
    (hu : u ≠ 0) :
    ‖normalizeOrDefault fallback u - normalizeOrDefault fallback v‖ ≤
      2 * ‖u - v‖ / ‖u‖ := by
  classical
  have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  by_cases hv : v = 0
  · simp only [normalizeOrDefault, hu, ↓reduceIte, hv, sub_zero]
    calc
      ‖NormedSpace.normalize u - fallback‖ ≤
          ‖NormedSpace.normalize u‖ + ‖fallback‖ := norm_sub_le _ _
      _ = 2 := by rw [NormedSpace.norm_normalize hu, hfallback]; norm_num
      _ = 2 * ‖u‖ / ‖u‖ := by field_simp
  · simp only [normalizeOrDefault, hu, hv, ↓reduceIte]
    let u₀ := NormedSpace.normalize u
    let v₀ := NormedSpace.normalize v
    have hv₀ : ‖v₀‖ = 1 := NormedSpace.norm_normalize hv
    have hrevu : ‖u‖ • u₀ = u :=
      NormedSpace.norm_smul_normalize u
    have hrevv : ‖v‖ • v₀ = v :=
      NormedSpace.norm_smul_normalize v
    have hreverse : |‖v‖ - ‖u‖| ≤ ‖u - v‖ := by
      simpa [norm_sub_rev] using abs_norm_sub_norm_le v u
    have hscaled :
        ‖u‖ * ‖u₀ - v₀‖ = ‖u - ‖u‖ • v₀‖ := by
      calc
        ‖u‖ * ‖u₀ - v₀‖ = ‖‖u‖ • (u₀ - v₀)‖ := by
          rw [norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (norm_nonneg u)]
        _ = ‖u - ‖u‖ • v₀‖ := by rw [smul_sub, hrevu]
    have hsecond : ‖v - ‖u‖ • v₀‖ = |‖v‖ - ‖u‖| := by
      calc
        ‖v - ‖u‖ • v₀‖ = ‖‖v‖ • v₀ - ‖u‖ • v₀‖ := by
          rw [hrevv]
        _ = ‖(‖v‖ - ‖u‖) • v₀‖ := by rw [sub_smul]
        _ = |‖v‖ - ‖u‖| := by
          rw [norm_smul, Real.norm_eq_abs, hv₀, mul_one]
    have hbound : ‖u‖ * ‖u₀ - v₀‖ ≤ 2 * ‖u - v‖ := by
      rw [hscaled]
      calc
        ‖u - ‖u‖ • v₀‖ ≤
            ‖u - v‖ + ‖v - ‖u‖ • v₀‖ := by
              have hsplit :
                  u - ‖u‖ • v₀ = (u - v) + (v - ‖u‖ • v₀) := by
                abel
              rw [hsplit]
              exact norm_add_le _ _
        _ = ‖u - v‖ + |‖v‖ - ‖u‖| := by rw [hsecond]
        _ ≤ 2 * ‖u - v‖ := by linarith
    change ‖u₀ - v₀‖ ≤ 2 * ‖u - v‖ / ‖u‖
    exact (le_div_iff₀ hupos).mpr (by nlinarith)

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 3072

def dSVCanonicalFailureUnitRankFamily
    (d : ℕ) (positive : 0 < d) (rank : Fin (d + 1)) :
    BipartiteUnitVector d :=
  ⟨normalizeOrDefault
      (embezzlementState d)
      (dSVCanonicalFailurePrefix rank),
    normalizeOrDefault_norm
      (embezzlementState d)
      (dSVCanonicalFailurePrefix rank)
      (embezzlementState_norm d positive)⟩

theorem dSVCanonicalFailurePrefix_eq_zero_of_rank_zero
    {d : ℕ} (rank : Fin (d + 1))
    (zero : rank.val = 0) :
    dSVCanonicalFailurePrefix rank = 0 := by
  have squared :
      ‖dSVCanonicalFailurePrefix rank‖ ^ 2 = 0 := by
    simpa [zero] using dSVCanonicalFailurePrefix_norm_sq rank
  have normzero : ‖dSVCanonicalFailurePrefix rank‖ = 0 := by
    nlinarith [norm_nonneg (dSVCanonicalFailurePrefix rank)]
  exact norm_eq_zero.mp normzero

theorem dSVCanonicalFailurePrefix_norm_eq_sqrt
    {d : ℕ} (rank : Fin (d + 1)) :
    ‖dSVCanonicalFailurePrefix rank‖ =
      Real.sqrt (rank.val : ℝ) := by
  have squared := dSVCanonicalFailurePrefix_norm_sq rank
  have root := Real.sq_sqrt (by positivity : 0 ≤ (rank.val : ℝ))
  nlinarith [norm_nonneg (dSVCanonicalFailurePrefix rank),
    Real.sqrt_nonneg (rank.val : ℝ)]

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

def dSVUniformDensityThresholdLeftBobBasis
    {d : ℕ} (ζ : BipartiteUnitVector d) :
    Matrix.unitaryGroup (Fin d) ℂ :=
  (dSVSoftBobLeftReducedDensity_posSemidef ζ).isHermitian.eigenvectorUnitary

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder MatrixOrder

def dSVUniformDensityPolarConjugateSwap
    {d : ℕ} (v : EuclideanSpace ℂ (Fin d × Fin d)) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  toLp 2 (fun q : Fin d × Fin d => star (v (q.2, q.1)))

theorem dSVUniformDensityPolarConjugateSwap_norm
    {d : ℕ} (v : EuclideanSpace ℂ (Fin d × Fin d)) :
    ‖dSVUniformDensityPolarConjugateSwap v‖ = ‖v‖ := by
  have squares :
      ‖dSVUniformDensityPolarConjugateSwap v‖ ^ 2 =
        ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [dSVUniformDensityPolarConjugateSwap,
      norm_star]
    exact Finset.sum_comm
  nlinarith [norm_nonneg
    (dSVUniformDensityPolarConjugateSwap v), norm_nonneg v]

def dSVUniformDensityPolarConjugateSwapTarget
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    BipartiteUnitVector d :=
  ⟨dSVUniformDensityPolarConjugateSwap ξ.val, by
    rw [dSVUniformDensityPolarConjugateSwap_norm]
    exact ξ.property⟩

theorem dSVUniformDensityPolarConjugateSwap_coefficient
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    targetCoefficientMatrix
        (dSVUniformDensityPolarConjugateSwapTarget ξ) =
      (targetCoefficientMatrix ξ).conjTranspose := by
  ext b a
  rfl

theorem dSVUniformDensityPolarConjugateSwap_reducedDensity
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    targetReducedDensity
        (dSVUniformDensityPolarConjugateSwapTarget ξ) =
      dSVSoftBobLeftReducedDensity ξ := by
  unfold targetReducedDensity
    dSVSoftBobLeftReducedDensity
  rw [dSVUniformDensityPolarConjugateSwap_coefficient]
  simp

def dSVUniformDensityPolarLeftSchmidtCoefficient
    {d : ℕ} (ξ : BipartiteUnitVector d)
    (i : Fin d) : ℝ :=
  Real.sqrt
    ((dSVSoftBobLeftReducedDensity_posSemidef ξ).isHermitian.eigenvalues i)

theorem exists_proofDSVUniformDensityPolarLeftCanonicalSchmidt
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    ∃ A : Matrix.unitaryGroup (Fin d) ℂ,
      ξ.val = schmidtVector
        (dSVUniformDensityPolarLeftSchmidtCoefficient ξ)
        A (dSVUniformDensityThresholdLeftBobBasis ξ) := by
  let χ := dSVUniformDensityPolarConjugateSwapTarget ξ
  have density : targetReducedDensity χ =
      dSVSoftBobLeftReducedDensity ξ :=
    dSVUniformDensityPolarConjugateSwap_reducedDensity ξ
  obtain ⟨V, decomposition⟩ :=
    exists_proofTargetCanonicalSpectralSchmidtDecomposition χ
  have canonical_basis :
      (targetReducedDensity_posSemidef χ).isHermitian.eigenvectorUnitary =
        dSVUniformDensityThresholdLeftBobBasis ξ := by
    unfold dSVUniformDensityThresholdLeftBobBasis
    simp only [density]
  have canonical_coefficient :
      targetCanonicalSchmidtCoefficient χ =
        dSVUniformDensityPolarLeftSchmidtCoefficient ξ := by
    funext i
    unfold targetCanonicalSchmidtCoefficient
      dSVUniformDensityPolarLeftSchmidtCoefficient
    simp only [density]
  rw [canonical_basis, canonical_coefficient] at decomposition
  refine ⟨conjugateUnitary V, ?_⟩
  ext ⟨a, b⟩
  have coordinate := congrArg
    (fun v : EuclideanSpace ℂ (Fin d × Fin d) => v (b, a))
    decomposition
  change star (ξ.val (a, b)) = _ at coordinate
  rw [schmidtVector_apply] at coordinate
  have unconjugated := congrArg star coordinate
  rw [schmidtVector_apply]
  simpa [map_sum, map_mul, conjugateUnitary_apply,
    mul_assoc, mul_left_comm, mul_comm] using unconjugated

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

def finiteTensorLocalUnitaryMatrix
    {ι β : Type*} [Fintype ι] [Fintype β] [DecidableEq β]
    (U : ι → Matrix.unitaryGroup β ℂ) :
    Matrix (ι → β) (ι → β) ℂ :=
  fun q r => ∏ i : ι, (U i : Matrix β β ℂ) (q i) (r i)

theorem finiteTensorLocalUnitaryMatrix_gram
    {ι β : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (U : ι → Matrix.unitaryGroup β ℂ) :
    (finiteTensorLocalUnitaryMatrix U).conjTranspose *
        finiteTensorLocalUnitaryMatrix U = 1 := by
  classical
  ext p q
  change
    (∑ r : ι → β,
      star (∏ i : ι, (U i : Matrix β β ℂ) (r i) (p i)) *
        (∏ i : ι, (U i : Matrix β β ℂ) (r i) (q i))) =
      (1 : Matrix (ι → β) (ι → β) ℂ) p q
  have factor :
      (∑ r : ι → β,
        star (∏ i : ι, (U i : Matrix β β ℂ) (r i) (p i)) *
          (∏ i : ι, (U i : Matrix β β ℂ) (r i) (q i))) =
        ∏ i : ι, ∑ x : β,
          star ((U i : Matrix β β ℂ) x (p i)) *
            (U i : Matrix β β ℂ) x (q i) := by
    calc
      _ = ∑ r : ι → β, ∏ i : ι,
          (star ((U i : Matrix β β ℂ) (r i) (p i)) *
            (U i : Matrix β β ℂ) (r i) (q i)) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [star_prod, ← Finset.prod_mul_distrib]
      _ = _ :=
        (Fintype.prod_sum fun i : ι => fun x : β =>
          star ((U i : Matrix β β ℂ) x (p i)) *
            (U i : Matrix β β ℂ) x (q i)).symm
  rw [factor]
  have single (i : ι) :
      (∑ x : β,
        star ((U i : Matrix β β ℂ) x (p i)) *
          (U i : Matrix β β ℂ) x (q i)) =
        (1 : Matrix β β ℂ) (p i) (q i) := by
    have gram := (Matrix.mem_unitaryGroup_iff').mp
      (U i).property
    have entry := congrArg
      (fun M : Matrix β β ℂ => M (p i) (q i)) gram
    simpa [Matrix.star_eq_conjTranspose,
      Matrix.mul_apply, Matrix.conjTranspose_apply] using entry
  simp_rw [single]
  by_cases equal : p = q
  · subst q
    simp
  · have different : ∃ i : ι, p i ≠ q i := by
      by_contra h
      push Not at h
      exact equal (funext h)
    obtain ⟨i, hi⟩ := different
    have zero :
        (∏ j : ι, (1 : Matrix β β ℂ) (p j) (q j)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
    rw [zero]
    simp [equal]

def finiteTensorLocalUnitary
    {ι β : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (U : ι → Matrix.unitaryGroup β ℂ) :
    Matrix.unitaryGroup (ι → β) ℂ := by
  refine ⟨finiteTensorLocalUnitaryMatrix U, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff',
    Matrix.star_eq_conjTranspose]
  exact finiteTensorLocalUnitaryMatrix_gram U

def controlledFiniteTensorLocalUnitary
    {Ω ι β : Type*}
    [Fintype Ω] [DecidableEq Ω]
    [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (U : Ω → ι → Matrix.unitaryGroup β ℂ) :
    Matrix.unitaryGroup (Σ _ : Ω, (ι → β)) ℂ :=
  coherentSharedRandomControlledUnitary
    (fun ω => finiteTensorLocalUnitary (U ω))

end

noncomputable section

open scoped BigOperators Kronecker ComplexOrder MatrixOrder

theorem controlledFiniteTensorLocalUnitary_apply
    {Ω ι β : Type*}
    [Fintype Ω] [DecidableEq Ω]
    [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (U : Ω → ι → Matrix.unitaryGroup β ℂ)
    (ω ν : Ω) (q r : ι → β) :
    (controlledFiniteTensorLocalUnitary U :
      Matrix (Σ _ : Ω, (ι → β)) (Σ _ : Ω, (ι → β)) ℂ)
        ⟨ω, q⟩ ⟨ν, r⟩ =
      if ω = ν then
        ∏ i : ι, (U ω i : Matrix β β ℂ) (q i) (r i)
      else 0 := by
  classical
  by_cases equal : ω = ν
  · subst ν
    simp [controlledFiniteTensorLocalUnitary,
      coherentSharedRandomControlledUnitary,
      finiteTensorLocalUnitary,
      finiteTensorLocalUnitaryMatrix,
      Matrix.blockDiagonal'_apply]
  · simp [controlledFiniteTensorLocalUnitary,
      coherentSharedRandomControlledUnitary,
      Matrix.blockDiagonal'_apply, equal]

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

abbrev DSVUniformDensityThresholdWholeHistoryLocalIndex
    (N d L : ℕ) :=
  Σ _ : Fin (L + 1),
    Fin (L + 1) → DSVUniformDensityThresholdLocalIndex N d

abbrev DSVUniformDensityThresholdWholeHistoryCatalystIndex
    (N d L : ℕ) :=
  Fin N × (Fin (L + 1) ×
    (Fin L → DSVUniformDensityThresholdLocalIndex N d))

def dSVUniformDensityThresholdWholeHistorySharedState
    (N d L : ℕ) :
    EuclideanSpace ℂ
      (DSVUniformDensityThresholdWholeHistoryLocalIndex N d L ×
        DSVUniformDensityThresholdWholeHistoryLocalIndex N d L) :=
  sharedThresholdResource
    (d := Fin (L + 1) →
      DSVUniformDensityThresholdLocalIndex N d)
    (fun flag : Fin (L + 1) =>
      if flag.val = 0 then (1 : ℝ) else 0)

theorem dSVUniformDensityThresholdWholeHistorySharedState_norm
    {N d : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (L : ℕ) :
    ‖dSVUniformDensityThresholdWholeHistorySharedState
      N d L‖ = 1 := by
  let k : Fin (L + 1) := ⟨0, by omega⟩
  let i : Fin (L + 1) →
      DSVUniformDensityThresholdLocalIndex N d :=
    fun _ => ⟨⟨0, grid⟩, ⟨0, dimension⟩⟩
  apply sharedThresholdResource_norm
    (fun flag : Fin (L + 1) =>
      if flag.val = 0 then (1 : ℝ) else 0) k i
  simp [k]

def dSVUniformDensityThresholdWholeHistoryTargetSplitEquiv
    (N d L : ℕ) :
    DSVUniformDensityThresholdWholeHistoryLocalIndex N d L ≃
      (Fin d ×
        DSVUniformDensityThresholdWholeHistoryCatalystIndex
          N d L) where
  toFun q :=
    ((q.2 0).2,
      ((q.2 0).1, (q.1, fun j => q.2 j.succ)))
  invFun q :=
    ⟨q.2.2.1,
      Fin.cons (⟨q.2.1, q.1⟩ :
        DSVUniformDensityThresholdLocalIndex N d)
        q.2.2.2⟩
  left_inv := by
    rintro ⟨flag, history⟩
    change
      (⟨flag, Fin.cons (history 0) (fun j => history j.succ)⟩ :
        DSVUniformDensityThresholdWholeHistoryLocalIndex
          N d L) = ⟨flag, history⟩
    congr 1
    exact Fin.cons_self_tail history
  right_inv := by
    rintro ⟨target, threshold, flag, history⟩
    simp

def dSVUniformDensityAliceHistorySpectralCopy
    {N d : ℕ} (ξ : BipartiteUnitVector d) :
    Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
  coherentSharedRandomControlledUnitary
    (fun _ : Fin N =>
      (dSVUniformDensityThresholdLeftBobBasis ξ)⁻¹)

def dSVUniformDensityBobHistoryCopyBasis
    {N d : ℕ} (ζ : BipartiteUnitVector d) :
    Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
  coherentSharedRandomControlledUnitary
    (fun _ : Fin N =>
      conjugateUnitary
        (dSVUniformDensityThresholdLeftBobBasis ζ))

theorem dSVUniformDensityCompletePureHistory_raw_norm
    (N d L : ℕ) :
    ‖sharedThresholdResourceRaw
      (d := Fin (L + 1) →
        DSVUniformDensityThresholdLocalIndex N d)
      (fun flag : Fin (L + 1) =>
        if flag.val = 0 then (1 : ℝ) else 0)‖ =
      ‖sharedThresholdResourceRaw (d := Fin d)
        (fun _ : Fin N => (1 : ℝ))‖ ^ (L + 1) := by
  let single := sharedThresholdResourceRaw (d := Fin d)
    (fun _ : Fin N => (1 : ℝ))
  let whole := sharedThresholdResourceRaw
    (d := Fin (L + 1) →
      DSVUniformDensityThresholdLocalIndex N d)
    (fun flag : Fin (L + 1) =>
      if flag.val = 0 then (1 : ℝ) else 0)
  have hsquare : ‖single‖ ^ 2 = (d : ℝ) * (N : ℝ) :=
    dSVUniformDensityThresholdRaw_norm_sq N d
  have hwhole :
      ‖whole‖ ^ 2 = (((N * d) ^ (L + 1) : ℕ) : ℝ) := by
    have original := sharedThresholdResourceRaw_norm_sq
      (d := Fin (L + 1) →
        DSVUniformDensityThresholdLocalIndex N d)
      (fun flag : Fin (L + 1) =>
        if flag.val = 0 then (1 : ℝ) else 0)
    simpa [DSVUniformDensityThresholdLocalIndex,
      whole] using original
  have hpower :
      (‖single‖ ^ (L + 1)) ^ 2 =
        (((N * d) ^ (L + 1) : ℕ) : ℝ) := by
    calc
      (‖single‖ ^ (L + 1)) ^ 2 =
        (‖single‖ ^ 2) ^ (L + 1) := by
          simp [← pow_mul, Nat.mul_comm]
      _ = (((N * d) ^ (L + 1) : ℕ) : ℝ) := by
          rw [hsquare]
          push_cast
          ring
  change ‖whole‖ = ‖single‖ ^ (L + 1)
  nlinarith [norm_nonneg whole,
    pow_nonneg (norm_nonneg single) (L + 1)]

theorem dSVUniformDensityCompletePureHistory_zeroFlag_apply
    (N d L : ℕ)
    (flag other : Fin (L + 1))
    (alice bob :
      DSVUniformDensityIndependentHistoryLocalIndex
        (L + 1) N d) :
    dSVUniformDensityThresholdWholeHistorySharedState N d L
      (⟨flag, alice⟩, ⟨other, bob⟩) =
      if flag.val = 0 ∧ other.val = 0 then
        dSVUniformDensityIndependentSharedState
          (L + 1) N d (alice, bob)
      else 0 := by
  classical
  let single := sharedThresholdResourceRaw (d := Fin d)
    (fun _ : Fin N => (1 : ℝ))
  let whole := sharedThresholdResourceRaw
    (d := Fin (L + 1) →
      DSVUniformDensityThresholdLocalIndex N d)
    (fun k : Fin (L + 1) =>
      if k.val = 0 then (1 : ℝ) else 0)
  have normalization :
      ‖whole‖ = ‖single‖ ^ (L + 1) :=
    dSVUniformDensityCompletePureHistory_raw_norm N d L
  have scalar :
      ‖whole‖⁻¹ = (‖single‖⁻¹) ^ (L + 1) := by
    rw [normalization, inv_pow]
  by_cases first_zero : flag = 0
  · subst flag
    by_cases second_zero : other = 0
    · subst other
      simp only [and_self]
      rw [dSVUniformDensityIndependentSharedState_apply]
      by_cases histories : alice = bob
      · subst bob
        have complex_scalar :
            ((‖whole‖⁻¹ : ℝ) : ℂ) =
              (((‖single‖⁻¹) ^ (L + 1) : ℝ) : ℂ) := by
          exact_mod_cast scalar
        have whole_amplitude :
            dSVUniformDensityThresholdWholeHistorySharedState
                N d L (⟨0, alice⟩, ⟨0, alice⟩) =
              ((‖whole‖⁻¹ : ℝ) : ℂ) := by
          simp [dSVUniformDensityThresholdWholeHistorySharedState,
            sharedThresholdResource,
            sharedThresholdResourceRaw, whole]
        have single_amplitude
            (q : DSVUniformDensityThresholdLocalIndex N d) :
            dSVUniformDensityThresholdSharedState N d (q, q) =
              ((‖single‖⁻¹ : ℝ) : ℂ) := by
          simp [dSVUniformDensityThresholdSharedState,
            sharedThresholdResource,
            sharedThresholdResourceRaw, single]
        rw [whole_amplitude]
        simp_rw [single_amplitude]
        simpa using complex_scalar
      · obtain ⟨j, different⟩ :
          ∃ j : Fin (L + 1), alice j ≠ bob j := by
          by_contra absent
          push Not at absent
          exact histories (funext absent)
        have zero :
            dSVUniformDensityThresholdSharedState N d
              (alice j, bob j) = 0 := by
          by_cases labels : (alice j).1 = (bob j).1
          · have works : (alice j).2 ≠ (bob j).2 := by
              intro same
              apply different
              exact Sigma.ext labels (by simpa using same)
            exact
              dSVUniformDensityThresholdSharedState_mismatchedWork
                N d (alice j).1 (bob j).1
                (alice j).2 (bob j).2 works
          · exact
              dSVUniformDensityThresholdSharedState_mismatchedFlag
                N d (alice j).1 (bob j).1
                (alice j).2 (bob j).2 labels
        have product_zero :
            (∏ i : Fin (L + 1),
              dSVUniformDensityThresholdSharedState N d
                (alice i, bob i)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ j) zero
        rw [product_zero]
        simp [dSVUniformDensityThresholdWholeHistorySharedState,
          sharedThresholdResource,
          sharedThresholdResourceRaw, histories]
    · have nonzero : other.val ≠ 0 := by
        simpa using second_zero
      have different : (0 : Fin (L + 1)) ≠ other := by
        exact Ne.symm second_zero
      simp [dSVUniformDensityThresholdWholeHistorySharedState,
        sharedThresholdResource,
        sharedThresholdResourceRaw, different, nonzero]
  · have nonzero : flag.val ≠ 0 := by
      simpa using first_zero
    simp [dSVUniformDensityThresholdWholeHistorySharedState,
      sharedThresholdResource,
      sharedThresholdResourceRaw, first_zero, nonzero]

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def scalarPurificationLp (z : ℝ) (hz : 0 ≤ z) :
    Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) :=
  ((scalarResolventFilter_memLp_two hz).ofReal (K := ℂ)).toLp
    (fun s : ℝ => ((z / (z + s) : ℝ) : ℂ))

theorem scalarPurificationLp_coeFn
    (z : ℝ) (hz : 0 ≤ z) :
    (scalarPurificationLp z hz : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)]
      (fun s : ℝ => ((z / (z + s) : ℝ) : ℂ)) :=
  ((scalarResolventFilter_memLp_two hz).ofReal
    (K := ℂ)).coeFn_toLp

def commonPurificationGenerator
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) :
    Sum (ι × d) d → Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))
  | .inl (i, k) =>
      scalarPurificationLp
        ((positive i).isHermitian.eigenvalues k)
        ((positive i).eigenvalues_nonneg k)
  | .inr k =>
      scalarPurificationLp
        (hM.isHermitian.eigenvalues k)
        (hM.eigenvalues_nonneg k)

def commonPurificationSubspace
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) :
    Submodule ℂ (Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))) :=
  Submodule.span ℂ
    (Set.range (commonPurificationGenerator F M positive hM))

theorem commonPurificationSubspace_finiteDimensional
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) :
    FiniteDimensional ℂ (commonPurificationSubspace F M positive hM) := by
  unfold commonPurificationSubspace
  exact FiniteDimensional.span_of_finite ℂ
    (Set.finite_range (commonPurificationGenerator F M positive hM))

theorem ensemble_scalarPurificationLp_mem_common
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (i : ι) (k : d) :
    scalarPurificationLp
        ((positive i).isHermitian.eigenvalues k)
        ((positive i).eigenvalues_nonneg k) ∈
      commonPurificationSubspace F M positive hM := by
  apply Submodule.subset_span
  exact ⟨Sum.inl (i, k), rfl⟩

theorem mean_scalarPurificationLp_mem_common
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (k : d) :
    scalarPurificationLp
        (hM.isHermitian.eigenvalues k)
        (hM.eigenvalues_nonneg k) ∈
      commonPurificationSubspace F M positive hM := by
  apply Submodule.subset_span
  exact ⟨Sum.inr k, rfl⟩

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder
  Matrix.Norms.Elementwise InnerProductSpace

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def spectralPurificationFilterEntryLp
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) (i j : d) :
    Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) :=
  (((spectralPurificationFilter_memLp_two F hF).eval i).eval j).toLp
    (fun s : ℝ => spectralPurificationFilter F hF s i j)

theorem spectralPurificationFilterEntryLp_coeFn
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) (i j : d) :
    (spectralPurificationFilterEntryLp F hF i j : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioi 0)]
        (fun s : ℝ => spectralPurificationFilter F hF s i j) :=
  (((spectralPurificationFilter_memLp_two F hF).eval i).eval j).coeFn_toLp

theorem spectralPurificationFilterEntryLp_eq_eigen_sum
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) (i j : d) :
    spectralPurificationFilterEntryLp F hF i j =
      ∑ k : d,
        (((hF.isHermitian.eigenvectorUnitary : Matrix d d ℂ) i k) *
          (star (hF.isHermitian.eigenvectorUnitary : Matrix d d ℂ)) k j) •
        scalarPurificationLp
          (hF.isHermitian.eigenvalues k)
          (hF.eigenvalues_nonneg k) := by
  classical
  let U := hF.isHermitian.eigenvectorUnitary
  let eigenvalue := hF.isHermitian.eigenvalues
  let coefficient : d → ℂ := fun k =>
    (U : Matrix d d ℂ) i k *
      star (U : Matrix d d ℂ) k j
  let generator : d → Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) :=
    fun k => scalarPurificationLp
      (eigenvalue k) (hF.eigenvalues_nonneg k)
  apply Lp.ext
  have hentry := spectralPurificationFilterEntryLp_coeFn F hF i j
  have hsum := Lp.coeFn_fun_finsetSum
    Finset.univ (fun k : d => coefficient k • generator k)
  have hgenerator :
      ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
        ∀ k : d,
          (coefficient k • generator k :
            Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))) s =
            coefficient k *
              ((eigenvalue k / (eigenvalue k + s) : ℝ) : ℂ) := by
    apply ae_all_iff.mpr
    intro k
    have hsmul := Lp.coeFn_smul (coefficient k) (generator k)
    have hscalar := scalarPurificationLp_coeFn
      (eigenvalue k) (hF.eigenvalues_nonneg k)
    filter_upwards [hsmul, hscalar] with s hs ht
    rw [hs]
    change
      coefficient k *
        (scalarPurificationLp (eigenvalue k)
          (hF.eigenvalues_nonneg k) : ℝ → ℂ) s = _
    rw [ht]
  filter_upwards [hentry, hsum, hgenerator] with s he hs hg
  rw [he, hs]
  change
    ((U : Matrix d d ℂ) *
      Matrix.diagonal (fun k =>
        ((eigenvalue k / (eigenvalue k + s) : ℝ) : ℂ)) *
      star (U : Matrix d d ℂ)) i j =
      ∑ k : d, (coefficient k • generator k :
        Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))) s
  simp_rw [hg]
  simp [Matrix.mul_apply, Matrix.diagonal, coefficient,
    mul_assoc, mul_comm]

theorem ensemble_spectralPurificationFilterEntryLp_mem_common
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef)
    (a : ι) (i j : d) :
    spectralPurificationFilterEntryLp (F a) (positive a) i j ∈
      commonPurificationSubspace F M positive hM := by
  rw [spectralPurificationFilterEntryLp_eq_eigen_sum]
  apply (commonPurificationSubspace F M positive hM).sum_mem
  intro k _
  apply (commonPurificationSubspace F M positive hM).smul_mem
  exact ensemble_scalarPurificationLp_mem_common
    F M positive hM a k

theorem mean_spectralPurificationFilterEntryLp_mem_common
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef)
    (i j : d) :
    spectralPurificationFilterEntryLp M hM i j ∈
      commonPurificationSubspace F M positive hM := by
  rw [spectralPurificationFilterEntryLp_eq_eigen_sum]
  apply (commonPurificationSubspace F M positive hM).sum_mem
  intro k _
  apply (commonPurificationSubspace F M positive hM).smul_mem
  exact mean_scalarPurificationLp_mem_common
    F M positive hM k

def ensemblePurificationSubspaceEntry
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef)
    (a : ι) (i j : d) :
    commonPurificationSubspace F M positive hM :=
  ⟨spectralPurificationFilterEntryLp (F a) (positive a) i j,
    ensemble_spectralPurificationFilterEntryLp_mem_common
      F M positive hM a i j⟩

def meanPurificationSubspaceEntry
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef)
    (i j : d) :
    commonPurificationSubspace F M positive hM :=
  ⟨spectralPurificationFilterEntryLp M hM i j,
    mean_spectralPurificationFilterEntryLp_mem_common
      F M positive hM i j⟩

noncomputable def commonPurificationOrthonormalBasis
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) :
    OrthonormalBasis
      (Fin (Module.finrank ℂ
        (commonPurificationSubspace F M positive hM)))
      ℂ (commonPurificationSubspace F M positive hM) := by
  letI : FiniteDimensional ℂ
      (commonPurificationSubspace F M positive hM) :=
    commonPurificationSubspace_finiteDimensional F M positive hM
  exact stdOrthonormalBasis ℂ
    (commonPurificationSubspace F M positive hM)

noncomputable def finitePurificationMatrix
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (a : ι) :
    Matrix
      (d × Fin (Module.finrank ℂ
        (commonPurificationSubspace F M positive hM))) d ℂ :=
  fun ik j =>
    (commonPurificationOrthonormalBasis F M positive hM).repr
      (ensemblePurificationSubspaceEntry F M positive hM a ik.1 j)
      ik.2

noncomputable def meanFinitePurificationMatrix
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) :
    Matrix
      (d × Fin (Module.finrank ℂ
        (commonPurificationSubspace F M positive hM))) d ℂ :=
  fun ik j =>
    (commonPurificationOrthonormalBasis F M positive hM).repr
      (meanPurificationSubspaceEntry F M positive hM ik.1 j)
      ik.2

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder
  Matrix.Norms.Elementwise InnerProductSpace

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem finitePurificationMatrix_gram_apply
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (a : ι) (i j : d) :
    ((finitePurificationMatrix F M positive hM a).conjTranspose *
      finitePurificationMatrix F M positive hM a) i j =
      ∑ r : d,
        inner ℂ
          (ensemblePurificationSubspaceEntry F M positive hM a r i)
          (ensemblePurificationSubspaceEntry F M positive hM a r j) := by
  classical
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    finitePurificationMatrix, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  let b := commonPurificationOrthonormalBasis F M positive hM
  let u := ensemblePurificationSubspaceEntry
    F M positive hM a r i
  let v := ensemblePurificationSubspaceEntry
    F M positive hM a r j
  have hisometry := b.repr.inner_map_map u v
  change (∑ k, star (b.repr u k) * b.repr v k) =
    inner ℂ u v
  rw [← hisometry, EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, mul_comm]

theorem ensemblePurificationSubspaceEntry_inner_eq_integral
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef)
    (a : ι) (r i j : d) :
    inner ℂ
        (ensemblePurificationSubspaceEntry F M positive hM a r i)
        (ensemblePurificationSubspaceEntry F M positive hM a r j) =
      ∫ s in Ioi (0 : ℝ),
        star (spectralPurificationFilter (F a) (positive a) s r i) *
          spectralPurificationFilter (F a) (positive a) s r j := by
  rw [Submodule.coe_inner, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  have hi := spectralPurificationFilterEntryLp_coeFn
    (F a) (positive a) r i
  have hj := spectralPurificationFilterEntryLp_coeFn
    (F a) (positive a) r j
  filter_upwards [hi, hj] with s hs ht
  change
    inner ℂ
      (spectralPurificationFilterEntryLp
        (F a) (positive a) r i s)
      (spectralPurificationFilterEntryLp
        (F a) (positive a) r j s) = _
  rw [hs, ht]
  simp [RCLike.inner_apply, mul_comm]

theorem finitePurificationMatrix_gram_eq_integral
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (a : ι) :
    (finitePurificationMatrix F M positive hM a).conjTranspose *
        finitePurificationMatrix F M positive hM a =
      ∫ s in Ioi (0 : ℝ),
        star (spectralPurificationFilter (F a) (positive a) s) *
          spectralPurificationFilter (F a) (positive a) s := by
  classical
  have hfilter := spectralPurificationFilter_memLp_two
    (F a) (positive a)
  have hmatrix := spectralPurificationFilter_gram_integrable
    (F a) (positive a)
  have hrows :
      ∀ i : d,
        Integrable
          (fun s : ℝ =>
            (star (spectralPurificationFilter (F a) (positive a) s) *
              spectralPurificationFilter (F a) (positive a) s) i)
          (volume.restrict (Ioi 0)) :=
    fun i => hmatrix.eval i
  ext i j
  rw [finitePurificationMatrix_gram_apply]
  rw [MeasureTheory.eval_integral hrows i,
    MeasureTheory.eval_integral (fun k => (hrows i).eval k) j]
  simp_rw [ensemblePurificationSubspaceEntry_inner_eq_integral]
  have hproduct (r : d) :
      Integrable
        (fun s : ℝ =>
          star (spectralPurificationFilter (F a) (positive a) s r i) *
            spectralPurificationFilter (F a) (positive a) s r j)
        (volume.restrict (Ioi 0)) :=
    (((hfilter.eval r).eval i).star).integrable_mul
      ((hfilter.eval r).eval j)
  rw [← integral_finsetSum Finset.univ (fun r _ => hproduct r)]
  apply integral_congr_ae
  filter_upwards with s
  simp [Matrix.mul_apply, Matrix.star_apply]

theorem finitePurificationMatrix_gram
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (a : ι) :
    (finitePurificationMatrix F M positive hM a).conjTranspose *
      finitePurificationMatrix F M positive hM a = F a := by
  rw [finitePurificationMatrix_gram_eq_integral]
  exact integral_spectralPurificationFilter_gram (F a) (positive a)

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder
  Matrix.Norms.Elementwise InnerProductSpace

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem finitePurificationMatrix_difference_gram_apply
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (a : ι) (i j : d) :
    ((finitePurificationMatrix F M positive hM a -
          meanFinitePurificationMatrix F M positive hM).conjTranspose *
        (finitePurificationMatrix F M positive hM a -
          meanFinitePurificationMatrix F M positive hM)) i j =
      ∑ r : d,
        inner ℂ
          (ensemblePurificationSubspaceEntry F M positive hM a r i -
            meanPurificationSubspaceEntry F M positive hM r i)
          (ensemblePurificationSubspaceEntry F M positive hM a r j -
            meanPurificationSubspaceEntry F M positive hM r j) := by
  classical
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.sub_apply, finitePurificationMatrix,
    meanFinitePurificationMatrix, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  let b := commonPurificationOrthonormalBasis F M positive hM
  let u := ensemblePurificationSubspaceEntry
    F M positive hM a r i
  let u₀ := meanPurificationSubspaceEntry
    F M positive hM r i
  let v := ensemblePurificationSubspaceEntry
    F M positive hM a r j
  let v₀ := meanPurificationSubspaceEntry
    F M positive hM r j
  have hisometry := b.repr.inner_map_map (u - u₀) (v - v₀)
  change
    (∑ k, star (b.repr u k - b.repr u₀ k) *
      (b.repr v k - b.repr v₀ k)) =
      inner ℂ (u - u₀) (v - v₀)
  rw [← hisometry, EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, map_sub, mul_comm]

theorem purificationSubspaceEntry_difference_inner_eq_integral
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (a : ι) (r i j : d) :
    inner ℂ
      (ensemblePurificationSubspaceEntry F M positive hM a r i -
        meanPurificationSubspaceEntry F M positive hM r i)
      (ensemblePurificationSubspaceEntry F M positive hM a r j -
        meanPurificationSubspaceEntry F M positive hM r j) =
      ∫ s in Ioi (0 : ℝ),
        star (spectralPurificationFilter (F a) (positive a) s r i -
          spectralPurificationFilter M hM s r i) *
        (spectralPurificationFilter (F a) (positive a) s r j -
          spectralPurificationFilter M hM s r j) := by
  rw [Submodule.coe_inner, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  let fi := spectralPurificationFilterEntryLp
    (F a) (positive a) r i
  let mi := spectralPurificationFilterEntryLp M hM r i
  let fj := spectralPurificationFilterEntryLp
    (F a) (positive a) r j
  let mj := spectralPurificationFilterEntryLp M hM r j
  have hsubi := Lp.coeFn_sub fi mi
  have hsubj := Lp.coeFn_sub fj mj
  have hfi := spectralPurificationFilterEntryLp_coeFn
    (F a) (positive a) r i
  have hmi := spectralPurificationFilterEntryLp_coeFn M hM r i
  have hfj := spectralPurificationFilterEntryLp_coeFn
    (F a) (positive a) r j
  have hmj := spectralPurificationFilterEntryLp_coeFn M hM r j
  filter_upwards [hsubi, hsubj, hfi, hmi, hfj, hmj]
    with s hi hj hfi' hmi' hfj' hmj'
  change inner ℂ ((fi - mi) s) ((fj - mj) s) = _
  rw [hi, hj]
  change inner ℂ (fi s - mi s) (fj s - mj s) = _
  change
    inner ℂ
      ((spectralPurificationFilterEntryLp
        (F a) (positive a) r i : ℝ → ℂ) s -
        (spectralPurificationFilterEntryLp M hM r i : ℝ → ℂ) s)
      ((spectralPurificationFilterEntryLp
        (F a) (positive a) r j : ℝ → ℂ) s -
        (spectralPurificationFilterEntryLp M hM r j : ℝ → ℂ) s) = _
  rw [hfi', hmi', hfj', hmj']
  simp [RCLike.inner_apply, mul_comm]

theorem finitePurificationMatrix_difference_gram_eq_integral
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (a : ι) :
    (finitePurificationMatrix F M positive hM a -
        meanFinitePurificationMatrix F M positive hM).conjTranspose *
      (finitePurificationMatrix F M positive hM a -
        meanFinitePurificationMatrix F M positive hM) =
      ∫ s in Ioi (0 : ℝ),
        star (spectralPurificationFilter (F a) (positive a) s -
          spectralPurificationFilter M hM s) *
        (spectralPurificationFilter (F a) (positive a) s -
          spectralPurificationFilter M hM s) := by
  classical
  have hdelta :
      MemLp (fun s : ℝ =>
        spectralPurificationFilter (F a) (positive a) s -
          spectralPurificationFilter M hM s)
        2 (volume.restrict (Ioi 0)) :=
    (spectralPurificationFilter_memLp_two (F a) (positive a)).sub
      (spectralPurificationFilter_memLp_two M hM)
  have hmatrix := spectralPurificationFilter_difference_gram_integrable
    (F a) M (positive a) hM
  have hrows :
      ∀ i : d,
        Integrable
          (fun s : ℝ =>
            (star (spectralPurificationFilter (F a) (positive a) s -
                spectralPurificationFilter M hM s) *
              (spectralPurificationFilter (F a) (positive a) s -
                spectralPurificationFilter M hM s)) i)
          (volume.restrict (Ioi 0)) :=
    fun i => hmatrix.eval i
  ext i j
  rw [finitePurificationMatrix_difference_gram_apply]
  rw [MeasureTheory.eval_integral hrows i,
    MeasureTheory.eval_integral (fun k => (hrows i).eval k) j]
  simp_rw [purificationSubspaceEntry_difference_inner_eq_integral]
  have hproduct (r : d) :
      Integrable
        (fun s : ℝ =>
          star (spectralPurificationFilter (F a) (positive a) s r i -
            spectralPurificationFilter M hM s r i) *
            (spectralPurificationFilter (F a) (positive a) s r j -
              spectralPurificationFilter M hM s r j))
        (volume.restrict (Ioi 0)) :=
    (((hdelta.eval r).eval i).star).integrable_mul
      ((hdelta.eval r).eval j)
  rw [← integral_finsetSum Finset.univ (fun r _ => hproduct r)]
  apply integral_congr_ae
  filter_upwards with s
  simp [Matrix.mul_apply, Matrix.star_apply]

theorem weighted_finitePurificationMatrix_difference_gram
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ)
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) :
    (∑ a : ι, weight a •
      ((finitePurificationMatrix F M positive hM a -
          meanFinitePurificationMatrix F M positive hM).conjTranspose *
        (finitePurificationMatrix F M positive hM a -
          meanFinitePurificationMatrix F M positive hM))) =
      ∫ s in Ioi (0 : ℝ),
        weightedSpectralFilterVariance weight F M positive hM s := by
  classical
  have hterm (a : ι) :
      Integrable
        (fun s : ℝ => weight a •
          (star (spectralPurificationFilter (F a) (positive a) s -
              spectralPurificationFilter M hM s) *
            (spectralPurificationFilter (F a) (positive a) s -
              spectralPurificationFilter M hM s)))
        (volume.restrict (Ioi 0)) :=
    (spectralPurificationFilter_difference_gram_integrable
      (F a) M (positive a) hM).smul (weight a)
  simp_rw [finitePurificationMatrix_difference_gram_eq_integral]
  unfold weightedSpectralFilterVariance
  rw [integral_finsetSum Finset.univ (fun a _ => hterm a)]
  simp_rw [integral_smul]

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder
  Matrix.Norms.Elementwise InnerProductSpace

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem finite_purification_log_entropy_jensen
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (M : Matrix d d ℂ)
    (nonnegative : ∀ i, 0 ≤ weight i)
    (normalized : (∑ i : ι, weight i) = 1)
    (mean : (∑ i : ι, weight i • F i) = M)
    (positive : ∀ i, (F i).PosSemidef) :
    let hM : M.PosSemidef := by
      rw [← mean]
      exact weighted_positive_matrix_mean weight F nonnegative positive
    ((∑ i : ι, weight i •
        cfc (fun z : ℝ => z * Real.log z) (F i)) -
      cfc (fun z : ℝ => z * Real.log z) M -
      (∑ i : ι, weight i •
        ((finitePurificationMatrix F M positive hM i -
            meanFinitePurificationMatrix F M positive hM).conjTranspose *
          (finitePurificationMatrix F M positive hM i -
            meanFinitePurificationMatrix F M positive hM)))).PosSemidef := by
  dsimp
  let hM : M.PosSemidef := by
    rw [← mean]
    exact weighted_positive_matrix_mean weight F nonnegative positive
  have h := exact_matrix_log_entropy_filter_jensen
    weight F M nonnegative normalized mean positive
  change
    ((∑ i : ι, weight i •
        cfc (fun z : ℝ => z * Real.log z) (F i)) -
      cfc (fun z : ℝ => z * Real.log z) M -
      (∫ s in Ioi (0 : ℝ),
        weightedSpectralFilterVariance weight F M positive hM s)).PosSemidef at h
  rw [← weighted_finitePurificationMatrix_difference_gram
    weight F M positive hM] at h
  exact h

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

def matrixPurificationVector
    {d : Type*} [Fintype d]
    (K : Matrix d d ℂ) : EuclideanSpace ℂ (d × d) :=
  toLp 2 (Matrix.vec K)

theorem matrixPurificationVector_norm_sq
    {d : Type*} [Fintype d]
    (K : Matrix d d ℂ) :
    ‖matrixPurificationVector K‖ ^ 2 =
      (Matrix.trace (Matrix.conjTranspose K * K)).re := by
  calc
    ‖matrixPurificationVector K‖ ^ 2 =
        (⟪matrixPurificationVector K,
          matrixPurificationVector K⟫_ℂ).re :=
      norm_sq_eq_re_inner (𝕜 := ℂ) (matrixPurificationVector K)
    _ = (star (Matrix.vec K) ⬝ᵥ Matrix.vec K).re := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      change
        (Matrix.vec K ⬝ᵥ star (Matrix.vec K)).re =
          (star (Matrix.vec K) ⬝ᵥ Matrix.vec K).re
      rw [dotProduct_comm]
    _ = (Matrix.trace (Matrix.conjTranspose K * K)).re := by
      rw [Matrix.star_vec_dotProduct_vec]

def strategyPurificationShuffle
    (dA dB : Type) :
    ((dA × (dA × dB)) × dB) ≃ ((dA × dB) × (dA × dB)) where
  toFun q := (q.1.2, (q.1.1, q.2))
  invFun q := ((q.2.1, q.1), q.2.2)
  left_inv := by
    rintro ⟨⟨a, k⟩, b⟩
    rfl
  right_inv := by
    rintro ⟨k, ⟨a, b⟩⟩
    rfl

def strategyPurificationVector
    {X Y A B : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} (S : Strategy G) :
    EuclideanSpace ℂ ((S.Alice × (S.Alice × S.Bob)) × S.Bob) :=
  toLp 2
    (fun q =>
      Matrix.vec (spectralSupportSqrt S.state.matrix S.state.positive)
        (strategyPurificationShuffle S.Alice S.Bob q))

theorem strategyPurificationVector_norm_sq
    {X Y A B : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} (S : Strategy G) :
    ‖strategyPurificationVector S‖ ^ 2 =
      ‖matrixPurificationVector
          (spectralSupportSqrt S.state.matrix S.state.positive)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simpa [strategyPurificationVector, matrixPurificationVector] using
    Equiv.sum_comp (strategyPurificationShuffle S.Alice S.Bob)
      (fun q : (S.Alice × S.Bob) × (S.Alice × S.Bob) =>
        ‖Matrix.vec
          (spectralSupportSqrt S.state.matrix S.state.positive) q‖ ^ 2)

theorem strategyPurificationVector_norm
    {X Y A B : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} (S : Strategy G) :
    ‖strategyPurificationVector S‖ = 1 := by
  let K := spectralSupportSqrt S.state.matrix S.state.positive
  have h_hermitian : (Matrix.conjTranspose K) = K :=
    (spectralSupportFunctional_isHermitian
      S.state.matrix S.state.positive Real.sqrt).eq
  have h_sq : ‖strategyPurificationVector S‖ ^ 2 = 1 := by
    calc
      ‖strategyPurificationVector S‖ ^ 2 =
          ‖matrixPurificationVector K‖ ^ 2 :=
            strategyPurificationVector_norm_sq S
      _ = (Matrix.trace (Matrix.conjTranspose K * K)).re :=
            matrixPurificationVector_norm_sq K
      _ = (Matrix.trace S.state.matrix).re := by
            rw [h_hermitian]
            change
              (Matrix.trace
                (spectralSupportSqrt S.state.matrix S.state.positive *
                  spectralSupportSqrt S.state.matrix S.state.positive)).re =
                (Matrix.trace S.state.matrix).re
            rw [spectralSupportSqrt_sq]
      _ = 1 := by rw [S.state.trace_one]; norm_num
  nlinarith [norm_nonneg (strategyPurificationVector S)]

theorem reindexedMatrixQuadratic
    {d e : Type*} [Fintype d] [Fintype e]
    [DecidableEq d] [DecidableEq e]
    (φ : e ≃ d) (M : Matrix d d ℂ) (v : d → ℂ) :
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := e) (𝕜 := ℂ)
        (M.submatrix φ φ))
      (toLp 2 (v ∘ φ)) =
      (star v ⬝ᵥ M.mulVec v).re := by
  unfold quadraticExpectation
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change
    (((M.submatrix φ φ).mulVec (v ∘ φ)) ⬝ᵥ
      star (v ∘ φ)).re = (star v ⬝ᵥ M.mulVec v).re
  have h_mul :
      (M.submatrix φ φ).mulVec (v ∘ φ) =
        M.mulVec v ∘ φ := by
    simpa [Function.comp_def] using
      Matrix.submatrix_mulVec_equiv M (v ∘ φ) φ φ
  have h_star : star (v ∘ φ) = star v ∘ φ := by
    rfl
  rw [h_mul, h_star, comp_equiv_dotProduct_comp_equiv]
  rw [dotProduct_comm]

def purificationAlicePOVM
    {ι d k : Type*} [Fintype ι]
    [Fintype d] [Fintype k] [DecidableEq d] [DecidableEq k]
    (P : POVM ι d) : POVM ι (d × k) where
  effect a := P.effect a ⊗ₖ (1 : Matrix k k ℂ)
  positive a := (P.positive a).kronecker Matrix.PosSemidef.one
  complete := by
    classical
    calc
      (∑ a : ι, P.effect a ⊗ₖ (1 : Matrix k k ℂ)) =
          (∑ a : ι, P.effect a) ⊗ₖ (1 : Matrix k k ℂ) := by
            ext ⟨i, u⟩ ⟨j, v⟩
            simp [Matrix.sum_apply, Matrix.kroneckerMap_apply,
              Finset.sum_mul]
      _ = 1 := by
        rw [P.complete]
        exact Matrix.one_kronecker_one

theorem purificationJointEffect_submatrix
    {dA dB : Type} [Fintype dA] [Fintype dB]
    [DecidableEq dA] [DecidableEq dB]
    (A : Matrix dA dA ℂ) (B : Matrix dB dB ℂ) :
    (A ⊗ₖ (1 : Matrix (dA × dB) (dA × dB) ℂ)) ⊗ₖ B =
      ((1 : Matrix (dA × dB) (dA × dB) ℂ) ⊗ₖ
        (A ⊗ₖ B)).submatrix
          (strategyPurificationShuffle dA dB)
          (strategyPurificationShuffle dA dB) := by
  classical
  ext ⟨⟨a, k⟩, b⟩ ⟨⟨a', k'⟩, b'⟩
  simp [Matrix.kroneckerMap_apply, Matrix.submatrix_apply,
    strategyPurificationShuffle, Matrix.one_apply]

theorem strategyPurificationVector_quadratic
    {X Y A B : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} (S : Strategy G)
    (EA : Matrix S.Alice S.Alice ℂ)
    (EB : Matrix S.Bob S.Bob ℂ) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := (S.Alice × (S.Alice × S.Bob)) × S.Bob) (𝕜 := ℂ)
        ((EA ⊗ₖ (1 : Matrix (S.Alice × S.Bob)
          (S.Alice × S.Bob) ℂ)) ⊗ₖ EB))
      (strategyPurificationVector S) =
      (Matrix.trace
        (S.state.matrix * (EA ⊗ₖ EB))).re := by
  let K := spectralSupportSqrt S.state.matrix S.state.positive
  let E := EA ⊗ₖ EB
  let φ := strategyPurificationShuffle S.Alice S.Bob
  have h_hermitian : (Matrix.conjTranspose K) = K :=
    (spectralSupportFunctional_isHermitian
      S.state.matrix S.state.positive Real.sqrt).eq
  have h_lift := purificationJointEffect_submatrix EA EB
  change
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := (S.Alice × (S.Alice × S.Bob)) × S.Bob) (𝕜 := ℂ)
        ((EA ⊗ₖ (1 : Matrix (S.Alice × S.Bob)
          (S.Alice × S.Bob) ℂ)) ⊗ₖ EB))
      (toLp 2 (Matrix.vec K ∘ φ)) =
      (Matrix.trace (S.state.matrix * E)).re
  rw [h_lift]
  rw [reindexedMatrixQuadratic φ
    ((1 : Matrix (S.Alice × S.Bob) (S.Alice × S.Bob) ℂ) ⊗ₖ E)
    (Matrix.vec K)]
  have h_vec :
      Matrix.mulVec
        ((1 : Matrix (S.Alice × S.Bob) (S.Alice × S.Bob) ℂ) ⊗ₖ E)
        (Matrix.vec K) =
        Matrix.vec (E * K) := by
    exact (Matrix.vec_mul_eq_mulVec E K).symm
  rw [h_vec, Matrix.star_vec_dotProduct_vec]
  rw [h_hermitian]
  congr 1
  calc
    Matrix.trace (K * (E * K)) =
      Matrix.trace (K * E * K) := by rw [Matrix.mul_assoc]
    _ = Matrix.trace (K * K * E) := by
      rw [Matrix.trace_mul_cycle]
    _ = Matrix.trace (S.state.matrix * E) := by
      change
        Matrix.trace
          (spectralSupportSqrt S.state.matrix S.state.positive *
            spectralSupportSqrt S.state.matrix S.state.positive * E) = _
      rw [spectralSupportSqrt_sq]

def purifiedStrategy
    {X Y A B : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} (S : Strategy G) : Strategy G :=
  pureVectorStrategy G (strategyPurificationVector S)
    (strategyPurificationVector_norm S)
    (fun x => purificationAlicePOVM (S.aliceMeasurement x))
    S.bobMeasurement

theorem purifiedStrategy_outcomeProbability
    {X Y A B : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} (S : Strategy G)
    (x : X) (y : Y) (a : A) (b : B) :
    (purifiedStrategy S).outcomeProbability x y a b =
      S.outcomeProbability x y a b := by
  unfold purifiedStrategy
  rw [pureVectorStrategy_outcomeProbability]
  exact strategyPurificationVector_quadratic S
    ((S.aliceMeasurement x).effect a)
    ((S.bobMeasurement y).effect b)

theorem purifiedStrategy_winProbability
    {X Y A B : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} (S : Strategy G) :
    (purifiedStrategy S).winProbability = S.winProbability := by
  unfold Strategy.winProbability
  simp_rw [purifiedStrategy_outcomeProbability]

theorem rectangular_matrix_mulVec_norm_sq
    {d e : Type*} [Fintype d] [Fintype e] [DecidableEq d]
    (K : Matrix e d ℂ) (z : EuclideanSpace ℂ d) :
    ‖toLp 2 (K.mulVec (ofLp z))‖ ^ 2 =
      quadraticExpectation
        (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ)
          (K.conjTranspose * K)) z := by
  calc
    ‖toLp 2 (K.mulVec (ofLp z))‖ ^ 2 =
        (⟪toLp 2 (K.mulVec (ofLp z)),
          toLp 2 (K.mulVec (ofLp z))⟫_ℂ).re :=
      norm_sq_eq_re_inner (𝕜 := ℂ)
        (toLp 2 (K.mulVec (ofLp z)))
    _ = (star (K.mulVec (ofLp z)) ⬝ᵥ
          K.mulVec (ofLp z)).re := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      change
        (K.mulVec (ofLp z) ⬝ᵥ star (K.mulVec (ofLp z))).re = _
      rw [dotProduct_comm]
    _ = (star (ofLp z) ⬝ᵥ
          (K.conjTranspose * K).mulVec (ofLp z)).re := by
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
        Matrix.mulVec_mulVec]
    _ = quadraticExpectation
          (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ)
            (K.conjTranspose * K)) z := by
      unfold quadraticExpectation
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      change
        (star (ofLp z) ⬝ᵥ
            (K.conjTranspose * K).mulVec (ofLp z)).re =
          ((K.conjTranspose * K).mulVec (ofLp z) ⬝ᵥ
            star (ofLp z)).re
      rw [dotProduct_comm]

def finiteLocalPurificationJointMatrix
    {X Y A B eA eB : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype eA] [Fintype eB]
    {G : Game X Y A B} (S : Strategy G)
    (KA : Matrix eA S.Alice ℂ) (KB : Matrix eB S.Bob ℂ) :
    Matrix ((eA × (S.Alice × S.Bob)) × eB)
      ((S.Alice × (S.Alice × S.Bob)) × S.Bob) ℂ :=
  (KA ⊗ₖ
    (1 : Matrix (S.Alice × S.Bob) (S.Alice × S.Bob) ℂ)) ⊗ₖ KB

def finiteLocalPurificationVector
    {X Y A B eA eB : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype eA] [Fintype eB]
    {G : Game X Y A B} (S : Strategy G)
    (KA : Matrix eA S.Alice ℂ) (KB : Matrix eB S.Bob ℂ) :
    EuclideanSpace ℂ ((eA × (S.Alice × S.Bob)) × eB) :=
  toLp 2
    ((finiteLocalPurificationJointMatrix S KA KB).mulVec
      (ofLp (strategyPurificationVector S)))

theorem finiteLocalPurificationJointMatrix_gram
    {X Y A B eA eB : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype eA] [Fintype eB]
    {G : Game X Y A B} (S : Strategy G)
    (KA : Matrix eA S.Alice ℂ) (KB : Matrix eB S.Bob ℂ) :
    (finiteLocalPurificationJointMatrix S KA KB).conjTranspose *
        finiteLocalPurificationJointMatrix S KA KB =
      ((KA.conjTranspose * KA) ⊗ₖ
        (1 : Matrix (S.Alice × S.Bob) (S.Alice × S.Bob) ℂ)) ⊗ₖ
        (KB.conjTranspose * KB) := by
  unfold finiteLocalPurificationJointMatrix
  rw [Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul]
  simp

theorem finiteLocalPurificationVector_norm_sq
    {X Y A B eA eB : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype eA] [Fintype eB]
    {G : Game X Y A B} (S : Strategy G)
    (KA : Matrix eA S.Alice ℂ) (KB : Matrix eB S.Bob ℂ) :
    ‖finiteLocalPurificationVector S KA KB‖ ^ 2 =
      (Matrix.trace
        (S.state.matrix *
          ((KA.conjTranspose * KA) ⊗ₖ
            (KB.conjTranspose * KB)))).re := by
  unfold finiteLocalPurificationVector
  rw [rectangular_matrix_mulVec_norm_sq,
    finiteLocalPurificationJointMatrix_gram]
  exact strategyPurificationVector_quadratic S
    (KA.conjTranspose * KA) (KB.conjTranspose * KB)

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder InnerProductSpace

theorem dSVUniformDensityMixedProtocolLocalAction_norm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U V : Matrix.unitaryGroup ι ℂ)
    (z : EuclideanSpace ℂ (ι × ι)) :
    ‖toLp 2
        (((U : Matrix ι ι ℂ) ⊗ₖ
          (V : Matrix ι ι ℂ)).mulVec (ofLp z))‖ = ‖z‖ := by
  classical
  let M : Matrix (ι × ι) (ι × ι) ℂ :=
    (U : Matrix ι ι ℂ) ⊗ₖ (V : Matrix ι ι ℂ)
  have unitary : M ∈ Matrix.unitaryGroup (ι × ι) ℂ :=
    Matrix.kronecker_mem_unitary U.property V.property
  have gram : M.conjTranspose * M = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff'.mp unitary)
  have squared :
      ‖toLp 2 (M.mulVec (ofLp z))‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [rectangular_matrix_mulVec_norm_sq, gram]
    simp [quadraticExpectation, ← Complex.ofReal_pow]
  change ‖toLp 2 (M.mulVec (ofLp z))‖ = ‖z‖
  nlinarith [norm_nonneg (toLp 2 (M.mulVec (ofLp z))),
    norm_nonneg z]

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

def dSVUniformDensityPhysicalAsyncSigmaContinuation
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (U V : ι → Matrix.unitaryGroup κ ℂ)
    (z : EuclideanSpace ℂ
      ((Σ _ : ι, κ) × (Σ _ : ι, κ))) :
    EuclideanSpace ℂ ((Σ _ : ι, κ) × (Σ _ : ι, κ)) := by
  classical
  let A := coherentSharedRandomControlledUnitary U
  let B := coherentSharedRandomControlledUnitary V
  exact toLp 2 ((A.val ⊗ₖ B.val).mulVec (ofLp z))

theorem dSVUniformDensityPhysicalAsyncSigmaContinuation_norm
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (U V : ι → Matrix.unitaryGroup κ ℂ)
    (z : EuclideanSpace ℂ
      ((Σ _ : ι, κ) × (Σ _ : ι, κ))) :
    ‖dSVUniformDensityPhysicalAsyncSigmaContinuation U V z‖ =
      ‖z‖ := by
  simpa [dSVUniformDensityPhysicalAsyncSigmaContinuation]
    using dSVUniformDensityMixedProtocolLocalAction_norm
      (coherentSharedRandomControlledUnitary U)
      (coherentSharedRandomControlledUnitary V) z

theorem dSVUniformDensityFirstAcceptFinitePrefix
    {L : ℕ} (s : Finset (Fin L)) (j : Fin L) :
    (if h : s.Nonempty then (s.min' h).succ else
      (0 : Fin (L + 1))) = j.succ ↔
      j ∈ s ∧ ∀ i : Fin L, i < j → i ∉ s := by
  classical
  constructor
  · intro selected
    by_cases nonempty : s.Nonempty
    · have minimum : s.min' nonempty = j := by
        have equal : (s.min' nonempty).succ = j.succ := by
          simpa [nonempty] using selected
        exact Fin.succ_injective L equal
      constructor
      · rw [← minimum]
        exact Finset.min'_mem s nonempty
      · intro i before contained
        have least : s.min' nonempty ≤ i := Finset.min'_le s i contained
        rw [minimum] at least
        exact (not_le_of_gt before) least
    · have impossible : (0 : Fin (L + 1)) = j.succ := by
        simpa [nonempty] using selected
      exact False.elim (Fin.succ_ne_zero j impossible.symm)
  · rintro ⟨accepted, prior⟩
    have nonempty : s.Nonempty := ⟨j, accepted⟩
    have minimum : s.min' nonempty = j := by
      apply (Finset.min'_eq_iff s nonempty j).mpr
      refine ⟨accepted, ?_⟩
      intro i contained
      exact le_of_not_gt (fun before => prior i before contained)
    simp [nonempty, minimum]

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 3072

theorem dSVUniformDensityFirstAcceptControlledTensor_inv_apply
    {Ω ι β : Type*}
    [Fintype Ω] [DecidableEq Ω]
    [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (U : Ω → ι → Matrix.unitaryGroup β ℂ)
    (ω ν : Ω) (q r : ι → β) :
    (((controlledFiniteTensorLocalUnitary U)⁻¹ :
      Matrix.unitaryGroup (Σ _ : Ω, (ι → β)) ℂ) :
      Matrix (Σ _ : Ω, (ι → β)) (Σ _ : Ω, (ι → β)) ℂ)
      ⟨ω, q⟩ ⟨ν, r⟩ =
      if ω = ν then
        ∏ i : ι, star ((U ω i : Matrix β β ℂ) (r i) (q i))
      else 0 := by
  classical
  change
    star ((controlledFiniteTensorLocalUnitary U :
      Matrix (Σ _ : Ω, (ι → β)) (Σ _ : Ω, (ι → β)) ℂ)
      ⟨ν, r⟩ ⟨ω, q⟩) = _
  rw [controlledFiniteTensorLocalUnitary_apply]
  by_cases same : ω = ν
  · subst ν
    simp [star_prod]
  · have reversed : ν ≠ ω := Ne.symm same
    simp [same, reversed]

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

theorem coherentSharedRandomControlledUnitary_inv
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (U : ι → Matrix.unitaryGroup κ ℂ) :
    (coherentSharedRandomControlledUnitary U)⁻¹ =
      coherentSharedRandomControlledUnitary
        (fun i => (U i)⁻¹) := by
  classical
  apply Subtype.ext
  ext ⟨i, x⟩ ⟨j, y⟩
  change
    star ((coherentSharedRandomControlledUnitary U :
      Matrix (Σ _ : ι, κ) (Σ _ : ι, κ) ℂ) ⟨j, y⟩ ⟨i, x⟩) =
      (coherentSharedRandomControlledUnitary
        (fun i => (U i)⁻¹) :
        Matrix (Σ _ : ι, κ) (Σ _ : ι, κ) ℂ) ⟨i, x⟩ ⟨j, y⟩
  by_cases same : i = j
  · subst j
    simp [coherentSharedRandomControlledUnitary,
      Matrix.blockDiagonal'_apply]
  · have reversed : j ≠ i := Ne.symm same
    simp [coherentSharedRandomControlledUnitary,
      Matrix.blockDiagonal'_apply, same, reversed]

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

theorem dSVUniformDensityPhysicalAsync_doubleProductSum
    {ι β γ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (f : ι → β → γ → ℝ) :
    (∑ x : ι → β, ∑ y : ι → γ,
      ∏ i : ι, f i (x i) (y i)) =
      ∏ i : ι, ∑ a : β, ∑ b : γ, f i a b := by
  classical
  calc
    (∑ x : ι → β, ∑ y : ι → γ,
      ∏ i : ι, f i (x i) (y i)) =
        ∑ x : ι → β,
          ∏ i : ι, ∑ b : γ, f i (x i) b := by
      apply Finset.sum_congr rfl
      intro x _
      exact (Fintype.prod_sum
        (fun i : ι => fun b : γ => f i (x i) b)).symm
    _ = ∏ i : ι, ∑ a : β, ∑ b : γ, f i a b :=
      (Fintype.prod_sum
        (fun i : ι => fun a : β => ∑ b : γ, f i a b)).symm

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

theorem spectralPartitionPOVM_effect_eq_spectralDiagonal
    {κ ι : Type*}
    [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (F : Matrix ι ι ℂ) (positive : F.PosSemidef)
    (bin : ι → κ) (outcome : κ) :
    (spectralPartitionPOVM F positive bin).effect outcome =
      spectralConjugationCLM positive.isHermitian.eigenvectorUnitary
        (Matrix.diagonal fun i : ι =>
          if bin i = outcome then (1 : ℂ) else 0) := by
  classical
  let selected : Finset ι :=
    Finset.univ.filter fun i : ι => bin i = outcome
  have diagonal :
      (∑ i ∈ selected,
        Matrix.diagonal (Pi.single i (1 : ℂ))) =
        Matrix.diagonal fun i : ι =>
          if bin i = outcome then (1 : ℂ) else 0 := by
    ext i j
    by_cases same : i = j
    · subst j
      simp [Matrix.sum_apply, selected, Pi.single_apply]
    · simp [Matrix.sum_apply, same]
  change
    (∑ i ∈ selected,
      spectralConjugationCLM positive.isHermitian.eigenvectorUnitary
        (Matrix.diagonal (Pi.single i (1 : ℂ)))) = _
  rw [← map_sum, diagonal]

theorem dSVUniformDensityPhysicalSpectralAliceCopy_inv
    {N d : ℕ} (ξ : BipartiteUnitVector d) :
    (dSVUniformDensityAliceHistorySpectralCopy
      (N := N) ξ)⁻¹ =
      coherentSharedRandomControlledUnitary
        (fun _ : Fin N =>
          dSVUniformDensityThresholdLeftBobBasis ξ) := by
  unfold dSVUniformDensityAliceHistorySpectralCopy
  rw [coherentSharedRandomControlledUnitary_inv]
  simp

theorem dSVUniformDensityPhysicalSpectralAliceCopy_transpose
    {N d : ℕ} (ξ : BipartiteUnitVector d) :
    (dSVUniformDensityAliceHistorySpectralCopy
      (N := N) ξ : Matrix
        (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ).transpose =
      (dSVUniformDensityBobHistoryCopyBasis
        (N := N) ξ : Matrix
          (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) := by
  classical
  change
    (Matrix.blockDiagonal'
      (fun _ : Fin N =>
        (((dSVUniformDensityThresholdLeftBobBasis ξ)⁻¹ :
          Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ))).transpose =
      Matrix.blockDiagonal'
        (fun _ : Fin N =>
          (conjugateUnitary
            (dSVUniformDensityThresholdLeftBobBasis ξ) :
            Matrix (Fin d) (Fin d) ℂ))
  rw [Matrix.blockDiagonal'_transpose]
  apply congrArg Matrix.blockDiagonal'
  funext k
  ext i j
  rfl

theorem dSVUniformDensityPhysicalSpectralAliceCopy_inv_transpose
    {N d : ℕ} (ξ : BipartiteUnitVector d) :
    ((((dSVUniformDensityAliceHistorySpectralCopy
      (N := N) ξ)⁻¹ : Matrix.unitaryGroup
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
        Matrix (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ)).transpose =
      (((dSVUniformDensityBobHistoryCopyBasis
        (N := N) ξ)⁻¹ : Matrix.unitaryGroup
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
        Matrix (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) := by
  calc
    _ = (dSVUniformDensityAliceHistorySpectralCopy
      (N := N) ξ : Matrix
        (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ).transpose.conjTranspose := by
          ext i j
          rfl
    _ = (dSVUniformDensityBobHistoryCopyBasis
      (N := N) ξ : Matrix
        (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ).conjTranspose := by
          rw [dSVUniformDensityPhysicalSpectralAliceCopy_transpose]
    _ = _ := by
          rfl

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096

attribute [local instance] Classical.propDecidable

theorem dSVUniformDensityPhysicalMatched_doubleTensorSourceFactor
    {ι β : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (A B : ι → Matrix β β ℂ)
    (source : β × β → ℂ)
    (a b : ι → β) :
    (∑ x : ι → β, ∑ y : ι → β,
      (∏ i : ι, A i (a i) (x i)) *
      (∏ i : ι, B i (b i) (y i)) *
      (∏ i : ι, source (x i, y i))) =
      ∏ i : ι, ∑ x : β, ∑ y : β,
        A i (a i) x * B i (b i) y * source (x, y) := by
  classical
  calc
    _ = ∑ x : ι → β, ∑ y : ι → β,
        ∏ i : ι,
          (A i (a i) (x i) * B i (b i) (y i) * source (x i, y i)) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    _ = ∑ x : ι → β,
        ∏ i : ι, ∑ y : β,
          (A i (a i) (x i) * B i (b i) y * source (x i, y)) := by
      apply Finset.sum_congr rfl
      intro x _
      exact (Fintype.prod_sum fun i : ι => fun y : β =>
        A i (a i) (x i) * B i (b i) y * source (x i, y)).symm
    _ = _ :=
      (Fintype.prod_sum fun i : ι => fun x : β =>
        ∑ y : β, A i (a i) x * B i (b i) y * source (x, y)).symm

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

def dSVUniformDensityCorrectedMatchedSigmaWeightedResidual
    {H : Type*} [Fintype H] {n : ℕ}
    (history : EuclideanSpace ℂ (H × H))
    (work : H → H → EuclideanSpace ℂ (Fin n × Fin n)) :
    EuclideanSpace ℂ
      ((Σ _ : H, Fin n) × (Σ _ : H, Fin n)) :=
  toLp 2 fun q : (Σ _ : H, Fin n) × (Σ _ : H, Fin n) =>
    history (q.1.1, q.2.1) * work q.1.1 q.2.1 (q.1.2, q.2.2)

theorem dSVUniformDensityCorrectedMatchedSigmaWeightedResidual_distance_sq
    {H : Type*} [Fintype H] {n : ℕ}
    (history : EuclideanSpace ℂ (H × H))
    (work target : H → H → EuclideanSpace ℂ (Fin n × Fin n)) :
    ‖dSVUniformDensityCorrectedMatchedSigmaWeightedResidual
        history work -
      dSVUniformDensityCorrectedMatchedSigmaWeightedResidual
        history target‖ ^ 2 =
      ∑ a : H, ∑ b : H,
        ‖history (a, b)‖ ^ 2 * ‖work a b - target a b‖ ^ 2 := by
  classical
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fintype.sum_prod_type, Fintype.sum_sigma]
  change
    (∑ a : H, ∑ i : Fin n,
      ∑ b : H, ∑ j : Fin n,
        ‖history (a, b) * work a b (i, j) -
          history (a, b) * target a b (i, j)‖ ^ 2) = _
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change
    ‖history (a, b) * work a b (i, j) -
      history (a, b) * target a b (i, j)‖ ^ 2 =
      ‖history (a, b)‖ ^ 2 *
        ‖work a b (i, j) - target a b (i, j)‖ ^ 2
  rw [← mul_sub, norm_mul, mul_pow]

theorem dSVUniformDensityCorrectedMatchedSigmaWeightedResidual_controlled
    {H : Type*} [Fintype H] [DecidableEq H] {n : ℕ}
    (history : EuclideanSpace ℂ (H × H))
    (work : H → H → EuclideanSpace ℂ (Fin n × Fin n))
    (U V : H → Matrix.unitaryGroup (Fin n) ℂ) :
    dSVUniformDensityPhysicalAsyncSigmaContinuation
        U V
        (dSVUniformDensityCorrectedMatchedSigmaWeightedResidual
          history work) =
      dSVUniformDensityCorrectedMatchedSigmaWeightedResidual
        history (fun a b =>
          localUnitaryAction (U a) (V b) (work a b)) := by
  classical
  ext ⟨⟨a, i⟩, ⟨b, j⟩⟩
  simp [dSVUniformDensityPhysicalAsyncSigmaContinuation,
    dSVUniformDensityCorrectedMatchedSigmaWeightedResidual,
    coherentSharedRandomControlledUnitary,
    localUnitaryAction, Matrix.mulVec, dotProduct,
    Matrix.kroneckerMap_apply, Matrix.blockDiagonal'_apply,
    Fintype.sum_prod_type, Fintype.sum_sigma,
    mul_assoc, mul_comm]
  simp_rw [Finset.mul_sum]

theorem
    dSVUniformDensityCorrectedMatchedSigmaControlledReset_distance_sq
    {H : Type*} [Fintype H] [DecidableEq H] {n : ℕ}
    (history : EuclideanSpace ℂ (H × H))
    (work target : H → H → EuclideanSpace ℂ (Fin n × Fin n))
    (U V : H → Matrix.unitaryGroup (Fin n) ℂ) :
    ‖dSVUniformDensityPhysicalAsyncSigmaContinuation U V
        (dSVUniformDensityCorrectedMatchedSigmaWeightedResidual
          history work) -
      dSVUniformDensityCorrectedMatchedSigmaWeightedResidual
        history target‖ ^ 2 =
      ∑ a : H, ∑ b : H,
        ‖history (a, b)‖ ^ 2 *
          ‖localUnitaryAction
              (U a) (V b) (work a b) - target a b‖ ^ 2 := by
  rw [dSVUniformDensityCorrectedMatchedSigmaWeightedResidual_controlled,
    dSVUniformDensityCorrectedMatchedSigmaWeightedResidual_distance_sq]

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

def dSVDensityRationalProjectiveThresholdBin
    (w : ℝ) (N : ℕ) (k : Fin N) (a : ℝ) : Bool :=
  decide (dSVUniformDensityThresholdGrid N k ≤
    dSVRationalSoftPass w a)

def dSVDensityRationalProjectiveThresholdPOVM
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ℝ) (N : ℕ) (k : Fin N)
    (F : Matrix ι ι ℂ) (positive : F.PosSemidef) : POVM Bool ι :=
  spectralPartitionPOVM F positive
    (fun i : ι => dSVDensityRationalProjectiveThresholdBin
      w N k (positive.isHermitian.eigenvalues i))

theorem dSVDensityRationalProjectiveThresholdPOVM_projective
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ℝ) (N : ℕ) (k : Fin N)
    (F : Matrix ι ι ℂ) (positive : F.PosSemidef) (outcome : Bool) :
    (dSVDensityRationalProjectiveThresholdPOVM
      w N k F positive).effect outcome *
      (dSVDensityRationalProjectiveThresholdPOVM
        w N k F positive).effect outcome =
      (dSVDensityRationalProjectiveThresholdPOVM
        w N k F positive).effect outcome := by
  exact spectralPartitionPOVM_projective F positive
    (fun i : ι => dSVDensityRationalProjectiveThresholdBin
      w N k (positive.isHermitian.eigenvalues i)) outcome

def dSVDensityRationalLeftProjectiveThresholdPOVM
    {d : ℕ} (w : ℝ) (N : ℕ) (k : Fin N)
    (ξ : BipartiteUnitVector d) : POVM Bool (Fin d) :=
  dSVDensityRationalProjectiveThresholdPOVM w N k
    (dSVSoftBobLeftReducedDensity ξ)
    (dSVSoftBobLeftReducedDensity_posSemidef ξ)

def dSVDensityRationalLeftProjectiveThresholdAtomMismatch
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  let F := dSVSoftBobLeftReducedDensity ξ
  let G := dSVSoftBobLeftReducedDensity ζ
  let hF := dSVSoftBobLeftReducedDensity_posSemidef ξ
  let hG := dSVSoftBobLeftReducedDensity_posSemidef ζ
  ∑ i : Fin d, ∑ j : Fin d,
    spectralAtomOverlap F G hF hG i j *
      dSVUniformDensityThresholdMismatch N
        (dSVRationalSoftPass w
          (hF.isHermitian.eigenvalues i))
        (dSVRationalSoftPass w
          (hG.isHermitian.eigenvalues j))

theorem
    dSVDensityRationalLeftProjectiveThresholdAtomMismatch_le_discrepancy
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalLeftProjectiveThresholdAtomMismatch
        w N ξ ζ ≤
      dSVUniformLeftDensitySpectralAtomDiscrepancy ξ ζ / w +
        (d : ℝ) / N := by
  let F := dSVSoftBobLeftReducedDensity ξ
  let G := dSVSoftBobLeftReducedDensity ζ
  let hF : F.PosSemidef :=
    dSVSoftBobLeftReducedDensity_posSemidef ξ
  let hG : G.PosSemidef :=
    dSVSoftBobLeftReducedDensity_posSemidef ζ
  have overlap_mass :
      (∑ i : Fin d, ∑ j : Fin d,
        spectralAtomOverlap F G hF hG i j) = (d : ℝ) := by
    simp_rw [spectralAtomOverlap_sum_right]
    simp
  have discrepancy :
      (∑ i : Fin d, ∑ j : Fin d,
        |hF.isHermitian.eigenvalues i -
          hG.isHermitian.eigenvalues j| *
            spectralAtomOverlap F G hF hG i j) =
        dSVUniformLeftDensitySpectralAtomDiscrepancy ξ ζ := by
    unfold dSVUniformLeftDensitySpectralAtomDiscrepancy
      dSVUniformLeftDensitySchmidtCoefficient
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp [Real.sq_sqrt
      ((dSVSoftBobLeftReducedDensity_posSemidef ξ).eigenvalues_nonneg i),
      Real.sq_sqrt
        ((dSVSoftBobLeftReducedDensity_posSemidef ζ).eigenvalues_nonneg j),
      F, G]
  calc
    dSVDensityRationalLeftProjectiveThresholdAtomMismatch
        w N ξ ζ ≤
      ∑ i : Fin d, ∑ j : Fin d,
        spectralAtomOverlap F G hF hG i j *
          (|hF.isHermitian.eigenvalues i -
            hG.isHermitian.eigenvalues j| / w + 1 / (N : ℝ)) := by
      unfold dSVDensityRationalLeftProjectiveThresholdAtomMismatch
      change
        (∑ i : Fin d, ∑ j : Fin d,
          spectralAtomOverlap F G hF hG i j *
            dSVUniformDensityThresholdMismatch N
              (dSVRationalSoftPass w
                (hF.isHermitian.eigenvalues i))
              (dSVRationalSoftPass w
                (hG.isHermitian.eigenvalues j))) ≤ _
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _
        (spectralAtomOverlap_nonneg F G hF hG i j)
      exact (dSVUniformDensityThresholdMismatch_le grid _ _).trans
        (by simpa [add_comm] using
          (add_le_add_right
            (dSVRationalSoftPass_lipschitz width
              (hF.eigenvalues_nonneg i) (hG.eigenvalues_nonneg j))
            (1 / (N : ℝ))))
    _ = (∑ i : Fin d, ∑ j : Fin d,
          |hF.isHermitian.eigenvalues i -
            hG.isHermitian.eigenvalues j| *
              spectralAtomOverlap F G hF hG i j) / w +
        (1 / (N : ℝ)) *
          (∑ i : Fin d, ∑ j : Fin d,
            spectralAtomOverlap F G hF hG i j) := by
      calc
        (∑ i : Fin d, ∑ j : Fin d,
          spectralAtomOverlap F G hF hG i j *
            (|hF.isHermitian.eigenvalues i -
              hG.isHermitian.eigenvalues j| / w + 1 / (N : ℝ))) =
          ∑ i : Fin d, ∑ j : Fin d,
            ((|hF.isHermitian.eigenvalues i -
                hG.isHermitian.eigenvalues j| *
                spectralAtomOverlap F G hF hG i j) / w +
              (1 / (N : ℝ)) *
                spectralAtomOverlap F G hF hG i j) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = _ := by
          simp_rw [Finset.sum_add_distrib, Finset.sum_div,
            Finset.mul_sum]
    _ = dSVUniformLeftDensitySpectralAtomDiscrepancy ξ ζ / w +
          (d : ℝ) / N := by
      rw [discrepancy, overlap_mass]
      ring

theorem dSVUniformDensityGridPrefix_le_density
    {N : ℕ} (positive : 0 < N)
    {a : ℝ} (nonnegative : 0 ≤ a) (bounded : a ≤ 1) :
    dSVUniformDensityGridPrefix N a ≤ a := by
  have cast : (0 : ℝ) < N := by exact_mod_cast positive
  rw [dSVUniformDensityGridPrefix_eq_count,
    dSVUniformDensityThresholdGrid_count_eq_floor
      positive a nonnegative bounded]
  apply (div_le_iff₀ cast).mpr
  exact Nat.floor_le (mul_nonneg nonnegative cast.le)

theorem dSVUniformDensityGridPrefix_density_sub_lt
    {N : ℕ} (positive : 0 < N)
    {a : ℝ} (nonnegative : 0 ≤ a) (bounded : a ≤ 1) :
    a - dSVUniformDensityGridPrefix N a < 1 / (N : ℝ) := by
  have cast : (0 : ℝ) < N := by exact_mod_cast positive
  rw [dSVUniformDensityGridPrefix_eq_count,
    dSVUniformDensityThresholdGrid_count_eq_floor
      positive a nonnegative bounded]
  apply (lt_div_iff₀ cast).mpr
  have floor := Nat.lt_floor_add_one (a * (N : ℝ))
  calc
    (a - (Nat.floor (a * (N : ℝ)) : ℝ) / (N : ℝ)) *
        (N : ℝ) =
      a * (N : ℝ) - (Nat.floor (a * (N : ℝ)) : ℝ) := by
        field_simp
    _ < 1 := by linarith

theorem dSVUniformDensityGridPrefix_density_sub_le
    {N : ℕ} (positive : 0 < N)
    {a : ℝ} (nonnegative : 0 ≤ a) (bounded : a ≤ 1) :
    a - 1 / (N : ℝ) ≤ dSVUniformDensityGridPrefix N a := by
  linarith [dSVUniformDensityGridPrefix_density_sub_lt
    positive nonnegative bounded]

def dSVDensityRationalLeftProjectiveDiagonalMass
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) : ℝ :=
  let hF := dSVSoftBobLeftReducedDensity_posSemidef ξ
  ∑ i : Fin d,
    dSVUniformDensityGridPrefix N
      (dSVRationalSoftPass w
        (hF.isHermitian.eigenvalues i))

theorem dSVSoftBobLeftReducedDensity_eigenvalue_le_one
    {d : ℕ} (ξ : BipartiteUnitVector d) (i : Fin d) :
    (dSVSoftBobLeftReducedDensity_posSemidef ξ).isHermitian.eigenvalues i
      ≤ 1 := by
  let F := dSVSoftBobLeftReducedDensity ξ
  let hF : F.PosSemidef :=
    dSVSoftBobLeftReducedDensity_posSemidef ξ
  change hF.isHermitian.eigenvalues i ≤ 1
  calc
    hF.isHermitian.eigenvalues i ≤
        ∑ j : Fin d, hF.isHermitian.eigenvalues j :=
      Finset.single_le_sum
        (fun j _ => hF.eigenvalues_nonneg j) (Finset.mem_univ i)
    _ = 1 := positiveDensity_eigenvalues_sum F hF
      (dSVSoftBobLeftReducedDensity_trace ξ)

theorem dSVRationalSoftPass_ge_density_div_width_add_one
    {w a : ℝ} (width : 0 < w)
    (nonnegative : 0 ≤ a) (bounded : a ≤ 1) :
    a / (w + 1) ≤ dSVRationalSoftPass w a := by
  unfold dSVRationalSoftPass
  have denominator : 0 < a + w := by linarith
  have wider : 0 < w + 1 := by linarith
  apply (div_le_div_iff₀ wider denominator).mpr
  nlinarith

theorem dSVDensityRationalLeftProjectiveDiagonalMass_lower
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (ξ : BipartiteUnitVector d) :
    1 / (w + 1) - (d : ℝ) / N ≤
      dSVDensityRationalLeftProjectiveDiagonalMass w N ξ := by
  let F := dSVSoftBobLeftReducedDensity ξ
  let hF : F.PosSemidef :=
    dSVSoftBobLeftReducedDensity_posSemidef ξ
  have density_sum :
      (∑ i : Fin d, hF.isHermitian.eigenvalues i) = 1 :=
    positiveDensity_eigenvalues_sum F hF
      (dSVSoftBobLeftReducedDensity_trace ξ)
  have rational_sum :
      1 / (w + 1) ≤
        ∑ i : Fin d,
          dSVRationalSoftPass w
            (hF.isHermitian.eigenvalues i) := by
    calc
      1 / (w + 1) =
          ∑ i : Fin d, hF.isHermitian.eigenvalues i / (w + 1) := by
        rw [← Finset.sum_div, density_sum]
      _ ≤ ∑ i : Fin d,
          dSVRationalSoftPass w
            (hF.isHermitian.eigenvalues i) := by
        apply Finset.sum_le_sum
        intro i _
        exact dSVRationalSoftPass_ge_density_div_width_add_one
          width (hF.eigenvalues_nonneg i)
          (dSVSoftBobLeftReducedDensity_eigenvalue_le_one ξ i)
  calc
    1 / (w + 1) - (d : ℝ) / N ≤
        (∑ i : Fin d,
          dSVRationalSoftPass w
            (hF.isHermitian.eigenvalues i)) - (d : ℝ) / N :=
      sub_le_sub_right rational_sum _
    _ = ∑ i : Fin d,
        (dSVRationalSoftPass w
          (hF.isHermitian.eigenvalues i) - 1 / (N : ℝ)) := by
      simp [Finset.sum_sub_distrib]
      ring
    _ ≤ dSVDensityRationalLeftProjectiveDiagonalMass w N ξ := by
      unfold dSVDensityRationalLeftProjectiveDiagonalMass
      change
        (∑ i : Fin d,
          (dSVRationalSoftPass w
            (hF.isHermitian.eigenvalues i) - 1 / (N : ℝ))) ≤
          ∑ i : Fin d,
            dSVUniformDensityGridPrefix N
              (dSVRationalSoftPass w
                (hF.isHermitian.eigenvalues i))
      apply Finset.sum_le_sum
      intro i _
      exact dSVUniformDensityGridPrefix_density_sub_le grid
        (dSVRationalSoftPass_mem_unit width
          (hF.eigenvalues_nonneg i)).1
        (dSVRationalSoftPass_mem_unit width
          (hF.eigenvalues_nonneg i)).2

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

def dSVDensityRationalPhysicalProjector
    {d N : ℕ} (w : ℝ)
    (ξ : BipartiteUnitVector d) (k : Fin N) :
    Matrix (Fin d) (Fin d) ℂ :=
  (dSVDensityRationalLeftProjectiveThresholdPOVM
    w N k ξ).effect true

theorem dSVDensityRationalPhysicalProjector_pos
    {d N : ℕ} (w : ℝ)
    (ξ : BipartiteUnitVector d) (k : Fin N) :
    (dSVDensityRationalPhysicalProjector w ξ k).PosSemidef :=
  (dSVDensityRationalLeftProjectiveThresholdPOVM
    w N k ξ).positive true

theorem dSVDensityRationalPhysicalProjector_projective
    {d N : ℕ} (w : ℝ)
    (ξ : BipartiteUnitVector d) (k : Fin N) :
    dSVDensityRationalPhysicalProjector w ξ k *
        dSVDensityRationalPhysicalProjector w ξ k =
      dSVDensityRationalPhysicalProjector w ξ k := by
  exact dSVDensityRationalProjectiveThresholdPOVM_projective
    w N k (dSVSoftBobLeftReducedDensity ξ)
    (dSVSoftBobLeftReducedDensity_posSemidef ξ) true

theorem dSVDensityRationalPhysicalProjector_complement_pos
    {d N : ℕ} (w : ℝ)
    (ξ : BipartiteUnitVector d) (k : Fin N) :
    (1 - dSVDensityRationalPhysicalProjector w ξ k).PosSemidef :=
  dSVProjectorComplement_posSemidef
    (dSVDensityRationalPhysicalProjector w ξ k)
    (dSVDensityRationalPhysicalProjector_pos w ξ k)
    (dSVDensityRationalPhysicalProjector_projective w ξ k)

def dSVDensityRationalPhysicalGlobalPOVM
    {d N : ℕ} (w : ℝ)
    (ξ : BipartiteUnitVector d) :
    POVM Bool (DSVUniformDensityThresholdLocalIndex N d) :=
  dSVGlobalProjectorBinaryPOVM
    (dSVDensityRationalPhysicalProjector w ξ)
    (dSVDensityRationalPhysicalProjector_pos w ξ)
    (dSVDensityRationalPhysicalProjector_complement_pos w ξ)

theorem dSVDensityRationalPhysicalProjectorSquare_eq_atomMismatch
    {d N : ℕ} (w : ℝ)
    (ξ ζ : BipartiteUnitVector d) (k : Fin N) :
    (Matrix.trace
      ((dSVDensityRationalPhysicalProjector w ξ k -
        dSVDensityRationalPhysicalProjector w ζ k) *
       (dSVDensityRationalPhysicalProjector w ξ k -
        dSVDensityRationalPhysicalProjector w ζ k))).re =
      ∑ i : Fin d, ∑ j : Fin d,
        if dSVDensityRationalProjectiveThresholdBin w N k
              ((dSVSoftBobLeftReducedDensity_posSemidef
                ξ).isHermitian.eigenvalues i) =
            dSVDensityRationalProjectiveThresholdBin w N k
              ((dSVSoftBobLeftReducedDensity_posSemidef
                ζ).isHermitian.eigenvalues j)
        then 0
        else spectralAtomOverlap
          (dSVSoftBobLeftReducedDensity ξ)
          (dSVSoftBobLeftReducedDensity ζ)
          (dSVSoftBobLeftReducedDensity_posSemidef ξ)
          (dSVSoftBobLeftReducedDensity_posSemidef ζ) i j := by
  classical
  let F := dSVSoftBobLeftReducedDensity ξ
  let G := dSVSoftBobLeftReducedDensity ζ
  let hF := dSVSoftBobLeftReducedDensity_posSemidef ξ
  let hG := dSVSoftBobLeftReducedDensity_posSemidef ζ
  let f : Fin d → Bool := fun i =>
    dSVDensityRationalProjectiveThresholdBin w N k
      (hF.isHermitian.eigenvalues i)
  let g : Fin d → Bool := fun j =>
    dSVDensityRationalProjectiveThresholdBin w N k
      (hG.isHermitian.eigenvalues j)
  let P := (spectralPartitionPOVM F hF f).effect true
  let R := (spectralPartitionPOVM G hG g).effect true
  have deficit :=
    spectralPartitionPOVM_weighted_trace_deficit_eq_mismatch
      F G hF hG f g (fun _ : Bool => (1 : ℝ))
  simp only [one_pow, one_mul] at deficit
  have ffalse := dSVUniformDensityBinarySpectral_false_eq_complement
    F hF f
  have gfalse := dSVUniformDensityBinarySpectral_false_eq_complement
    G hG g
  have hp : P * P = P :=
    spectralPartitionPOVM_projective F hF f true
  have hr : R * R = R :=
    spectralPartitionPOVM_projective G hG g true
  change (Matrix.trace ((P - R) * (P - R))).re = _
  change
    (∑ b : Bool, (Matrix.trace
      ((spectralPartitionPOVM G hG g).effect b)).re) -
      (∑ b : Bool, (Matrix.trace
        ((spectralPartitionPOVM F hF f).effect b *
          (spectralPartitionPOVM G hG g).effect b)).re) =
      ∑ i : Fin d, ∑ j : Fin d,
        if f i = g j then 0
        else spectralAtomOverlap F G hF hG i j at deficit
  rw [← deficit]
  simp only [Fintype.sum_bool]
  rw [ffalse, gfalse]
  change (Matrix.trace ((P - R) * (P - R))).re =
    (Matrix.trace R).re + (Matrix.trace (1 - R)).re -
      ((Matrix.trace (P * R)).re +
        (Matrix.trace ((1 - P) * (1 - R))).re)
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
    Matrix.mul_one, Matrix.trace_sub, Complex.sub_re, hp, hr]
  rw [Matrix.trace_mul_comm R P]
  ring

theorem dSVDensityRationalPhysicalProjectorSquare_grid_eq
    {d N : ℕ} (w : ℝ)
    (ξ ζ : BipartiteUnitVector d) :
    (∑ k : Fin N,
      (Matrix.trace
        ((dSVDensityRationalPhysicalProjector w ξ k -
          dSVDensityRationalPhysicalProjector w ζ k) *
         (dSVDensityRationalPhysicalProjector w ξ k -
          dSVDensityRationalPhysicalProjector w ζ k))).re) /
        (N : ℝ) =
      dSVDensityRationalLeftProjectiveThresholdAtomMismatch
        w N ξ ζ := by
  classical
  simp_rw [dSVDensityRationalPhysicalProjectorSquare_eq_atomMismatch]
  let F := dSVSoftBobLeftReducedDensity ξ
  let G := dSVSoftBobLeftReducedDensity ζ
  let hF := dSVSoftBobLeftReducedDensity_posSemidef ξ
  let hG := dSVSoftBobLeftReducedDensity_posSemidef ζ
  let overlap := spectralAtomOverlap F G hF hG
  have commute :
      (∑ k : Fin N, ∑ i : Fin d, ∑ j : Fin d,
        if dSVDensityRationalProjectiveThresholdBin w N k
              (hF.isHermitian.eigenvalues i) =
            dSVDensityRationalProjectiveThresholdBin w N k
              (hG.isHermitian.eigenvalues j)
        then 0 else overlap i j) =
      ∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin N,
        if dSVDensityRationalProjectiveThresholdBin w N k
              (hF.isHermitian.eigenvalues i) =
            dSVDensityRationalProjectiveThresholdBin w N k
              (hG.isHermitian.eigenvalues j)
        then 0 else overlap i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  change
    (∑ k : Fin N, ∑ i : Fin d, ∑ j : Fin d,
      if dSVDensityRationalProjectiveThresholdBin w N k
            (hF.isHermitian.eigenvalues i) =
          dSVDensityRationalProjectiveThresholdBin w N k
            (hG.isHermitian.eigenvalues j)
      then 0 else overlap i j) / (N : ℝ) = _
  rw [commute]
  unfold dSVDensityRationalLeftProjectiveThresholdAtomMismatch
  change
    (∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin N,
      if dSVDensityRationalProjectiveThresholdBin w N k
            (hF.isHermitian.eigenvalues i) =
          dSVDensityRationalProjectiveThresholdBin w N k
            (hG.isHermitian.eigenvalues j)
      then 0 else overlap i j) / (N : ℝ) =
      ∑ i : Fin d, ∑ j : Fin d,
        overlap i j * dSVUniformDensityThresholdMismatch N
          (dSVRationalSoftPass w
            (hF.isHermitian.eigenvalues i))
          (dSVRationalSoftPass w
            (hG.isHermitian.eigenvalues j))
  simp_rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  unfold dSVUniformDensityThresholdMismatch
    dSVUniformDensityThresholdWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  unfold dSVDensityRationalProjectiveThresholdBin
  by_cases left : dSVUniformDensityThresholdGrid N k ≤
      dSVRationalSoftPass w (hF.isHermitian.eigenvalues i)
  · by_cases right : dSVUniformDensityThresholdGrid N k ≤
        dSVRationalSoftPass w (hG.isHermitian.eigenvalues j)
    · simp [left, right]
    · simp [left, right, div_eq_mul_inv]
  · by_cases right : dSVUniformDensityThresholdGrid N k ≤
        dSVRationalSoftPass w (hG.isHermitian.eigenvalues j)
    · simp [left, right, div_eq_mul_inv]
    · simp [left, right]

theorem dSVDensityRationalPhysicalProjector_weighted_rank_eq
    {d N : ℕ} (w : ℝ) (ξ : BipartiteUnitVector d) :
    (∑ k : Fin N, dSVUniformDensityThresholdWeight N k *
      (Matrix.trace
        (dSVDensityRationalPhysicalProjector w ξ k)).re) =
      dSVDensityRationalLeftProjectiveDiagonalMass w N ξ := by
  classical
  let F := dSVSoftBobLeftReducedDensity ξ
  let hF := dSVSoftBobLeftReducedDensity_posSemidef ξ
  change
    (∑ k : Fin N, dSVUniformDensityThresholdWeight N k *
      (Matrix.trace
        ((spectralPartitionPOVM F hF
          (fun i : Fin d =>
            dSVDensityRationalProjectiveThresholdBin w N k
              (hF.isHermitian.eigenvalues i))).effect true)).re) =
      ∑ i : Fin d, dSVUniformDensityGridPrefix N
        (dSVRationalSoftPass w
          (hF.isHermitian.eigenvalues i))
  simp_rw [spectralPartitionPOVM_trace_eq_atom_count]
  unfold dSVUniformDensityGridPrefix
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  unfold dSVDensityRationalProjectiveThresholdBin
  by_cases accepted : dSVUniformDensityThresholdGrid N k ≤
      dSVRationalSoftPass w
        (hF.isHermitian.eigenvalues i)
  · simp [accepted]
  · simp [accepted]

def dSVDensityRationalPhysicalDiagonalBornSuccess
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (w : ℝ) (ξ : BipartiteUnitVector d) : ℝ :=
  binaryJointSuccessProbability
    (dSVUniformDensityThresholdSharedDensity grid dimension)
    (dSVDensityRationalPhysicalGlobalPOVM w ξ)
    (transposePOVM
      (dSVDensityRationalPhysicalGlobalPOVM w ξ))

theorem dSVDensityRationalPhysicalDiagonalBornSuccess_eq
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (w : ℝ) (ξ : BipartiteUnitVector d) :
    dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension w ξ =
      dSVDensityRationalLeftProjectiveDiagonalMass w N ξ /
        (d : ℝ) := by
  have d_nonzero : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt dimension)
  have n_nonzero : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt grid)
  unfold dSVDensityRationalPhysicalDiagonalBornSuccess
    dSVDensityRationalPhysicalGlobalPOVM
  rw [dSVUniformDensityThresholdShared_diagonalBorn_eq
    grid dimension
    (dSVDensityRationalPhysicalProjector w ξ)
    (dSVDensityRationalPhysicalProjector_pos w ξ)
    (dSVDensityRationalPhysicalProjector_complement_pos w ξ)
    (dSVDensityRationalPhysicalProjector_projective w ξ)]
  rw [← dSVDensityRationalPhysicalProjector_weighted_rank_eq w ξ]
  unfold dSVUniformDensityThresholdWeight
  rw [← Finset.mul_sum]
  field_simp

def dSVDensityRationalPhysicalProjectorCrossHazard
    {d : ℕ} (N : ℕ) (w : ℝ)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  (∑ k : Fin N,
    (Matrix.trace
      ((dSVDensityRationalPhysicalProjector w ξ k -
        dSVDensityRationalPhysicalProjector w ζ k) *
       (dSVDensityRationalPhysicalProjector w ξ k -
        dSVDensityRationalPhysicalProjector w ζ k))).re) /
      ((d : ℝ) * (N : ℝ))

theorem dSVDensityRationalPhysicalProjectorCrossHazard_eq
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (w : ℝ) (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalPhysicalProjectorCrossHazard N w ξ ζ =
      dSVDensityRationalLeftProjectiveThresholdAtomMismatch
        w N ξ ζ / (d : ℝ) := by
  have d_nonzero : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt dimension)
  have n_nonzero : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt grid)
  unfold dSVDensityRationalPhysicalProjectorCrossHazard
  calc
    (∑ k : Fin N,
      (Matrix.trace
        ((dSVDensityRationalPhysicalProjector w ξ k -
          dSVDensityRationalPhysicalProjector w ζ k) *
         (dSVDensityRationalPhysicalProjector w ξ k -
          dSVDensityRationalPhysicalProjector w ζ k))).re) /
        ((d : ℝ) * (N : ℝ)) =
      ((∑ k : Fin N,
        (Matrix.trace
          ((dSVDensityRationalPhysicalProjector w ξ k -
            dSVDensityRationalPhysicalProjector w ζ k) *
           (dSVDensityRationalPhysicalProjector w ξ k -
            dSVDensityRationalPhysicalProjector w ζ k))).re) /
          (N : ℝ)) / (d : ℝ) := by
      field_simp
    _ = dSVDensityRationalLeftProjectiveThresholdAtomMismatch
          w N ξ ζ / (d : ℝ) := by
      rw [dSVDensityRationalPhysicalProjectorSquare_grid_eq w ξ ζ]

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

def dSVDensityRationalCompleteProjectiveThresholdProjector
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (k : Fin N) :
    Matrix (Fin d) (Fin d) ℂ :=
  (dSVDensityRationalLeftProjectiveThresholdPOVM
    w N k ξ).effect true

theorem dSVDensityRationalCompleteProjectiveThresholdProjector_pos
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (k : Fin N) :
    (dSVDensityRationalCompleteProjectiveThresholdProjector
      w N ξ k).PosSemidef :=
  (dSVDensityRationalLeftProjectiveThresholdPOVM
    w N k ξ).positive true

theorem dSVDensityRationalCompleteProjectiveThresholdEffect_projective
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d)
    (k : Fin N) (a : Bool) :
    (dSVDensityRationalLeftProjectiveThresholdPOVM
      w N k ξ).effect a *
      (dSVDensityRationalLeftProjectiveThresholdPOVM
        w N k ξ).effect a =
      (dSVDensityRationalLeftProjectiveThresholdPOVM
        w N k ξ).effect a := by
  exact dSVDensityRationalProjectiveThresholdPOVM_projective
    w N k
    (dSVSoftBobLeftReducedDensity ξ)
    (dSVSoftBobLeftReducedDensity_posSemidef ξ) a

theorem dSVDensityRationalCompleteProjectiveThresholdEffect_false
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (k : Fin N) :
    (dSVDensityRationalLeftProjectiveThresholdPOVM
      w N k ξ).effect false =
      1 - dSVDensityRationalCompleteProjectiveThresholdProjector
        w N ξ k := by
  have complete :=
    (dSVDensityRationalLeftProjectiveThresholdPOVM
      w N k ξ).complete
  rw [Fintype.sum_bool, add_comm] at complete
  exact eq_sub_of_add_eq complete

theorem
    dSVDensityRationalCompleteProjectiveThresholdProjector_complement_pos
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (k : Fin N) :
    (1 - dSVDensityRationalCompleteProjectiveThresholdProjector
      w N ξ k).PosSemidef := by
  rw [← dSVDensityRationalCompleteProjectiveThresholdEffect_false]
  exact (dSVDensityRationalLeftProjectiveThresholdPOVM
    w N k ξ).positive false

def dSVDensityRationalCompleteProjectiveBinaryPOVM
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) :
    POVM Bool (DSVUniformDensityThresholdLocalIndex N d) :=
  dSVGlobalProjectorBinaryPOVM
    (dSVDensityRationalCompleteProjectiveThresholdProjector
      w N ξ)
    (dSVDensityRationalCompleteProjectiveThresholdProjector_pos
      w N ξ)
    (dSVDensityRationalCompleteProjectiveThresholdProjector_complement_pos
      w N ξ)

theorem dSVDensityRationalCompleteProjectiveBinaryPOVM_effect
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (a : Bool) :
    (dSVDensityRationalCompleteProjectiveBinaryPOVM
      w N ξ).effect a =
      Matrix.blockDiagonal' (fun k : Fin N =>
        (dSVDensityRationalLeftProjectiveThresholdPOVM
          w N k ξ).effect a) := by
  cases a
  · change
      Matrix.blockDiagonal' (fun k : Fin N =>
        1 - dSVDensityRationalCompleteProjectiveThresholdProjector
          w N ξ k) = _
    congr 1
    funext k
    exact
      (dSVDensityRationalCompleteProjectiveThresholdEffect_false
        w N ξ k).symm
  · rfl

theorem dSVDensityRationalCompleteProjectiveBinaryPOVM_projective
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (a : Bool) :
    (dSVDensityRationalCompleteProjectiveBinaryPOVM
      w N ξ).effect a *
      (dSVDensityRationalCompleteProjectiveBinaryPOVM
        w N ξ).effect a =
      (dSVDensityRationalCompleteProjectiveBinaryPOVM
        w N ξ).effect a := by
  exact dSVGlobalProjectorBinaryPOVM_projective
    (dSVDensityRationalCompleteProjectiveThresholdProjector
      w N ξ)
    (dSVDensityRationalCompleteProjectiveThresholdProjector_pos
      w N ξ)
    (dSVDensityRationalCompleteProjectiveThresholdProjector_complement_pos
      w N ξ)
    (fun k =>
      dSVDensityRationalCompleteProjectiveThresholdEffect_projective
        w N ξ k true)
    a

def dSVDensityRationalCompleteProjectiveOutcome
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) (a b : Bool) :
    EuclideanSpace ℂ
      (DSVUniformDensityThresholdLocalIndex N d ×
        DSVUniformDensityThresholdLocalIndex N d) :=
  coherentBinaryJointOutcome
    (dSVDensityRationalCompleteProjectiveBinaryPOVM
      w N ξ)
    (transposePOVM
      (dSVDensityRationalCompleteProjectiveBinaryPOVM
        w N ζ))
    (dSVUniformDensityThresholdSharedState N d) a b

theorem dSVDensityRationalCompleteProjectiveOutcome_eq_block_action
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) (a b : Bool) :
    dSVDensityRationalCompleteProjectiveOutcome
        w N ξ ζ a b =
      toLp 2
        ((Matrix.blockDiagonal'
            (fun k : Fin N =>
              (dSVDensityRationalLeftProjectiveThresholdPOVM
                w N k ξ).effect a) ⊗ₖ
          (Matrix.blockDiagonal'
            (fun k : Fin N =>
              (dSVDensityRationalLeftProjectiveThresholdPOVM
                w N k ζ).effect b)).transpose).mulVec
          (ofLp
            (dSVUniformDensityThresholdSharedState N d))) := by
  unfold dSVDensityRationalCompleteProjectiveOutcome
    coherentBinaryJointOutcome
  change
    toLp 2
      (((dSVDensityRationalCompleteProjectiveBinaryPOVM
            w N ξ).effect a ⊗ₖ
         ((dSVDensityRationalCompleteProjectiveBinaryPOVM
            w N ζ).effect b).transpose).mulVec
        (ofLp (dSVUniformDensityThresholdSharedState N d))) = _
  rw [dSVDensityRationalCompleteProjectiveBinaryPOVM_effect,
    dSVDensityRationalCompleteProjectiveBinaryPOVM_effect]

theorem dSVDensityRationalCompleteProjectiveOutcome_eq_blockVector
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) (a b : Bool) :
    dSVDensityRationalCompleteProjectiveOutcome
        w N ξ ζ a b =
      (‖sharedThresholdResourceRaw (d := Fin d)
          (fun _ : Fin N => (1 : ℝ))‖⁻¹ : ℝ) •
        toLp 2
          (Matrix.vec
            ((Matrix.blockDiagonal' fun k : Fin N =>
              (dSVDensityRationalLeftProjectiveThresholdPOVM
                  w N k ξ).effect a *
                (dSVDensityRationalLeftProjectiveThresholdPOVM
                  w N k ζ).effect b).transpose)) := by
  classical
  rw [dSVDensityRationalCompleteProjectiveOutcome_eq_block_action]
  let τ : Fin N → ℝ := fun _ => 1
  let P : Fin N → Matrix (Fin d) (Fin d) ℂ :=
    fun k => (dSVDensityRationalLeftProjectiveThresholdPOVM
      w N k ξ).effect a
  let R : Fin N → Matrix (Fin d) (Fin d) ℂ :=
    fun k => (dSVDensityRationalLeftProjectiveThresholdPOVM
      w N k ζ).effect b
  let M : Matrix
      (DSVUniformDensityThresholdLocalIndex N d ×
        DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d ×
        DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    Matrix.blockDiagonal' P ⊗ₖ
      (Matrix.blockDiagonal' R).transpose
  change
    Matrix.toEuclideanLin M
      (sharedThresholdResource (d := Fin d) τ) = _
  rw [sharedThresholdResource,
    (Matrix.toEuclideanLin M).map_smul_of_tower]
  congr 1
  have raw := sharedThresholdResourceRaw_block_action τ P R
  change
    toLp 2
      (M.mulVec
        (ofLp (sharedThresholdResourceRaw (d := Fin d) τ))) =
      toLp 2
        (Matrix.vec
          ((Matrix.blockDiagonal' fun k : Fin N => P k * R k).transpose))
  simpa only [M, P, R, τ, Complex.ofReal_one, one_smul] using raw

theorem dSVDensityRationalCompleteProjectiveOutcome_norm_sq_eq
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) (a b : Bool) :
    ‖dSVDensityRationalCompleteProjectiveOutcome
        w N ξ ζ a b‖ ^ 2 =
      (∑ k : Fin N,
        (Matrix.trace
          ((dSVDensityRationalLeftProjectiveThresholdPOVM
              w N k ξ).effect a *
           (dSVDensityRationalLeftProjectiveThresholdPOVM
              w N k ζ).effect b)).re) /
        ((d : ℝ) * (N : ℝ)) := by
  classical
  rw [dSVDensityRationalCompleteProjectiveOutcome_eq_block_action]
  let τ : Fin N → ℝ := fun _ => 1
  let P : Fin N → Matrix (Fin d) (Fin d) ℂ :=
    fun k => (dSVDensityRationalLeftProjectiveThresholdPOVM
      w N k ξ).effect a
  let R : Fin N → Matrix (Fin d) (Fin d) ℂ :=
    fun k => (dSVDensityRationalLeftProjectiveThresholdPOVM
      w N k ζ).effect b
  change
    ‖toLp 2
      ((Matrix.blockDiagonal' P ⊗ₖ
        (Matrix.blockDiagonal' R).transpose).mulVec
          (ofLp (sharedThresholdResource (d := Fin d) τ)))‖ ^ 2 =
      (∑ k : Fin N, (Matrix.trace (P k * R k)).re) /
        ((d : ℝ) * (N : ℝ))
  simpa [τ] using
    sharedThresholdResource_block_action_norm_sq
      τ P R
      (fun k =>
        (dSVDensityRationalLeftProjectiveThresholdPOVM
          w N k ξ).positive a)
      (fun k =>
        (dSVDensityRationalLeftProjectiveThresholdPOVM
          w N k ζ).positive b)
      (fun k =>
        dSVDensityRationalCompleteProjectiveThresholdEffect_projective
          w N ξ k a)
      (fun k =>
        dSVDensityRationalCompleteProjectiveThresholdEffect_projective
          w N ζ k b)

end

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder

theorem dSVDensityRationalGridPrefix_nonneg
    (N : ℕ) (a : ℝ) :
    0 ≤ dSVUniformDensityGridPrefix N a := by
  unfold dSVUniformDensityGridPrefix
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg
    (dSVUniformDensityThresholdWeight_nonneg N k)
    (by split <;> norm_num)

theorem dSVDensityRationalSoftPass_rescaled_le_density
    {w a : ℝ} (width : 0 < w) (nonnegative : 0 ≤ a) :
    w * dSVRationalSoftPass w a ≤ a := by
  have denominator : 0 < a + w := by linarith
  unfold dSVRationalSoftPass
  calc
    w * (a / (a + w)) = w * a / (a + w) := by ring
    _ ≤ a := (div_le_iff₀ denominator).mpr (by
      nlinarith [sq_nonneg a])

theorem dSVDensityRationalSoftPass_density_defect_le
    {w a : ℝ} (width : 0 < w)
    (nonnegative : 0 ≤ a) (bounded : a ≤ 1) :
    a - w * dSVRationalSoftPass w a ≤ a / w := by
  have denominator : 0 < a + w := by linarith
  calc
    a - w * dSVRationalSoftPass w a =
        a ^ 2 / (a + w) := by
      unfold dSVRationalSoftPass
      field_simp
      ring
    _ ≤ a / w := by
      apply (div_le_div_iff₀ denominator width).mpr
      nlinarith [mul_nonneg (mul_nonneg nonnegative width.le)
        (sub_nonneg.mpr bounded), sq_nonneg a]

theorem dSVDensityRationalGrid_rescaled_le_density
    {N : ℕ} {w a : ℝ} (width : 0 < w) (grid : 0 < N)
    (nonnegative : 0 ≤ a) :
    w * dSVUniformDensityGridPrefix N
        (dSVRationalSoftPass w a) ≤ a := by
  obtain ⟨pass_nonnegative, pass_bounded⟩ :=
    dSVRationalSoftPass_mem_unit width nonnegative
  calc
    w * dSVUniformDensityGridPrefix N
        (dSVRationalSoftPass w a) ≤
      w * dSVRationalSoftPass w a :=
        mul_le_mul_of_nonneg_left
          (dSVUniformDensityGridPrefix_le_density grid
            pass_nonnegative pass_bounded) width.le
    _ ≤ a :=
      dSVDensityRationalSoftPass_rescaled_le_density
        width nonnegative

theorem dSVDensityRationalGrid_density_defect_le
    {N : ℕ} {w a : ℝ} (width : 0 < w) (grid : 0 < N)
    (nonnegative : 0 ≤ a) (bounded : a ≤ 1) :
    a - w * dSVUniformDensityGridPrefix N
        (dSVRationalSoftPass w a) ≤
      a / w + w / (N : ℝ) := by
  obtain ⟨pass_nonnegative, pass_bounded⟩ :=
    dSVRationalSoftPass_mem_unit width nonnegative
  have cell_bound :
      dSVRationalSoftPass w a -
        dSVUniformDensityGridPrefix N
          (dSVRationalSoftPass w a) ≤ 1 / (N : ℝ) :=
    (dSVUniformDensityGridPrefix_density_sub_lt grid
      pass_nonnegative pass_bounded).le
  have scaled := mul_le_mul_of_nonneg_left cell_bound width.le
  have rational := dSVDensityRationalSoftPass_density_defect_le
    width nonnegative bounded
  calc
    a - w * dSVUniformDensityGridPrefix N
        (dSVRationalSoftPass w a) =
      (a - w * dSVRationalSoftPass w a) +
        w * (dSVRationalSoftPass w a -
          dSVUniformDensityGridPrefix N
            (dSVRationalSoftPass w a)) := by ring
    _ ≤ a / w + w * (1 / (N : ℝ)) :=
      add_le_add rational scaled
    _ = a / w + w / (N : ℝ) := by ring

def dSVDensityRationalCanonicalAcceptedCoefficient
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (i : Fin d) : ℝ :=
  Real.sqrt (w * dSVUniformDensityGridPrefix N
    (dSVRationalSoftPass w
      ((dSVSoftBobLeftReducedDensity_posSemidef ξ).isHermitian.eigenvalues i)))

theorem dSVDensityRationalCanonicalAcceptedCoefficient_nonneg
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (i : Fin d) :
    0 ≤ dSVDensityRationalCanonicalAcceptedCoefficient
      w N ξ i := Real.sqrt_nonneg _

theorem dSVDensityRationalCanonicalAcceptedCoefficient_sq
    {d : ℕ} {w : ℝ} (width : 0 < w) (N : ℕ)
    (ξ : BipartiteUnitVector d) (i : Fin d) :
    dSVDensityRationalCanonicalAcceptedCoefficient
        w N ξ i ^ 2 =
      w * dSVUniformDensityGridPrefix N
        (dSVRationalSoftPass w
          ((dSVSoftBobLeftReducedDensity_posSemidef ξ).isHermitian.eigenvalues i)) := by
  unfold dSVDensityRationalCanonicalAcceptedCoefficient
  apply Real.sq_sqrt
  exact mul_nonneg width.le
    (dSVDensityRationalGridPrefix_nonneg _ _)

def dSVDensityRationalCanonicalAliceBasis
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    Matrix.unitaryGroup (Fin d) ℂ :=
  Classical.choose
    (exists_proofDSVUniformDensityPolarLeftCanonicalSchmidt ξ)

theorem dSVDensityRationalCanonicalAliceBasis_target
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    ξ.val = schmidtVector
      (dSVUniformDensityPolarLeftSchmidtCoefficient ξ)
      (dSVDensityRationalCanonicalAliceBasis ξ)
      (dSVUniformDensityThresholdLeftBobBasis ξ) :=
  Classical.choose_spec
    (exists_proofDSVUniformDensityPolarLeftCanonicalSchmidt ξ)

def dSVDensityRationalCanonicalAcceptedTarget
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  schmidtVector
    (dSVDensityRationalCanonicalAcceptedCoefficient w N ξ)
    (dSVDensityRationalCanonicalAliceBasis ξ)
    (dSVUniformDensityThresholdLeftBobBasis ξ)

theorem dSVDensityRationalCanonicalAcceptedTarget_norm_sq
    {d : ℕ} {w : ℝ} (width : 0 < w) (N : ℕ)
    (ξ : BipartiteUnitVector d) :
    ‖dSVDensityRationalCanonicalAcceptedTarget w N ξ‖ ^ 2 =
      w * dSVDensityRationalLeftProjectiveDiagonalMass w N ξ := by
  unfold dSVDensityRationalCanonicalAcceptedTarget
  rw [schmidtVector_norm_sq]
  simp_rw [dSVDensityRationalCanonicalAcceptedCoefficient_sq width]
  unfold dSVDensityRationalLeftProjectiveDiagonalMass
  rw [Finset.mul_sum]

theorem dSVDensityRationalCanonicalAcceptedTarget_distance_sq_eq
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) :
    ‖ξ.val - dSVDensityRationalCanonicalAcceptedTarget
      w N ξ‖ ^ 2 =
      ∑ i : Fin d,
        (dSVUniformDensityPolarLeftSchmidtCoefficient ξ i -
          dSVDensityRationalCanonicalAcceptedCoefficient
            w N ξ i) ^ 2 := by
  rw [dSVDensityRationalCanonicalAliceBasis_target ξ]
  unfold dSVDensityRationalCanonicalAcceptedTarget
  rw [dSVUniformDensitySchmidtVector_sub,
    schmidtVector_norm_sq]

theorem dSVDensityRationalCanonicalAcceptedCoefficient_error_sq_le
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (ξ : BipartiteUnitVector d) (i : Fin d) :
    (dSVUniformDensityPolarLeftSchmidtCoefficient ξ i -
        dSVDensityRationalCanonicalAcceptedCoefficient
          w N ξ i) ^ 2 ≤
      ((dSVSoftBobLeftReducedDensity_posSemidef ξ).isHermitian.eigenvalues i) / w +
        w / (N : ℝ) := by
  let a :=
    ((dSVSoftBobLeftReducedDensity_posSemidef ξ).isHermitian.eigenvalues i)
  let b := w * dSVUniformDensityGridPrefix N
    (dSVRationalSoftPass w a)
  have ha : 0 ≤ a :=
    (dSVSoftBobLeftReducedDensity_posSemidef ξ).eigenvalues_nonneg i
  have ha_one : a ≤ 1 :=
    dSVSoftBobLeftReducedDensity_eigenvalue_le_one ξ i
  have hb : 0 ≤ b := mul_nonneg width.le
    (dSVDensityRationalGridPrefix_nonneg N _)
  have below : b ≤ a :=
    dSVDensityRationalGrid_rescaled_le_density width grid ha
  have roots := dSVAdaptiveSoft_sqrt_sub_sq_le_abs a b ha hb
  rw [abs_of_nonneg (sub_nonneg.mpr below)] at roots
  have defect := dSVDensityRationalGrid_density_defect_le
    width grid ha ha_one
  change (Real.sqrt a - Real.sqrt b) ^ 2 ≤ a / w + w / (N : ℝ)
  exact roots.trans defect

theorem dSVDensityRationalCanonicalAcceptedTarget_distance_sq_le
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (ξ : BipartiteUnitVector d) :
    ‖ξ.val - dSVDensityRationalCanonicalAcceptedTarget
        w N ξ‖ ^ 2 ≤ 1 / w + (d : ℝ) * w / (N : ℝ) := by
  rw [dSVDensityRationalCanonicalAcceptedTarget_distance_sq_eq]
  calc
    (∑ i : Fin d,
      (dSVUniformDensityPolarLeftSchmidtCoefficient ξ i -
        dSVDensityRationalCanonicalAcceptedCoefficient
          w N ξ i) ^ 2) ≤
      ∑ i : Fin d,
        (((dSVSoftBobLeftReducedDensity_posSemidef ξ).isHermitian.eigenvalues i) / w +
          w / (N : ℝ)) :=
      Finset.sum_le_sum (fun i _ =>
        dSVDensityRationalCanonicalAcceptedCoefficient_error_sq_le
          width grid ξ i)
    _ = 1 / w + (d : ℝ) * w / (N : ℝ) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div]
      rw [positiveDensity_eigenvalues_sum
        (dSVSoftBobLeftReducedDensity ξ)
        (dSVSoftBobLeftReducedDensity_posSemidef ξ)
        (dSVSoftBobLeftReducedDensity_trace ξ)]
      simp
      ring

theorem dSVDensityRationalCanonicalAcceptedTarget_distance_le
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (ξ : BipartiteUnitVector d) :
    ‖ξ.val - dSVDensityRationalCanonicalAcceptedTarget
        w N ξ‖ ≤
      Real.sqrt (1 / w + (d : ℝ) * w / (N : ℝ)) := by
  have nonnegative : 0 ≤ 1 / w + (d : ℝ) * w / (N : ℝ) := by
    positivity
  have squared :=
    dSVDensityRationalCanonicalAcceptedTarget_distance_sq_le
      width grid ξ
  have exact_sqrt := Real.sq_sqrt nonnegative
  nlinarith [norm_nonneg
    (ξ.val - dSVDensityRationalCanonicalAcceptedTarget w N ξ),
    Real.sqrt_nonneg (1 / w + (d : ℝ) * w / (N : ℝ))]

theorem dSVDensityRationalCanonicalAcceptedTarget_ne_zero
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (w + 1))
    (ξ : BipartiteUnitVector d) :
    dSVDensityRationalCanonicalAcceptedTarget w N ξ ≠ 0 := by
  intro zero
  have actual :=
    dSVDensityRationalCanonicalAcceptedTarget_norm_sq
      width N ξ
  rw [zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at actual
  have lower :=
    dSVDensityRationalLeftProjectiveDiagonalMass_lower
      width grid ξ
  nlinarith

def dSVDensityRationalCanonicalNormalizedTarget
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  NormedSpace.normalize
    (dSVDensityRationalCanonicalAcceptedTarget w N ξ)

theorem dSVDensityRationalCanonicalNormalizedTarget_norm
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (w + 1))
    (ξ : BipartiteUnitVector d) :
    ‖dSVDensityRationalCanonicalNormalizedTarget
      w N ξ‖ = 1 := by
  unfold dSVDensityRationalCanonicalNormalizedTarget
  exact NormedSpace.norm_normalize
    (dSVDensityRationalCanonicalAcceptedTarget_ne_zero
      width grid fine ξ)

theorem dSVDensityRationalCanonicalNormalizedTarget_distance_le
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (w + 1))
    (ξ : BipartiteUnitVector d) :
    ‖ξ.val - dSVDensityRationalCanonicalNormalizedTarget
        w N ξ‖ ≤
      2 * Real.sqrt (1 / w + (d : ℝ) * w / (N : ℝ)) := by
  let v := dSVDensityRationalCanonicalAcceptedTarget w N ξ
  have nonzero : v ≠ 0 :=
    dSVDensityRationalCanonicalAcceptedTarget_ne_zero
      width grid fine ξ
  have reverse : |1 - ‖v‖| ≤ ‖ξ.val - v‖ := by
    have actual := abs_norm_sub_norm_le ξ.val v
    simpa [ξ.property] using actual
  have movement :
      ‖v - NormedSpace.normalize v‖ = |1 - ‖v‖| := by
    rw [norm_sub_rev]
    exact dSVUniformDensity_normalize_sub_self_norm v nonzero
  change ‖ξ.val - NormedSpace.normalize v‖ ≤ _
  calc
    ‖ξ.val - NormedSpace.normalize v‖ =
      ‖(ξ.val - v) + (v - NormedSpace.normalize v)‖ := by
        congr 1
        abel
    _ ≤ ‖ξ.val - v‖ + ‖v - NormedSpace.normalize v‖ :=
      norm_add_le _ _
    _ ≤ 2 * ‖ξ.val - v‖ := by
      rw [movement]
      linarith
    _ ≤ 2 * Real.sqrt (1 / w + (d : ℝ) * w / (N : ℝ)) := by
      gcongr
      exact dSVDensityRationalCanonicalAcceptedTarget_distance_le
        width grid ξ

def dSVDensityRationalCanonicalAcceptedUnitTarget
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (w + 1))
    (ξ : BipartiteUnitVector d) :
    BipartiteUnitVector d :=
  ⟨dSVDensityRationalCanonicalNormalizedTarget w N ξ,
    dSVDensityRationalCanonicalNormalizedTarget_norm
      width grid fine ξ⟩

theorem dSVDensityRationalCanonicalAcceptedUnitTarget_distance_le
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (w + 1))
    (ξ : BipartiteUnitVector d) :
    ‖ξ.val -
        (dSVDensityRationalCanonicalAcceptedUnitTarget
          width grid fine ξ).val‖ ≤
      2 * Real.sqrt (1 / w + (d : ℝ) * w / (N : ℝ)) :=
  dSVDensityRationalCanonicalNormalizedTarget_distance_le
    width grid fine ξ

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder MatrixOrder

theorem dSVDensityRationalLargeWidthDiagonalMass_half
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / N ≤ 1 / (2 * (w + 1)))
    (ξ : BipartiteUnitVector d) :
    1 / (2 * (w + 1)) ≤
      dSVDensityRationalLeftProjectiveDiagonalMass w N ξ := by
  have denominator : 0 < w + 1 := by linarith
  have arithmetic :
      1 / (2 * (w + 1)) ≤ 1 / (w + 1) - (d : ℝ) / N := by
    have identity :
        1 / (w + 1) - 1 / (2 * (w + 1)) =
          1 / (2 * (w + 1)) := by
      field_simp; ring
    linarith
  exact arithmetic.trans
    (dSVDensityRationalLeftProjectiveDiagonalMass_lower
      width grid ξ)

theorem dSVDensityRationalLargeWidthDiagonalMass_pos
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / N ≤ 1 / (2 * (w + 1)))
    (ξ : BipartiteUnitVector d) :
    0 < dSVDensityRationalLeftProjectiveDiagonalMass w N ξ := by
  have lower := dSVDensityRationalLargeWidthDiagonalMass_half
    width grid fine ξ
  have positive : 0 < 1 / (2 * (w + 1)) := by positivity
  exact positive.trans_le lower

theorem
    dSVDensityRationalLargeWidthRelativeMismatch_le_discrepancy
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / N ≤ 1 / (2 * (w + 1)))
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalLeftProjectiveThresholdAtomMismatch
        w N ξ ζ /
      dSVDensityRationalLeftProjectiveDiagonalMass w N ξ ≤
      2 * (w + 1) *
        (dSVUniformLeftDensitySpectralAtomDiscrepancy ξ ζ / w +
          (d : ℝ) / N) := by
  let M := dSVDensityRationalLeftProjectiveDiagonalMass w N ξ
  let D := dSVUniformLeftDensitySpectralAtomDiscrepancy ξ ζ / w +
    (d : ℝ) / N
  have mass_positive : 0 < M :=
    dSVDensityRationalLargeWidthDiagonalMass_pos
      width grid fine ξ
  have mass_floor : 1 / (2 * (w + 1)) ≤ M :=
    dSVDensityRationalLargeWidthDiagonalMass_half
      width grid fine ξ
  have difference_nonnegative :
      0 ≤ dSVUniformLeftDensitySpectralAtomDiscrepancy ξ ζ := by
    unfold dSVUniformLeftDensitySpectralAtomDiscrepancy
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (abs_nonneg _)
      (spectralAtomOverlap_nonneg _ _ _ _ i j)
  have defect_nonnegative : 0 ≤ D := by
    dsimp [D]
    exact add_nonneg
      (div_nonneg difference_nonnegative width.le) (by positivity)
  have actual :=
    dSVDensityRationalLeftProjectiveThresholdAtomMismatch_le_discrepancy
      width grid ξ ζ
  change
    dSVDensityRationalLeftProjectiveThresholdAtomMismatch
        w N ξ ζ / M ≤ 2 * (w + 1) * D
  apply (div_le_iff₀ mass_positive).mpr
  have floor_scaled : 1 ≤ 2 * (w + 1) * M := by
    have denominator : 0 < 2 * (w + 1) := by positivity
    have crossed := (div_le_iff₀ denominator).mp mass_floor
    nlinarith
  change
    dSVDensityRationalLeftProjectiveThresholdAtomMismatch
      w N ξ ζ ≤ (2 * (w + 1) * D) * M
  calc
    dSVDensityRationalLeftProjectiveThresholdAtomMismatch
        w N ξ ζ ≤ D := actual
    _ ≤ D * (2 * (w + 1) * M) := by
      nlinarith [mul_nonneg defect_nonnegative
        (show 0 ≤ 2 * (w + 1) * M - 1 by linarith)]
    _ = (2 * (w + 1) * D) * M := by ring

theorem
    dSVDensityRationalLargeWidthRelativeMismatch_le_targetDistance
    {d N : ℕ} {w : ℝ} (large : 1 ≤ w) (grid : 0 < N)
    (fine : (d : ℝ) / N ≤ 1 / (2 * (w + 1)))
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalLeftProjectiveThresholdAtomMismatch
        w N ξ ζ /
      dSVDensityRationalLeftProjectiveDiagonalMass w N ξ ≤
        8 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ +
          2 * (w + 1) * ((d : ℝ) / N) := by
  have width : 0 < w := lt_of_lt_of_le (by norm_num) large
  have distance := dSVUniformLeftDensitySpectralAtomDiscrepancy_le
    ξ ζ
  have root : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
  have distance_nonnegative : 0 ≤ ‖ξ.val - ζ.val‖ := norm_nonneg _
  have denominator : 0 < w := width
  have ratio : (w + 1) / w ≤ 2 := by
    apply (div_le_iff₀ denominator).mpr
    nlinarith
  calc
    dSVDensityRationalLeftProjectiveThresholdAtomMismatch
        w N ξ ζ /
      dSVDensityRationalLeftProjectiveDiagonalMass w N ξ ≤
        2 * (w + 1) *
          (dSVUniformLeftDensitySpectralAtomDiscrepancy ξ ζ / w +
            (d : ℝ) / N) :=
      dSVDensityRationalLargeWidthRelativeMismatch_le_discrepancy
        width grid fine ξ ζ
    _ ≤ 2 * (w + 1) *
          ((2 * Real.sqrt 2 * ‖ξ.val - ζ.val‖) / w +
            (d : ℝ) / N) := by
      gcongr
    _ = 4 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ * ((w + 1) / w) +
          2 * (w + 1) * ((d : ℝ) / N) := by
      field_simp; ring
    _ ≤ (4 * Real.sqrt 2 * ‖ξ.val - ζ.val‖) * 2 +
          2 * (w + 1) * ((d : ℝ) / N) := by
      have scale_nonnegative :
          0 ≤ 4 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ := by positivity
      have scaled := mul_le_mul_of_nonneg_left ratio scale_nonnegative
      exact add_le_add scaled (le_refl _)
    _ = 8 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ +
          2 * (w + 1) * ((d : ℝ) / N) := by
      ring

theorem dSVDensityRationalLargeWidth_exists_fine_grid
    (d : ℕ) (dimension : 0 < d)
    (w : ℝ) (width : 0 < w)
    (ε : ℝ) (precision : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧
      2 * (w + 1) * ((d : ℝ) / N) ≤ ε := by
  have denominator : 0 < ε / (2 * (w + 1)) := by positivity
  obtain ⟨N, large⟩ :=
    exists_nat_gt ((d : ℝ) / (ε / (2 * (w + 1))))
  have real_dimension : 0 < (d : ℝ) := by exact_mod_cast dimension
  have real_grid : 0 < (N : ℝ) :=
    lt_trans (div_pos real_dimension denominator) large
  have grid : 0 < N := by exact_mod_cast real_grid
  refine ⟨N, grid, ?_⟩
  have crossed := (div_lt_iff₀ denominator).mp large
  have small : (d : ℝ) / N < ε / (2 * (w + 1)) := by
    apply (div_lt_iff₀ real_grid).mpr
    nlinarith
  have positive : 0 < 2 * (w + 1) := by positivity
  have scaled := (lt_div_iff₀ positive).mp small
  linarith

theorem dSVDensityRationalLargeWidth_exists_sourceUniformParameters
    (d : ℕ) (dimension : 0 < d)
    (ε : ℝ) (precision : 0 < ε) (small : ε ≤ 1) :
    ∃ (w : ℝ) (N : ℕ),
      1 ≤ w ∧ 0 < N ∧
      2 * (w + 1) * ((d : ℝ) / N) ≤ ε ∧
      (1 / w + w * ((d : ℝ) / N) ≤ 3 * ε / 2) ∧
      (∀ ξ : BipartiteUnitVector d,
        0 < dSVDensityRationalLeftProjectiveDiagonalMass
          w N ξ) ∧
      (∀ ξ ζ : BipartiteUnitVector d,
        dSVDensityRationalLeftProjectiveThresholdAtomMismatch
            w N ξ ζ /
          dSVDensityRationalLeftProjectiveDiagonalMass w N ξ ≤
            8 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ + ε) := by
  let w : ℝ := 1 / ε
  have width : 0 < w := by dsimp [w]; positivity
  have large : 1 ≤ w := by
    dsimp [w]
    exact (le_div_iff₀ precision).mpr (by simpa using small)
  obtain ⟨N, grid, budget⟩ :=
    dSVDensityRationalLargeWidth_exists_fine_grid
      d dimension w width ε precision
  have fine : (d : ℝ) / N ≤ 1 / (2 * (w + 1)) := by
    have denominator : 0 < 2 * (w + 1) := by positivity
    apply (le_div_iff₀ denominator).mpr
    nlinarith
  have inverse : 1 / w = ε := by
    dsimp [w]
    field_simp
  have rounding : 1 / w + w * ((d : ℝ) / N) ≤ 3 * ε / 2 := by
    have grid_cost : w * ((d : ℝ) / N) ≤ ε / 2 := by
      have weight : 0 ≤ (d : ℝ) / N := by positivity
      nlinarith
    rw [inverse]
    linarith
  refine ⟨w, N, large, grid, budget, rounding, ?_, ?_⟩
  · intro ξ
    exact dSVDensityRationalLargeWidthDiagonalMass_pos
      width grid fine ξ
  · intro ξ ζ
    exact
      (dSVDensityRationalLargeWidthRelativeMismatch_le_targetDistance
        large grid fine ξ ζ).trans (by gcongr)

theorem dSVDensityRationalLargeWidthPhysicalDiagonalBornSuccess_pos
    {d N : ℕ} (dimension : 0 < d) {w : ℝ}
    (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / N ≤ 1 / (2 * (w + 1)))
    (ξ : BipartiteUnitVector d) :
    0 < dSVDensityRationalPhysicalDiagonalBornSuccess
      grid dimension w ξ := by
  rw [dSVDensityRationalPhysicalDiagonalBornSuccess_eq
    grid dimension w ξ]
  exact div_pos
    (dSVDensityRationalLargeWidthDiagonalMass_pos
      width grid fine ξ)
    (by exact_mod_cast dimension)

theorem dSVDensityRationalLargeWidthPhysicalRelativeHazard_eq
    {d N : ℕ} (dimension : 0 < d) {w : ℝ}
    (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / N ≤ 1 / (2 * (w + 1)))
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalPhysicalProjectorCrossHazard N w ξ ζ /
      dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension w ξ =
      dSVDensityRationalLeftProjectiveThresholdAtomMismatch
        w N ξ ζ /
        dSVDensityRationalLeftProjectiveDiagonalMass w N ξ := by
  rw [dSVDensityRationalPhysicalProjectorCrossHazard_eq
    grid dimension w ξ ζ,
    dSVDensityRationalPhysicalDiagonalBornSuccess_eq
      grid dimension w ξ]
  have dimension_ne : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt dimension)
  have mass_ne :
      dSVDensityRationalLeftProjectiveDiagonalMass w N ξ ≠ 0 :=
    ne_of_gt (dSVDensityRationalLargeWidthDiagonalMass_pos
      width grid fine ξ)
  field_simp

theorem dSVDensityRationalLargeWidthPhysicalRelativeHazard_le
    {d N : ℕ} (dimension : 0 < d) {w : ℝ}
    (large : 1 ≤ w) (grid : 0 < N)
    (fine : (d : ℝ) / N ≤ 1 / (2 * (w + 1)))
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalPhysicalProjectorCrossHazard N w ξ ζ /
      dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension w ξ ≤
      8 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ +
        2 * (w + 1) * ((d : ℝ) / N) := by
  have width : 0 < w := lt_of_lt_of_le (by norm_num) large
  rw [dSVDensityRationalLargeWidthPhysicalRelativeHazard_eq
    dimension width grid fine ξ ζ]
  exact
    dSVDensityRationalLargeWidthRelativeMismatch_le_targetDistance
      large grid fine ξ ζ

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

def dSVDensityRationalPhysicalMixedBornSuccess
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (w : ℝ) (ξ ζ : BipartiteUnitVector d) : ℝ :=
  binaryJointSuccessProbability
    (dSVUniformDensityThresholdSharedDensity grid dimension)
    (dSVDensityRationalPhysicalGlobalPOVM w ξ)
    (transposePOVM
      (dSVDensityRationalPhysicalGlobalPOVM w ζ))

theorem dSVDensityRationalPhysicalMixedBornSuccess_eq
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (w : ℝ) (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalPhysicalMixedBornSuccess
        grid dimension w ξ ζ =
      (∑ k : Fin N, (Matrix.trace
        (dSVDensityRationalPhysicalProjector w ξ k *
          dSVDensityRationalPhysicalProjector w ζ k)).re) /
        ((d : ℝ) * (N : ℝ)) := by
  unfold dSVDensityRationalPhysicalMixedBornSuccess
    dSVDensityRationalPhysicalGlobalPOVM
  exact dSVUniformDensityThresholdShared_mixedBorn_eq
    grid dimension
    (dSVDensityRationalPhysicalProjector w ξ)
    (dSVDensityRationalPhysicalProjector w ζ)
    (dSVDensityRationalPhysicalProjector_pos w ξ)
    (dSVDensityRationalPhysicalProjector_complement_pos w ξ)
    (dSVDensityRationalPhysicalProjector_pos w ζ)
    (dSVDensityRationalPhysicalProjector_complement_pos w ζ)
    (dSVDensityRationalPhysicalProjector_projective w ξ)
    (dSVDensityRationalPhysicalProjector_projective w ζ)

theorem dSVDensityRationalPhysicalMixedBornSuccess_loss_le
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (w : ℝ) (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension w ξ -
      dSVDensityRationalPhysicalMixedBornSuccess
        grid dimension w ξ ζ ≤
      dSVDensityRationalPhysicalProjectorCrossHazard
        N w ξ ζ := by
  have denominator : 0 < (d : ℝ) * (N : ℝ) := by
    exact mul_pos (by exact_mod_cast dimension)
      (by exact_mod_cast grid)
  have diagonal :
      dSVDensityRationalPhysicalDiagonalBornSuccess
          grid dimension w ξ =
        (∑ k : Fin N,
          (Matrix.trace
            (dSVDensityRationalPhysicalProjector w ξ k)).re) /
          ((d : ℝ) * (N : ℝ)) := by
    unfold dSVDensityRationalPhysicalDiagonalBornSuccess
      dSVDensityRationalPhysicalGlobalPOVM
    exact dSVUniformDensityThresholdShared_diagonalBorn_eq
      grid dimension
      (dSVDensityRationalPhysicalProjector w ξ)
      (dSVDensityRationalPhysicalProjector_pos w ξ)
      (dSVDensityRationalPhysicalProjector_complement_pos w ξ)
      (dSVDensityRationalPhysicalProjector_projective w ξ)
  have ledger := dSVWeightedMixedProjectorSuccessLoss_le_square
    (fun _ : Fin N => (1 : ℝ)) (fun _ => zero_le_one)
    (dSVDensityRationalPhysicalProjector w ξ)
    (dSVDensityRationalPhysicalProjector w ζ)
    (dSVDensityRationalPhysicalProjector_complement_pos w ξ)
    (dSVDensityRationalPhysicalProjector_pos w ζ)
    (dSVDensityRationalPhysicalProjector_projective w ξ)
    (dSVDensityRationalPhysicalProjector_projective w ζ)
  simp only [one_mul] at ledger
  rw [diagonal,
    dSVDensityRationalPhysicalMixedBornSuccess_eq
      grid dimension w ξ ζ]
  unfold dSVDensityRationalPhysicalProjectorCrossHazard
  rw [← sub_div]
  exact (div_le_div_iff_of_pos_right denominator).mpr ledger

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder

def dSVDensityRationalActualMixedSuccessMass
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  ‖dSVDensityRationalCompleteProjectiveOutcome
    w N ξ ζ true true‖ ^ 2

def dSVDensityRationalActualMixedContinueMass
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  ‖dSVDensityRationalCompleteProjectiveOutcome
    w N ξ ζ false false‖ ^ 2

def dSVDensityRationalActualMixedAsynchronousMass
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  ‖dSVDensityRationalCompleteProjectiveOutcome
      w N ξ ζ true false‖ ^ 2 +
    ‖dSVDensityRationalCompleteProjectiveOutcome
      w N ξ ζ false true‖ ^ 2

theorem dSVDensityRationalActualMixedSuccessMass_eq
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (w : ℝ) (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalActualMixedSuccessMass w N ξ ζ =
      dSVDensityRationalPhysicalMixedBornSuccess
        grid dimension w ξ ζ := by
  unfold dSVDensityRationalActualMixedSuccessMass
  rw [dSVDensityRationalCompleteProjectiveOutcome_norm_sq_eq,
    dSVDensityRationalPhysicalMixedBornSuccess_eq
      grid dimension w ξ ζ]
  rfl

theorem dSVDensityRationalActualMixedOutcome_norm_sq_eq_born
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (w : ℝ) (ξ ζ : BipartiteUnitVector d)
    (a b : Bool) :
    ‖dSVDensityRationalCompleteProjectiveOutcome
      w N ξ ζ a b‖ ^ 2 =
      binaryBornProbability
        (dSVUniformDensityThresholdSharedDensity
          grid dimension)
        (dSVDensityRationalPhysicalGlobalPOVM w ξ)
        (transposePOVM
          (dSVDensityRationalPhysicalGlobalPOVM w ζ)) a b := by
  let A := dSVDensityRationalCompleteProjectiveBinaryPOVM
    w N ξ
  let B := dSVDensityRationalCompleteProjectiveBinaryPOVM
    w N ζ
  let z := dSVUniformDensityThresholdSharedState N d
  have alice_physical :
      A = dSVDensityRationalPhysicalGlobalPOVM w ξ := by
    rfl
  have bob_physical :
      B = dSVDensityRationalPhysicalGlobalPOVM w ζ := by
    rfl
  have actual := coherentBinaryJointOutcome_norm_sq
    A (transposePOVM B)
    (dSVDensityRationalCompleteProjectiveBinaryPOVM_projective
      w N ξ)
    (transposePOVM_projective B
      (dSVDensityRationalCompleteProjectiveBinaryPOVM_projective
        w N ζ))
    z (dSVUniformDensityThresholdSharedState_norm
      grid dimension) a b
  rw [alice_physical, bob_physical] at actual
  simpa [z,
    dSVDensityRationalCompleteProjectiveOutcome,
    dSVUniformDensityThresholdSharedDensity,
    binaryBornProbability,
    ← alice_physical, ← bob_physical] using actual

theorem dSVDensityRationalActualMixedContinueMass_eq_born
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (w : ℝ) (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalActualMixedContinueMass w N ξ ζ =
      binaryContinueProbability
        (dSVUniformDensityThresholdSharedDensity
          grid dimension)
        (dSVDensityRationalPhysicalGlobalPOVM w ξ)
        (transposePOVM
          (dSVDensityRationalPhysicalGlobalPOVM w ζ)) := by
  unfold dSVDensityRationalActualMixedContinueMass
    binaryContinueProbability
  exact dSVDensityRationalActualMixedOutcome_norm_sq_eq_born
    grid dimension w ξ ζ false false

theorem dSVDensityRationalActualMixedAsynchronousMass_eq_born
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (w : ℝ) (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalActualMixedAsynchronousMass w N ξ ζ =
      binaryMismatchProbability
        (dSVUniformDensityThresholdSharedDensity
          grid dimension)
        (dSVDensityRationalPhysicalGlobalPOVM w ξ)
        (transposePOVM
          (dSVDensityRationalPhysicalGlobalPOVM w ζ)) := by
  unfold dSVDensityRationalActualMixedAsynchronousMass
    binaryMismatchProbability
  rw [dSVDensityRationalActualMixedOutcome_norm_sq_eq_born
    grid dimension w ξ ζ true false,
    dSVDensityRationalActualMixedOutcome_norm_sq_eq_born
      grid dimension w ξ ζ false true]

theorem dSVDensityRationalActualMixed_mass_partition
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (w : ℝ) (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalActualMixedContinueMass w N ξ ζ +
      dSVDensityRationalActualMixedSuccessMass w N ξ ζ +
      dSVDensityRationalActualMixedAsynchronousMass
        w N ξ ζ = 1 := by
  rw [dSVDensityRationalActualMixedContinueMass_eq_born
    grid dimension w ξ ζ,
    dSVDensityRationalActualMixedSuccessMass_eq
      grid dimension w ξ ζ,
    dSVDensityRationalActualMixedAsynchronousMass_eq_born
      grid dimension w ξ ζ]
  unfold dSVDensityRationalPhysicalMixedBornSuccess
  exact binaryStoppingPartition
    (dSVUniformDensityThresholdSharedDensity
      grid dimension)
    (dSVDensityRationalPhysicalGlobalPOVM w ξ)
    (transposePOVM
      (dSVDensityRationalPhysicalGlobalPOVM w ζ))

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

def dSVDensityRationalCompletePhysicalStoppingCopyAccepted
    {N d : ℕ} (w : ℝ) (ξ : BipartiteUnitVector d)
    (q : DSVUniformDensityThresholdLocalIndex N d) : Prop :=
  dSVDensityRationalProjectiveThresholdBin w N q.1
    ((dSVSoftBobLeftReducedDensity_posSemidef
      ξ).isHermitian.eigenvalues q.2) = true

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

def dSVDensityRationalPhysicalAcceptedOutcome
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      (DSVUniformDensityThresholdLocalIndex N d ×
        DSVUniformDensityThresholdLocalIndex N d) :=
  dSVDensityRationalCompleteProjectiveOutcome
    w N ξ ζ true true

def dSVDensityRationalPhysicalAcceptedRank
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (i : Fin d) :
    Fin (N + 1) :=
  let selected : Finset (Fin N) :=
    Finset.univ.filter fun k : Fin N =>
      dSVDensityRationalProjectiveThresholdBin w N k
        ((dSVSoftBobLeftReducedDensity_posSemidef
          ξ).isHermitian.eigenvalues i) = true
  ⟨selected.card, by
    have bounded : selected.card ≤ N := by
      simpa using Finset.card_le_univ selected
    omega⟩

theorem dSVDensityRationalPhysicalAcceptedRank_gridPrefix
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (i : Fin d) :
    dSVUniformDensityGridPrefix N
        (dSVRationalSoftPass w
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ξ).isHermitian.eigenvalues i)) =
      ((dSVDensityRationalPhysicalAcceptedRank
        w N ξ i).val : ℝ) / (N : ℝ) := by
  classical
  rw [dSVUniformDensityGridPrefix_eq_count]
  simp [dSVDensityRationalPhysicalAcceptedRank,
    dSVDensityRationalProjectiveThresholdBin]

theorem dSVDensityRationalPhysicalAcceptedRank_targetCoefficient_sq
    {d : ℕ} {w : ℝ} (width : 0 < w) (N : ℕ)
    (ξ : BipartiteUnitVector d) (i : Fin d) :
    dSVDensityRationalCanonicalAcceptedCoefficient
        w N ξ i ^ 2 =
      w * ((dSVDensityRationalPhysicalAcceptedRank
        w N ξ i).val : ℝ) / (N : ℝ) := by
  rw [dSVDensityRationalCanonicalAcceptedCoefficient_sq
    width N ξ i,
    dSVDensityRationalPhysicalAcceptedRank_gridPrefix]
  ring

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

theorem dSVUniformDensityGridPrefix_mono
    (N : ℕ) {a b : ℝ} (ordered : a ≤ b) :
    dSVUniformDensityGridPrefix N a ≤
      dSVUniformDensityGridPrefix N b := by
  unfold dSVUniformDensityGridPrefix
  apply Finset.sum_le_sum
  intro k _
  apply mul_le_mul_of_nonneg_left _
    (dSVUniformDensityThresholdWeight_nonneg N k)
  by_cases low : dSVUniformDensityThresholdGrid N k ≤ a
  · have high : dSVUniformDensityThresholdGrid N k ≤ b :=
      low.trans ordered
    simp [low, high]
  · by_cases high : dSVUniformDensityThresholdGrid N k ≤ b
    · simp [low, high]
    · simp [low, high]

theorem dSVUniformDensityThresholdMismatch_eq_sub_of_le
    (N : ℕ) {a b : ℝ} (ordered : a ≤ b) :
    dSVUniformDensityThresholdMismatch N a b =
      dSVUniformDensityGridPrefix N b -
        dSVUniformDensityGridPrefix N a := by
  unfold dSVUniformDensityThresholdMismatch
    dSVUniformDensityGridPrefix
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases low : dSVUniformDensityThresholdGrid N k ≤ a
  · have high : dSVUniformDensityThresholdGrid N k ≤ b :=
      low.trans ordered
    simp [low, high]
  · by_cases high : dSVUniformDensityThresholdGrid N k ≤ b
    · simp [low, high]
    · simp [low, high]

theorem dSVUniformDensityThresholdMismatch_eq_abs_gridPrefix
    (N : ℕ) (a b : ℝ) :
    dSVUniformDensityThresholdMismatch N a b =
      |dSVUniformDensityGridPrefix N a -
        dSVUniformDensityGridPrefix N b| := by
  rcases le_total a b with ordered | ordered
  · rw [dSVUniformDensityThresholdMismatch_eq_sub_of_le
      N ordered]
    rw [abs_of_nonpos (sub_nonpos.mpr
      (dSVUniformDensityGridPrefix_mono N ordered))]
    ring
  · have symmetric :
        dSVUniformDensityThresholdMismatch N a b =
          dSVUniformDensityThresholdMismatch N b a := by
      unfold dSVUniformDensityThresholdMismatch
      apply Finset.sum_congr rfl
      intro k _
      by_cases low : dSVUniformDensityThresholdGrid N k ≤ a
      · by_cases high : dSVUniformDensityThresholdGrid N k ≤ b
        · simp [low, high]
        · simp [low, high]
      · by_cases high : dSVUniformDensityThresholdGrid N k ≤ b
        · simp [low, high]
        · simp [low, high]
    rw [symmetric,
      dSVUniformDensityThresholdMismatch_eq_sub_of_le
        N ordered,
      abs_of_nonneg (sub_nonneg.mpr
        (dSVUniformDensityGridPrefix_mono N ordered))]

theorem
    dSVDensityRationalPhysicalAcceptedRankMismatch_eq_thresholdMismatch
    {d N : ℕ} (w : ℝ)
    (ξ ζ : BipartiteUnitVector d) (i j : Fin d) :
    |((dSVDensityRationalPhysicalAcceptedRank
          w N ξ i).val : ℝ) -
      ((dSVDensityRationalPhysicalAcceptedRank
          w N ζ j).val : ℝ)| / (N : ℝ) =
      dSVUniformDensityThresholdMismatch N
        (dSVRationalSoftPass w
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ξ).isHermitian.eigenvalues i))
        (dSVRationalSoftPass w
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ζ).isHermitian.eigenvalues j)) := by
  rw [dSVUniformDensityThresholdMismatch_eq_abs_gridPrefix,
    dSVDensityRationalPhysicalAcceptedRank_gridPrefix,
    dSVDensityRationalPhysicalAcceptedRank_gridPrefix,
    ← sub_div, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ N)]

def dSVDensityRationalPrefixRankMismatch
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  (∑ i : Fin d, ∑ j : Fin d,
    spectralAtomOverlap
      (dSVSoftBobLeftReducedDensity ξ)
      (dSVSoftBobLeftReducedDensity ζ)
      (dSVSoftBobLeftReducedDensity_posSemidef ξ)
      (dSVSoftBobLeftReducedDensity_posSemidef ζ) i j *
      |((dSVDensityRationalPhysicalAcceptedRank
            w N ξ i).val : ℝ) -
        ((dSVDensityRationalPhysicalAcceptedRank
            w N ζ j).val : ℝ)|) / (N : ℝ)

theorem dSVDensityRationalPrefixRankMismatch_eq_atomMismatch
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalPrefixRankMismatch w N ξ ζ =
      dSVDensityRationalLeftProjectiveThresholdAtomMismatch
        w N ξ ζ := by
  unfold dSVDensityRationalPrefixRankMismatch
    dSVDensityRationalLeftProjectiveThresholdAtomMismatch
  simp_rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_div_assoc,
    dSVDensityRationalPhysicalAcceptedRankMismatch_eq_thresholdMismatch]

theorem dSVDensityRationalPrefixRankMismatch_physicalHazard
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (w : ℝ) (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalPrefixRankMismatch w N ξ ζ / (d : ℝ) =
      dSVDensityRationalPhysicalProjectorCrossHazard
        N w ξ ζ := by
  rw [dSVDensityRationalPrefixRankMismatch_eq_atomMismatch,
    dSVDensityRationalPhysicalProjectorCrossHazard_eq
      grid dimension w ξ ζ]

end

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder

theorem dSVDensityRationalPhysicalAcceptedRank_eq_floor
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (ξ : BipartiteUnitVector d) (i : Fin d) :
    (dSVDensityRationalPhysicalAcceptedRank
      w N ξ i).val =
      Nat.floor
        (dSVRationalSoftPass w
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ξ).isHermitian.eigenvalues i) * (N : ℝ)) := by
  have unit := dSVRationalSoftPass_mem_unit width
    ((dSVSoftBobLeftReducedDensity_posSemidef
      ξ).eigenvalues_nonneg i)
  simpa [dSVDensityRationalPhysicalAcceptedRank,
    dSVDensityRationalProjectiveThresholdBin] using
    (dSVUniformDensityThresholdGrid_count_eq_floor grid
      (dSVRationalSoftPass w
        ((dSVSoftBobLeftReducedDensity_posSemidef
          ξ).isHermitian.eigenvalues i)) unit.1 unit.2)

theorem dSVDensityRationalProjectiveThresholdBin_eq_true_iff_prefix
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (ξ : BipartiteUnitVector d)
    (i : Fin d) (k : Fin N) :
    dSVDensityRationalProjectiveThresholdBin w N k
        ((dSVSoftBobLeftReducedDensity_posSemidef
          ξ).isHermitian.eigenvalues i) = true ↔
      k.val <
        (dSVDensityRationalPhysicalAcceptedRank w N ξ i).val := by
  have real_grid : (0 : ℝ) < N := by exact_mod_cast grid
  have pass_nonnegative :=
    (dSVRationalSoftPass_mem_unit width
      ((dSVSoftBobLeftReducedDensity_posSemidef
        ξ).eigenvalues_nonneg i)).1
  have product_nonnegative :
      0 ≤ dSVRationalSoftPass w
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ξ).isHermitian.eigenvalues i) * (N : ℝ) :=
    mul_nonneg pass_nonnegative real_grid.le
  rw [dSVDensityRationalPhysicalAcceptedRank_eq_floor
    width grid ξ i]
  unfold dSVDensityRationalProjectiveThresholdBin
  simp only [decide_eq_true_eq]
  rw [dSVUniformDensityThresholdGrid_apply grid,
    div_le_iff₀ real_grid]
  constructor
  · intro accepted
    have cast :
        ((k.val + 1 : ℕ) : ℝ) ≤
          dSVRationalSoftPass w
            ((dSVSoftBobLeftReducedDensity_posSemidef
              ξ).isHermitian.eigenvalues i) * (N : ℝ) := by
      simpa using accepted
    have below := (Nat.le_floor_iff product_nonnegative).2 cast
    omega
  · intro below
    have integer :
        k.val + 1 ≤
          Nat.floor
            (dSVRationalSoftPass w
              ((dSVSoftBobLeftReducedDensity_posSemidef
                ξ).isHermitian.eigenvalues i) * (N : ℝ)) := by
      omega
    have cast := (Nat.le_floor_iff product_nonnegative).1 integer
    simpa using cast

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

def dSVDensityRationalMixedSpectralAtomBlock
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d)
    (a b : Bool) (k : Fin N) : Matrix (Fin d) (Fin d) ℂ :=
  let F := dSVSoftBobLeftReducedDensity ξ
  let G := dSVSoftBobLeftReducedDensity ζ
  let hF := dSVSoftBobLeftReducedDensity_posSemidef ξ
  let hG := dSVSoftBobLeftReducedDensity_posSemidef ζ
  ∑ i : Fin d, ∑ j : Fin d,
    if dSVDensityRationalProjectiveThresholdBin w N k
        (hF.isHermitian.eigenvalues i) = a ∧
      dSVDensityRationalProjectiveThresholdBin w N k
        (hG.isHermitian.eigenvalues j) = b
    then positiveMatrixSpectralAtom F hF i *
      positiveMatrixSpectralAtom G hG j
    else 0

theorem dSVDensityRationalMixedSpectralAtomBlock_eq_projectorProduct
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d)
    (a b : Bool) (k : Fin N) :
    dSVDensityRationalMixedSpectralAtomBlock
        w N ξ ζ a b k =
      (dSVDensityRationalLeftProjectiveThresholdPOVM
          w N k ξ).effect a *
        (dSVDensityRationalLeftProjectiveThresholdPOVM
          w N k ζ).effect b := by
  classical
  unfold dSVDensityRationalMixedSpectralAtomBlock
    dSVDensityRationalLeftProjectiveThresholdPOVM
    dSVDensityRationalProjectiveThresholdPOVM
    spectralPartitionPOVM
  simp only [Finset.sum_filter]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases alice : dSVDensityRationalProjectiveThresholdBin w N k
      ((dSVSoftBobLeftReducedDensity_posSemidef
        ξ).isHermitian.eigenvalues i) = a
  · by_cases bob : dSVDensityRationalProjectiveThresholdBin w N k
        ((dSVSoftBobLeftReducedDensity_posSemidef
          ζ).isHermitian.eigenvalues j) = b
    · simp [alice, bob]
    · simp [alice, bob]
  · by_cases bob : dSVDensityRationalProjectiveThresholdBin w N k
        ((dSVSoftBobLeftReducedDensity_posSemidef
          ζ).isHermitian.eigenvalues j) = b
    · simp [alice, bob]
    · simp [alice, bob]

theorem dSVDensityRationalMixedSpectralAtomBlock_trace_eq
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d)
    (a b : Bool) (k : Fin N) :
    (Matrix.trace
      (dSVDensityRationalMixedSpectralAtomBlock
        w N ξ ζ a b k)).re =
      ∑ i : Fin d, ∑ j : Fin d,
        if dSVDensityRationalProjectiveThresholdBin w N k
            ((dSVSoftBobLeftReducedDensity_posSemidef
              ξ).isHermitian.eigenvalues i) = a ∧
          dSVDensityRationalProjectiveThresholdBin w N k
            ((dSVSoftBobLeftReducedDensity_posSemidef
              ζ).isHermitian.eigenvalues j) = b
        then spectralAtomOverlap
          (dSVSoftBobLeftReducedDensity ξ)
          (dSVSoftBobLeftReducedDensity ζ)
          (dSVSoftBobLeftReducedDensity_posSemidef ξ)
          (dSVSoftBobLeftReducedDensity_posSemidef ζ) i j
        else 0 := by
  unfold dSVDensityRationalMixedSpectralAtomBlock
  simp only [Matrix.trace_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp [spectralAtomOverlap]

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder

theorem dSVDensityRationalActualMixedAsynchronousMass_eq_crossHazard
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalActualMixedAsynchronousMass
        w N ξ ζ =
      dSVDensityRationalPhysicalProjectorCrossHazard
        N w ξ ζ := by
  classical
  unfold dSVDensityRationalActualMixedAsynchronousMass
  rw [dSVDensityRationalCompleteProjectiveOutcome_norm_sq_eq,
    dSVDensityRationalCompleteProjectiveOutcome_norm_sq_eq]
  unfold dSVDensityRationalPhysicalProjectorCrossHazard
  rw [← add_div]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [dSVDensityRationalCompleteProjectiveThresholdEffect_false
    w N ζ k,
    dSVDensityRationalCompleteProjectiveThresholdEffect_false
      w N ξ k]
  let P := dSVDensityRationalPhysicalProjector w ξ k
  let R := dSVDensityRationalPhysicalProjector w ζ k
  change
    (Matrix.trace (P * (1 - R))).re +
        (Matrix.trace ((1 - P) * R)).re =
      (Matrix.trace ((P - R) * (P - R))).re
  have square := dSVProjectorSquaredDifference_trace P R
    (dSVDensityRationalPhysicalProjector_projective w ξ k)
    (dSVDensityRationalPhysicalProjector_projective w ζ k)
  rw [square]
  simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub]
  ring

theorem dSVDensityRationalActualMixed_escape_ge_diagonal
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (w : ℝ) (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension w ξ ≤
      dSVDensityRationalActualMixedSuccessMass w N ξ ζ +
        dSVDensityRationalActualMixedAsynchronousMass
          w N ξ ζ := by
  have loss := dSVDensityRationalPhysicalMixedBornSuccess_loss_le
    grid dimension w ξ ζ
  rw [← dSVDensityRationalActualMixedSuccessMass_eq
      grid dimension w ξ ζ,
    ← dSVDensityRationalActualMixedAsynchronousMass_eq_crossHazard
      w N ξ ζ] at loss
  linarith

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

def dSVDensityRationalPhysicalMixedAcceptedIntersectionRank
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d)
    (i j : Fin d) : Fin (N + 1) :=
  ⟨min
      (dSVDensityRationalPhysicalAcceptedRank w N ξ i).val
      (dSVDensityRationalPhysicalAcceptedRank w N ζ j).val,
    by
      have left :=
        (dSVDensityRationalPhysicalAcceptedRank w N ξ i).isLt
      have right :=
        (dSVDensityRationalPhysicalAcceptedRank w N ζ j).isLt
      omega⟩

theorem dSVDensityRationalPhysicalMixedAcceptedThreshold_iff
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (ξ ζ : BipartiteUnitVector d)
    (i j : Fin d) (k : Fin N) :
    (dSVDensityRationalProjectiveThresholdBin w N k
        ((dSVSoftBobLeftReducedDensity_posSemidef
          ξ).isHermitian.eigenvalues i) = true ∧
      dSVDensityRationalProjectiveThresholdBin w N k
        ((dSVSoftBobLeftReducedDensity_posSemidef
          ζ).isHermitian.eigenvalues j) = true) ↔
      k.val <
        (dSVDensityRationalPhysicalMixedAcceptedIntersectionRank
          w N ξ ζ i j).val := by
  rw [dSVDensityRationalProjectiveThresholdBin_eq_true_iff_prefix
    width grid ξ i k,
    dSVDensityRationalProjectiveThresholdBin_eq_true_iff_prefix
      width grid ζ j k]
  change _ ↔ k.val < min
    (dSVDensityRationalPhysicalAcceptedRank w N ξ i).val
    (dSVDensityRationalPhysicalAcceptedRank w N ζ j).val
  omega

theorem dSVDensityRationalPhysicalMixedAcceptedThreshold_count
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (ξ ζ : BipartiteUnitVector d)
    (i j : Fin d) :
    (Finset.univ.filter fun k : Fin N =>
      dSVDensityRationalProjectiveThresholdBin w N k
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ξ).isHermitian.eigenvalues i) = true ∧
        dSVDensityRationalProjectiveThresholdBin w N k
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ζ).isHermitian.eigenvalues j) = true).card =
      (dSVDensityRationalPhysicalMixedAcceptedIntersectionRank
        w N ξ ζ i j).val := by
  let rank :=
    dSVDensityRationalPhysicalMixedAcceptedIntersectionRank
      w N ξ ζ i j
  have bound : rank.val ≤ N := by
    have actual := rank.isLt
    omega
  have same :
      (Finset.univ.filter fun k : Fin N =>
        dSVDensityRationalProjectiveThresholdBin w N k
            ((dSVSoftBobLeftReducedDensity_posSemidef
              ξ).isHermitian.eigenvalues i) = true ∧
          dSVDensityRationalProjectiveThresholdBin w N k
            ((dSVSoftBobLeftReducedDensity_posSemidef
              ζ).isHermitian.eigenvalues j) = true) =
        Finset.univ.filter fun k : Fin N => k.val < rank.val := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact dSVDensityRationalPhysicalMixedAcceptedThreshold_iff
      width grid ξ ζ i j k
  rw [same, Fin.card_filter_val_lt, min_eq_right bound]

theorem dSVDensityRationalMixedAcceptedPrefix_norm_sq
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (ξ ζ : BipartiteUnitVector d) :
    ‖dSVDensityRationalCompleteProjectiveOutcome
        w N ξ ζ true true‖ ^ 2 =
      (∑ i : Fin d, ∑ j : Fin d,
        spectralAtomOverlap
          (dSVSoftBobLeftReducedDensity ξ)
          (dSVSoftBobLeftReducedDensity ζ)
          (dSVSoftBobLeftReducedDensity_posSemidef ξ)
          (dSVSoftBobLeftReducedDensity_posSemidef ζ) i j *
          ((dSVDensityRationalPhysicalMixedAcceptedIntersectionRank
            w N ξ ζ i j).val : ℝ)) /
        ((d : ℝ) * (N : ℝ)) := by
  classical
  rw [dSVDensityRationalCompleteProjectiveOutcome_norm_sq_eq]
  congr 1
  let overlap := spectralAtomOverlap
    (dSVSoftBobLeftReducedDensity ξ)
    (dSVSoftBobLeftReducedDensity ζ)
    (dSVSoftBobLeftReducedDensity_posSemidef ξ)
    (dSVSoftBobLeftReducedDensity_posSemidef ζ)
  have expand (k : Fin N) :
      (Matrix.trace
        ((dSVDensityRationalLeftProjectiveThresholdPOVM
            w N k ξ).effect true *
         (dSVDensityRationalLeftProjectiveThresholdPOVM
            w N k ζ).effect true)).re =
        ∑ i : Fin d, ∑ j : Fin d,
          if dSVDensityRationalProjectiveThresholdBin w N k
              ((dSVSoftBobLeftReducedDensity_posSemidef
                ξ).isHermitian.eigenvalues i) = true ∧
            dSVDensityRationalProjectiveThresholdBin w N k
              ((dSVSoftBobLeftReducedDensity_posSemidef
                ζ).isHermitian.eigenvalues j) = true
          then overlap i j else 0 := by
    rw [← dSVDensityRationalMixedSpectralAtomBlock_eq_projectorProduct]
    exact dSVDensityRationalMixedSpectralAtomBlock_trace_eq
      w N ξ ζ true true k
  simp_rw [expand]
  calc
    (∑ k : Fin N, ∑ i : Fin d, ∑ j : Fin d,
      if dSVDensityRationalProjectiveThresholdBin w N k
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ξ).isHermitian.eigenvalues i) = true ∧
        dSVDensityRationalProjectiveThresholdBin w N k
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ζ).isHermitian.eigenvalues j) = true
      then overlap i j else 0) =
      ∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin N,
        if dSVDensityRationalProjectiveThresholdBin w N k
            ((dSVSoftBobLeftReducedDensity_posSemidef
              ξ).isHermitian.eigenvalues i) = true ∧
          dSVDensityRationalProjectiveThresholdBin w N k
            ((dSVSoftBobLeftReducedDensity_posSemidef
              ζ).isHermitian.eigenvalues j) = true
        then overlap i j else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ i : Fin d, ∑ j : Fin d,
        overlap i j *
          ((dSVDensityRationalPhysicalMixedAcceptedIntersectionRank
            w N ξ ζ i j).val : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      have counted := congrArg (fun r : ℕ => (r : ℝ))
        (dSVDensityRationalPhysicalMixedAcceptedThreshold_count
          width grid ξ ζ i j)
      calc
        (∑ k : Fin N,
          if dSVDensityRationalProjectiveThresholdBin w N k
              ((dSVSoftBobLeftReducedDensity_posSemidef
                ξ).isHermitian.eigenvalues i) = true ∧
            dSVDensityRationalProjectiveThresholdBin w N k
              ((dSVSoftBobLeftReducedDensity_posSemidef
                ζ).isHermitian.eigenvalues j) = true
          then overlap i j else 0) =
          overlap i j *
            ((Finset.univ.filter fun k : Fin N =>
              dSVDensityRationalProjectiveThresholdBin w N k
                  ((dSVSoftBobLeftReducedDensity_posSemidef
                    ξ).isHermitian.eigenvalues i) = true ∧
                dSVDensityRationalProjectiveThresholdBin w N k
                  ((dSVSoftBobLeftReducedDensity_posSemidef
                    ζ).isHermitian.eigenvalues j) = true).card : ℝ) := by
            rw [← Finset.sum_boole]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            split_ifs <;> simp
        _ = _ := by rw [counted]

def dSVDensityRationalPhysicalMixedAcceptedPrefixWork
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) (i j : Fin d) :
    EuclideanSpace ℂ (Fin N × Fin N) :=
  dSVCanonicalFailurePrefix
    (dSVDensityRationalPhysicalMixedAcceptedIntersectionRank
      w N ξ ζ i j)

theorem dSVDensityRationalPhysicalMixedAcceptedPrefixWork_norm_sq
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) (i j : Fin d) :
    ‖dSVDensityRationalPhysicalMixedAcceptedPrefixWork
        w N ξ ζ i j‖ ^ 2 =
      ((dSVDensityRationalPhysicalMixedAcceptedIntersectionRank
        w N ξ ζ i j).val : ℝ) := by
  exact dSVCanonicalFailurePrefix_norm_sq
    (dSVDensityRationalPhysicalMixedAcceptedIntersectionRank
      w N ξ ζ i j)

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

def dSVDensityRationalCanonicalPrefixMask
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) :
    Matrix (DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
  Matrix.blockDiagonal' fun k : Fin N =>
    Matrix.diagonal fun i : Fin d =>
      if dSVDensityRationalProjectiveThresholdBin w N k
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ξ).isHermitian.eigenvalues i) = true
      then (1 : ℂ) else 0

theorem dSVDensityRationalCanonicalPrefixMask_transpose
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) :
    (dSVDensityRationalCanonicalPrefixMask
      w N ξ).transpose =
      dSVDensityRationalCanonicalPrefixMask w N ξ := by
  classical
  simp [dSVDensityRationalCanonicalPrefixMask]

theorem dSVDensityRationalPhysicalAcceptedProjector_eq_spectralMask
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) :
    Matrix.blockDiagonal'
        (dSVDensityRationalPhysicalProjector w ξ) =
      (((dSVUniformDensityAliceHistorySpectralCopy
        (N := N) ξ)⁻¹ : Matrix.unitaryGroup
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
          Matrix (DSVUniformDensityThresholdLocalIndex N d)
            (DSVUniformDensityThresholdLocalIndex N d) ℂ) *
        dSVDensityRationalCanonicalPrefixMask w N ξ *
        (dSVUniformDensityAliceHistorySpectralCopy
          (N := N) ξ :
          Matrix (DSVUniformDensityThresholdLocalIndex N d)
            (DSVUniformDensityThresholdLocalIndex N d) ℂ) := by
  classical
  rw [dSVUniformDensityPhysicalSpectralAliceCopy_inv]
  change
    Matrix.blockDiagonal'
      (dSVDensityRationalPhysicalProjector w ξ) =
      Matrix.blockDiagonal'
          (fun _ : Fin N =>
            (dSVUniformDensityThresholdLeftBobBasis ξ :
              Matrix (Fin d) (Fin d) ℂ)) *
        Matrix.blockDiagonal'
          (fun k : Fin N =>
            Matrix.diagonal fun i : Fin d =>
              if dSVDensityRationalProjectiveThresholdBin w N k
                  ((dSVSoftBobLeftReducedDensity_posSemidef
                    ξ).isHermitian.eigenvalues i) = true
              then (1 : ℂ) else 0) *
        Matrix.blockDiagonal'
          (fun _ : Fin N =>
            (((dSVUniformDensityThresholdLeftBobBasis ξ)⁻¹ :
              Matrix.unitaryGroup (Fin d) ℂ) :
                Matrix (Fin d) (Fin d) ℂ))
  rw [← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
  apply congrArg Matrix.blockDiagonal'
  funext k
  unfold dSVDensityRationalPhysicalProjector
    dSVDensityRationalLeftProjectiveThresholdPOVM
    dSVDensityRationalProjectiveThresholdPOVM
  rw [spectralPartitionPOVM_effect_eq_spectralDiagonal]
  rfl

def dSVDensityRationalCanonicalPrefixSpectralOutcome
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      (DSVUniformDensityThresholdLocalIndex N d ×
        DSVUniformDensityThresholdLocalIndex N d) :=
  toLp 2
    (((dSVUniformDensityAliceHistorySpectralCopy
        (N := N) ξ :
        Matrix (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) ⊗ₖ
      (((dSVUniformDensityBobHistoryCopyBasis
          (N := N) ζ)⁻¹ : Matrix.unitaryGroup
            (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
        Matrix (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ)).mulVec
      (ofLp (dSVDensityRationalPhysicalAcceptedOutcome
        w N ξ ζ)))

def dSVDensityRationalCompleteStoppedOptionalLocalEffect
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) :
    Option Bool → Matrix
      (DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d) ℂ
  | none => 1
  | some outcome =>
      (dSVDensityRationalCompleteProjectiveBinaryPOVM
        w N ξ).effect outcome

def dSVDensityRationalCompleteStoppedOptionalOutcome
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d)
    (alice bob : Option Bool) :
    EuclideanSpace ℂ
      (DSVUniformDensityThresholdLocalIndex N d ×
       DSVUniformDensityThresholdLocalIndex N d) :=
  toLp 2
    (((dSVDensityRationalCompleteStoppedOptionalLocalEffect
          w N ξ alice) ⊗ₖ
        (dSVDensityRationalCompleteStoppedOptionalLocalEffect
          w N ζ bob).transpose).mulVec
      (ofLp (dSVUniformDensityThresholdSharedState N d)))

theorem dSVDensityRationalCompleteStoppedOptionalOutcome_some_some
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) (alice bob : Bool) :
    dSVDensityRationalCompleteStoppedOptionalOutcome
        w N ξ ζ (some alice) (some bob) =
      dSVDensityRationalCompleteProjectiveOutcome
        w N ξ ζ alice bob := by
  rw [dSVDensityRationalCompleteProjectiveOutcome_eq_block_action]
  simp [dSVDensityRationalCompleteStoppedOptionalOutcome,
    dSVDensityRationalCompleteStoppedOptionalLocalEffect,
    dSVDensityRationalCompleteProjectiveBinaryPOVM_effect]

theorem dSVDensityRationalCompleteStoppedOptionalOutcome_none_none
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalCompleteStoppedOptionalOutcome
        w N ξ ζ none none =
      dSVUniformDensityThresholdSharedState N d := by
  simp [dSVDensityRationalCompleteStoppedOptionalOutcome,
    dSVDensityRationalCompleteStoppedOptionalLocalEffect]

def dSVDensityRationalCompleteStoppedOptionalLocalSchedule
    (L : ℕ) (hit copy : Fin (L + 1)) : Option Bool :=
  if copy.val < L then
    if hit = 0 then some false
    else if copy.val + 1 < hit.val then some false
    else if copy.val + 1 = hit.val then some true
    else none
  else none

theorem dSVDensityRationalCompleteStoppedOptionalLocalSchedule_zero
    (L : ℕ) (copy : Fin (L + 1)) :
    dSVDensityRationalCompleteStoppedOptionalLocalSchedule
      L 0 copy =
      if copy.val < L then some false else none := by
  simp [dSVDensityRationalCompleteStoppedOptionalLocalSchedule]

theorem dSVDensityRationalCompleteStoppedOptionalLocalSchedule_hit
    {L : ℕ} (j : Fin L) :
    dSVDensityRationalCompleteStoppedOptionalLocalSchedule
      L j.succ j.castSucc = some true := by
  simp [dSVDensityRationalCompleteStoppedOptionalLocalSchedule,
    j.isLt]

end

noncomputable section

open scoped Kronecker ComplexOrder MatrixOrder

def dSVDensityRationalFirstAcceptLocalSpectralMask
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (outcome : Bool) :
    Matrix (DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
  Matrix.blockDiagonal' fun k : Fin N =>
    Matrix.diagonal fun i : Fin d =>
      if dSVDensityRationalProjectiveThresholdBin w N k
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ξ).isHermitian.eigenvalues i) = outcome
      then (1 : ℂ) else 0

theorem dSVDensityRationalFirstAcceptPhysicalEffect_eq_spectralMask
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (outcome : Bool) :
    (dSVDensityRationalCompleteProjectiveBinaryPOVM
        w N ξ).effect outcome =
      (((dSVUniformDensityAliceHistorySpectralCopy
          (N := N) ξ)⁻¹ : Matrix.unitaryGroup
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
        Matrix (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) *
        dSVDensityRationalFirstAcceptLocalSpectralMask
          w N ξ outcome *
        (dSVUniformDensityAliceHistorySpectralCopy
          (N := N) ξ :
          Matrix (DSVUniformDensityThresholdLocalIndex N d)
            (DSVUniformDensityThresholdLocalIndex N d) ℂ) := by
  classical
  rw [dSVDensityRationalCompleteProjectiveBinaryPOVM_effect,
    dSVUniformDensityPhysicalSpectralAliceCopy_inv]
  change
    Matrix.blockDiagonal'
        (fun k : Fin N =>
          (dSVDensityRationalLeftProjectiveThresholdPOVM
            w N k ξ).effect outcome) =
      Matrix.blockDiagonal'
          (fun _ : Fin N =>
            (dSVUniformDensityThresholdLeftBobBasis ξ :
              Matrix (Fin d) (Fin d) ℂ)) *
        Matrix.blockDiagonal'
          (fun k : Fin N =>
            Matrix.diagonal fun i : Fin d =>
              if dSVDensityRationalProjectiveThresholdBin w N k
                  ((dSVSoftBobLeftReducedDensity_posSemidef
                    ξ).isHermitian.eigenvalues i) = outcome
              then (1 : ℂ) else 0) *
        Matrix.blockDiagonal'
          (fun _ : Fin N =>
            (((dSVUniformDensityThresholdLeftBobBasis ξ)⁻¹ :
              Matrix.unitaryGroup (Fin d) ℂ) :
                Matrix (Fin d) (Fin d) ℂ))
  rw [← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
  apply congrArg Matrix.blockDiagonal'
  funext k
  unfold dSVDensityRationalLeftProjectiveThresholdPOVM
    dSVDensityRationalProjectiveThresholdPOVM
  rw [spectralPartitionPOVM_effect_eq_spectralDiagonal]
  rfl

theorem dSVDensityRationalFirstAcceptLocalSpectralMask_transpose
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (outcome : Bool) :
    (dSVDensityRationalFirstAcceptLocalSpectralMask
      w N ξ outcome).transpose =
      dSVDensityRationalFirstAcceptLocalSpectralMask
        w N ξ outcome := by
  classical
  simp [dSVDensityRationalFirstAcceptLocalSpectralMask]

theorem
    dSVDensityRationalFirstAcceptPhysicalBobEffect_eq_spectralMask
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ζ : BipartiteUnitVector d) (outcome : Bool) :
    (transposePOVM
        (dSVDensityRationalCompleteProjectiveBinaryPOVM
          w N ζ)).effect outcome =
      (dSVUniformDensityBobHistoryCopyBasis
          (N := N) ζ :
          Matrix (DSVUniformDensityThresholdLocalIndex N d)
            (DSVUniformDensityThresholdLocalIndex N d) ℂ) *
        dSVDensityRationalFirstAcceptLocalSpectralMask
          w N ζ outcome *
        (((dSVUniformDensityBobHistoryCopyBasis
            (N := N) ζ)⁻¹ : Matrix.unitaryGroup
              (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
            Matrix (DSVUniformDensityThresholdLocalIndex N d)
              (DSVUniformDensityThresholdLocalIndex N d) ℂ) := by
  change
    ((dSVDensityRationalCompleteProjectiveBinaryPOVM
      w N ζ).effect outcome).transpose = _
  rw [dSVDensityRationalFirstAcceptPhysicalEffect_eq_spectralMask
    w N ζ outcome, Matrix.transpose_mul, Matrix.transpose_mul,
    dSVDensityRationalFirstAcceptLocalSpectralMask_transpose,
    dSVUniformDensityPhysicalSpectralAliceCopy_transpose,
    dSVUniformDensityPhysicalSpectralAliceCopy_inv_transpose]
  simp [Matrix.mul_assoc]

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

def dSVDensityRationalFirstAcceptActualTensorBasis
    {β : Type*} [Fintype β] [DecidableEq β]
    {L : ℕ} (U : Matrix.unitaryGroup β ℂ) :
    Matrix.unitaryGroup (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ :=
  controlledFiniteTensorLocalUnitary
    (fun (_stop : Fin (L + 1)) (_copy : Fin (L + 1)) => U)

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048

theorem tensorEmbezzlementTarget_sub_norm
    {d n : ℕ} (positive : 0 < n)
    (ξ ζ : BipartiteUnitVector d) :
    ‖tensorEmbezzlementTarget (n := n) ξ -
      tensorEmbezzlementTarget (n := n) ζ‖ =
      ‖ξ.val - ζ.val‖ := by
  classical
  let e : ((Fin d × Fin d) × (Fin n × Fin n)) ≃
      (Fin (d * n) × Fin (d * n)) :=
    (Equiv.prodProdProdComm (Fin d) (Fin d) (Fin n) (Fin n)).trans
      (Equiv.prodCongr finProdFinEquiv finProdFinEquiv)
  have point (q : (Fin d × Fin d) × (Fin n × Fin n)) :
      (tensorEmbezzlementTarget (n := n) ξ -
        tensorEmbezzlementTarget (n := n) ζ) (e q) =
        (ξ.val q.1 - ζ.val q.1) *
          embezzlementState n q.2 := by
    rcases q with ⟨⟨a, b⟩, ⟨i, j⟩⟩
    change
      ξ.val
          ((finProdFinEquiv.symm (finProdFinEquiv (a, i))).1,
            (finProdFinEquiv.symm (finProdFinEquiv (b, j))).1) *
          embezzlementState n
            ((finProdFinEquiv.symm (finProdFinEquiv (a, i))).2,
              (finProdFinEquiv.symm (finProdFinEquiv (b, j))).2) -
        ζ.val
          ((finProdFinEquiv.symm (finProdFinEquiv (a, i))).1,
            (finProdFinEquiv.symm (finProdFinEquiv (b, j))).1) *
          embezzlementState n
            ((finProdFinEquiv.symm (finProdFinEquiv (a, i))).2,
              (finProdFinEquiv.symm (finProdFinEquiv (b, j))).2) = _
    simp only [Equiv.symm_apply_apply]
    ring
  have reindex :
      (∑ q : Fin (d * n) × Fin (d * n),
        ‖(tensorEmbezzlementTarget (n := n) ξ -
          tensorEmbezzlementTarget (n := n) ζ) q‖ ^ 2) =
        ∑ q : (Fin d × Fin d) × (Fin n × Fin n),
          ‖(ξ.val q.1 - ζ.val q.1) *
            embezzlementState n q.2‖ ^ 2 := by
    calc
      (∑ q : Fin (d * n) × Fin (d * n),
        ‖(tensorEmbezzlementTarget (n := n) ξ -
          tensorEmbezzlementTarget (n := n) ζ) q‖ ^ 2) =
          ∑ q : (Fin d × Fin d) × (Fin n × Fin n),
            ‖(tensorEmbezzlementTarget (n := n) ξ -
              tensorEmbezzlementTarget (n := n) ζ)
                (e q)‖ ^ 2 :=
            (Equiv.sum_comp e
              (fun q : Fin (d * n) × Fin (d * n) =>
                ‖(tensorEmbezzlementTarget (n := n) ξ -
                  tensorEmbezzlementTarget (n := n) ζ)
                    q‖ ^ 2)).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro q _
        rw [point q]
  have factor :
      (∑ q : (Fin d × Fin d) × (Fin n × Fin n),
        ‖(ξ.val q.1 - ζ.val q.1) *
          embezzlementState n q.2‖ ^ 2) =
        (∑ q : Fin d × Fin d, ‖(ξ.val - ζ.val) q‖ ^ 2) *
          (∑ q : Fin n × Fin n,
            ‖embezzlementState n q‖ ^ 2) := by
    rw [Fintype.sum_prod_type]
    simp_rw [norm_mul, mul_pow]
    exact (Fintype.sum_mul_sum
      (fun q : Fin d × Fin d => ‖(ξ.val - ζ.val) q‖ ^ 2)
      (fun q : Fin n × Fin n =>
        ‖embezzlementState n q‖ ^ 2)).symm
  have squares :
      ‖tensorEmbezzlementTarget (n := n) ξ -
        tensorEmbezzlementTarget (n := n) ζ‖ ^ 2 =
        ‖ξ.val - ζ.val‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, reindex, factor,
      ← EuclideanSpace.norm_sq_eq, ← EuclideanSpace.norm_sq_eq,
      embezzlementState_norm n positive]
    ring
  nlinarith [norm_nonneg
    (tensorEmbezzlementTarget (n := n) ξ -
      tensorEmbezzlementTarget (n := n) ζ),
    norm_nonneg (ξ.val - ζ.val)]

end

noncomputable section

open scoped BigOperators Kronecker ComplexOrder MatrixOrder

theorem dSVBobTargetLocalHarmonicCleanup_stable
    {d n : ℕ} (hn : 0 < n)
    (U V : Matrix.unitaryGroup (Fin (d * n)) ℂ)
    (ξ ζ : BipartiteUnitVector d)
    (ε : ℝ)
    (clean :
      ‖localUnitaryAction U V
          (tensorEmbezzlementTarget (n := n) ζ) -
        embezzlementState (d * n)‖ ≤ ε) :
    ‖localUnitaryAction U V
        (tensorEmbezzlementTarget (n := n) ξ) -
      embezzlementState (d * n)‖ ≤
        ‖ξ.val - ζ.val‖ + ε := by
  let source := localUnitaryAction U V
    (tensorEmbezzlementTarget (n := n) ξ)
  let reference := localUnitaryAction U V
    (tensorEmbezzlementTarget (n := n) ζ)
  let residual := embezzlementState (d * n)
  have preserved : ‖source - reference‖ = ‖ξ.val - ζ.val‖ := by
    dsimp [source, reference]
    rw [← localUnitaryAction_sub,
      localUnitaryAction_norm,
      tensorEmbezzlementTarget_sub_norm hn]
  have triangle : ‖source - residual‖ ≤
      ‖source - reference‖ + ‖reference - residual‖ := by
    simpa [dist_eq_norm] using dist_triangle source reference residual
  change ‖source - residual‖ ≤ ‖ξ.val - ζ.val‖ + ε
  calc
    ‖source - residual‖ ≤
        ‖source - reference‖ + ‖reference - residual‖ := triangle
    _ ≤ ‖ξ.val - ζ.val‖ + ε := by
      rw [preserved]
      simpa [add_comm] using add_le_add_left
        (show ‖reference - residual‖ ≤ ε by
          simpa [reference, residual] using clean)
        ‖ξ.val - ζ.val‖

theorem dSVBobTargetLocalUniformHarmonicWorkCleanup
    {T : Type*}
    (d : ℕ) (dimension : 0 < d)
    (work : T → BipartiteUnitVector d)
    (ε : ℝ) (precision : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧
      ∃ (A B : T → Matrix.unitaryGroup (Fin (d * n)) ℂ),
        (∀ ζ : T,
          ‖localUnitaryAction (A ζ) (B ζ)
              (tensorEmbezzlementTarget (n := n) (work ζ)) -
            embezzlementState (d * n)‖ ≤ ε) ∧
        (∀ ξ ζ : T,
          ‖localUnitaryAction (A ζ) (B ζ)
              (tensorEmbezzlementTarget (n := n) (work ξ)) -
            embezzlementState (d * n)‖ ≤
              ‖(work ξ).val - (work ζ).val‖ + ε) := by
  classical
  obtain ⟨n, positive, universal⟩ :=
    exists_proofUniversalHarmonicCatalyst
      d dimension ε precision
  have each (ζ : T) :
      ∃ U V : Matrix.unitaryGroup (Fin (d * n)) ℂ,
        ‖localUnitaryAction U V
            (embezzlementState (d * n)) -
          tensorEmbezzlementTarget (n := n)
            (work ζ)‖ ≤ ε :=
    universal (work ζ)
  choose U V prepared using each
  refine ⟨n, positive,
    (fun ζ => (U ζ)⁻¹),
    (fun ζ => (V ζ)⁻¹), ?_, ?_⟩
  · intro ζ
    rw [harmonicCoherentSharedResource_inverseAbsorption_distance]
    exact prepared ζ
  · intro ξ ζ
    apply dSVBobTargetLocalHarmonicCleanup_stable
      positive ((U ζ)⁻¹) ((V ζ)⁻¹)
      (work ξ) (work ζ) ε
    rw [harmonicCoherentSharedResource_inverseAbsorption_distance]
    exact prepared ζ

theorem dSVDensityRationalCanonicalUnitPrefix_relative_distance_sq
    {N : ℕ} (grid : 0 < N) (r s : Fin (N + 1)) :
    ‖(dSVCanonicalFailureUnitRankFamily N grid r).val -
        (dSVCanonicalFailureUnitRankFamily N grid s).val‖ ^ 2 ≤
      4 * |(r.val : ℝ) - (s.val : ℝ)| /
        (max 1 (min r.val s.val) : ℕ) := by
  classical
  let x : ℝ :=
    ‖(dSVCanonicalFailureUnitRankFamily N grid r).val -
      (dSVCanonicalFailureUnitRankFamily N grid s).val‖
  let y : ℝ :=
    ‖dSVCanonicalFailurePrefix r -
      dSVCanonicalFailurePrefix s‖
  have x_nonnegative : 0 ≤ x := norm_nonneg _
  have y_nonnegative : 0 ≤ y := norm_nonneg _
  have y_squared : y ^ 2 = |(r.val : ℝ) - (s.val : ℝ)| :=
    dSVCanonicalFailurePrefix_sub_norm_sq r s
  by_cases zero : r.val = 0
  · by_cases zero_s : s.val = 0
    · have same : r = s := Fin.ext (zero.trans zero_s.symm)
      subst s
      simp
    · have s_positive : 0 < s.val := Nat.pos_of_ne_zero zero_s
      have s_one : (1 : ℝ) ≤ (s.val : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr zero_s)
      have x_two : x ≤ 2 := by
        dsimp [x]
        calc
          _ ≤ ‖(dSVCanonicalFailureUnitRankFamily
                N grid r).val‖ +
              ‖(dSVCanonicalFailureUnitRankFamily
                N grid s).val‖ := norm_sub_le _ _
          _ = 2 := by
            rw [(dSVCanonicalFailureUnitRankFamily
              N grid r).property,
              (dSVCanonicalFailureUnitRankFamily
                N grid s).property]
            norm_num
      have magnitude :
          |(r.val : ℝ) - (s.val : ℝ)| = (s.val : ℝ) := by
        simp [zero]
      have denominator : max 1 (min r.val s.val) = 1 := by
        simp [zero]
      change x ^ 2 ≤ _
      rw [magnitude, denominator]
      norm_num only [Nat.cast_one, div_one]
      nlinarith [sq_nonneg x]
  · have r_positive_nat : 0 < r.val := Nat.pos_of_ne_zero zero
    have r_positive : (0 : ℝ) < r.val := by
      exact_mod_cast r_positive_nat
    have root_positive : 0 < Real.sqrt (r.val : ℝ) :=
      Real.sqrt_pos.mpr r_positive
    have raw_nonzero : dSVCanonicalFailurePrefix r ≠ 0 := by
      intro vanished
      have mass := dSVCanonicalFailurePrefix_norm_sq r
      rw [vanished] at mass
      norm_num at mass
      exact zero (by exact_mod_cast mass.symm)
    have normalized := normalizeOrDefault_sub_le
      (embezzlementState N)
      (dSVCanonicalFailurePrefix r)
      (dSVCanonicalFailurePrefix s)
      (embezzlementState_norm N grid)
      raw_nonzero
    change x ≤ 2 * y /
      ‖dSVCanonicalFailurePrefix r‖ at normalized
    rw [dSVCanonicalFailurePrefix_norm_eq_sqrt]
      at normalized
    have linear : x * Real.sqrt (r.val : ℝ) ≤ 2 * y :=
      (le_div_iff₀ root_positive).mp normalized
    have square := mul_self_le_mul_self
      (mul_nonneg x_nonnegative root_positive.le) linear
    have weighted : x ^ 2 * (r.val : ℝ) ≤
        4 * |(r.val : ℝ) - (s.val : ℝ)| := by
      have root_square := Real.sq_sqrt r_positive.le
      nlinarith [y_squared]
    have rank_relative :
        x ^ 2 ≤ 4 * |(r.val : ℝ) - (s.val : ℝ)| /
          (r.val : ℝ) :=
      (le_div_iff₀ r_positive).mpr weighted
    have denominator_positive :
        (0 : ℝ) < (max 1 (min r.val s.val) : ℕ) := by
      exact_mod_cast (show 0 < max 1 (min r.val s.val) by omega)
    have denominator_le :
        ((max 1 (min r.val s.val) : ℕ) : ℝ) ≤ (r.val : ℝ) := by
      exact_mod_cast
        (max_le (Nat.one_le_iff_ne_zero.mpr zero)
          (min_le_left r.val s.val))
    change x ^ 2 ≤ _
    calc
      x ^ 2 ≤ 4 * |(r.val : ℝ) - (s.val : ℝ)| /
          (r.val : ℝ) := rank_relative
      _ ≤ 4 * |(r.val : ℝ) - (s.val : ℝ)| /
          (max 1 (min r.val s.val) : ℕ) := by
            apply (div_le_div_iff₀ r_positive denominator_positive).mpr
            exact mul_le_mul_of_nonneg_left denominator_le
              (mul_nonneg (by norm_num) (abs_nonneg _))

theorem dSVDensityRationalPublicBucketLocalHarmonicCleanup_sq
    {Ω I : Type*} [DecidableEq I] {N D : ℕ} (dimension : 0 < N)
    (work : Fin D → BipartiteUnitVector N)
    (bucket : Ω → Fin D → I)
    (representative : Ω → I → Fin D)
    (ε : ℝ) (precision : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧
      ∃ A B : Ω → I → Matrix.unitaryGroup (Fin (N * n)) ℂ,
        ∀ (phase : Ω) (r s : Fin D),
          ‖localUnitaryAction
              (A phase (bucket phase r))
              (B phase (bucket phase s))
              (tensorEmbezzlementTarget (n := n) (work r)) -
            embezzlementState (N * n)‖ ^ 2 ≤
              2 * ε ^ 2 +
              2 * ‖(work r).val -
                (work (representative phase (bucket phase r))).val‖ ^ 2 +
              4 * (if bucket phase r = bucket phase s
                then (0 : ℝ) else 1) := by
  classical
  obtain ⟨n, positive, A, B, diagonal, _stable⟩ :=
    dSVBobTargetLocalUniformHarmonicWorkCleanup
      N dimension
      (fun q : Ω × I => work (representative q.1 q.2))
      ε precision
  refine ⟨n, positive,
    fun phase label => A (phase, label),
    fun phase label => B (phase, label), ?_⟩
  intro phase r s
  by_cases same : bucket phase r = bucket phase s
  · have clean := diagonal (phase, bucket phase r)
    have stable := dSVBobTargetLocalHarmonicCleanup_stable
      positive
      (A (phase, bucket phase r))
      (B (phase, bucket phase r))
      (work r)
      (work (representative phase (bucket phase r)))
      ε clean
    have actual :
        ‖localUnitaryAction
            (A (phase, bucket phase r))
            (B (phase, bucket phase s))
            (tensorEmbezzlementTarget (n := n) (work r)) -
          embezzlementState (N * n)‖ ≤
            ‖(work r).val -
              (work (representative phase (bucket phase r))).val‖ + ε := by
      simpa only [same] using stable
    simp only [if_pos same, mul_zero, add_zero]
    nlinarith [
      norm_nonneg
        (localUnitaryAction
            (A (phase, bucket phase r))
            (B (phase, bucket phase s))
            (tensorEmbezzlementTarget (n := n) (work r)) -
          embezzlementState (N * n)),
      norm_nonneg ((work r).val -
        (work (representative phase (bucket phase r))).val),
      sq_nonneg
        (‖(work r).val -
          (work (representative phase (bucket phase r))).val‖ - ε)]
  · have bound :
        ‖localUnitaryAction
            (A (phase, bucket phase r))
            (B (phase, bucket phase s))
            (tensorEmbezzlementTarget (n := n) (work r)) -
          embezzlementState (N * n)‖ ≤ 2 := by
      calc
        _ ≤ ‖localUnitaryAction
              (A (phase, bucket phase r))
              (B (phase, bucket phase s))
              (tensorEmbezzlementTarget (n := n) (work r))‖ +
            ‖embezzlementState (N * n)‖ := norm_sub_le _ _
        _ = 2 := by
          rw [localUnitaryAction_norm,
            tensorEmbezzlementTarget_norm positive,
            embezzlementState_norm (N * n)
              (Nat.mul_pos dimension positive)]
          norm_num
    simp only [if_neg same, mul_one]
    nlinarith [
      norm_nonneg
        (localUnitaryAction
            (A (phase, bucket phase r))
            (B (phase, bucket phase s))
            (tensorEmbezzlementTarget (n := n) (work r)) -
          embezzlementState (N * n)),
      sq_nonneg ε,
      sq_nonneg
        ‖(work r).val -
          (work (representative phase (bucket phase r))).val‖]

theorem dSVDensityRationalPublicBucketCanonicalPrefixCleanup_sq
    {Ω I : Type*} [DecidableEq I] {N : ℕ} (grid : 0 < N)
    (bucket : Ω → Fin (N + 1) → I)
    (representative : Ω → I → Fin (N + 1))
    (ε : ℝ) (precision : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧
      ∃ A B : Ω → I → Matrix.unitaryGroup (Fin (N * n)) ℂ,
        ∀ (phase : Ω) (r s : Fin (N + 1)),
          ‖localUnitaryAction
              (A phase (bucket phase r))
              (B phase (bucket phase s))
              (tensorEmbezzlementTarget (n := n)
                (dSVCanonicalFailureUnitRankFamily N grid r)) -
            embezzlementState (N * n)‖ ^ 2 ≤
              2 * ε ^ 2 +
              8 * |(r.val : ℝ) -
                ((representative phase (bucket phase r)).val : ℝ)| /
                (max 1
                  (min r.val
                    (representative phase (bucket phase r)).val) : ℕ) +
              4 * (if bucket phase r = bucket phase s
                then (0 : ℝ) else 1) := by
  obtain ⟨n, positive, A, B, accurate⟩ :=
    dSVDensityRationalPublicBucketLocalHarmonicCleanup_sq
      grid (dSVCanonicalFailureUnitRankFamily N grid)
      bucket representative ε precision
  refine ⟨n, positive, A, B, ?_⟩
  intro phase r s
  have actual := accurate phase r s
  have relative :=
    dSVDensityRationalCanonicalUnitPrefix_relative_distance_sq
      grid r (representative phase (bucket phase r))
  calc
    _ ≤ 2 * ε ^ 2 +
        2 * ‖(dSVCanonicalFailureUnitRankFamily N grid r).val -
          (dSVCanonicalFailureUnitRankFamily N grid
            (representative phase (bucket phase r))).val‖ ^ 2 +
        4 * (if bucket phase r = bucket phase s
          then (0 : ℝ) else 1) := actual
    _ ≤ 2 * ε ^ 2 +
        2 * (4 * |(r.val : ℝ) -
          ((representative phase (bucket phase r)).val : ℝ)| /
            (max 1
              (min r.val
                (representative phase (bucket phase r)).val) : ℕ)) +
        4 * (if bucket phase r = bucket phase s
          then (0 : ℝ) else 1) := by
      gcongr
    _ = _ := by ring

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

def dSVDensityRationalPublicBucketCoherentPhaseHistory
    {H : Type*} [Fintype H] (B : ℕ)
    (history : EuclideanSpace ℂ (H × H)) :
    EuclideanSpace ℂ ((Fin B × H) × (Fin B × H)) :=
  toLp 2 fun q : (Fin B × H) × (Fin B × H) =>
    ePRState B (q.1.1, q.2.1) *
      history (q.1.2, q.2.2)

theorem dSVDensityRationalPublicBucketCoherentPhaseHistory_apply
    {H : Type*} [Fintype H] (B : ℕ)
    (history : EuclideanSpace ℂ (H × H))
    (φ ψ : Fin B) (a b : H) :
    dSVDensityRationalPublicBucketCoherentPhaseHistory
        B history ((φ, a), (ψ, b)) =
      ePRState B (φ, ψ) * history (a, b) := by
  rfl

theorem dSVDensityRationalPublicBucketCoherentPhaseHistory_apply_norm_sq
    {H : Type*} [Fintype H] {B : ℕ}
    (positive : 0 < B)
    (history : EuclideanSpace ℂ (H × H))
    (φ ψ : Fin B) (a b : H) :
    ‖dSVDensityRationalPublicBucketCoherentPhaseHistory
        B history ((φ, a), (ψ, b))‖ ^ 2 =
      (if φ = ψ then (B : ℝ)⁻¹ else 0) *
        ‖history (a, b)‖ ^ 2 := by
  rw [dSVDensityRationalPublicBucketCoherentPhaseHistory_apply,
    norm_mul, mul_pow]
  by_cases same : φ = ψ
  · subst ψ
    simp only [ePRState, ↓reduceIte]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),
      inv_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ B)]
  · simp [ePRState, same]

def dSVDensityRationalPublicBucketCoherentPhaseSigmaState
    {H : Type*} [Fintype H] {m : ℕ} (B : ℕ)
    (history : EuclideanSpace ℂ (H × H))
    (work : Fin B → H → H →
      EuclideanSpace ℂ (Fin m × Fin m)) :
    EuclideanSpace ℂ
      ((Σ _ : Fin B × H, Fin m) ×
       (Σ _ : Fin B × H, Fin m)) :=
  dSVUniformDensityCorrectedMatchedSigmaWeightedResidual
    (dSVDensityRationalPublicBucketCoherentPhaseHistory
      B history)
    (fun a b => work a.1 a.2 b.2)

def dSVDensityRationalPublicBucketCoherentPhaseLocalUnitary
    {H I : Type*} [Fintype H] [DecidableEq H]
    [DecidableEq I] {B D m : ℕ}
    (rank : H → Fin D)
    (bucket : Fin B → Fin D → I)
    (A : Fin B → I → Matrix.unitaryGroup (Fin m) ℂ) :
    Matrix.unitaryGroup (Σ _ : Fin B × H, Fin m) ℂ :=
  coherentSharedRandomControlledUnitary
    (fun q : Fin B × H => A q.1 (bucket q.1 (rank q.2)))

theorem dSVDensityRationalPublicBucketCoherentPhaseSigmaReset_distance_sq
    {H I : Type*} [Fintype H] [DecidableEq H]
    [DecidableEq I] {B D m : ℕ}
    (phase_positive : 0 < B)
    (history : EuclideanSpace ℂ (H × H))
    (rankA rankB : H → Fin D)
    (bucket : Fin B → Fin D → I)
    (A C : Fin B → I → Matrix.unitaryGroup (Fin m) ℂ)
    (work target : Fin B → H → H →
      EuclideanSpace ℂ (Fin m × Fin m)) :
    ‖dSVUniformDensityPhysicalAsyncSigmaContinuation
          (fun q : Fin B × H =>
            A q.1 (bucket q.1 (rankA q.2)))
          (fun q : Fin B × H =>
            C q.1 (bucket q.1 (rankB q.2)))
          (dSVDensityRationalPublicBucketCoherentPhaseSigmaState
            B history work) -
        dSVDensityRationalPublicBucketCoherentPhaseSigmaState
          B history target‖ ^ 2 =
      (∑ φ : Fin B, ∑ a : H, ∑ b : H,
        ‖history (a, b)‖ ^ 2 *
          ‖localUnitaryAction
              (A φ (bucket φ (rankA a)))
              (C φ (bucket φ (rankB b)))
              (work φ a b) - target φ a b‖ ^ 2) /
        (B : ℝ) := by
  classical
  unfold dSVDensityRationalPublicBucketCoherentPhaseSigmaState
  rw [dSVUniformDensityCorrectedMatchedSigmaControlledReset_distance_sq]
  simp_rw [Fintype.sum_prod_type]
  change
    (∑ φ : Fin B, ∑ a : H,
      ∑ ψ : Fin B, ∑ b : H,
        ‖dSVDensityRationalPublicBucketCoherentPhaseHistory
            B history ((φ, a), (ψ, b))‖ ^ 2 *
          ‖localUnitaryAction
              (A φ (bucket φ (rankA a)))
              (C ψ (bucket ψ (rankB b)))
              (work φ a b) - target φ a b‖ ^ 2) = _
  simp_rw [
    dSVDensityRationalPublicBucketCoherentPhaseHistory_apply_norm_sq
      phase_positive]
  calc
    (∑ φ : Fin B, ∑ a : H,
      ∑ ψ : Fin B, ∑ b : H,
        ((if φ = ψ then (B : ℝ)⁻¹ else 0) *
          ‖history (a, b)‖ ^ 2) *
          ‖localUnitaryAction
              (A φ (bucket φ (rankA a)))
              (C ψ (bucket ψ (rankB b)))
              (work φ a b) - target φ a b‖ ^ 2) =
      ∑ φ : Fin B, ∑ a : H, ∑ b : H,
        (B : ℝ)⁻¹ *
          (‖history (a, b)‖ ^ 2 *
            ‖localUnitaryAction
                (A φ (bucket φ (rankA a)))
                (C φ (bucket φ (rankB b)))
                (work φ a b) - target φ a b‖ ^ 2) := by
      apply Finset.sum_congr rfl
      intro φ _
      apply Finset.sum_congr rfl
      intro a _
      simp [mul_assoc]
    _ = (B : ℝ)⁻¹ *
        (∑ φ : Fin B, ∑ a : H, ∑ b : H,
          ‖history (a, b)‖ ^ 2 *
            ‖localUnitaryAction
                (A φ (bucket φ (rankA a)))
                (C φ (bucket φ (rankB b)))
                (work φ a b) - target φ a b‖ ^ 2) := by
      simp_rw [Finset.mul_sum]
    _ = _ := by ring

end

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder

theorem dSVDensityRationalPublicLogRank_real_log_bound
    {r s : ℝ} (positive_r : 0 < r) (positive_s : 0 < s) :
    min r s * |Real.log r - Real.log s| ≤ |r - s| := by
  have in_order :
      ∀ {x y : ℝ}, 0 < x → 0 < y → x ≤ y →
        min x y * |Real.log x - Real.log y| ≤ |x - y| := by
    intro x y positive_x positive_y ordered
    have logarithmic :=
      Real.log_le_sub_one_of_pos (div_pos positive_y positive_x)
    have monotone := Real.log_le_log positive_x ordered
    have bound : x * (Real.log y - Real.log x) ≤ y - x := by
      calc
        x * (Real.log y - Real.log x) =
            x * Real.log (y / x) := by
          rw [Real.log_div positive_y.ne' positive_x.ne']
        _ ≤ x * (y / x - 1) :=
          mul_le_mul_of_nonneg_left logarithmic positive_x.le
        _ = y - x := by
          field_simp
    calc
      min x y * |Real.log x - Real.log y| =
          x * (Real.log y - Real.log x) := by
        rw [min_eq_left ordered,
          abs_of_nonpos (sub_nonpos.mpr monotone)]
        ring
      _ ≤ y - x := bound
      _ = |x - y| := by
        rw [abs_of_nonpos (sub_nonpos.mpr ordered)]
        ring
  rcases le_total r s with ordered | ordered
  · exact in_order positive_r positive_s ordered
  · simpa [min_comm, abs_sub_comm] using
      in_order positive_s positive_r ordered

theorem dSVDensityRationalPublicLogRank_zeroSafe_nat_bound
    (r s : ℕ) :
    min (r : ℝ) (s : ℝ) *
        |Real.log ((max 1 r : ℕ) : ℝ) -
          Real.log ((max 1 s : ℕ) : ℝ)| ≤
      |(r : ℝ) - (s : ℝ)| := by
  by_cases zero_r : r = 0
  · simp [zero_r]
  by_cases zero_s : s = 0
  · simp [zero_s]
  have positive_r : 0 < r := Nat.pos_of_ne_zero zero_r
  have positive_s : 0 < s := Nat.pos_of_ne_zero zero_s
  have one_r : 1 ≤ r := positive_r
  have one_s : 1 ≤ s := positive_s
  simpa [max_eq_right one_r, max_eq_right one_s] using
    (dSVDensityRationalPublicLogRank_real_log_bound
      (by exact_mod_cast positive_r : (0 : ℝ) < r)
      (by exact_mod_cast positive_s : (0 : ℝ) < s))

theorem dSVDensityRationalPublicLogRank_zeroSafe_fin_bound
    {N : ℕ} (r s : Fin (N + 1)) :
    min (r.val : ℝ) (s.val : ℝ) *
        |Real.log ((max 1 r.val : ℕ) : ℝ) -
          Real.log ((max 1 s.val : ℕ) : ℝ)| ≤
      |(r.val : ℝ) - (s.val : ℝ)| :=
  dSVDensityRationalPublicLogRank_zeroSafe_nat_bound
    r.val s.val

def dSVDensityRationalPublicLogRankFineLabel
    {N : ℕ} (Q : ℕ) (r : Fin (N + 1)) : ℕ :=
  Nat.floor ((Q : ℝ) * Real.log ((max 1 r.val : ℕ) : ℝ))

def dSVDensityRationalPublicLogRankPhaseWeight
    (B : ℕ) (_ : Fin B) : ℝ :=
  1 / (B : ℝ)

theorem dSVDensityRationalPublicLogRankPhaseWeight_sum
    {B : ℕ} (positive : 0 < B) :
    (∑ phase : Fin B,
      dSVDensityRationalPublicLogRankPhaseWeight B phase) = 1 := by
  have real_positive : (0 : ℝ) < (B : ℝ) := by
    exact_mod_cast positive
  simp [dSVDensityRationalPublicLogRankPhaseWeight,
    real_positive.ne']

def dSVDensityRationalPublicLogRankBucket
    {N B : ℕ} (Q : ℕ) (phase : Fin B)
    (r : Fin (N + 1)) : Option ℕ :=
  if r.val = 0 then none
  else some
    ((dSVDensityRationalPublicLogRankFineLabel Q r + phase.val) / B)

theorem dSVDensityRationalPublicLogRankBucket_fineLabel_sub_lt
    {N B : ℕ} (Q : ℕ) (phase : Fin B)
    (r s : Fin (N + 1))
    (nonzero_r : r.val ≠ 0) (nonzero_s : s.val ≠ 0)
    (same :
      dSVDensityRationalPublicLogRankBucket Q phase r =
        dSVDensityRationalPublicLogRankBucket Q phase s) :
    |(dSVDensityRationalPublicLogRankFineLabel Q r : ℝ) -
      (dSVDensityRationalPublicLogRankFineLabel Q s : ℝ)| <
      (B : ℝ) := by
  have positive : 0 < B := by
    have bound := phase.isLt
    omega
  have quotient :
      (dSVDensityRationalPublicLogRankFineLabel Q r +
        phase.val) / B =
      (dSVDensityRationalPublicLogRankFineLabel Q s +
        phase.val) / B := by
    simpa [dSVDensityRationalPublicLogRankBucket,
      nonzero_r, nonzero_s] using same
  have remainder_r := Nat.mod_lt
    (dSVDensityRationalPublicLogRankFineLabel Q r + phase.val)
    positive
  have remainder_s := Nat.mod_lt
    (dSVDensityRationalPublicLogRankFineLabel Q s + phase.val)
    positive
  have reconstruction_r := Nat.mod_add_div
    (dSVDensityRationalPublicLogRankFineLabel Q r + phase.val) B
  have reconstruction_s := Nat.mod_add_div
    (dSVDensityRationalPublicLogRankFineLabel Q s + phase.val) B
  rw [quotient] at reconstruction_r
  rcases le_total
    (dSVDensityRationalPublicLogRankFineLabel Q r)
    (dSVDensityRationalPublicLogRankFineLabel Q s)
    with ordered | ordered
  · have difference :
        dSVDensityRationalPublicLogRankFineLabel Q s -
          dSVDensityRationalPublicLogRankFineLabel Q r < B := by
      omega
    have real_difference :
        (dSVDensityRationalPublicLogRankFineLabel Q s : ℝ) -
          (dSVDensityRationalPublicLogRankFineLabel Q r : ℝ) <
            (B : ℝ) := by
      exact_mod_cast difference
    rw [abs_of_nonpos
      (sub_nonpos.mpr (by exact_mod_cast ordered))]
    linarith
  · have difference :
        dSVDensityRationalPublicLogRankFineLabel Q r -
          dSVDensityRationalPublicLogRankFineLabel Q s < B := by
      omega
    have real_difference :
        (dSVDensityRationalPublicLogRankFineLabel Q r : ℝ) -
          (dSVDensityRationalPublicLogRankFineLabel Q s : ℝ) <
            (B : ℝ) := by
      exact_mod_cast difference
    rw [abs_of_nonneg
      (sub_nonneg.mpr (by exact_mod_cast ordered))]
    exact real_difference

theorem dSVDensityRationalPublicLogRank_logCoordinate_nonneg
    {N : ℕ} (Q : ℕ) (r : Fin (N + 1)) :
    0 ≤ (Q : ℝ) * Real.log ((max 1 r.val : ℕ) : ℝ) := by
  apply mul_nonneg (Nat.cast_nonneg Q)
  apply Real.log_nonneg
  exact_mod_cast (le_max_left 1 r.val)

theorem dSVDensityRationalPublicLogRankFineLabel_bounds
    {N : ℕ} (Q : ℕ) (r : Fin (N + 1)) :
    (dSVDensityRationalPublicLogRankFineLabel Q r : ℝ) ≤
        (Q : ℝ) * Real.log ((max 1 r.val : ℕ) : ℝ) ∧
      (Q : ℝ) * Real.log ((max 1 r.val : ℕ) : ℝ) <
        (dSVDensityRationalPublicLogRankFineLabel Q r : ℝ) + 1 := by
  constructor
  · exact Nat.floor_le
      (dSVDensityRationalPublicLogRank_logCoordinate_nonneg Q r)
  · exact Nat.lt_floor_add_one _

theorem dSVDensityRationalPublicLogRankBucket_log_sub_lt
    {N B : ℕ} {Q : ℕ} (positive_Q : 0 < Q)
    (phase : Fin B) (r s : Fin (N + 1))
    (nonzero_r : r.val ≠ 0) (nonzero_s : s.val ≠ 0)
    (same :
      dSVDensityRationalPublicLogRankBucket Q phase r =
        dSVDensityRationalPublicLogRankBucket Q phase s) :
    |Real.log ((max 1 r.val : ℕ) : ℝ) -
      Real.log ((max 1 s.val : ℕ) : ℝ)| <
      ((B : ℝ) + 1) / (Q : ℝ) := by
  have real_Q : (0 : ℝ) < (Q : ℝ) := by
    exact_mod_cast positive_Q
  have rank_bounds :=
    dSVDensityRationalPublicLogRankFineLabel_bounds Q r
  have other_bounds :=
    dSVDensityRationalPublicLogRankFineLabel_bounds Q s
  have bucket_bounds :=
    dSVDensityRationalPublicLogRankBucket_fineLabel_sub_lt
      Q phase r s nonzero_r nonzero_s same
  apply (lt_div_iff₀ real_Q).2
  rcases le_total
      (Real.log ((max 1 r.val : ℕ) : ℝ))
      (Real.log ((max 1 s.val : ℕ) : ℝ)) with ordered | ordered
  · rw [abs_of_nonpos (sub_nonpos.mpr ordered)]
    have integer_order := (abs_lt.mp bucket_bounds).1
    nlinarith [rank_bounds.1, other_bounds.2]
  · rw [abs_of_nonneg (sub_nonneg.mpr ordered)]
    have integer_order := (abs_lt.mp bucket_bounds).2
    nlinarith [rank_bounds.2, other_bounds.1]

def dSVDensityRationalPublicLogRankBucketFiber
    {N B : ℕ} (Q : ℕ) (phase : Fin B) (label : Option ℕ) :
    Finset (Fin (N + 1)) :=
  Finset.univ.filter fun r : Fin (N + 1) =>
    r.val ≠ 0 ∧
      dSVDensityRationalPublicLogRankBucket Q phase r = label

theorem dSVDensityRationalPublicLogRankBucketFiber_mem
    {N B : ℕ} (Q : ℕ) (phase : Fin B) (label : Option ℕ)
    (r : Fin (N + 1)) :
    r ∈ dSVDensityRationalPublicLogRankBucketFiber
        Q phase label ↔
      r.val ≠ 0 ∧
        dSVDensityRationalPublicLogRankBucket Q phase r = label := by
  simp [dSVDensityRationalPublicLogRankBucketFiber]

def dSVDensityRationalPublicLogRankBucketRepresentative
    {N B : ℕ} (Q : ℕ) (phase : Fin B) (label : Option ℕ) :
    Fin (N + 1) :=
  if present :
    (dSVDensityRationalPublicLogRankBucketFiber
      Q phase label).Nonempty
  then (dSVDensityRationalPublicLogRankBucketFiber
      Q phase label).min' present
  else 0

theorem dSVDensityRationalPublicLogRankBucketRepresentative_mem
    {N B : ℕ} (Q : ℕ) (phase : Fin B) (label : Option ℕ)
    (present :
      (dSVDensityRationalPublicLogRankBucketFiber
        (N := N) Q phase label).Nonempty) :
    dSVDensityRationalPublicLogRankBucketRepresentative
        (N := N) Q phase label ∈
      dSVDensityRationalPublicLogRankBucketFiber
        (N := N) Q phase label := by
  simpa [dSVDensityRationalPublicLogRankBucketRepresentative,
    present] using
    (Finset.min'_mem
      (dSVDensityRationalPublicLogRankBucketFiber
        (N := N) Q phase label) present)

theorem dSVDensityRationalPublicLogRankBucketRepresentative_same
    {N B : ℕ} (Q : ℕ) (phase : Fin B)
    (r : Fin (N + 1)) (nonzero : r.val ≠ 0) :
    (dSVDensityRationalPublicLogRankBucketRepresentative
        (N := N) Q phase
          (dSVDensityRationalPublicLogRankBucket
            Q phase r)).val ≠ 0 ∧
      dSVDensityRationalPublicLogRankBucket Q phase
        (dSVDensityRationalPublicLogRankBucketRepresentative
          (N := N) Q phase
            (dSVDensityRationalPublicLogRankBucket
              Q phase r)) =
        dSVDensityRationalPublicLogRankBucket Q phase r := by
  have member :
      r ∈ dSVDensityRationalPublicLogRankBucketFiber
        Q phase
          (dSVDensityRationalPublicLogRankBucket
            Q phase r) :=
    (dSVDensityRationalPublicLogRankBucketFiber_mem
      Q phase _ r).mpr ⟨nonzero, rfl⟩
  have present :
      (dSVDensityRationalPublicLogRankBucketFiber
        Q phase
          (dSVDensityRationalPublicLogRankBucket
            Q phase r)).Nonempty := ⟨r, member⟩
  exact
    (dSVDensityRationalPublicLogRankBucketFiber_mem
      Q phase _ _).mp
      (dSVDensityRationalPublicLogRankBucketRepresentative_mem
        (N := N) Q phase _ present)

theorem dSVDensityRationalPublicLogRankBucketRepresentative_le
    {N B : ℕ} (Q : ℕ) (phase : Fin B)
    (r : Fin (N + 1)) (nonzero : r.val ≠ 0) :
    dSVDensityRationalPublicLogRankBucketRepresentative
        (N := N) Q phase
          (dSVDensityRationalPublicLogRankBucket
            Q phase r) ≤ r := by
  have member :
      r ∈ dSVDensityRationalPublicLogRankBucketFiber
        Q phase
          (dSVDensityRationalPublicLogRankBucket
            Q phase r) :=
    (dSVDensityRationalPublicLogRankBucketFiber_mem
      Q phase _ r).mpr ⟨nonzero, rfl⟩
  have present :
      (dSVDensityRationalPublicLogRankBucketFiber
        Q phase
          (dSVDensityRationalPublicLogRankBucket
            Q phase r)).Nonempty := ⟨r, member⟩
  simp only
    [dSVDensityRationalPublicLogRankBucketRepresentative,
      dif_pos present]
  exact Finset.min'_le _ r member

theorem dSVDensityRationalPublicLogRankBucketRepresentative_log_sub_lt
    {N B : ℕ} {Q : ℕ} (positive_Q : 0 < Q)
    (phase : Fin B) (r : Fin (N + 1)) (nonzero : r.val ≠ 0) :
    |Real.log ((max 1 r.val : ℕ) : ℝ) -
      Real.log
        ((max 1
          (dSVDensityRationalPublicLogRankBucketRepresentative
            (N := N) Q phase
              (dSVDensityRationalPublicLogRankBucket
                Q phase r)).val : ℕ) : ℝ)| <
      ((B : ℝ) + 1) / (Q : ℝ) := by
  have same :=
    dSVDensityRationalPublicLogRankBucketRepresentative_same
      Q phase r nonzero
  exact dSVDensityRationalPublicLogRankBucket_log_sub_lt
    positive_Q phase r _ nonzero same.1 same.2.symm

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

abbrev DSVDensityRationalPublicMultiscalePhase
    (S B : ℕ) :=
  Fin S → Fin B

abbrev DSVDensityRationalPublicMultiscalePhaseIndex
    (S B : ℕ) :=
  Fin (Fintype.card
    (DSVDensityRationalPublicMultiscalePhase S B))

theorem dSVDensityRationalPublicMultiscalePhase_card
    (S B : ℕ) :
    Fintype.card
        (DSVDensityRationalPublicMultiscalePhase S B) =
      B ^ S := by
  simp [DSVDensityRationalPublicMultiscalePhase]

theorem dSVDensityRationalPublicMultiscalePhase_card_pos
    {S B : ℕ} (positive : 0 < B) :
    0 < Fintype.card
      (DSVDensityRationalPublicMultiscalePhase S B) := by
  rw [dSVDensityRationalPublicMultiscalePhase_card]
  exact pow_pos positive S

def dSVDensityRationalPrefixHarmonicSpectralOverlap
    {d : ℕ} (ξ ζ : BipartiteUnitVector d)
    (i j : Fin d) : ℝ :=
  spectralAtomOverlap
    (dSVSoftBobLeftReducedDensity ξ)
    (dSVSoftBobLeftReducedDensity ζ)
    (dSVSoftBobLeftReducedDensity_posSemidef ξ)
    (dSVSoftBobLeftReducedDensity_posSemidef ζ) i j

theorem dSVDensityRationalPrefixHarmonicSpectralOverlap_nonneg
    {d : ℕ} (ξ ζ : BipartiteUnitVector d)
    (i j : Fin d) :
    0 ≤ dSVDensityRationalPrefixHarmonicSpectralOverlap
      ξ ζ i j :=
  spectralAtomOverlap_nonneg _ _ _ _ i j

def dSVDensityRationalLocalSpectralPairBasisOverlap
    {d : ℕ} (ξ ζ : BipartiteUnitVector d)
    (i j : Fin d) : ℂ :=
  unitaryBasisOverlap
    (dSVSoftBobLeftReducedDensity_posSemidef
      ξ).isHermitian.eigenvectorUnitary
    (dSVSoftBobLeftReducedDensity_posSemidef
      ζ).isHermitian.eigenvectorUnitary i j

theorem dSVDensityRationalLocalSpectralPairBasisOverlap_norm_sq
    {d : ℕ} (ξ ζ : BipartiteUnitVector d)
    (i j : Fin d) :
    ‖dSVDensityRationalLocalSpectralPairBasisOverlap
        ξ ζ i j‖ ^ 2 =
      dSVDensityRationalPrefixHarmonicSpectralOverlap
        ξ ζ i j := by
  unfold dSVDensityRationalLocalSpectralPairBasisOverlap
    dSVDensityRationalPrefixHarmonicSpectralOverlap
  exact (targetSpectralAtomOverlap_eq_basis_norm_sq
    (dSVSoftBobLeftReducedDensity ξ)
    (dSVSoftBobLeftReducedDensity ζ)
    (dSVSoftBobLeftReducedDensity_posSemidef ξ)
    (dSVSoftBobLeftReducedDensity_posSemidef ζ) i j).symm

def dSVDensityRationalLocalSpectralPairHistory
    {d : ℕ} (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  toLp 2 fun q : Fin d × Fin d =>
    ((‖sharedThresholdResourceRaw (d := Fin d)
      (fun _ : Fin N => (1 : ℝ))‖⁻¹ : ℝ) : ℂ) *
      dSVDensityRationalLocalSpectralPairBasisOverlap
        ξ ζ q.1 q.2

theorem dSVDensityRationalLocalSpectralPairHistory_apply_norm_sq
    {d : ℕ} (N : ℕ)
    (ξ ζ : BipartiteUnitVector d)
    (i j : Fin d) :
    ‖dSVDensityRationalLocalSpectralPairHistory
        N ξ ζ (i, j)‖ ^ 2 =
      dSVDensityRationalPrefixHarmonicSpectralOverlap
        ξ ζ i j / ((d : ℝ) * (N : ℝ)) := by
  unfold dSVDensityRationalLocalSpectralPairHistory
  change
    ‖((‖sharedThresholdResourceRaw (d := Fin d)
        (fun _ : Fin N => (1 : ℝ))‖⁻¹ : ℝ) : ℂ) *
      dSVDensityRationalLocalSpectralPairBasisOverlap
        ξ ζ i j‖ ^ 2 = _
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    sq_abs,
    dSVDensityRationalLocalSpectralPairBasisOverlap_norm_sq,
    inv_pow, dSVUniformDensityThresholdRaw_norm_sq]
  ring

def dSVDensityRationalMixedCanonicalCrossMatrix
    {d : ℕ} (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    Matrix (DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
  (Matrix.blockDiagonal' fun _ : Fin N =>
    (unitaryBasisOverlap
      (dSVSoftBobLeftReducedDensity_posSemidef
        ξ).isHermitian.eigenvectorUnitary
      (dSVSoftBobLeftReducedDensity_posSemidef
        ζ).isHermitian.eigenvectorUnitary :
      Matrix (Fin d) (Fin d) ℂ)).transpose

theorem dSVDensityRationalMixedCanonicalCrossGauge_eq
    {d : ℕ} (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    (((dSVUniformDensityBobHistoryCopyBasis
        (N := N) ζ)⁻¹ : Matrix.unitaryGroup
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
      Matrix (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) *
      (dSVUniformDensityBobHistoryCopyBasis
        (N := N) ξ :
        Matrix (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) =
      dSVDensityRationalMixedCanonicalCrossMatrix N ξ ζ := by
  rw [← dSVUniformDensityPhysicalSpectralAliceCopy_inv_transpose ζ,
    ← dSVUniformDensityPhysicalSpectralAliceCopy_transpose ξ,
    ← Matrix.transpose_mul]
  unfold dSVDensityRationalMixedCanonicalCrossMatrix
  congr 1
  rw [dSVUniformDensityPhysicalSpectralAliceCopy_inv]
  change
    Matrix.blockDiagonal' (fun _ : Fin N =>
      (((dSVUniformDensityThresholdLeftBobBasis ξ)⁻¹ :
        Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ)) *
      Matrix.blockDiagonal' (fun _ : Fin N =>
        (dSVUniformDensityThresholdLeftBobBasis ζ :
          Matrix (Fin d) (Fin d) ℂ)) =
      Matrix.blockDiagonal' (fun _ : Fin N =>
        (unitaryBasisOverlap
          (dSVSoftBobLeftReducedDensity_posSemidef
            ξ).isHermitian.eigenvectorUnitary
          (dSVSoftBobLeftReducedDensity_posSemidef
            ζ).isHermitian.eigenvectorUnitary :
          Matrix (Fin d) (Fin d) ℂ))
  rw [← Matrix.blockDiagonal'_mul]
  rfl

theorem dSVDensityRationalCanonicalPrefixMask_eq_diagonal
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) :
    dSVDensityRationalCanonicalPrefixMask w N ξ =
      Matrix.diagonal
        (fun q : DSVUniformDensityThresholdLocalIndex N d =>
          if dSVDensityRationalProjectiveThresholdBin w N q.1
              ((dSVSoftBobLeftReducedDensity_posSemidef
                ξ).isHermitian.eigenvalues q.2) = true
          then (1 : ℂ) else 0) := by
  unfold dSVDensityRationalCanonicalPrefixMask
  rw [Matrix.blockDiagonal'_diagonal]

def dSVDensityRationalMixedCanonicalRawSource
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      (DSVUniformDensityThresholdLocalIndex N d ×
        DSVUniformDensityThresholdLocalIndex N d) :=
  toLp 2
    (Matrix.vec
      (dSVDensityRationalCanonicalPrefixMask w N ζ *
        dSVDensityRationalMixedCanonicalCrossMatrix N ξ ζ *
        dSVDensityRationalCanonicalPrefixMask w N ξ))

theorem dSVDensityRationalMixedCanonicalRawSource_apply
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d)
    (k l : Fin N) (i j : Fin d) :
    dSVDensityRationalMixedCanonicalRawSource
        w N ξ ζ (⟨k, i⟩, ⟨l, j⟩) =
      if k = l ∧
        dSVDensityRationalProjectiveThresholdBin w N k
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ξ).isHermitian.eigenvalues i) = true ∧
        dSVDensityRationalProjectiveThresholdBin w N l
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ζ).isHermitian.eigenvalues j) = true
      then
        dSVDensityRationalLocalSpectralPairBasisOverlap ξ ζ i j
      else 0 := by
  classical
  unfold dSVDensityRationalMixedCanonicalRawSource
  rw [dSVDensityRationalCanonicalPrefixMask_eq_diagonal w N ζ,
    dSVDensityRationalCanonicalPrefixMask_eq_diagonal w N ξ]
  change
    (Matrix.diagonal
        (fun q : DSVUniformDensityThresholdLocalIndex N d =>
          if dSVDensityRationalProjectiveThresholdBin w N q.1
              ((dSVSoftBobLeftReducedDensity_posSemidef
                ζ).isHermitian.eigenvalues q.2) = true
          then (1 : ℂ) else 0) *
        dSVDensityRationalMixedCanonicalCrossMatrix N ξ ζ *
        Matrix.diagonal
          (fun q : DSVUniformDensityThresholdLocalIndex N d =>
            if dSVDensityRationalProjectiveThresholdBin w N q.1
                ((dSVSoftBobLeftReducedDensity_posSemidef
                  ξ).isHermitian.eigenvalues q.2) = true
            then (1 : ℂ) else 0)) ⟨l, j⟩ ⟨k, i⟩ = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases flags : k = l
  · subst l
    by_cases alice :
        dSVDensityRationalProjectiveThresholdBin w N k
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ξ).isHermitian.eigenvalues i) = true
    · by_cases bob :
          dSVDensityRationalProjectiveThresholdBin w N k
            ((dSVSoftBobLeftReducedDensity_posSemidef
              ζ).isHermitian.eigenvalues j) = true
      · simp [dSVDensityRationalMixedCanonicalCrossMatrix,
          dSVDensityRationalLocalSpectralPairBasisOverlap,
          Matrix.blockDiagonal'_apply, alice, bob]
      · simp [bob]
    · simp [alice]
  · simp [dSVDensityRationalMixedCanonicalCrossMatrix,
      Matrix.blockDiagonal'_apply, flags]

theorem dSVDensityRationalMixedCanonicalProjectorMatrix_eq
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    (((dSVUniformDensityBobHistoryCopyBasis
        (N := N) ζ)⁻¹ : Matrix.unitaryGroup
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
      Matrix (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) *
      ((Matrix.blockDiagonal'
          (fun k : Fin N =>
            dSVDensityRationalPhysicalProjector w ξ k) *
        Matrix.blockDiagonal'
          (fun k : Fin N =>
            dSVDensityRationalPhysicalProjector w ζ k)).transpose) *
      (dSVUniformDensityAliceHistorySpectralCopy
        (N := N) ξ :
        Matrix (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ).transpose =
      dSVDensityRationalCanonicalPrefixMask w N ζ *
        dSVDensityRationalMixedCanonicalCrossMatrix N ξ ζ *
        dSVDensityRationalCanonicalPrefixMask w N ξ := by
  let S : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    dSVUniformDensityAliceHistorySpectralCopy (N := N) ξ
  let X : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    dSVUniformDensityBobHistoryCopyBasis (N := N) ξ
  let Z : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    dSVUniformDensityBobHistoryCopyBasis (N := N) ζ
  let XI : Matrix
      (DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    ((X⁻¹ : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
      Matrix (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ)
  let ZI : Matrix
      (DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    ((Z⁻¹ : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
      Matrix (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ)
  let M : Matrix
      (DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    dSVDensityRationalCanonicalPrefixMask w N ξ
  let R : Matrix
      (DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    dSVDensityRationalCanonicalPrefixMask w N ζ
  have physical_x :
      Matrix.blockDiagonal'
          (fun k : Fin N =>
            dSVDensityRationalPhysicalProjector w ξ k) =
        (((S⁻¹ : Matrix.unitaryGroup
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
          Matrix (DSVUniformDensityThresholdLocalIndex N d)
            (DSVUniformDensityThresholdLocalIndex N d) ℂ)) *
          M * (S : Matrix _ _ ℂ) :=
    dSVDensityRationalPhysicalAcceptedProjector_eq_spectralMask
      w N ξ
  have physical_z :
      Matrix.blockDiagonal'
          (fun k : Fin N =>
            dSVDensityRationalPhysicalProjector w ζ k) =
        ((((dSVUniformDensityAliceHistorySpectralCopy
          (N := N) ζ)⁻¹ : Matrix.unitaryGroup
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
          Matrix (DSVUniformDensityThresholdLocalIndex N d)
            (DSVUniformDensityThresholdLocalIndex N d) ℂ)) *
          R * (dSVUniformDensityAliceHistorySpectralCopy
            (N := N) ζ : Matrix _ _ ℂ) :=
    dSVDensityRationalPhysicalAcceptedProjector_eq_spectralMask
      w N ζ
  have transpose_x :
      (S : Matrix
        (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ).transpose =
        (X : Matrix
          (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) :=
    dSVUniformDensityPhysicalSpectralAliceCopy_transpose
      (N := N) ξ
  have transpose_z :
      (dSVUniformDensityAliceHistorySpectralCopy
          (N := N) ζ : Matrix
            (DSVUniformDensityThresholdLocalIndex N d)
            (DSVUniformDensityThresholdLocalIndex N d) ℂ).transpose =
        (Z : Matrix
          (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) :=
    dSVUniformDensityPhysicalSpectralAliceCopy_transpose
      (N := N) ζ
  have inverse_x :
      (((S⁻¹ : Matrix.unitaryGroup
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
        Matrix (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ)).transpose =
        (((X⁻¹ : Matrix.unitaryGroup
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
          Matrix (DSVUniformDensityThresholdLocalIndex N d)
            (DSVUniformDensityThresholdLocalIndex N d) ℂ)) :=
    dSVUniformDensityPhysicalSpectralAliceCopy_inv_transpose
      (N := N) ξ
  have inverse_z :
      ((((dSVUniformDensityAliceHistorySpectralCopy
        (N := N) ζ)⁻¹ : Matrix.unitaryGroup
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
        Matrix (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ)).transpose =
        (((Z⁻¹ : Matrix.unitaryGroup
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
          Matrix (DSVUniformDensityThresholdLocalIndex N d)
            (DSVUniformDensityThresholdLocalIndex N d) ℂ)) :=
    dSVUniformDensityPhysicalSpectralAliceCopy_inv_transpose
      (N := N) ζ
  have cancel_x :
      XI * (X : Matrix
        (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) = 1 := by
    change
      star (X : Matrix
        (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) *
        (X : Matrix
          (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) = 1
    exact (Matrix.mem_unitaryGroup_iff').mp X.property
  have cancel_z :
      ZI * (Z : Matrix
        (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) = 1 := by
    change
      star (Z : Matrix
        (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) *
        (Z : Matrix
          (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) = 1
    exact (Matrix.mem_unitaryGroup_iff').mp Z.property
  change
    ZI *
      ((Matrix.blockDiagonal'
          (fun k : Fin N =>
            dSVDensityRationalPhysicalProjector w ξ k) *
        Matrix.blockDiagonal'
          (fun k : Fin N =>
            dSVDensityRationalPhysicalProjector w ζ k)).transpose) *
      (S : Matrix _ _ ℂ).transpose =
        R * dSVDensityRationalMixedCanonicalCrossMatrix N ξ ζ * M
  calc
    _ = ((ZI * (Z : Matrix _ _ ℂ)) * R) *
        (ZI * (X : Matrix _ _ ℂ)) *
        (M * (XI * (X : Matrix _ _ ℂ))) := by
          rw [physical_x, physical_z]
          dsimp only [XI, ZI]
          simp only [Matrix.transpose_mul,
            dSVDensityRationalCanonicalPrefixMask_transpose,
            transpose_x, transpose_z, inverse_x, inverse_z,
            Matrix.mul_assoc, M, R]
    _ = R * (ZI * (X : Matrix _ _ ℂ)) * M := by
          rw [cancel_x, cancel_z]
          simp
    _ = _ := by
      dsimp only [ZI]
      rw [dSVDensityRationalMixedCanonicalCrossGauge_eq N ξ ζ]

theorem dSVDensityRationalMixedCanonicalSpectralOutcome_eq
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalCanonicalPrefixSpectralOutcome
        w N ξ ζ =
      (‖sharedThresholdResourceRaw (d := Fin d)
          (fun _ : Fin N => (1 : ℝ))‖⁻¹ : ℝ) •
        dSVDensityRationalMixedCanonicalRawSource w N ξ ζ := by
  classical
  let S : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    dSVUniformDensityAliceHistorySpectralCopy (N := N) ξ
  let T : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    dSVUniformDensityBobHistoryCopyBasis (N := N) ζ
  let c : ℝ :=
    ‖sharedThresholdResourceRaw (d := Fin d)
      (fun _ : Fin N => (1 : ℝ))‖⁻¹
  let K : Matrix
      (DSVUniformDensityThresholdLocalIndex N d ×
        DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d ×
        DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    (S : Matrix _ _ ℂ) ⊗ₖ
      (((T⁻¹ : Matrix.unitaryGroup
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
        Matrix (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ))
  unfold dSVDensityRationalCanonicalPrefixSpectralOutcome
    dSVDensityRationalPhysicalAcceptedOutcome
  rw [dSVDensityRationalCompleteProjectiveOutcome_eq_blockVector]
  unfold dSVDensityRationalMixedCanonicalRawSource
  change
    Matrix.toEuclideanLin K
      (c • toLp 2
        (Matrix.vec
          ((Matrix.blockDiagonal' fun k : Fin N =>
            dSVDensityRationalPhysicalProjector w ξ k *
              dSVDensityRationalPhysicalProjector
                w ζ k).transpose))) =
      c • toLp 2
        (Matrix.vec
          (dSVDensityRationalCanonicalPrefixMask w N ζ *
            dSVDensityRationalMixedCanonicalCrossMatrix N ξ ζ *
            dSVDensityRationalCanonicalPrefixMask w N ξ))
  rw [(Matrix.toEuclideanLin K).map_smul_of_tower]
  congr 1
  apply WithLp.ofLp_injective
  change
    K.mulVec
        (Matrix.vec
          ((Matrix.blockDiagonal' fun k : Fin N =>
            dSVDensityRationalPhysicalProjector w ξ k *
              dSVDensityRationalPhysicalProjector
                w ζ k).transpose)) =
      Matrix.vec
        (dSVDensityRationalCanonicalPrefixMask w N ζ *
          dSVDensityRationalMixedCanonicalCrossMatrix N ξ ζ *
          dSVDensityRationalCanonicalPrefixMask w N ξ)
  dsimp [K]
  rw [Matrix.kronecker_mulVec_vec]
  apply congrArg Matrix.vec
  rw [Matrix.blockDiagonal'_mul]
  exact dSVDensityRationalMixedCanonicalProjectorMatrix_eq
    w N ξ ζ

def dSVDensityRationalPublicLogBilateralPureTensor
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (v : EuclideanSpace ℂ (ι × ι))
    (u : EuclideanSpace ℂ (κ × κ)) :
    EuclideanSpace ℂ ((ι × κ) × (ι × κ)) :=
  toLp 2 fun q : (ι × κ) × (ι × κ) =>
    v (q.1.1, q.2.1) * u (q.1.2, q.2.2)

theorem dSVDensityRationalPublicLogBilateralPureTensor_norm_sq
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (v : EuclideanSpace ℂ (ι × ι))
    (u : EuclideanSpace ℂ (κ × κ)) :
    ‖dSVDensityRationalPublicLogBilateralPureTensor v u‖ ^ 2 =
      ‖v‖ ^ 2 * ‖u‖ ^ 2 := by
  classical
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq]
  change
    (∑ q : (ι × κ) × (ι × κ),
      ‖v (q.1.1, q.2.1) * u (q.1.2, q.2.2)‖ ^ 2) =
      (∑ q : ι × ι, ‖v q‖ ^ 2) *
        (∑ q : κ × κ, ‖u q‖ ^ 2)
  simp only [Fintype.sum_prod_type, norm_mul, mul_pow]
  calc
    (∑ a : ι, ∑ x : κ, ∑ b : ι, ∑ y : κ,
      ‖v (a, b)‖ ^ 2 * ‖u (x, y)‖ ^ 2) =
      ∑ a : ι, ∑ b : ι, ∑ x : κ, ∑ y : κ,
        ‖v (a, b)‖ ^ 2 * ‖u (x, y)‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
    _ = (∑ a : ι, ∑ b : ι, ‖v (a, b)‖ ^ 2) *
          (∑ x : κ, ∑ y : κ, ‖u (x, y)‖ ^ 2) := by
            symm
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro b _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            rw [Finset.mul_sum]

abbrev DSVDensityRationalPublicLogPhaseHistoryLocalIndex
    (B N d L : ℕ) :=
  Fin B × DSVUniformDensityThresholdWholeHistoryLocalIndex N d L

def dSVDensityRationalPublicLogPhasePureSource
    (B N d L : ℕ) :
    EuclideanSpace ℂ
      (DSVDensityRationalPublicLogPhaseHistoryLocalIndex B N d L ×
       DSVDensityRationalPublicLogPhaseHistoryLocalIndex B N d L) :=
  dSVDensityRationalPublicLogBilateralPureTensor
    (ePRState B)
    (dSVUniformDensityThresholdWholeHistorySharedState N d L)

theorem dSVDensityRationalPublicLogPhasePureSource_apply
    (B N d L : ℕ)
    (φ ψ : Fin B)
    (a b : DSVUniformDensityThresholdWholeHistoryLocalIndex
      N d L) :
    dSVDensityRationalPublicLogPhasePureSource
        B N d L ((φ, a), (ψ, b)) =
      (if φ = ψ then
        (((Real.sqrt (B : ℝ))⁻¹ : ℝ) : ℂ)
      else 0) *
        dSVUniformDensityThresholdWholeHistorySharedState
          N d L (a, b) := by
  simp [dSVDensityRationalPublicLogPhasePureSource,
    dSVDensityRationalPublicLogBilateralPureTensor, ePRState]

theorem dSVDensityRationalPublicLogPhasePureSource_norm
    {B N d L : ℕ}
    (phases : 0 < B) (grid : 0 < N) (dimension : 0 < d) :
    ‖dSVDensityRationalPublicLogPhasePureSource
      B N d L‖ = 1 := by
  have squared :
      ‖dSVDensityRationalPublicLogPhasePureSource
        B N d L‖ ^ 2 = 1 := by
    unfold dSVDensityRationalPublicLogPhasePureSource
    rw [dSVDensityRationalPublicLogBilateralPureTensor_norm_sq,
      ePRState_norm B phases,
      dSVUniformDensityThresholdWholeHistorySharedState_norm
        grid dimension L]
    norm_num
  nlinarith [norm_nonneg
    (dSVDensityRationalPublicLogPhasePureSource B N d L)]

def dSVDensityRationalPublicLogPhaseHarmonicPureSource
    (B N d L m : ℕ) :
    EuclideanSpace ℂ
      ((DSVDensityRationalPublicLogPhaseHistoryLocalIndex
        B N d L × Fin m) ×
       (DSVDensityRationalPublicLogPhaseHistoryLocalIndex
        B N d L × Fin m)) :=
  dSVDensityRationalPublicLogBilateralPureTensor
    (dSVDensityRationalPublicLogPhasePureSource B N d L)
    (embezzlementState m)

theorem dSVDensityRationalPublicLogPhaseHarmonicPureSource_apply
    (B N d L m : ℕ)
    (φ ψ : Fin B)
    (a b : DSVUniformDensityThresholdWholeHistoryLocalIndex
      N d L) (i j : Fin m) :
    dSVDensityRationalPublicLogPhaseHarmonicPureSource
        B N d L m (((φ, a), i), ((ψ, b), j)) =
      (if φ = ψ then
        (((Real.sqrt (B : ℝ))⁻¹ : ℝ) : ℂ)
      else 0) *
        dSVUniformDensityThresholdWholeHistorySharedState
          N d L (a, b) *
        embezzlementState m (i, j) := by
  change
    dSVDensityRationalPublicLogPhasePureSource
        B N d L ((φ, a), (ψ, b)) *
      embezzlementState m (i, j) = _
  rw [dSVDensityRationalPublicLogPhasePureSource_apply]

theorem dSVDensityRationalPublicLogPhaseHarmonicPureSource_norm
    {B N d L m : ℕ}
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m) :
    ‖dSVDensityRationalPublicLogPhaseHarmonicPureSource
      B N d L m‖ = 1 := by
  have squared :
      ‖dSVDensityRationalPublicLogPhaseHarmonicPureSource
        B N d L m‖ ^ 2 = 1 := by
    unfold dSVDensityRationalPublicLogPhaseHarmonicPureSource
    rw [dSVDensityRationalPublicLogBilateralPureTensor_norm_sq,
      dSVDensityRationalPublicLogPhasePureSource_norm
        phases grid dimension,
      embezzlementState_norm m harmonic]
    norm_num
  nlinarith [norm_nonneg
    (dSVDensityRationalPublicLogPhaseHarmonicPureSource
      B N d L m)]

abbrev DSVDensityRationalPublicLogPhaseCatalystIndex
    (B N d L : ℕ) :=
  Fin B × DSVUniformDensityThresholdWholeHistoryCatalystIndex N d L

def dSVDensityRationalPublicLogPhaseTargetSplitEquiv
    (B N d L : ℕ) :
    DSVDensityRationalPublicLogPhaseHistoryLocalIndex B N d L ≃
      (Fin d ×
        DSVDensityRationalPublicLogPhaseCatalystIndex B N d L) where
  toFun q :=
    let actual :=
      dSVUniformDensityThresholdWholeHistoryTargetSplitEquiv
        N d L q.2
    (actual.1, (q.1, actual.2))
  invFun q :=
    (q.2.1,
      (dSVUniformDensityThresholdWholeHistoryTargetSplitEquiv
        N d L).symm (q.1, q.2.2))
  left_inv := by
    rintro ⟨phase, history⟩
    simp
  right_inv := by
    rintro ⟨target, phase, catalyst⟩
    simp

def dSVDensityRationalPublicLogPhaseResidual
    (B N d L m : ℕ) : ℕ :=
  Fintype.card
      (DSVDensityRationalPublicLogPhaseCatalystIndex
        B N d L) * m

def dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
    (B N d L m : ℕ) :
    (DSVDensityRationalPublicLogPhaseHistoryLocalIndex
      B N d L × Fin m) ≃
      Fin (d *
        dSVDensityRationalPublicLogPhaseResidual B N d L m) :=
  (Equiv.prodCongr
    (dSVDensityRationalPublicLogPhaseTargetSplitEquiv B N d L)
    (Equiv.refl (Fin m))).trans
      (dSVRankControlledTargetCatalystIndexEquiv
        (ι := DSVDensityRationalPublicLogPhaseCatalystIndex
          B N d L) d m)

def dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource
    (B N d L m : ℕ) :
    EuclideanSpace ℂ
      (Fin (d *
        dSVDensityRationalPublicLogPhaseResidual B N d L m) ×
       Fin (d *
        dSVDensityRationalPublicLogPhaseResidual B N d L m)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (Equiv.prodCongr
      (dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
        B N d L m)
      (dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
        B N d L m))
    (dSVDensityRationalPublicLogPhaseHarmonicPureSource
      B N d L m)

theorem dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource_apply
    (B N d L m : ℕ)
    (φ ψ : Fin B)
    (a b : DSVUniformDensityThresholdWholeHistoryLocalIndex
      N d L) (i j : Fin m) :
    dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource
        B N d L m
        (dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
            B N d L m ((φ, a), i),
          dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
            B N d L m ((ψ, b), j)) =
      (if φ = ψ then
        (((Real.sqrt (B : ℝ))⁻¹ : ℝ) : ℂ)
      else 0) *
        dSVUniformDensityThresholdWholeHistorySharedState
          N d L (a, b) *
        embezzlementState m (i, j) := by
  unfold dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource
  simpa [LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft'] using
    (dSVDensityRationalPublicLogPhaseHarmonicPureSource_apply
      B N d L m φ ψ a b i j)

theorem dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource_norm
    {B N d L m : ℕ}
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m) :
    ‖dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource
      B N d L m‖ = 1 := by
  unfold dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource
  rw [LinearIsometryEquiv.norm_map]
  exact dSVDensityRationalPublicLogPhaseHarmonicPureSource_norm
    phases grid dimension harmonic

abbrev DSVDensityRationalPublicMultiscalePhaseHistoryLocalIndex
    (S B N d L : ℕ) :=
  DSVDensityRationalPublicMultiscalePhaseIndex S B ×
    DSVUniformDensityThresholdWholeHistoryLocalIndex N d L

def dSVDensityRationalPublicMultiscalePhaseResidual
    (S B N d L m : ℕ) : ℕ :=
  dSVDensityRationalPublicLogPhaseResidual
    (Fintype.card (DSVDensityRationalPublicMultiscalePhase S B))
    N d L m

def dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
    (S B N d L m : ℕ) :
    (DSVDensityRationalPublicMultiscalePhaseHistoryLocalIndex
      S B N d L × Fin m) ≃
      Fin (d *
        dSVDensityRationalPublicMultiscalePhaseResidual
          S B N d L m) :=
  dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
    (Fintype.card (DSVDensityRationalPublicMultiscalePhase S B))
    N d L m

def dSVDensityRationalPublicMultiscalePhaseTargetFirstPreparedSource
    (S B N d L m : ℕ) :
    EuclideanSpace ℂ
      (Fin (d *
         dSVDensityRationalPublicMultiscalePhaseResidual
           S B N d L m) ×
       Fin (d *
         dSVDensityRationalPublicMultiscalePhaseResidual
           S B N d L m)) :=
  dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource
    (Fintype.card (DSVDensityRationalPublicMultiscalePhase S B))
    N d L m

theorem
    dSVDensityRationalPublicMultiscalePhaseTargetFirstPreparedSource_norm
    {S B N d L m : ℕ}
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m) :
    ‖dSVDensityRationalPublicMultiscalePhaseTargetFirstPreparedSource
      S B N d L m‖ = 1 := by
  unfold
    dSVDensityRationalPublicMultiscalePhaseTargetFirstPreparedSource
  exact
    dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource_norm
      (dSVDensityRationalPublicMultiscalePhase_card_pos phases)
      grid dimension harmonic

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder

def dSVDensityRationalPublicLogPhaseActualTargetFirstLocalLift
    (B N d L m : ℕ)
    (U : Matrix.unitaryGroup
      (DSVDensityRationalPublicLogPhaseHistoryLocalIndex
        B N d L) ℂ) :
    Matrix.unitaryGroup
      (Fin (d *
        dSVDensityRationalPublicLogPhaseResidual
          B N d L m)) ℂ := by
  classical
  let whole : Matrix.unitaryGroup
      (DSVDensityRationalPublicLogPhaseHistoryLocalIndex
          B N d L × Fin m) ℂ :=
    ⟨U.val ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ),
      Matrix.kronecker_mem_unitary U.property
        (Matrix.unitaryGroup (Fin m) ℂ).one_mem⟩
  exact dSVOriginalComputationalReindexedUnitary
    (dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
      B N d L m) whole

theorem
    dSVDensityRationalPublicLogPhaseActualTargetFirstLocalLift_apply
    (B N d L m : ℕ)
    (U : Matrix.unitaryGroup
      (DSVDensityRationalPublicLogPhaseHistoryLocalIndex
        B N d L) ℂ)
    (a b : DSVDensityRationalPublicLogPhaseHistoryLocalIndex
      B N d L) (i j : Fin m) :
    dSVDensityRationalPublicLogPhaseActualTargetFirstLocalLift
      B N d L m U
      (dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
        B N d L m (a, i))
      (dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
        B N d L m (b, j)) =
      if i = j then U a b else 0 := by
  classical
  change
    (Matrix.reindex
      (dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
        B N d L m)
      (dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
        B N d L m)
      (U.val ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)))
      (dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
        B N d L m (a, i))
      (dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
        B N d L m (b, j)) = _
  simp [Matrix.reindex_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply]

def dSVDensityRationalPublicLogPhasePhysicalHistoryUnitary
    (B : ℕ) {N d L : ℕ}
    (U : Matrix.unitaryGroup
      (DSVUniformDensityThresholdWholeHistoryLocalIndex
        N d L) ℂ) :
    Matrix.unitaryGroup
      (DSVDensityRationalPublicLogPhaseHistoryLocalIndex
        B N d L) ℂ := by
  classical
  exact ⟨(1 : Matrix (Fin B) (Fin B) ℂ) ⊗ₖ U.val,
    Matrix.kronecker_mem_unitary
      (Matrix.unitaryGroup (Fin B) ℂ).one_mem U.property⟩

theorem dSVDensityRationalPublicLogPhasePhysicalHistoryUnitary_apply
    (B : ℕ) {N d L : ℕ}
    (U : Matrix.unitaryGroup
      (DSVUniformDensityThresholdWholeHistoryLocalIndex
        N d L) ℂ)
    (φ ψ : Fin B)
    (a b : DSVUniformDensityThresholdWholeHistoryLocalIndex
      N d L) :
    dSVDensityRationalPublicLogPhasePhysicalHistoryUnitary
        B U (φ, a) (ψ, b) =
      if φ = ψ then U a b else 0 := by
  classical
  change
    ((1 : Matrix (Fin B) (Fin B) ℂ) ⊗ₖ U.val)
      (φ, a) (ψ, b) = _
  simp [Matrix.kroneckerMap_apply, Matrix.one_apply]

end

end QuantumParallelRepetition
