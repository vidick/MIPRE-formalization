/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AuxiliaryDualKernel
import MIPRE.Foundations.Introspection.AdaptiveResidual

/-! # Decoding quotient-valued hiding answers

The executable dual check only compares cosets of a row space. Decode each
reported register to the semantic canonical representative. This decoding is
used to return soundness to the existing finite game; it is not part of the
executable verifier and makes no computability claim about `Fintype.equivFin`.
-/

noncomputable section
namespace MIPRE.Introspection.AuxiliaryDual

open Finset CLChecks
variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

theorem registerDual_proj {S : Finset (ι)} (L : CL.RegLinear F S) (x : ι → F) :
    CL.proj S (registerDual L x) = registerDual L x := by
  ext i
  by_cases hi : i ∈ S
  · simp [CL.proj_apply, hi]
  · simp [registerDual, LinearMap.comp_apply, coordinateInsert, CL.proj_apply, hi]

theorem registerDual_proj_input {S U : Finset (ι)} (L : CL.RegLinear F S)
    (hSU : S ⊆ U) (x : ι → F) : registerDual L (CL.proj U x) = registerDual L x := by
  simp only [registerDual, LinearMap.comp_apply, coordinateRestrict_proj hSU]

/-- The semantic dual map at a single reported stage. -/
def stageDual (P : CL.CLFun F (ι) ℓ) (k : ℕ) (y : ι → F) :
    (ι → F) →ₗ[F] (ι → F) := registerDual (stageLinear P k y)

theorem stageDual_apply {P : CL.CLFun F (ι) ℓ} {T : Finset (ι)}
    (hP : P.SupportedOn T) (k : ℕ) (y x : ι → F) :
    stageDual P k y x = dualReadout P k y x := by
  rw [dualReadout_stageLinear hP]
  rfl

theorem stageDual_prefix_congr {P : CL.CLFun F (ι) ℓ} {T : Finset (ι)}
    (hP : P.SupportedOn T) (k : ℕ) {y z : ι → F}
    (h : P.outputPrefix k y = P.outputPrefix k z) : stageDual P k y = stageDual P k z := by
  apply LinearMap.ext
  intro x
  rw [stageDual_apply hP, stageDual_apply hP,
    ← dualReadout_outputPrefix hP k y, ← dualReadout_outputPrefix hP k z, h]

/-- Selected registers are disjoint even for an unattainable reported output. -/
theorem stageFactors_disjoint {P : CL.CLFun F (ι) ℓ} {T : Finset (ι)}
    (hP : P.SupportedOn T) (y : ι → F) {i j : ℕ} (hij : i < j) :
    Disjoint (P.factorOfPrefix i y) (P.factorOfPrefix j y) := by
  have hi : P.factorOfPrefix i y ⊆ prefixRegister P j y :=
    (factorOfPrefix_subset_prefixRegister P i y).trans
      (prefixRegister_mono P y (by omega))
  exact disjoint_of_subset_left hi
    (disjoint_of_subset_right (stageFactor_subset_residual hP j y) disjoint_sdiff)

/-- Decode all stage labels while preserving the original claimed output. -/
def decodeDual (P : CL.CLFun F (ι) ℓ) (y : ι → F) :
    (ι → F) →ₗ[F] (ι → F) := ∑ j ∈ range ℓ, stageDual P j y

theorem decodeDual_apply (P : CL.CLFun F (ι) ℓ) (y x : ι → F) :
    decodeDual P y x = ∑ j ∈ range ℓ, stageDual P j y x := by
  simp only [decodeDual, LinearMap.sum_apply]

/-- Projection of the decoded answer extracts exactly its selected dual block. -/
theorem proj_decodeDual {P : CL.CLFun F (ι) ℓ} {T : Finset (ι)}
    (hP : P.SupportedOn T) (y x : ι → F) {k : ℕ} (hk : k < ℓ) :
    CL.proj (P.factorOfPrefix k y) (decodeDual P y x) = stageDual P k y x := by
  rw [decodeDual_apply, map_sum]
  rw [sum_eq_single k]
  · exact registerDual_proj _ _
  · intro j _ hj
    have hd : Disjoint (P.factorOfPrefix k y) (P.factorOfPrefix j y) := by
      rcases lt_or_gt_of_ne hj with h | h
      · exact (stageFactors_disjoint hP y h).symm
      · exact stageFactors_disjoint hP y h
    rw [stageDual, ← registerDual_proj (stageLinear P j y) x,
      CL.proj_proj_of_disjoint hd]
  · intro h
    exact (h (mem_range.mpr hk)).elim

/-- On every already visited register the decoder only uses that same raw prefix. -/
theorem proj_prefix_decodeDual {P : CL.CLFun F (ι) ℓ} {T : Finset (ι)}
    (hP : P.SupportedOn T) (y x : ι → F) {k : ℕ} (hk : k ≤ ℓ) :
    CL.proj (prefixRegister P k y) (decodeDual P y x) =
      ∑ j ∈ range k, stageDual P j y x := by
  induction k with
  | zero => simp [prefixRegister]
  | succ k ih =>
    have hd : Disjoint (prefixRegister P k y) (P.factorOfPrefix k y) :=
      disjoint_of_subset_right (stageFactor_subset_residual hP k y) disjoint_sdiff
    rw [prefixRegister_step, CL.proj_union_of_disjoint hd,
      ih (by omega), proj_decodeDual hP y x (by omega), sum_range_succ]

theorem outputPrefix_congr_le {P : CL.CLFun F (ι) ℓ} {T : Finset (ι)}
    (hP : P.SupportedOn T) {j k : ℕ} (hjk : j ≤ k) {y z : ι → F}
    (h : P.outputPrefix k y = P.outputPrefix k z) :
    P.outputPrefix j y = P.outputPrefix j z := by
  rw [← outputPrefix_outputPrefix hP y hjk, ← outputPrefix_outputPrefix hP z hjk, h]

/-- Equal raw dual prefixes remain equal after decoding, even when the untested
tails of the two claimed questions differ. -/
theorem proj_prefix_decodeDual_congr {P : CL.CLFun F (ι) ℓ} {T : Finset (ι)}
    (hP : P.SupportedOn T) {k : ℕ} (hk : k + 1 ≤ ℓ)
    {y z a b : ι → F} (hyz : P.outputPrefix k y = P.outputPrefix k z)
    (hab : CL.proj (prefixRegister P (k + 1) z) a =
      CL.proj (prefixRegister P (k + 1) z) b) :
    CL.proj (prefixRegister P (k + 1) z) (decodeDual P y a) =
      CL.proj (prefixRegister P (k + 1) z) (decodeDual P z b) := by
  have hr := prefixRegister_congr hP k hyz
  rw [← hr, proj_prefix_decodeDual hP y a hk, hr, proj_prefix_decodeDual hP z b hk]
  apply sum_congr rfl
  intro j hj
  have hjk : j ≤ k := by simpa only [mem_range, Nat.lt_succ_iff] using hj
  rw [stageDual_prefix_congr hP j (outputPrefix_congr_le hP hjk hyz)]
  have hs : P.factorOfPrefix j z ⊆ prefixRegister P (k + 1) z :=
    (factorOfPrefix_subset_prefixRegister P j z).trans
      (prefixRegister_mono P z (by omega))
  change registerDual (stageLinear P j z) a = registerDual (stageLinear P j z) b
  rw [← registerDual_proj_input (stageLinear P j z) hs a,
    ← registerDual_proj_input (stageLinear P j z) hs b, hab]

/-- The prefix preceding the last stage determines the entire dual decoder. -/
theorem decodeDual_prefix_congr {P : CL.CLFun F (ι) ℓ} {T : Finset (ι)}
    (hP : P.SupportedOn T) {y z : ι → F}
    (h : P.outputPrefix (ℓ - 1) y = P.outputPrefix (ℓ - 1) z) :
    decodeDual P y = decodeDual P z := by
  unfold decodeDual
  apply sum_congr rfl
  intro j hj
  apply stageDual_prefix_congr hP j
  exact outputPrefix_congr_le hP (by have := mem_range.mp hj; omega) h

end MIPRE.Introspection.AuxiliaryDual
end
