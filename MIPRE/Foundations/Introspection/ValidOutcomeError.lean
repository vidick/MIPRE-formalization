/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.SubmeasurementCompletion
public import MIPRE.Foundations.Introspection.IsometricCompletionError

@[expose] public section

/-! # Recovering all outcomes from valid-outcome extraction estimates

Pauli extraction sums only the valid full-register answers. The actual
introspection induction also retains every malformed answer. Positivity
and the submeasurement mass estimate extend the former guarantee to the
whole mapped alphabet, without an answer-cardinality factor or a premise
that malformed effects vanish.

Stated for a state model, with positivity on the represented operators, and for a local isometry
of bipartite models (Phase 4 of `planning/mipco-track.md`).
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Classical
set_option linter.unusedSectionVars false

section State

variable {𝒞 : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] (Ψ : StateModel 𝒞)
  {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- Extending a positive submeasurement inside another submeasurement
costs at most the missing mass. Normalization of the extension is not needed. -/
theorem submeasurement_extension_mass (hΨ : ‖Ψ.ψ‖ = 1)
    (M C : A → 𝒞) (hM : ∀ a, 0 ≤ Ψ.π (M a)) (hC : ∀ a, 0 ≤ Ψ.π (C a))
    (hCsum : ∑ a, Ψ.π (C a) ≤ 1) (hMC : ∀ a, Ψ.π (M a) ≤ Ψ.π (C a)) :
    (∑ a, Ψ.snorm (M a - C a) ^ 2) ≤ 1 - ∑ a, Ψ.qform (M a) := by
  have hdiff a : 0 ≤ Ψ.π (C a - M a) := by rw [map_sub]; exact sub_nonneg.mpr (hMC a)
  have hdiff1 a : Ψ.π (C a - M a) ≤ 1 := by
    rw [map_sub]
    exact (sub_le_self _ (hM a)).trans
      ((single_le_sum (fun b _ => hC b) (mem_univ a)).trans hCsum)
  have hterm a : Ψ.snorm (M a - C a) ^ 2 ≤ Ψ.qform (C a - M a) := by
    rw [Ψ.snorm_sub_comm]
    exact Ψ.snorm_sq_le_qform (hdiff a) (hdiff1 a)
  have hs := sum_le_sum fun a (_ : a ∈ univ) => hterm a
  simp_rw [Ψ.qform_sub] at hs
  rw [sum_sub_distrib] at hs
  have hc : ∑ a, Ψ.qform (C a) ≤ 1 := by
    calc ∑ a, Ψ.qform (C a) = Op.qform Ψ.ψ (∑ a, Ψ.π (C a)) := by rw [Op.qform_sum]; rfl
      _ ≤ Op.qform Ψ.ψ 1 := Op.qform_mono _ hCsum
      _ = 1 := Op.qform_one _ hΨ
  linarith

/-- A nearby positive submeasurement may be extended arbitrarily inside
the identity with the same dimension-independent completion bound. -/
theorem submeasurement_extension_dist (hΨ : ‖Ψ.ψ‖ = 1)
    (P M C : A → 𝒞) (hP : IsPVMIn P)
    (hM : ∀ a, 0 ≤ Ψ.π (M a)) (hC : ∀ a, 0 ≤ Ψ.π (C a))
    (hCsum : ∑ a, Ψ.π (C a) ≤ 1) (hMC : ∀ a, Ψ.π (M a) ≤ Ψ.π (C a))
    {δ : ℝ} (hclose : ∑ a, Ψ.snorm (P a - M a) ^ 2 ≤ δ) :
    (∑ a, Ψ.snorm (P a - C a) ^ 2) ≤ 2 * δ + 4 * Real.sqrt δ := by
  have hMsum : ∑ a, Ψ.π (M a) ≤ 1 := (sum_le_sum fun a _ => hMC a).trans hCsum
  have hmass := Ψ.qform_sum_ge_of_close hΨ hP hM hMsum hclose
  have hfill := submeasurement_extension_mass Ψ hΨ M C hM hC hCsum hMC
  have htri := Ψ.sum_snorm_sq_triangle univ P M C
  linarith

/-- Closeness on one correctly labelled raw answer for each valid outcome
controls the complete coarse measurement, including all malformed answers.
The ideal measurement has zero effect at the explicit malformed outcome. -/
theorem valid_outcome_error_le (hΨ : ‖Ψ.ψ‖ = 1)
    (M : B → 𝒞) (hM : ∀ b, 0 ≤ Ψ.π (M b)) (hMsum : ∑ b, Ψ.π (M b) ≤ 1)
    (f : B → Option A) (v : A → B) (hv : ∀ a, f (v a) = some a)
    (P : Option A → 𝒞) (hP : IsPVMIn P) (hPnone : P none = 0)
    {δ : ℝ} (hclose : ∑ a, Ψ.snorm (M (v a) - P (some a)) ^ 2 ≤ δ) :
    (∑ a, Ψ.snorm (fibSumIn M f a - P a) ^ 2) ≤ 2 * δ + 4 * Real.sqrt δ := by
  let Q : Option A → 𝒞 := fun a => a.elim 0 (fun a => M (v a))
  have hQ a : 0 ≤ Ψ.π (Q a) := by
    cases a <;> simp only [Q, Option.elim_none, Option.elim_some, map_zero]
    exacts [le_refl _, hM _]
  have hCpi a : Ψ.π (fibSumIn M f a) = ∑ b ∈ univ.filter (fun b => f b = a), Ψ.π (M b) := by
    rw [fibSumIn, map_sum]
  have hC a : 0 ≤ Ψ.π (fibSumIn M f a) := by
    rw [hCpi]
    exact sum_nonneg fun b _ => hM b
  have hCsum : ∑ a, Ψ.π (fibSumIn M f a) ≤ 1 := by
    have he : (∑ a, Ψ.π (fibSumIn M f a)) = ∑ b, Ψ.π (M b) := by
      simp only [hCpi, sum_filter]
      rw [sum_comm]
      simp
    rw [he]
    exact hMsum
  have hQC a : Ψ.π (Q a) ≤ Ψ.π (fibSumIn M f a) := by
    cases a with
    | none => simpa only [Q, Option.elim_none, map_zero] using hC none
    | some a =>
      rw [hCpi]
      exact single_le_sum (fun b _ => hM b) (by simp [hv a])
  have hc : ∑ a, Ψ.snorm (P a - Q a) ^ 2 ≤ δ := by
    simpa only [Fintype.sum_option, Q, Option.elim_none, Option.elim_some,
      hPnone, sub_self, Ψ.snorm_zero, zero_pow (by decide : 2 ≠ 0), zero_add,
      Ψ.snorm_sub_comm] using hclose
  have h := submeasurement_extension_dist Ψ hΨ P Q (fibSumIn M f) hP hQ hC hCsum hQC hc
  simpa only [Ψ.snorm_sub_comm] using h

end State

section Isometric

variable {𝒞 𝒜 ℬ 𝒞' 𝒜' ℬ' : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [Ring 𝒞'] [StarRing 𝒞'] [Algebra ℂ 𝒞']
  [Ring 𝒜'] [StarRing 𝒜'] [Algebra ℂ 𝒜'] [Ring ℬ'] [StarRing ℬ'] [Algebra ℂ ℬ']
  [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder 𝒜'] [StarOrderedRing 𝒜']
  {M : BipartiteModel 𝒞 𝒜 ℬ} {M' : BipartiteModel 𝒞' 𝒜' ℬ'}
  (Φ : BipartiteModel.LocalIsometry M M')
  {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The image of the unit is represented below the identity. -/
theorem π_πA_ΦA_one_le : M'.π (M'.πA (Φ.ΦA 1)) ≤ 1 := by
  have h : (0 : 𝒜') ≤ 1 - Φ.ΦA 1 := by
    have he : 1 - Φ.ΦA 1 = star (1 - Φ.ΦA 1) * (1 - Φ.ΦA 1) := by
      rw [Φ.star_compl_ΦA_one, Φ.compl_ΦA_one_mul_self]
    rw [he]
    exact star_mul_self_nonneg _
  have h' := M'.π_πA_nonneg h
  rwa [map_sub, map_sub, map_one, map_one, sub_nonneg] at h'

/-- Valid raw-answer estimates for an isometric image imply the complete
mapped estimate on Alice, including the explicit malformed outcome. -/
theorem isometric_valid_outcome_alice_error_le (hM' : ‖M'.ψ‖ = 1) (N : POVMIn B 𝒜)
    (f : B → Option A) (v : A → B) (hv : ∀ a, f (v a) = some a)
    (P : Option A → 𝒜') (hP : IsPVMIn P) (hPnone : P none = 0)
    {δ : ℝ} (hclose : ∑ a, M'.snorm (M'.πA (Φ.ΦA (N.op (v a)) - P (some a))) ^ 2 ≤ δ) :
    (∑ a, M'.snorm (M'.πA (Φ.ΦA ((N.map f).op a) - P a)) ^ 2) ≤ 2 * δ + 4 * Real.sqrt δ := by
  have hm b : 0 ≤ M'.π (M'.πA (Φ.ΦA (N.op b))) := M'.π_πA_nonneg (map_nonneg Φ.ΦA (N.op_nonneg b))
  have hs : ∑ b, M'.π (M'.πA (Φ.ΦA (N.op b))) ≤ 1 := by
    rw [← map_sum, ← map_sum, ← map_sum, N.sum_op]
    exact π_πA_ΦA_one_le Φ
  have h := valid_outcome_error_le M'.toStateModel hM' _ hm hs f v hv (fun a => M'.πA (P a))
    (hP.map M'.πA) (by rw [hPnone, map_zero]) (by simpa only [map_sub] using hclose)
  have he a : fibSumIn (fun b => M'.πA (Φ.ΦA (N.op b))) f a = M'.πA (Φ.ΦA ((N.map f).op a)) := by
    rw [POVMIn.map_op, map_sum, map_sum]
    rfl
  simpa only [he, ← map_sub] using h

/-- The corresponding full-outcome estimate on Bob. -/
theorem isometric_valid_outcome_bob_error_le [PartialOrder ℬ] [StarOrderedRing ℬ]
    [PartialOrder ℬ'] [StarOrderedRing ℬ'] (hM' : ‖M'.ψ‖ = 1) (N : POVMIn B ℬ)
    (f : B → Option A) (v : A → B) (hv : ∀ a, f (v a) = some a)
    (P : Option A → ℬ') (hP : IsPVMIn P) (hPnone : P none = 0)
    {δ : ℝ} (hclose : ∑ a, M'.snorm (M'.πB (Φ.ΦB (N.op (v a)) - P (some a))) ^ 2 ≤ δ) :
    (∑ a, M'.snorm (M'.πB (Φ.ΦB ((N.map f).op a) - P a)) ^ 2) ≤ 2 * δ + 4 * Real.sqrt δ :=
  isometric_valid_outcome_alice_error_le Φ.swap hM' N f v hv P hP hPnone hclose

end Isometric
end MIPRE.Introspection
end

end
