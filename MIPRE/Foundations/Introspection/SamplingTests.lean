/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.SamplingPrefix
public import MIPRE.Foundations.Commutation

@[expose] public section

/-! # Sampling tests after answer coarse-graining

The selection probability is retained explicitly. The question map need not
be injective: many sampler seeds may give the same question pair. Prefix
coarse-graining is done on the acceptance predicate, before passing to squared
distance, so no answer-fibre cardinality enters the error.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`).
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Classical

set_option linter.unusedSectionVars false

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] (Ψ : BipartiteModel 𝒞 𝒜 ℬ)
variable {X Y A B C J : Type*}
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype A] [Fintype B] [Fintype C] [DecidableEq C] [Fintype J] [DecidableEq J]

/-- A tested equality of processed answers gives averaged cross-party closeness, including
all output values of the processing maps. -/
theorem agreement_subtest_average (G : Game X Y A B) (hΨ : ‖Ψ.ψ‖ = 1)
    (MA : X → POVMIn A 𝒜) (MB : Y → POVMIn B ℬ)
    {ε : ℝ} (hfail : 1 - Ψ.povmValue G MA MB ≤ ε)
    (D : J → ℝ) (hD : ∀ j, 0 ≤ D j) (q : J → X × Y)
    {c : ℝ} (hc : 0 < c)
    (hpush : ∀ p : X × Y, c * ∑ j ∈ univ.filter (fun j => q j = p), D j ≤ G.μ p.1 p.2)
    (f : J → A → C) (g : J → B → C)
    (hcheck : ∀ j a b, G.D (q j).1 (q j).2 a b = true → f j a = g j b) :
    (∑ j, D j * ∑ z, Ψ.xSqNorm (((MA (q j).1).map (f j)).op z)
      (((MB (q j).2).map (g j)).op z)) ≤ 2 * (ε / c) := by
  have hcond := Ψ.sum_condFail_le_of_pushforward hΨ hfail D q hc hpush
  have hpoint j := Ψ.xSqNorm_sum_le_condFail (G := G) (MA := MA) (MB := MB)
    hΨ (f j) (g j) (hcheck j)
  calc
    _ ≤ ∑ j, D j * (2 * Ψ.condFail G MA MB (q j).1 (q j).2) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hpoint j) (hD j)
    _ = 2 * ∑ j, D j * Ψ.condFail G MA MB (q j).1 (q j).2 := by
      simp only [mul_left_comm (b := (2 : ℝ)), ← Finset.mul_sum]
    _ ≤ 2 * (ε / c) := mul_le_mul_of_nonneg_left hcond (by norm_num)

/-- The Pauli sampling test remains sound after replacing the tested Pauli measurement
by its ideal one. The explicit loss is `2 η + 4 ε / c`. -/
theorem sampling_pauli_estimate (G : Game X Y A B) (hΨ : ‖Ψ.ψ‖ = 1)
    (MA : X → POVMIn A 𝒜) (MB : Y → POVMIn B ℬ)
    {ε : ℝ} (hfail : 1 - Ψ.povmValue G MA MB ≤ ε)
    (D : J → ℝ) (hD : ∀ j, 0 ≤ D j) (q : J → X × Y)
    {c : ℝ} (hc : 0 < c)
    (hpush : ∀ p : X × Y, c * ∑ j ∈ univ.filter (fun j => q j = p), D j ≤ G.μ p.1 p.2)
    (f : J → A → C) (g : J → B → C)
    (hcheck : ∀ j a b, G.D (q j).1 (q j).2 a b = true → f j a = g j b)
    (P : J → C → 𝒜) {η : ℝ}
    (hP : ∑ j, D j * ∑ z, Ψ.stateSqNorm (P j z - ((MA (q j).1).map (f j)).op z) ≤ η) :
    (∑ j, D j * ∑ z, Ψ.xSqNorm (P j z) (((MB (q j).2).map (g j)).op z)) ≤
      2 * η + 4 * (ε / c) := by
  have htest := agreement_subtest_average Ψ G hΨ MA MB hfail D hD q hc hpush f g hcheck
  have hpoint j := Ψ.sum_xSqNorm_le_of_two_step (P j)
    (fun z => ((MA (q j).1).map (f j)).op z)
    (fun z => ((MB (q j).2).map (g j)).op z) le_rfl le_rfl
  have hsum := Finset.sum_le_sum fun j (_ : j ∈ univ) =>
    mul_le_mul_of_nonneg_left (hpoint j) (hD j)
  simp only [mul_add, Finset.sum_add_distrib,
    mul_left_comm (b := (2 : ℝ)), ← Finset.mul_sum] at hsum
  linarith

section Prefix

variable {F ι O : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype O] [DecidableEq O] {ℓ : ℕ}

/-- The introspection sampling test, at every CL prefix. The output sum is over the entire
ambient answer alphabet, including vectors outside the marginal CL image. -/
theorem sampling_prefix_estimate (G : Game X Y ((ι → F) × O) ((ι → F) × O))
    (hΨ : ‖Ψ.ψ‖ = 1)
    (MA : X → POVMIn ((ι → F) × O) 𝒜) (MB : Y → POVMIn ((ι → F) × O) ℬ)
    {ε : ℝ} (hfail : 1 - Ψ.povmValue G MA MB ≤ ε)
    (D : J → ℝ) (hD : ∀ j, 0 ≤ D j) (q : J → X × Y)
    {c : ℝ} (hc : 0 < c)
    (hpush : ∀ p : X × Y, c * ∑ j ∈ univ.filter (fun j => q j = p), D j ≤ G.μ p.1 p.2)
    (P : J → CL.CLFun F ι ℓ) (hP : ∀ j, (P j).SupportedOn univ)
    (hcheck : ∀ j a b, G.D (q j).1 (q j).2 a b = true → a = ((P j).eval b.1, b.2))
    (k : ℕ) :
    (∑ j, D j * ∑ z : (ι → F) × O, Ψ.xSqNorm
      (((MA (q j).1).map (fun a => ((P j).outputPrefix k a.1, a.2))).op z)
      (((MB (q j).2).map (fun b => (((P j).truncate k).eval b.1, b.2))).op z)) ≤
        2 * (ε / c) := by
  apply agreement_subtest_average Ψ G hΨ MA MB hfail D hD q hc hpush
  intro j a b hab
  rw [hcheck j a b hab]
  exact Prod.ext ((hP j).outputPrefix_eval k b.1) rfl

end Prefix

/-- A coarse-grained outcome outside the image has exactly the zero operator. -/
theorem mapped_operator_zero_of_not_range (N : POVMIn B ℬ) (g : B → C) {z : C}
    (hz : z ∉ Set.range g) : (N.map g).op z = 0 := by
  rw [POVMIn.map_op]
  have hf : univ.filter (fun b => g b = z) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro b hb
    exact hz ⟨b, (Finset.mem_filter.mp hb).2⟩
  rw [hf, Finset.sum_empty]

/-- The consistency estimate controls the total squared weight of all impossible answers.
No restriction to the honest image is made in a later use of the sampling estimate. -/
theorem off_range_weight_le (M : POVMIn C 𝒜) (N : POVMIn B ℬ) (g : B → C) :
    (∑ z ∈ univ.filter (fun z => z ∉ Set.range g), Ψ.stateSqNorm (M.op z)) ≤
      ∑ z, Ψ.xSqNorm (M.op z) ((N.map g).op z) := by
  calc
    _ = ∑ z ∈ univ.filter (fun z => z ∉ Set.range g), Ψ.xSqNorm (M.op z) ((N.map g).op z) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [mapped_operator_zero_of_not_range N g (Finset.mem_filter.mp hz).2]
      simp only [BipartiteModel.xSqNorm, BipartiteModel.xNorm, map_zero, sub_zero,
        BipartiteModel.stateSqNorm, BipartiteModel.stateNorm]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun z _ _ => Ψ.xSqNorm_nonneg _ _)

end MIPRE.Introspection

end

end
