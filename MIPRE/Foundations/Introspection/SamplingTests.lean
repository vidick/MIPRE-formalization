/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.SamplingPrefix
import MIPRE.Foundations.Commutation

/-! # The two sampling-test estimates

The selection probability is retained explicitly. The question map need not
be injective: many sampler seeds may give the same question pair. Prefix
coarse-graining is done on the acceptance predicate, before passing to squared
distance, so no answer-fibre cardinality enters the error.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical

variable {X Y A B C J H K : Type*}
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype A] [Fintype B] [Fintype C] [DecidableEq C]
  [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

/-- A tested equality of processed answers gives averaged cross-party closeness, including
all output values of the processing maps. -/
theorem agreement_subtest_average (G : Game X Y A B) (ψ : H × K → ℂ)
    (hψ : star ψ ⬝ᵥ ψ = 1) (MA : X → POVM A H) (MB : Y → POVM B K)
    {ε : ℝ} (hfail : 1 - povmValue G ψ MA MB ≤ ε)
    (D : J → ℝ) (hD : ∀ j, 0 ≤ D j) (q : J → X × Y)
    {c : ℝ} (hc : 0 < c)
    (hpush : ∀ p : X × Y, c * ∑ j ∈ univ.filter (fun j => q j = p), D j ≤ G.μ p.1 p.2)
    (f : J → A → C) (g : J → B → C)
    (hcheck : ∀ j a b, G.D (q j).1 (q j).2 a b = true → f j a = g j b) :
    (∑ j, D j * ∑ z, xSqNorm ψ
      ((((MA (q j).1).map (f j)).mats z).val)
      ((((MB (q j).2).map (g j)).mats z).val)) ≤ 2 * (ε / c) := by
  have hcond := sum_condFail_le_of_pushforward hψ hfail D q hc hpush
  have hpoint j := xSqNorm_sum_le_condFail (G := G) (ψ := ψ) (MA := MA) (MB := MB)
    hψ (f j) (g j) (hcheck j)
  calc
    _ ≤ ∑ j, D j * (2 * condFail G ψ MA MB (q j).1 (q j).2) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hpoint j) (hD j)
    _ = 2 * ∑ j, D j * condFail G ψ MA MB (q j).1 (q j).2 := by
      simp only [mul_left_comm (b := (2 : ℝ)), ← Finset.mul_sum]
    _ ≤ 2 * (ε / c) := mul_le_mul_of_nonneg_left hcond (by norm_num)

/-- The Pauli sampling test remains sound after replacing the tested Pauli measurement
by its ideal one. The explicit loss is `2 η + 4 ε / c`. -/
theorem sampling_pauli_estimate (G : Game X Y A B) (ψ : H × K → ℂ)
    (hψ : star ψ ⬝ᵥ ψ = 1) (MA : X → POVM A H) (MB : Y → POVM B K)
    {ε : ℝ} (hfail : 1 - povmValue G ψ MA MB ≤ ε)
    (D : J → ℝ) (hD : ∀ j, 0 ≤ D j) (q : J → X × Y)
    {c : ℝ} (hc : 0 < c)
    (hpush : ∀ p : X × Y, c * ∑ j ∈ univ.filter (fun j => q j = p), D j ≤ G.μ p.1 p.2)
    (f : J → A → C) (g : J → B → C)
    (hcheck : ∀ j a b, G.D (q j).1 (q j).2 a b = true → f j a = g j b)
    (P : J → C → Matrix H H ℂ) {η : ℝ}
    (hP : ∑ j, D j * ∑ z, stateSqNorm ψ
      (P j z - (((MA (q j).1).map (f j)).mats z).val) ≤ η) :
    (∑ j, D j * ∑ z, xSqNorm ψ (P j z)
      ((((MB (q j).2).map (g j)).mats z).val)) ≤ 2 * η + 4 * (ε / c) := by
  have htest := agreement_subtest_average G ψ hψ MA MB hfail D hD q hc hpush f g hcheck
  have hpoint j := sum_xSqNorm_le_of_two_step (ψ := ψ) (P j)
    (fun z => (((MA (q j).1).map (f j)).mats z).val)
    (fun z => (((MB (q j).2).map (g j)).mats z).val) le_rfl le_rfl
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
    (ψ : H × K → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1)
    (MA : X → POVM ((ι → F) × O) H) (MB : Y → POVM ((ι → F) × O) K)
    {ε : ℝ} (hfail : 1 - povmValue G ψ MA MB ≤ ε)
    (D : J → ℝ) (hD : ∀ j, 0 ≤ D j) (q : J → X × Y)
    {c : ℝ} (hc : 0 < c)
    (hpush : ∀ p : X × Y, c * ∑ j ∈ univ.filter (fun j => q j = p), D j ≤ G.μ p.1 p.2)
    (P : J → CL.CLFun F ι ℓ) (hP : ∀ j, (P j).SupportedOn univ)
    (hcheck : ∀ j a b, G.D (q j).1 (q j).2 a b = true → a = ((P j).eval b.1, b.2))
    (k : ℕ) :
    (∑ j, D j * ∑ z : (ι → F) × O, xSqNorm ψ
      ((((MA (q j).1).map (fun a => ((P j).outputPrefix k a.1, a.2))).mats z).val)
      ((((MB (q j).2).map (fun b => (((P j).truncate k).eval b.1, b.2))).mats z).val)) ≤
        2 * (ε / c) := by
  apply agreement_subtest_average G ψ hψ MA MB hfail D hD q hc hpush
  intro j a b hab
  rw [hcheck j a b hab]
  exact Prod.ext ((hP j).outputPrefix_eval k b.1) rfl

end Prefix

/-- A coarse-grained outcome outside the image has exactly the zero operator. -/
theorem mapped_operator_zero_of_not_range (N : POVM B K) (g : B → C) {z : C}
    (hz : z ∉ Set.range g) : ((N.map g).mats z).val = 0 := by
  rw [POVM.map_mats]
  have hf : univ.filter (fun b => g b = z) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro b hb
    exact hz ⟨b, (Finset.mem_filter.mp hb).2⟩
  rw [hf, Finset.sum_empty]

/-- The consistency estimate controls the total squared weight of all impossible answers.
No restriction to the honest image is made in a later use of the sampling estimate. -/
theorem off_range_weight_le (ψ : H × K → ℂ) (M : POVM C H) (N : POVM B K) (g : B → C) :
    (∑ z ∈ univ.filter (fun z => z ∉ Set.range g), stateSqNorm ψ (M.mats z).val) ≤
      ∑ z, xSqNorm ψ (M.mats z).val ((N.map g).mats z).val := by
  calc
    _ = ∑ z ∈ univ.filter (fun z => z ∉ Set.range g),
        xSqNorm ψ (M.mats z).val ((N.map g).mats z).val := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [mapped_operator_zero_of_not_range N g (Finset.mem_filter.mp hz).2]
      simp only [xSqNorm, stateVecB, Matrix.kronecker_zero, Matrix.zero_mulVec,
        WithLp.toLp_zero, sub_zero, stateSqNorm, stateNorm]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun z _ _ => xSqNorm_nonneg _ _ _)

end MIPRE.Introspection

end
