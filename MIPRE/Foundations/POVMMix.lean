/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.Pasting

@[expose] public section

/-!
# Mixtures and extensions of POVMs, and the agreement triangle

Three constructions on bundled POVMs that the padded strategy of the Pauli basis test's stage 4
needs, and one inequality.

* `POVM.aOp` extends a POVM on `d` by the identity to `d × E`; `POVM.dirac a₀` answers `a₀` with
  certainty; `POVM.mix w Q` is a convex combination of POVMs with the same outcomes. A strategy
  that must be a *function of the question* while the analysis controls it *sample by sample* is
  a mixture over the samples producing the question, and the Born rule's linearity
  (`bornProb_mix_left`, `bornProb_mix_right`) turns a bound on the mixture into the average of the
  per-sample bounds.
* `agreeSum_triangle` is the paper's triangle-like inequality for the consistency relation
  (`fact:triangle-for-simeq`, item 1): if Alice's `A` agrees with Bob's `B`, Alice's `C` agrees
  with Bob's `B`, and Alice's `C` agrees with Bob's `D`, each with probability at least `1 - δ`,
  then Alice's `A` agrees with Bob's `D` with probability at least `1 - 11 δ`. No projectivity is
  assumed: for POVMs the agreement is not a squared distance, and the argument goes through the
  vectors `(R_a ⊗ I)|ψ⟩`, whose weighted squared norms are at most one and, by Cauchy--Schwarz
  against a partner they agree with, at least `1 - 2δ`. The paper pads these vectors to unit
  vectors and gets `9 δ`; the unpadded argument here costs the extra `2 δ` and needs no auxiliary
  space.

The Born-rule facts, the failure bounds and the agreement triangle are proved once, for a
bipartite model (`BipartiteModel.bornProb_mix_left`, `BipartiteModel.agreeSum_triangle`, ...), with
`POVMIn.dirac` and `POVMIn.mix` the constructions in a player's algebra; the matrix statements are
their instances in the tensor-product model.
-/

noncomputable section

namespace MIPRE

open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder

/-! ## Mixtures in a `⋆`-algebra -/

namespace POVMIn

variable {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]

section Dirac

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The deterministic POVM answering `a₀`. -/
def dirac (a₀ : A) : POVMIn A R where
  mats a := if a = a₀ then 1 else 0
  nonneg a := by
    split_ifs
    · refine Subtype.coe_le_coe.mp ?_
      show (0 : R) ≤ 1
      simp
    · exact le_rfl
  normalized := by simp

theorem dirac_op (a₀ a : A) : (dirac (R := R) a₀).op a = if a = a₀ then 1 else 0 := by
  show ((if a = a₀ then 1 else 0 : selfAdjoint R) : R) = _
  split_ifs <;> rfl

end Dirac

variable [Algebra ℂ R] [StarModule ℂ R]

/-- A real multiple of a nonnegative element, with a nonnegative real, is nonnegative:
`r • x = √r x √r`. -/
theorem real_smul_nonneg {r : ℝ} (hr : 0 ≤ r) {x : R} (hx : 0 ≤ x) : 0 ≤ (r : ℂ) • x := by
  have h : (r : ℂ) • x
      = star ((Real.sqrt r : ℂ) • (1 : R)) * x * ((Real.sqrt r : ℂ) • (1 : R)) := by
    rw [star_smul, star_one, Complex.star_def, Complex.conj_ofReal, smul_mul_assoc, one_mul,
      mul_smul_comm, mul_one, smul_smul, ← Complex.ofReal_mul, Real.mul_self_sqrt hr]
  rw [h]
  exact star_left_conjugate_nonneg hx _

section Mix

variable {A : Type*} [Fintype A] {ι : Type*} [Fintype ι]

/-- **A convex combination of POVMs** with the same outcomes, with real weights `w` summing to
one. -/
def mix (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (Q : ι → POVMIn A R) :
    POVMIn A R where
  mats a := ⟨∑ i, (w i : ℂ) • (Q i).op a, by
    rw [selfAdjoint.mem_iff, star_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [star_smul, Complex.star_def, Complex.conj_ofReal, (Q i).star_op]⟩
  nonneg a := Subtype.coe_le_coe.mp
    (Finset.sum_nonneg fun i _ => real_smul_nonneg (hw i) ((Q i).op_nonneg a))
  normalized := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    show ∑ a, ∑ i, (w i : ℂ) • (Q i).op a = 1
    rw [Finset.sum_comm]
    simp_rw [← Finset.smul_sum, POVMIn.sum_op]
    rw [← Finset.sum_smul, ← Complex.ofReal_sum, hw1, Complex.ofReal_one, one_smul]

theorem mix_op (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (Q : ι → POVMIn A R)
    (a : A) : (mix w hw hw1 Q).op a = ∑ i, (w i : ℂ) • (Q i).op a := rfl

end Mix

end POVMIn

/-! ## Mixtures and relabellings in a bipartite model -/

namespace BipartiteModel

open scoped InnerProductSpace

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] (M : BipartiteModel 𝒞 𝒜 ℬ)

/-- The Born probability is linear in a real multiple of the first player's operator. -/
theorem bornProb_smul_left (r : ℝ) (a : 𝒜) (b : ℬ) :
    M.bornProb ((r : ℂ) • a) b = r * M.bornProb a b := by
  unfold bornProb
  rw [map_smul, smul_mul_assoc, M.qform_smul_real]

/-- The Born probability is linear in a real multiple of the second player's operator. -/
theorem bornProb_smul_right (r : ℝ) (a : 𝒜) (b : ℬ) :
    M.bornProb a ((r : ℂ) • b) = r * M.bornProb a b := by
  unfold bornProb
  rw [map_smul, mul_smul_comm, M.qform_smul_real]

theorem bornProb_zero_left (b : ℬ) : M.bornProb 0 b = 0 := by
  unfold bornProb
  rw [map_zero, zero_mul, M.qform_zero]

theorem bornProb_zero_right (a : 𝒜) : M.bornProb a 0 = 0 := by
  unfold bornProb
  rw [map_zero, mul_zero, M.qform_zero]

theorem bornProb_one_one (hψ : ‖M.ψ‖ = 1) : M.bornProb 1 1 = 1 := by
  unfold bornProb
  rw [map_one, map_one, mul_one, M.qform_one hψ]

section Order

variable [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ]

section Mix

variable [StarModule ℂ 𝒜] [StarModule ℂ ℬ] {A : Type*} [Fintype A] {ι : Type*} [Fintype ι]

omit [PartialOrder ℬ] [StarOrderedRing ℬ] [StarModule ℂ ℬ] in
/-- **The Born probability of a mixture is the mixture of the Born probabilities**, on the first
player's side. -/
theorem bornProb_mix_left (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (Q : ι → POVMIn A 𝒜) (a : A) (b : ℬ) :
    M.bornProb ((POVMIn.mix w hw hw1 Q).op a) b = ∑ i, w i * M.bornProb ((Q i).op a) b := by
  rw [POVMIn.mix_op, M.bornProb_sum_left]
  exact Finset.sum_congr rfl fun i _ => M.bornProb_smul_left (w i) _ _

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarModule ℂ 𝒜] in
/-- The same, on the second player's side. -/
theorem bornProb_mix_right (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (a : 𝒜)
    (Q : ι → POVMIn A ℬ) (b : A) :
    M.bornProb a ((POVMIn.mix w hw hw1 Q).op b) = ∑ i, w i * M.bornProb a ((Q i).op b) := by
  rw [POVMIn.mix_op, M.bornProb_sum_right]
  exact Finset.sum_congr rfl fun i _ => M.bornProb_smul_right (w i) _ _

end Mix

variable {X Y A B C : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq C] {G : Game X Y A B} {MA : X → POVMIn A 𝒜} {MB : Y → POVMIn B ℬ} {x : X} {y : Y}

/-- **Agreement on the support implies acceptance bounds the conditional failure by the
disagreement of the relabelled POVMs.** Only outcomes both parties can produce are asked to be
accepted. -/
theorem condFail_le_one_sub_sum_bornProb_map (f : A → C) (g : B → C)
    (hD : ∀ a b, (MA x).op a ≠ 0 → (MB y).op b ≠ 0 → f a = g b → G.D x y a b = true) :
    M.condFail G MA MB x y
      ≤ 1 - ∑ c, M.bornProb (((MA x).map f).op c) (((MB y).map g).op c) := by
  rw [M.sum_bornProb_map, condFail]
  have hle : ∑ a, ∑ b, (if f a = g b then (1 : ℝ) else 0)
      * M.bornProb ((MA x).op a) ((MB y).op b) ≤ M.condWin G MA MB x y := by
    rw [condWin]
    refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
    by_cases hfg : f a = g b
    · rw [ite_eq_left hfg]
      by_cases hA : (MA x).op a = 0
      · rw [hA, M.bornProb_zero_left, mul_zero, mul_zero]
      by_cases hB : (MB y).op b = 0
      · rw [hB, M.bornProb_zero_right, mul_zero, mul_zero]
      rw [ite_eq_left (hD a b hA hB hfg)]
    · rw [ite_eq_right hfg, zero_mul]
      exact mul_nonneg (by split_ifs <;> norm_num)
        (M.bornProb_nonneg ((MA x).op_nonneg a) ((MB y).op_nonneg b))
  linarith

omit [DecidableEq C] in
/-- The same with both parties' outcomes read as they are: acceptance of every diagonal pair
on the support bounds the conditional failure by the diagonal disagreement. -/
theorem condFail_le_one_sub_sum_bornProb_diag {G : Game X Y A A} {MB : Y → POVMIn A ℬ}
    (hD : ∀ a, (MA x).op a ≠ 0 → (MB y).op a ≠ 0 → G.D x y a a = true) :
    M.condFail G MA MB x y ≤ 1 - ∑ a, M.bornProb ((MA x).op a) ((MB y).op a) := by
  rw [condFail]
  have hle : ∑ a, M.bornProb ((MA x).op a) ((MB y).op a) ≤ M.condWin G MA MB x y := by
    rw [condWin]
    refine Finset.sum_le_sum fun a _ => ?_
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun b => (if G.D x y a b then (1 : ℝ) else 0)
        * M.bornProb ((MA x).op a) ((MB y).op b))
      (fun b _ => mul_nonneg (by split_ifs <;> norm_num)
        (M.bornProb_nonneg ((MA x).op_nonneg a) ((MB y).op_nonneg b))) (Finset.mem_univ a))
    by_cases hA : (MA x).op a = 0
    · rw [hA, M.bornProb_zero_left, mul_zero]
    by_cases hB : (MB y).op a = 0
    · rw [hB, M.bornProb_zero_right, mul_zero]
    rw [ite_eq_left (hD a hA hB), one_mul]
  linarith

end Order

/-! ### The agreement triangle -/

section Triangle

variable [PartialOrder 𝒜] [PartialOrder ℬ] {X Λ : Type*} [Fintype X] [Fintype Λ]

/-- The agreement probability of two families of POVMs, one per party, on the same questions,
averaged over the question distribution `μ`: the paper's `p(R, S)`. -/
def agreeSum (μ : X → ℝ) (MA : X → POVMIn Λ 𝒜) (MB : X → POVMIn Λ ℬ) : ℝ :=
  ∑ x, μ x * ∑ a, M.bornProb ((MA x).op a) ((MB x).op a)

/-- The weighted squared norm of the first player's measurement vectors. -/
def weightA (μ : X → ℝ) (MA : X → POVMIn Λ 𝒜) : ℝ :=
  ∑ x, μ x * ∑ a, M.stateSqNorm ((MA x).op a)

/-- The weighted cross-party deviation of two families. -/
def xDev (μ : X → ℝ) (MA : X → POVMIn Λ 𝒜) (MB : X → POVMIn Λ ℬ) : ℝ :=
  ∑ x, μ x * ∑ a, M.xSqNorm ((MA x).op a) ((MB x).op a)

variable {μ : X → ℝ}

/-- Exchanging the players leaves the agreement unchanged. -/
theorem agreeSum_swap (MA : X → POVMIn Λ 𝒜) (MB : X → POVMIn Λ ℬ) :
    M.swap.agreeSum μ MB MA = M.agreeSum μ MA MB := by
  unfold agreeSum
  exact Finset.sum_congr rfl fun x _ => by
    rw [Finset.sum_congr rfl fun a _ => M.bornProb_swap ((MA x).op a) ((MB x).op a)]

omit [PartialOrder ℬ] in
theorem weightA_nonneg (hμ : ∀ x, 0 ≤ μ x) (MA : X → POVMIn Λ 𝒜) : 0 ≤ M.weightA μ MA :=
  Finset.sum_nonneg fun x _ =>
    mul_nonneg (hμ x) (Finset.sum_nonneg fun _ _ => M.stateSqNorm_nonneg _)

/-- **The cross deviation expands**: `xDev = weightA + weightB - 2 agreeSum`, with the second
player's weight the first player's in the swapped model. -/
theorem xDev_eq (MA : X → POVMIn Λ 𝒜) (MB : X → POVMIn Λ ℬ) :
    M.xDev μ MA MB = M.weightA μ MA + M.swap.weightA μ MB - 2 * M.agreeSum μ MA MB := by
  unfold xDev weightA agreeSum
  have hx : ∀ x, μ x * ∑ a, M.xSqNorm ((MA x).op a) ((MB x).op a)
      = μ x * ∑ a, M.stateSqNorm ((MA x).op a) + μ x * ∑ a, M.swap.stateSqNorm ((MB x).op a)
        - 2 * (μ x * ∑ a, M.bornProb ((MA x).op a) ((MB x).op a)) := by
    intro x
    simp only [M.xSqNorm_eq ((MA x).star_op _), Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum]
    ring
  simp only [hx, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

omit [PartialOrder 𝒜] [PartialOrder ℬ] in
/-- **A Born probability is at most the product of the two state norms** (Cauchy--Schwarz). -/
theorem bornProb_le_stateNorm_mul {a : 𝒜} (ha : star a = a) (b : ℬ) :
    M.bornProb a b ≤ M.stateNorm a * M.swap.stateNorm b := by
  have h : M.bornProb a b = (⟪M.π (M.πA a) M.ψ, M.π (M.πB b) M.ψ⟫_ℂ).re := by
    rw [M.inner_πA_πB ha b]
    rfl
  rw [h]
  exact le_trans (Complex.re_le_norm _) (norm_inner_le_norm _ _)

/-- **Cauchy--Schwarz for the agreement**: `agreeSum ≤ √weightA · √weightB`. -/
theorem agreeSum_le_sqrt_mul_sqrt (hμ : ∀ x, 0 ≤ μ x) (MA : X → POVMIn Λ 𝒜)
    (MB : X → POVMIn Λ ℬ) :
    M.agreeSum μ MA MB ≤ Real.sqrt (M.weightA μ MA) * Real.sqrt (M.swap.weightA μ MB) := by
  have h1 : M.agreeSum μ MA MB ≤ ∑ p : X × Λ, μ p.1
      * (M.stateNorm ((MA p.1).op p.2) * M.swap.stateNorm ((MB p.1).op p.2)) := by
    rw [agreeSum, Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun x _ => ?_
    dsimp only
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ =>
      M.bornProb_le_stateNorm_mul ((MA x).star_op a) _) (hμ x)
  refine le_trans h1 (le_of_le_of_eq (sum_weighted_mul_le_sqrt (fun p : X × Λ => μ p.1)
    (fun p => M.stateNorm ((MA p.1).op p.2))
    (fun p => M.swap.stateNorm ((MB p.1).op p.2)) fun p => hμ p.1) ?_)
  congr 1 <;> congr 1
  · rw [weightA, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun x _ => by rw [Finset.mul_sum]; rfl
  · rw [weightA, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun x _ => by rw [Finset.mul_sum]; rfl

section Order

variable [StarOrderedRing 𝒜] [StarOrderedRing ℬ]

omit [PartialOrder ℬ] [StarOrderedRing ℬ] in
theorem weightA_le_one (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) (hψ : ‖M.ψ‖ = 1)
    (MA : X → POVMIn Λ 𝒜) : M.weightA μ MA ≤ 1 := by
  calc M.weightA μ MA ≤ ∑ x, μ x * 1 :=
        Finset.sum_le_sum fun x _ =>
          mul_le_mul_of_nonneg_left (M.sum_stateSqNorm_le_one hψ (MA x)) (hμ x)
    _ = 1 := by simp [hμ1]

omit [StarOrderedRing 𝒜] in
/-- A family that agrees with some partner with probability at least `1 - δ` has weight at least
`1 - 2δ`. -/
theorem weightA_ge (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) (hψ : ‖M.ψ‖ = 1)
    (MA : X → POVMIn Λ 𝒜) (MB : X → POVMIn Λ ℬ) {δ : ℝ} (h : 1 - M.agreeSum μ MA MB ≤ δ) :
    1 - 2 * δ ≤ M.weightA μ MA := by
  have hcs := M.agreeSum_le_sqrt_mul_sqrt hμ MA MB
  have hB : Real.sqrt (M.swap.weightA μ MB) ≤ 1 :=
    Real.sqrt_le_one.mpr (M.swap.weightA_le_one hμ hμ1 hψ MB)
  have hA0 : 0 ≤ M.weightA μ MA := M.weightA_nonneg hμ MA
  have hsA : M.agreeSum μ MA MB ≤ Real.sqrt (M.weightA μ MA) :=
    le_trans hcs (by
      calc Real.sqrt (M.weightA μ MA) * Real.sqrt (M.swap.weightA μ MB)
          ≤ Real.sqrt (M.weightA μ MA) * 1 :=
            mul_le_mul_of_nonneg_left hB (Real.sqrt_nonneg _)
        _ = Real.sqrt (M.weightA μ MA) := mul_one _)
  by_cases hδ : 1 - δ ≤ 0
  · nlinarith
  · have h1 : 1 - δ ≤ Real.sqrt (M.weightA μ MA) := by linarith
    have h2 : (1 - δ) ^ 2 ≤ M.weightA μ MA := by
      have := Real.sq_sqrt hA0
      nlinarith [Real.sqrt_nonneg (M.weightA μ MA)]
    have hsq : 1 - 2 * δ ≤ (1 - δ) ^ 2 := by nlinarith [sq_nonneg δ]
    linarith

/-- The cross deviation is at most twice the disagreement. -/
theorem xDev_le (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) (hψ : ‖M.ψ‖ = 1)
    (MA : X → POVMIn Λ 𝒜) (MB : X → POVMIn Λ ℬ) :
    M.xDev μ MA MB ≤ 2 * (1 - M.agreeSum μ MA MB) := by
  rw [M.xDev_eq]
  have := M.weightA_le_one hμ hμ1 hψ MA
  have := M.swap.weightA_le_one hμ hμ1 hψ MB
  linarith

omit [StarOrderedRing 𝒜] [StarOrderedRing ℬ] in
/-- **The weighted triangle inequality for cross deviations**: the first player's `A` against the
second player's `D`, through the second player's `B` and the first player's `C`. -/
theorem xDev_triangle (hμ : ∀ x, 0 ≤ μ x) (A C : X → POVMIn Λ 𝒜) (B D : X → POVMIn Λ ℬ) :
    M.xDev μ A D ≤ 3 * M.xDev μ A B + 3 * M.xDev μ C B + 3 * M.xDev μ C D := by
  have h := M.sum_weighted_snorm_sq_triangle3 hμ (univ : Finset X)
    (fun x a => M.πA ((A x).op a)) (fun x a => M.πB ((B x).op a))
    (fun x a => M.πA ((C x).op a)) (fun x a => M.πB ((D x).op a))
  have hmid : ∀ x a, M.snorm (M.πB ((B x).op a) - M.πA ((C x).op a)) ^ 2
      = M.xSqNorm ((C x).op a) ((B x).op a) := fun x a => by
    rw [M.snorm_sub_comm]
    rfl
  simp only [hmid] at h
  exact h

/-- **The agreement triangle** (`fact:triangle-for-simeq`, item 1, with `11 δ` in place of the
paper's `9 δ`): agreement is transitive across the two parties, for POVMs. -/
theorem agreeSum_triangle (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) (hψ : ‖M.ψ‖ = 1)
    (A C : X → POVMIn Λ 𝒜) (B D : X → POVMIn Λ ℬ) {δ : ℝ}
    (hAB : 1 - M.agreeSum μ A B ≤ δ) (hCB : 1 - M.agreeSum μ C B ≤ δ)
    (hCD : 1 - M.agreeSum μ C D ≤ δ) :
    1 - M.agreeSum μ A D ≤ 11 * δ := by
  have hAD := M.xDev_eq (μ := μ) A D
  have htri := M.xDev_triangle hμ A C B D
  have h1 := M.xDev_le hμ hμ1 hψ A B
  have h2 := M.xDev_le hμ hμ1 hψ C B
  have h3 := M.xDev_le hμ hμ1 hψ C D
  have hwA := M.weightA_ge hμ hμ1 hψ A B hAB
  have hwD : 1 - 2 * δ ≤ M.swap.weightA μ D := by
    refine M.swap.weightA_ge hμ hμ1 hψ D C ?_
    rw [M.agreeSum_swap]
    exact hCD
  linarith

end Order

end Triangle

end BipartiteModel

/-! ## Extension by the identity, and the deterministic POVM -/

section Lift

variable {A : Type*} [Fintype A] {d E : Type*} [Fintype d] [DecidableEq d] [Fintype E]
  [DecidableEq E]

/-- A POVM on `d`, extended by the identity to `d × E`. -/
def POVM.aOp (M : POVM A d) : POVM A (d × E) where
  mats a := ⟨MIPRE.aOp (M.mats a).val, by
    rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose, aOp_conjTranspose,
      ← Matrix.star_eq_conjTranspose, selfAdjoint.mem_iff.mp (M.mats a).prop]⟩
  nonneg a :=
    Subtype.coe_le_coe.mp (Matrix.nonneg_iff_posSemidef.mpr
      ((M.posSemidef a).kronecker Matrix.PosSemidef.one))
  normalized := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    show ∑ a, MIPRE.aOp (M.mats a).val = 1
    rw [← aOp_sum, POVM.sum_val, aOp_one]

@[simp] theorem POVM.aOp_mats (M : POVM A d) (a : A) :
    ((M.aOp (E := E)).mats a).val = MIPRE.aOp (M.mats a).val := rfl

/-- Extending by the identity commutes with relabelling the outcomes. -/
theorem POVM.map_aOp {B : Type*} [Fintype B] [DecidableEq B] (f : A → B) (M : POVM A d) :
    (M.map f).aOp (E := E) = (M.aOp (E := E)).map f :=
  POVM.ext' fun b => by
    rw [POVM.aOp_mats, POVM.map_mats, POVM.map_mats, aOp_sum]
    rfl

variable [DecidableEq A]

/-- The deterministic POVM answering `a₀`. -/
def POVM.dirac (a₀ : A) : POVM A d where
  mats a := ⟨if a = a₀ then 1 else 0, by
    rw [selfAdjoint.mem_iff]
    split_ifs <;> simp⟩
  nonneg a := by
    refine Subtype.coe_le_coe.mp (Matrix.nonneg_iff_posSemidef.mpr ?_)
    show (if a = a₀ then (1 : Matrix d d ℂ) else 0).PosSemidef
    split_ifs
    · exact Matrix.PosSemidef.one
    · exact Matrix.PosSemidef.zero
  normalized := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    show ∑ a, (if a = a₀ then (1 : Matrix d d ℂ) else 0) = 1
    rw [Finset.sum_ite_eq' univ a₀]
    simp

end Lift

/-! ## Mixtures -/

section Mix

variable {A : Type*} [Fintype A] {d : Type*} [Fintype d] [DecidableEq d] {ι : Type*} [Fintype ι]

/-- **A convex combination of POVMs** with the same outcomes, with real weights `w` summing to
one. -/
def POVM.mix (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (Q : ι → POVM A d) :
    POVM A d where
  mats a := ⟨∑ i, w i • ((Q i).mats a).val, by
    rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.conjTranspose_smul, star_trivial, ← Matrix.star_eq_conjTranspose,
      selfAdjoint.mem_iff.mp ((Q i).mats a).prop]⟩
  nonneg a :=
    Subtype.coe_le_coe.mp (Matrix.nonneg_iff_posSemidef.mpr
      (Matrix.posSemidef_sum _ fun i _ => ((Q i).posSemidef a).smul (hw i)))
  normalized := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    show ∑ a, ∑ i, w i • ((Q i).mats a).val = 1
    rw [Finset.sum_comm]
    simp_rw [← Finset.smul_sum, POVM.sum_val]
    rw [← Finset.sum_smul, hw1, one_smul]

@[simp] theorem POVM.mix_mats (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (Q : ι → POVM A d) (a : A) :
    ((POVM.mix w hw hw1 Q).mats a).val = ∑ i, w i • ((Q i).mats a).val := rfl

variable {dA dB : Type*} [Fintype dA] [Fintype dB]

/-- The Born probability is linear in a real multiple of Alice's operator. -/
theorem bornProb_smul_left (ψ : dA × dB → ℂ) (r : ℝ) (EA : Matrix dA dA ℂ)
    (EB : Matrix dB dB ℂ) : bornProb ψ (r • EA) EB = r * bornProb ψ EA EB := by
  classical
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), bornProb_eq_tensor, bornProb_eq_tensor]
  exact (BipartiteModel.tensor ψ).bornProb_smul_left r EA EB

/-- The Born probability is linear in a real multiple of Bob's operator. -/
theorem bornProb_smul_right (ψ : dA × dB → ℂ) (r : ℝ) (EA : Matrix dA dA ℂ)
    (EB : Matrix dB dB ℂ) : bornProb ψ EA (r • EB) = r * bornProb ψ EA EB := by
  classical
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), bornProb_eq_tensor, bornProb_eq_tensor]
  exact (BipartiteModel.tensor ψ).bornProb_smul_right r EA EB

omit [Fintype dA] [Fintype dB] in
/-- **A matrix mixture is a mixture in the matrix algebra.** -/
theorem POVM.mix_toIn (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (Q : ι → POVM A d) :
    (POVM.mix w hw hw1 Q).toIn = POVMIn.mix w hw hw1 fun i => (Q i).toIn :=
  POVMIn.ext' fun a => by
    rw [POVMIn.mix_op, POVM.toIn_op, POVM.mix_mats]
    exact Finset.sum_congr rfl fun i _ => RCLike.real_smul_eq_coe_smul (K := ℂ) _ _

variable [DecidableEq dA] [DecidableEq dB]

/-- **The Born probability of a mixture is the mixture of the Born probabilities**, on Alice's
side. -/
theorem bornProb_mix_left (ψ : dA × dB → ℂ) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (Q : ι → POVM A dA) (a : A) (EB : Matrix dB dB ℂ) :
    bornProb ψ (((POVM.mix w hw hw1 Q).mats a).val) EB
      = ∑ i, w i * bornProb ψ (((Q i).mats a).val) EB := by
  have h := (BipartiteModel.tensor ψ).bornProb_mix_left w hw hw1 (fun i => (Q i).toIn) a EB
  rw [← POVM.mix_toIn] at h
  simpa only [bornProb_eq_tensor, POVM.toIn_op] using h

/-- The same, on Bob's side. -/
theorem bornProb_mix_right (ψ : dA × dB → ℂ) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (EA : Matrix dA dA ℂ) (Q : ι → POVM A dB) (a : A) :
    bornProb ψ EA (((POVM.mix w hw hw1 Q).mats a).val)
      = ∑ i, w i * bornProb ψ EA (((Q i).mats a).val) := by
  have h := (BipartiteModel.tensor ψ).bornProb_mix_right w hw hw1 EA (fun i => (Q i).toIn) a
  rw [← POVM.mix_toIn] at h
  simpa only [bornProb_eq_tensor, POVM.toIn_op] using h

end Mix

/-! ## A POVM from a positive family, and uniform averages -/

section Of

variable {A : Type*} [Fintype A] {d : Type*} [Fintype d] [DecidableEq d]

/-- A POVM from a family of positive semidefinite matrices summing to the identity. -/
def POVM.ofPosSemidef (E : A → Matrix d d ℂ) (hpos : ∀ a, (E a).PosSemidef)
    (hsum : ∑ a, E a = 1) : POVM A d where
  mats a := ⟨E a, by
    rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose]
    exact (hpos a).isHermitian.eq⟩
  nonneg a := Subtype.coe_le_coe.mp (Matrix.nonneg_iff_posSemidef.mpr (hpos a))
  normalized := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact hsum

@[simp] theorem POVM.ofPosSemidef_mats (E : A → Matrix d d ℂ) (hpos : ∀ a, (E a).PosSemidef)
    (hsum : ∑ a, E a = 1) (a : A) : ((POVM.ofPosSemidef E hpos hsum).mats a).val = E a := rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The uniform weights on a finset. -/
def unifOn (S : Finset ι) : ι → ℝ := fun i => if i ∈ S then (S.card : ℝ)⁻¹ else 0

omit [Fintype ι] in
theorem unifOn_nonneg (S : Finset ι) (i : ι) : 0 ≤ unifOn S i := by
  unfold unifOn
  split_ifs <;> positivity

theorem sum_unifOn (S : Finset ι) (hS : S.Nonempty) : ∑ i, unifOn S i = 1 := by
  unfold unifOn
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hS).ne')

variable [DecidableEq A]

/-- **The uniform average of POVMs over a finset**, defaulting to the deterministic answer `a₀`
when the finset is empty. -/
def POVM.avgOn (S : Finset ι) (Q : ι → POVM A d) (a₀ : A) : POVM A d :=
  if hS : S.Nonempty then POVM.mix (unifOn S) (unifOn_nonneg S) (sum_unifOn S hS) Q
  else POVM.dirac a₀

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

theorem bornProb_avgOn_left (ψ : dA × dB → ℂ) {S : Finset ι} (hS : S.Nonempty)
    (Q : ι → POVM A dA) (a₀ : A) (a : A) (EB : Matrix dB dB ℂ) :
    bornProb ψ (((POVM.avgOn S Q a₀).mats a).val) EB
      = (S.card : ℝ)⁻¹ * ∑ i ∈ S, bornProb ψ (((Q i).mats a).val) EB := by
  rw [POVM.avgOn, dif_pos hS, bornProb_mix_left]
  simp only [unifOn, ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]

theorem bornProb_avgOn_right (ψ : dA × dB → ℂ) (EA : Matrix dA dA ℂ) {S : Finset ι}
    (hS : S.Nonempty) (Q : ι → POVM A dB) (a₀ : A) (a : A) :
    bornProb ψ EA (((POVM.avgOn S Q a₀).mats a).val)
      = (S.card : ℝ)⁻¹ * ∑ i ∈ S, bornProb ψ EA (((Q i).mats a).val) := by
  rw [POVM.avgOn, dif_pos hS, bornProb_mix_right]
  simp only [unifOn, ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]

end Of

/-! ## Averages and relabelling -/

section AvgMap

variable {A : Type*} [Fintype A] [DecidableEq A] {d : Type*} [Fintype d] [DecidableEq d]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The operators of a uniform average over a nonempty finset. -/
theorem POVM.avgOn_mats {S : Finset ι} (hS : S.Nonempty) (Q : ι → POVM A d) (a₀ : A) (a : A) :
    ((POVM.avgOn S Q a₀).mats a).val = (S.card : ℝ)⁻¹ • ∑ i ∈ S, ((Q i).mats a).val := by
  rw [POVM.avgOn, dif_pos hS, POVM.mix_mats, Finset.smul_sum]
  simp only [unifOn, ite_smul, zero_smul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

omit [DecidableEq A] [DecidableEq ι] in
/-- Relabelling commutes with mixing. -/
theorem POVM.map_mix {B : Type*} [Fintype B] [DecidableEq B] (g : A → B) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (Q : ι → POVM A d) :
    (POVM.mix w hw hw1 Q).map g = POVM.mix w hw hw1 fun i => (Q i).map g :=
  POVM.ext' fun b => by
    simp only [POVM.map_mats, POVM.mix_mats, Finset.smul_sum]
    exact Finset.sum_comm

/-- Relabelling the deterministic POVM. -/
theorem POVM.map_dirac {B : Type*} [Fintype B] [DecidableEq B] (g : A → B) (a₀ : A) :
    (POVM.dirac (d := d) a₀).map g = POVM.dirac (g a₀) :=
  POVM.ext' fun b => by
    rw [POVM.map_mats]
    show (∑ a ∈ univ.filter fun a => g a = b, if a = a₀ then (1 : Matrix d d ℂ) else 0)
      = if b = g a₀ then 1 else 0
    rw [Finset.sum_ite_eq' (univ.filter fun a => g a = b) a₀ fun _ => (1 : Matrix d d ℂ)]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact if_congr eq_comm rfl rfl

/-- Relabelling commutes with the uniform average. -/
theorem POVM.map_avgOn {B : Type*} [Fintype B] [DecidableEq B] (g : A → B) (S : Finset ι)
    (Q : ι → POVM A d) (a₀ : A) :
    (POVM.avgOn S Q a₀).map g = POVM.avgOn S (fun i => (Q i).map g) (g a₀) := by
  by_cases hS : S.Nonempty
  · rw [POVM.avgOn, POVM.avgOn, dif_pos hS, dif_pos hS, POVM.map_mix]
  · rw [POVM.avgOn, POVM.avgOn, dif_neg hS, dif_neg hS, POVM.map_dirac]

/-- Relabelling along the identity does nothing. -/
theorem POVM.map_id (M : POVM A d) : M.map (fun a => a) = M :=
  POVM.ext' fun b => by
    rw [POVM.map_mats, Finset.sum_filter, Finset.sum_ite_eq' univ b fun a => (M.mats a).val]
    simp

omit [DecidableEq A] in
/-- An outcome outside the range of the relabelling carries the zero operator. -/
theorem POVM.map_mats_eq_zero_of_forall_ne {B : Type*} [Fintype B] [DecidableEq B] (f : A → B)
    (M : POVM A d) {b : B} (h : ∀ a, f a ≠ b) : ((M.map f).mats b).val = 0 := by
  rw [POVM.map_mats]
  exact Finset.sum_eq_zero fun a ha => absurd (Finset.mem_filter.mp ha).2 (h a)

omit [DecidableEq A] in
/-- Two relabellings that agree on the support of a POVM relabel it the same way. -/
theorem POVM.map_congr_of_support {B : Type*} [Fintype B] [DecidableEq B] {f g : A → B}
    (M : POVM A d) (h : ∀ a, (M.mats a).val ≠ 0 → f a = g a) : M.map f = M.map g :=
  POVM.ext' fun b => by
    rw [POVM.map_mats, POVM.map_mats, Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : (M.mats a).val = 0
    · rw [ha]
      simp
    · rw [h a ha]

end AvgMap

/-! ## Acceptance on the support, and the conditional failure -/

section Fail

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

omit [DecidableEq dA] [DecidableEq dB] in
theorem bornProb_zero_left (ψ : dA × dB → ℂ) (EB : Matrix dB dB ℂ) : bornProb ψ 0 EB = 0 := by
  classical
  rw [bornProb_eq_tensor]
  exact (BipartiteModel.tensor ψ).bornProb_zero_left EB

omit [DecidableEq dA] [DecidableEq dB] in
theorem bornProb_zero_right (ψ : dA × dB → ℂ) (EA : Matrix dA dA ℂ) : bornProb ψ EA 0 = 0 := by
  classical
  rw [bornProb_eq_tensor]
  exact (BipartiteModel.tensor ψ).bornProb_zero_right EA

variable {X Y A B C : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq C] {ψ : dA × dB → ℂ} {x : X} {y : Y}

/-- **Agreement on the support implies acceptance bounds the conditional failure by the
disagreement of the relabelled POVMs.** Only outcomes both parties can produce are asked to be
accepted, which is what a strategy answering every question in its own format needs. -/
theorem condFail_le_one_sub_sum_bornProb_map {G : Game X Y A B} {MA : X → POVM A dA}
    {MB : Y → POVM B dB} (f : A → C) (g : B → C)
    (hD : ∀ a b, ((MA x).mats a).val ≠ 0 → ((MB y).mats b).val ≠ 0 → f a = g b →
      G.D x y a b = true) :
    condFail G ψ MA MB x y
      ≤ 1 - ∑ c, bornProb ψ ((((MA x).map f).mats c).val) ((((MB y).map g).mats c).val) := by
  simp only [condFail_eq_tensor, bornProb_eq_tensor]
  exact (BipartiteModel.tensor ψ).condFail_le_one_sub_sum_bornProb_map
    (MA := fun x => (MA x).toIn) (MB := fun y => (MB y).toIn) f g hD

/-- The same with both parties' outcomes read as they are: acceptance of every diagonal pair
on the support bounds the conditional failure by the diagonal disagreement. -/
theorem condFail_le_one_sub_sum_bornProb_diag {G : Game X Y A A} {MA : X → POVM A dA}
    {MB : Y → POVM A dB}
    (hD : ∀ a, ((MA x).mats a).val ≠ 0 → ((MB y).mats a).val ≠ 0 → G.D x y a a = true) :
    condFail G ψ MA MB x y
      ≤ 1 - ∑ a, bornProb ψ (((MA x).mats a).val) (((MB y).mats a).val) := by
  simp only [condFail_eq_tensor, bornProb_eq_tensor]
  exact (BipartiteModel.tensor ψ).condFail_le_one_sub_sum_bornProb_diag
    (MA := fun x => (MA x).toIn) (MB := fun y => (MB y).toIn) hD

/-- `sum_bornProb_map` for two bare POVMs. -/
theorem sum_bornProb_map' {A B : Type*} [Fintype A] [Fintype B] (P : POVM A dA) (Q : POVM B dB)
    (f : A → C) (g : B → C) :
    ∑ c, bornProb ψ (((P.map f).mats c).val) (((Q.map g).mats c).val)
      = ∑ a, ∑ b, (if f a = g b then (1 : ℝ) else 0)
          * bornProb ψ ((P.mats a).val) ((Q.mats b).val) :=
  sum_bornProb_map (MA := fun _ : Unit => P) (MB := fun _ : Unit => Q) (x := ()) (y := ()) f g

/-- Forgetting the outcome altogether gives the identity operator. -/
theorem POVM.map_const_mats {A : Type*} [Fintype A] (P : POVM A dA) :
    ((P.map fun _ => ()).mats ()).val = 1 := by
  rw [POVM.map_mats, Finset.filter_true_of_mem fun _ _ => rfl, POVM.sum_val]

theorem bornProb_one_one {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) :
    bornProb ψ (1 : Matrix dA dA ℂ) (1 : Matrix dB dB ℂ) = 1 := by
  rw [bornProb_eq_tensor]
  exact (BipartiteModel.tensor ψ).bornProb_one_one (norm_evec_eq_one hψ)

end Fail

/-! ## The agreement triangle -/

section Triangle

variable {X Λ : Type*} [Fintype X] [Fintype Λ] {dA dB : Type*} [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB]

/-- The agreement probability of two families of POVMs, one per party, on the same questions,
averaged over the question distribution `μ`: the paper's `p(R, S)`. -/
def agreeSum (μ : X → ℝ) (ψ : dA × dB → ℂ) (M : X → POVM Λ dA) (N : X → POVM Λ dB) : ℝ :=
  ∑ x, μ x * ∑ a, bornProb ψ (((M x).mats a).val) (((N x).mats a).val)

/-- The weighted squared norm of Alice's measurement vectors, `∑_x μ_x ∑_a ‖(M^x_a ⊗ I)ψ‖²`. -/
def weightA (μ : X → ℝ) (ψ : dA × dB → ℂ) (M : X → POVM Λ dA) : ℝ :=
  ∑ x, μ x * ∑ a, stateSqNorm ψ (((M x).mats a).val)

/-- Bob's version. -/
def weightB (μ : X → ℝ) (ψ : dA × dB → ℂ) (N : X → POVM Λ dB) : ℝ :=
  ∑ x, μ x * ∑ a, ‖stateVecB ψ (((N x).mats a).val)‖ ^ 2

/-- The weighted cross-party deviation of two families. -/
def xDev (μ : X → ℝ) (ψ : dA × dB → ℂ) (M : X → POVM Λ dA) (N : X → POVM Λ dB) : ℝ :=
  ∑ x, μ x * ∑ a, xSqNorm ψ (((M x).mats a).val) (((N x).mats a).val)

variable {μ : X → ℝ} {ψ : dA × dB → ℂ}

theorem agreeSum_eq_tensor (M : X → POVM Λ dA) (N : X → POVM Λ dB) :
    agreeSum μ ψ M N
      = (BipartiteModel.tensor ψ).agreeSum μ (fun x => (M x).toIn) (fun x => (N x).toIn) := by
  simp only [agreeSum, BipartiteModel.agreeSum, bornProb_eq_tensor, POVM.toIn_op]

theorem weightA_eq_tensor (M : X → POVM Λ dA) :
    weightA μ ψ M = (BipartiteModel.tensor ψ).weightA μ (fun x => (M x).toIn) :=
  rfl

theorem weightB_eq_tensor (N : X → POVM Λ dB) :
    weightB μ ψ N = (BipartiteModel.tensor ψ).swap.weightA μ (fun x => (N x).toIn) :=
  rfl

theorem xDev_eq_tensor (M : X → POVM Λ dA) (N : X → POVM Λ dB) :
    xDev μ ψ M N = (BipartiteModel.tensor ψ).xDev μ (fun x => (M x).toIn) (fun x => (N x).toIn) := by
  simp only [xDev, BipartiteModel.xDev, xSqNorm_eq_tensor, POVM.toIn_op]

theorem weightA_le_one (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) (hψ : star ψ ⬝ᵥ ψ = 1)
    (M : X → POVM Λ dA) : weightA μ ψ M ≤ 1 := by
  rw [weightA_eq_tensor]
  exact (BipartiteModel.tensor ψ).weightA_le_one hμ hμ1 (norm_evec_eq_one hψ) _

theorem weightB_le_one (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) (hψ : star ψ ⬝ᵥ ψ = 1)
    (N : X → POVM Λ dB) : weightB μ ψ N ≤ 1 := by
  rw [weightB_eq_tensor]
  exact (BipartiteModel.tensor ψ).swap.weightA_le_one hμ hμ1 (norm_evec_eq_one hψ) _

theorem weightA_nonneg (hμ : ∀ x, 0 ≤ μ x) (M : X → POVM Λ dA) : 0 ≤ weightA μ ψ M := by
  rw [weightA_eq_tensor]
  exact (BipartiteModel.tensor ψ).weightA_nonneg hμ _

theorem weightB_nonneg (hμ : ∀ x, 0 ≤ μ x) (N : X → POVM Λ dB) : 0 ≤ weightB μ ψ N := by
  rw [weightB_eq_tensor]
  exact (BipartiteModel.tensor ψ).swap.weightA_nonneg hμ _

/-- **The cross deviation expands**: `xDev = weightA + weightB - 2 agreeSum`. -/
theorem xDev_eq (M : X → POVM Λ dA) (N : X → POVM Λ dB) :
    xDev μ ψ M N = weightA μ ψ M + weightB μ ψ N - 2 * agreeSum μ ψ M N := by
  rw [xDev_eq_tensor, agreeSum_eq_tensor, weightA_eq_tensor, weightB_eq_tensor]
  exact (BipartiteModel.tensor ψ).xDev_eq _ _

/-- A Born probability is at most the product of the two state norms (Cauchy--Schwarz). -/
theorem bornProb_le_norm_mul_norm (ψ : dA × dB → ℂ) {EA : Matrix dA dA ℂ} (hEA : EAᴴ = EA)
    (EB : Matrix dB dB ℂ) :
    bornProb ψ EA EB ≤ ‖stateVec ψ EA‖ * ‖stateVecB ψ EB‖ := by
  rw [bornProb_eq_tensor]
  exact (BipartiteModel.tensor ψ).bornProb_le_stateNorm_mul hEA EB

/-- **Cauchy--Schwarz for the agreement**: `agreeSum ≤ √weightA · √weightB`. -/
theorem agreeSum_le_sqrt_mul_sqrt (hμ : ∀ x, 0 ≤ μ x) (M : X → POVM Λ dA) (N : X → POVM Λ dB) :
    agreeSum μ ψ M N ≤ Real.sqrt (weightA μ ψ M) * Real.sqrt (weightB μ ψ N) := by
  rw [agreeSum_eq_tensor, weightA_eq_tensor, weightB_eq_tensor]
  exact (BipartiteModel.tensor ψ).agreeSum_le_sqrt_mul_sqrt hμ _ _

/-- A family that agrees with some partner with probability at least `1 - δ` has weight at least
`1 - 2δ`. -/
theorem weightA_ge (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) (hψ : star ψ ⬝ᵥ ψ = 1)
    (M : X → POVM Λ dA) (N : X → POVM Λ dB) {δ : ℝ} (h : 1 - agreeSum μ ψ M N ≤ δ) :
    1 - 2 * δ ≤ weightA μ ψ M := by
  rw [agreeSum_eq_tensor] at h
  rw [weightA_eq_tensor]
  exact (BipartiteModel.tensor ψ).weightA_ge hμ hμ1 (norm_evec_eq_one hψ) _ _ h

/-- Bob's version. -/
theorem weightB_ge (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) (hψ : star ψ ⬝ᵥ ψ = 1)
    (M : X → POVM Λ dA) (N : X → POVM Λ dB) {δ : ℝ} (h : 1 - agreeSum μ ψ M N ≤ δ) :
    1 - 2 * δ ≤ weightB μ ψ N := by
  rw [agreeSum_eq_tensor, ← BipartiteModel.agreeSum_swap] at h
  rw [weightB_eq_tensor]
  exact (BipartiteModel.tensor ψ).swap.weightA_ge hμ hμ1 (norm_evec_eq_one hψ) _ _ h

/-- The cross deviation is at most twice the disagreement. -/
theorem xDev_le (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) (hψ : star ψ ⬝ᵥ ψ = 1)
    (M : X → POVM Λ dA) (N : X → POVM Λ dB) :
    xDev μ ψ M N ≤ 2 * (1 - agreeSum μ ψ M N) := by
  rw [xDev_eq_tensor, agreeSum_eq_tensor]
  exact (BipartiteModel.tensor ψ).xDev_le hμ hμ1 (norm_evec_eq_one hψ) _ _

/-- **The weighted triangle inequality for cross deviations**: Alice's `A` against Bob's `D`,
through Bob's `B` and Alice's `C`. -/
theorem xDev_triangle (hμ : ∀ x, 0 ≤ μ x) (A C : X → POVM Λ dA) (B D : X → POVM Λ dB) :
    xDev μ ψ A D ≤ 3 * xDev μ ψ A B + 3 * xDev μ ψ C B + 3 * xDev μ ψ C D := by
  simp only [xDev_eq_tensor]
  exact (BipartiteModel.tensor ψ).xDev_triangle hμ _ _ _ _

/-- **The agreement triangle** (`fact:triangle-for-simeq`, item 1, with `11 δ` in place of the
paper's `9 δ`): agreement is transitive across the two parties, for POVMs. -/
theorem agreeSum_triangle (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) (hψ : star ψ ⬝ᵥ ψ = 1)
    (A C : X → POVM Λ dA) (B D : X → POVM Λ dB) {δ : ℝ}
    (hAB : 1 - agreeSum μ ψ A B ≤ δ) (hCB : 1 - agreeSum μ ψ C B ≤ δ)
    (hCD : 1 - agreeSum μ ψ C D ≤ δ) :
    1 - agreeSum μ ψ A D ≤ 11 * δ := by
  simp only [agreeSum_eq_tensor] at hAB hCB hCD ⊢
  exact (BipartiteModel.tensor ψ).agreeSum_triangle hμ hμ1 (norm_evec_eq_one hψ) _ _ _ _ hAB hCB
    hCD

end Triangle

end MIPRE

end

end
