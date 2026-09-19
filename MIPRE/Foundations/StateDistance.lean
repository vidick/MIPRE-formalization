/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Closeness

/-!
# The state-dependent distance on a bipartite state

Every soundness argument in the Pauli basis test's appendix compares operators in the distance

`A^x ≈_δ B^x` ⟺ `𝔼_{x ∼ μ} ⟨ψ| (A^x - B^x)† (A^x - B^x) |ψ⟩ ≤ δ`,

where the operators act on **Alice's factor** of a bipartite state `|ψ⟩ ∈ ℂ^{dA} ⊗ ℂ^{dB}`. That
is not the distance `MIPRE/Foundations/Distances.lean` defines: `povmDistance` and
`IsPOVMClose` use the normalized Hilbert--Schmidt norm, which is the *tracial* — synchronous —
specialization, and `MIPRE/Foundations/Closeness.lean` says so in its own docstring. This file
is the state-dependent one, and it is what blueprint `def:state-distance` names.

Two deliberate departures from the paper's `qld-prelim.tex`:

* **no `O(·)` inside the definition.** The paper writes `≤ O(δ)`; here the relation is
  `stateDist μ ψ A B ≤ δ` and the constants appear in the lemmas that produce them. That is
  stronger, not weaker: `stateSqNorm_avg_le` preserves `δ` exactly and `povm_to_obs` gives
  exactly `|𝒜| · δ`.
* **answer-indexed families as well.** The paper's `≈_δ` is for operators indexed by questions
  but not answers; the applications also need the form summed over a common outcome set
  (`cor:ortho-from-consistency` concludes `P_a ⊗ Id ≈ Q_a ⊗ Id`). Both are here, the second as
  `povmStateDist`.

## Implementation

`stateVec ψ A = (A ⊗ Id)|ψ⟩`, carried in `EuclideanSpace ℂ (dA × dB)` so that the triangle
inequality and `‖c • v‖ = ‖c‖‖v‖` are Mathlib's rather than rebuilt. The bridge to the
blueprint's quadratic-form spelling is `stateSqNorm_eq`, which is the only place the Kronecker
adjoint is used.
-/

namespace MIPRE

open Finset Matrix Kronecker

variable {X : Type*} [Fintype X]
variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]

/-! ## The vector `(A ⊗ Id)|ψ⟩` -/

/-- `(M ⊗ Id)|ψ⟩`, as a vector of `EuclideanSpace ℂ (dA × dB)`. -/
noncomputable def stateVec (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) :
    EuclideanSpace ℂ (dA × dB) :=
  WithLp.toLp 2 ((M ⊗ₖ (1 : Matrix dB dB ℂ)) *ᵥ ψ)

@[simp] theorem stateVec_add (ψ : dA × dB → ℂ) (M N : Matrix dA dA ℂ) :
    stateVec ψ (M + N) = stateVec ψ M + stateVec ψ N := by
  show WithLp.toLp 2 _ = WithLp.toLp 2 _ + WithLp.toLp 2 _
  rw [Matrix.add_kronecker, Matrix.add_mulVec]
  rfl

@[simp] theorem stateVec_smul (ψ : dA × dB → ℂ) (c : ℂ) (M : Matrix dA dA ℂ) :
    stateVec ψ (c • M) = c • stateVec ψ M := by
  show WithLp.toLp 2 _ = c • WithLp.toLp 2 _
  rw [Matrix.smul_kronecker, Matrix.smul_mulVec]
  rfl

@[simp] theorem stateVec_zero (ψ : dA × dB → ℂ) :
    stateVec ψ (0 : Matrix dA dA ℂ) = 0 := by
  show WithLp.toLp 2 _ = 0
  rw [Matrix.zero_kronecker, Matrix.zero_mulVec]
  rfl

@[simp] theorem stateVec_neg (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) :
    stateVec ψ (-M) = -stateVec ψ M := by
  have h : stateVec ψ M + stateVec ψ (-M) = 0 := by
    rw [← stateVec_add, add_neg_cancel, stateVec_zero]
  linear_combination (norm := module) h

@[simp] theorem stateVec_sub (ψ : dA × dB → ℂ) (M N : Matrix dA dA ℂ) :
    stateVec ψ (M - N) = stateVec ψ M - stateVec ψ N := by
  rw [sub_eq_add_neg, stateVec_add, stateVec_neg, sub_eq_add_neg]

theorem stateVec_sum {ι : Type*} (ψ : dA × dB → ℂ) (s : Finset ι) (f : ι → Matrix dA dA ℂ) :
    stateVec ψ (∑ i ∈ s, f i) = ∑ i ∈ s, stateVec ψ (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, stateVec_add, ih, Finset.sum_insert hi]

/-! ## The norm, and the distance -/

/-- `‖(M ⊗ Id)|ψ⟩‖`. -/
noncomputable def stateNorm (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) : ℝ := ‖stateVec ψ M‖

/-- `⟨ψ| M† M ⊗ Id |ψ⟩`, the squared state-dependent norm. -/
noncomputable def stateSqNorm (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) : ℝ := stateNorm ψ M ^ 2

/-- The sesquilinear form of two matrices applied to the same vector, moved onto one side:
`⟨A ψ, B ψ⟩ = ⟨ψ, A† B ψ⟩`. -/
theorem star_mulVec_dotProduct {n : Type*} [Fintype n] (A B : Matrix n n ℂ) (ψ : n → ℂ) :
    star (A *ᵥ ψ) ⬝ᵥ (B *ᵥ ψ) = star ψ ⬝ᵥ ((Aᴴ * B) *ᵥ ψ) := by
  rw [Matrix.star_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec]

/-- **The squared norm is the blueprint's quadratic form**, as a complex number:
`⟨ψ| M† M ⊗ Id |ψ⟩` is real and equal to `stateSqNorm ψ M`. This is the only place the Kronecker
adjoint is needed, and it is what makes the Lean definition and `def:state-distance`'s spelling
the same object rather than informally the same. The complex form is what a positivity
hypothesis on a linear functional wants. -/
theorem quadForm_eq (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) :
    star ψ ⬝ᵥ ((((Mᴴ * M) ⊗ₖ (1 : Matrix dB dB ℂ))) *ᵥ ψ) = (stateSqNorm ψ M : ℂ) := by
  classical
  set A : Matrix (dA × dB) (dA × dB) ℂ := M ⊗ₖ (1 : Matrix dB dB ℂ) with hA
  have hAdj : Aᴴ * A = (Mᴴ * M) ⊗ₖ (1 : Matrix dB dB ℂ) := by
    rw [hA, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  have h1 : star (A *ᵥ ψ) ⬝ᵥ (A *ᵥ ψ) = star ψ ⬝ᵥ ((Aᴴ * A) *ᵥ ψ) :=
    star_mulVec_dotProduct A A ψ
  rw [← hAdj, ← h1, dotProduct]
  have hentry : ∀ i, star (A *ᵥ ψ) i * (A *ᵥ ψ) i = ((‖(A *ᵥ ψ) i‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [Pi.star_apply, RCLike.star_def, RCLike.conj_mul]
    norm_cast
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hentry i, ← Complex.ofReal_sum]
  show _ = ((‖stateVec ψ M‖ ^ 2 : ℝ) : ℂ)
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  rfl

/-- The real form of `quadForm_eq`, which is how `def:state-distance` is written. -/
theorem stateSqNorm_eq (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) :
    stateSqNorm ψ M
      = (star ψ ⬝ᵥ ((((Mᴴ * M) ⊗ₖ (1 : Matrix dB dB ℂ))) *ᵥ ψ)).re := by
  rw [quadForm_eq, Complex.ofReal_re]

theorem stateNorm_nonneg (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) : 0 ≤ stateNorm ψ M :=
  norm_nonneg _

theorem stateSqNorm_nonneg (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) : 0 ≤ stateSqNorm ψ M :=
  sq_nonneg _

theorem sqrt_stateSqNorm (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) :
    Real.sqrt (stateSqNorm ψ M) = stateNorm ψ M :=
  Real.sqrt_sq (stateNorm_nonneg ψ M)

theorem stateNorm_smul (ψ : dA × dB → ℂ) (c : ℂ) (M : Matrix dA dA ℂ) :
    stateNorm ψ (c • M) = ‖c‖ * stateNorm ψ M := by
  rw [stateNorm, stateNorm, stateVec_smul, norm_smul]

theorem stateNorm_sum_le {ι : Type*} (ψ : dA × dB → ℂ) (s : Finset ι)
    (f : ι → Matrix dA dA ℂ) :
    stateNorm ψ (∑ i ∈ s, f i) ≤ ∑ i ∈ s, stateNorm ψ (f i) := by
  rw [stateNorm, stateVec_sum]
  exact norm_sum_le _ _

/-- **The state-dependent distance** of two families of operators on Alice's factor, relative to
a question distribution `μ` and the state `ψ`: blueprint `def:state-distance`. -/
noncomputable def stateDist (μ : X → ℝ) (ψ : dA × dB → ℂ) (A B : X → Matrix dA dA ℂ) : ℝ :=
  ∑ x, μ x * stateSqNorm ψ (A x - B x)

/-- `A ≈_δ B` on `ψ`, relative to `μ`. -/
def IsStateClose (μ : X → ℝ) (ψ : dA × dB → ℂ) (δ : ℝ) (A B : X → Matrix dA dA ℂ) : Prop :=
  stateDist μ ψ A B ≤ δ

theorem stateDist_nonneg {μ : X → ℝ} (hμ : ∀ x, 0 ≤ μ x) (ψ : dA × dB → ℂ)
    (A B : X → Matrix dA dA ℂ) : 0 ≤ stateDist μ ψ A B :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hμ x) (stateSqNorm_nonneg ψ _)

section POVMs

variable {A : Type*} [Fintype A] [DecidableEq A] [DecidableEq dA]

/-- **The same distance for families indexed by answers as well**, which is the form the
consistency statements take: the outcome sum is inside the question average. -/
noncomputable def povmStateDist (μ : X → ℝ) (ψ : dA × dB → ℂ) (M N : X → POVM A dA) : ℝ :=
  ∑ x, μ x * ∑ a, stateSqNorm ψ (((M x).mats a).val - ((N x).mats a).val)

/-- `M_a ≈_δ N_a` on `ψ`, relative to `μ`. -/
def IsPOVMStateClose (μ : X → ℝ) (ψ : dA × dB → ℂ) (δ : ℝ) (M N : X → POVM A dA) : Prop :=
  povmStateDist μ ψ M N ≤ δ

omit [DecidableEq A] in
theorem povmStateDist_nonneg {μ : X → ℝ} (hμ : ∀ x, 0 ≤ μ x) (ψ : dA × dB → ℂ)
    (M N : X → POVM A dA) : 0 ≤ povmStateDist μ ψ M N :=
  Finset.sum_nonneg fun x _ =>
    mul_nonneg (hμ x) (Finset.sum_nonneg fun _ _ => stateSqNorm_nonneg ψ _)

/-! ## The two closeness lemmas of the appendix's preliminaries -/

/-- The generalized observable of a POVM family and a weighting of the outcomes:
`A^x = ∑_a α_a A^x_a`. -/
noncomputable def obsOf (α : A → ℂ) (M : X → POVM A dA) (x : X) : Matrix dA dA ℂ :=
  ∑ a, α a • ((M x).mats a).val

omit [DecidableEq A] in
/-- **From POVM elements to generalized observables**, blueprint `lem:qld-povm-to-obs`: the
weighting costs a factor `|𝒜|`, from Cauchy--Schwarz over the outcome set. The paper asks the
weights to be of unit modulus; `‖α a‖ ≤ 1` is all the proof uses. -/
theorem stateDist_obsOf_le {μ : X → ℝ} (hμ0 : ∀ x, 0 ≤ μ x) (ψ : dA × dB → ℂ)
    (M N : X → POVM A dA) (α : A → ℂ) (hα : ∀ a, ‖α a‖ ≤ 1) :
    stateDist μ ψ (obsOf α M) (obsOf α N)
      ≤ (Fintype.card A : ℝ) * povmStateDist μ ψ M N := by
  classical
  rw [povmStateDist, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [← mul_assoc, mul_comm ((Fintype.card A : ℝ)) (μ x), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (hμ0 x)
  -- pointwise in `x`: the triangle inequality, then Cauchy--Schwarz over the outcomes
  have hsub : obsOf α M x - obsOf α N x
      = ∑ a, α a • (((M x).mats a).val - ((N x).mats a).val) := by
    rw [obsOf, obsOf, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => (smul_sub _ _ _).symm
  have htri : stateNorm ψ (obsOf α M x - obsOf α N x)
      ≤ ∑ a, stateNorm ψ (((M x).mats a).val - ((N x).mats a).val) := by
    rw [hsub]
    refine (stateNorm_sum_le ψ Finset.univ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [stateNorm_smul]
    calc ‖α a‖ * stateNorm ψ _ ≤ 1 * stateNorm ψ _ :=
          mul_le_mul_of_nonneg_right (hα a) (stateNorm_nonneg ψ _)
      _ = stateNorm ψ _ := one_mul _
  calc stateSqNorm ψ (obsOf α M x - obsOf α N x)
      ≤ (∑ a, stateNorm ψ (((M x).mats a).val - ((N x).mats a).val)) ^ 2 :=
        pow_le_pow_left₀ (stateNorm_nonneg ψ _) htri 2
    _ ≤ (Fintype.card A : ℝ)
          * ∑ a, stateNorm ψ (((M x).mats a).val - ((N x).mats a).val) ^ 2 :=
        sq_sum_le_card_mul_sum_sq _ (fun a => stateNorm_nonneg ψ _)
    _ = (Fintype.card A : ℝ)
          * ∑ a, stateSqNorm ψ (((M x).mats a).val - ((N x).mats a).val) := rfl

end POVMs

/-! ## Bob's factor, by the swap

`cor:ortho-from-consistency` compares `(Q_a ⊗ Id)|ψ⟩` against `(Id ⊗ R_a)|ψ⟩`, so it needs the
vectors of the *other* factor too. Rather than duplicate the calculus above, observe that Bob's
factor is Alice's factor of the swapped state: `swapVec` exchanges the two tensor factors, and
`norm_stateVecB` identifies the two norms. Every lemma proved above then applies on Bob's side
with `dA` and `dB` exchanged. -/

section Swap

variable [DecidableEq dA]

/-- `|ψ⟩` with its two tensor factors exchanged. -/
def swapVec (ψ : dA × dB → ℂ) : dB × dA → ℂ := fun p => ψ p.swap

/-- `(Id ⊗ N)|ψ⟩`, as a vector of `EuclideanSpace ℂ (dA × dB)`: the `stateVec` of Bob's
factor. -/
noncomputable def stateVecB (ψ : dA × dB → ℂ) (N : Matrix dB dB ℂ) :
    EuclideanSpace ℂ (dA × dB) :=
  WithLp.toLp 2 (((1 : Matrix dA dA ℂ) ⊗ₖ N) *ᵥ ψ)

omit [DecidableEq dB] in
theorem stateVecB_entry (ψ : dA × dB → ℂ) (N : Matrix dB dB ℂ) (i : dA) (j : dB) :
    (((1 : Matrix dA dA ℂ) ⊗ₖ N) *ᵥ ψ) (i, j) = ∑ l, N j l * ψ (i, l) := by
  classical
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply,
    Finset.sum_ite_eq, mul_comm]

omit [DecidableEq dB] in
theorem stateVec_swapVec_entry (ψ : dA × dB → ℂ) (N : Matrix dB dB ℂ) (i : dA) (j : dB) :
    ((N ⊗ₖ (1 : Matrix dA dA ℂ)) *ᵥ swapVec ψ) (j, i) = ∑ l, N j l * ψ (i, l) := by
  classical
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply, swapVec, mul_ite,
    Finset.sum_ite_eq]

omit [DecidableEq dB] in
/-- **Bob's norm is Alice's norm of the swapped state.** -/
theorem norm_stateVecB (ψ : dA × dB → ℂ) (N : Matrix dB dB ℂ) :
    ‖stateVecB ψ N‖ = stateNorm (swapVec ψ) N := by
  classical
  rw [stateNorm, stateVecB, stateVec, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Fintype.sum_equiv (Equiv.prodComm dA dB) _ _ fun p => ?_
  obtain ⟨i, j⟩ := p
  show ‖(((1 : Matrix dA dA ℂ) ⊗ₖ N) *ᵥ ψ) (i, j)‖ ^ 2
      = ‖((N ⊗ₖ (1 : Matrix dA dA ℂ)) *ᵥ swapVec ψ) (j, i)‖ ^ 2
  rw [stateVecB_entry, stateVec_swapVec_entry]

/-- The inner product of the two factors' vectors is the blueprint's `⟨ψ| Q ⊗ R |ψ⟩`, for
self-adjoint `Q`. -/
theorem inner_stateVec_stateVecB (ψ : dA × dB → ℂ) {Q : Matrix dA dA ℂ} (hQ : Qᴴ = Q)
    (R : Matrix dB dB ℂ) :
    inner ℂ (stateVec ψ Q) (stateVecB ψ R) = star ψ ⬝ᵥ ((Q ⊗ₖ R) *ᵥ ψ) := by
  classical
  have hadj : (Q ⊗ₖ (1 : Matrix dB dB ℂ))ᴴ * ((1 : Matrix dA dA ℂ) ⊗ₖ R) = Q ⊗ₖ R := by
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
      Matrix.mul_one, Matrix.one_mul, hQ]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  show ((1 : Matrix dA dA ℂ) ⊗ₖ R) *ᵥ ψ ⬝ᵥ star ((Q ⊗ₖ (1 : Matrix dB dB ℂ)) *ᵥ ψ) = _
  rw [dotProduct_comm, star_mulVec_dotProduct, hadj]

omit [DecidableEq dB] [DecidableEq dA] in
/-- The swap is a reindexing, so it preserves the norm of the state. -/
theorem swapVec_dotProduct (ψ : dA × dB → ℂ) :
    star (swapVec ψ) ⬝ᵥ swapVec ψ = star ψ ⬝ᵥ ψ :=
  (Fintype.sum_equiv (Equiv.prodComm dA dB) _ _ fun _ => rfl).symm

end Swap

/-- **Averaging preserves closeness**, blueprint `lem:qld-averaging`: a weighted average with
weights of modulus at most one is no further apart than the families are. Triangle inequality,
then Jensen for the square root (`sum_mul_sqrt_le`). -/
theorem stateSqNorm_avg_le {μ : X → ℝ} (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (ψ : dA × dB → ℂ) (A B : X → Matrix dA dA ℂ) (α : X → ℂ) (hα : ∀ x, ‖α x‖ ≤ 1) :
    stateSqNorm ψ ((∑ x, ((μ x : ℂ) * α x) • A x) - ∑ x, ((μ x : ℂ) * α x) • B x)
      ≤ stateDist μ ψ A B := by
  classical
  have hsub : (∑ x, ((μ x : ℂ) * α x) • A x) - (∑ x, ((μ x : ℂ) * α x) • B x)
      = ∑ x, ((μ x : ℂ) * α x) • (A x - B x) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => (smul_sub _ _ _).symm
  have htri : stateNorm ψ (∑ x, ((μ x : ℂ) * α x) • (A x - B x))
      ≤ ∑ x, μ x * stateNorm ψ (A x - B x) := by
    refine (stateNorm_sum_le ψ Finset.univ _).trans (Finset.sum_le_sum fun x _ => ?_)
    rw [stateNorm_smul]
    refine mul_le_mul_of_nonneg_right ?_ (stateNorm_nonneg ψ _)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hμ0 x)]
    calc μ x * ‖α x‖ ≤ μ x * 1 := mul_le_mul_of_nonneg_left (hα x) (hμ0 x)
      _ = μ x := mul_one _
  have hjensen : ∑ x, μ x * stateNorm ψ (A x - B x) ≤ Real.sqrt (stateDist μ ψ A B) := by
    have h := sum_mul_sqrt_le (Finset.univ : Finset X) μ
      (fun x => stateSqNorm ψ (A x - B x)) hμ0 (fun x => stateSqNorm_nonneg ψ _)
    rw [hμ1, Real.sqrt_one, one_mul] at h
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun x _ => ?_)) h
    rw [sqrt_stateSqNorm]
  have hd : 0 ≤ stateDist μ ψ A B := stateDist_nonneg hμ0 ψ A B
  rw [hsub]
  calc stateSqNorm ψ (∑ x, ((μ x : ℂ) * α x) • (A x - B x))
      ≤ Real.sqrt (stateDist μ ψ A B) ^ 2 :=
        pow_le_pow_left₀ (stateNorm_nonneg ψ _) (htri.trans hjensen) 2
    _ = stateDist μ ψ A B := Real.sq_sqrt hd

end MIPRE
