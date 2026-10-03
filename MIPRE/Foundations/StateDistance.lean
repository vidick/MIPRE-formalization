/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.Closeness
public import MIPRE.Foundations.OpBound
public import MIPRE.Foundations.POVMValue

@[expose] public section

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

## In a bipartite model

The norm, the distances and the two closeness lemmas are stated for any bipartite model
(`MIPRE/Foundations/BipartiteModel.lean`) with the first player's operators in its algebra, and
the matrix ones are their instances in the tensor-product model (`stateNorm_eq_tensor`,
`stateDist_eq_tensor`, `povmStateDist_eq_tensor`). What stays about matrices is the vector
`stateVec` itself and the factor swap, which a model does not need: its second player's norm is
`‖πB b ψ‖`, by the same definition.
-/

namespace MIPRE

open Finset Matrix Kronecker

/-! ## The state norm and distance in a bipartite model -/

namespace BipartiteModel

open scoped InnerProductSpace

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] (M : BipartiteModel 𝒞 𝒜 ℬ)

/-- `‖πA a ψ‖`: the norm of the first player's operator on the state. -/
def stateNorm (a : 𝒜) : ℝ := M.snorm (M.πA a)

/-- `⟨ψ| πA(a† a) |ψ⟩`, the squared state-dependent norm. -/
def stateSqNorm (a : 𝒜) : ℝ := M.stateNorm a ^ 2

/-- **The squared norm is the quadratic form of `a† a`.** -/
theorem stateSqNorm_eq (a : 𝒜) : M.stateSqNorm a = M.qform (M.πA (star a * a)) := by
  rw [stateSqNorm, stateNorm, M.snorm_sq_eq_qform, map_mul, map_star]

/-- **The squared norm is the quadratic form of `a† a`, as a complex number**: the inner product
is real. -/
theorem inner_stateSqNorm (a : 𝒜) :
    ⟪M.ψ, M.π (M.πA (star a * a)) M.ψ⟫_ℂ = (M.stateSqNorm a : ℂ) := by
  rw [map_mul, map_star, map_mul, map_star]
  show ⟪M.ψ, (star (M.π (M.πA a))) (M.π (M.πA a) M.ψ)⟫_ℂ = _
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K, stateSqNorm, stateNorm, StateModel.snorm, Op.snorm]
  push_cast
  rfl

theorem stateNorm_nonneg (a : 𝒜) : 0 ≤ M.stateNorm a := M.snorm_nonneg _

theorem stateSqNorm_nonneg (a : 𝒜) : 0 ≤ M.stateSqNorm a := sq_nonneg _

theorem sqrt_stateSqNorm (a : 𝒜) : Real.sqrt (M.stateSqNorm a) = M.stateNorm a :=
  Real.sqrt_sq (M.stateNorm_nonneg a)

theorem stateNorm_smul (c : ℂ) (a : 𝒜) : M.stateNorm (c • a) = ‖c‖ * M.stateNorm a := by
  rw [stateNorm, stateNorm, map_smul]
  exact M.snorm_smul c _

theorem stateNorm_sum_le {ι : Type*} (s : Finset ι) (f : ι → 𝒜) :
    M.stateNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, M.stateNorm (f i) := by
  rw [stateNorm, map_sum]
  exact M.snorm_sum_le s _

/-- **The inner product of the two players' vectors** is the quadratic form of their product,
for a self-adjoint first operator. -/
theorem inner_πA_πB {q : 𝒜} (hq : star q = q) (r : ℬ) :
    ⟪M.π (M.πA q) M.ψ, M.π (M.πB r) M.ψ⟫_ℂ = ⟪M.ψ, M.π (M.πA q * M.πB r) M.ψ⟫_ℂ := by
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
    ← map_star M.π, ← map_star M.πA, hq, map_mul]
  rfl

variable {X : Type*} [Fintype X]

/-- **The state-dependent distance** of two families of the first player's operators, relative
to a question distribution `μ`: blueprint `def:state-distance`. -/
def stateDist (μ : X → ℝ) (A B : X → 𝒜) : ℝ :=
  ∑ x, μ x * M.stateSqNorm (A x - B x)

theorem stateDist_nonneg {μ : X → ℝ} (hμ : ∀ x, 0 ≤ μ x) (A B : X → 𝒜) :
    0 ≤ M.stateDist μ A B :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hμ x) (M.stateSqNorm_nonneg _)

section POVMs

variable [PartialOrder 𝒜] {A : Type*} [Fintype A]

/-- **The same distance for families indexed by answers as well.** -/
def povmStateDist (μ : X → ℝ) (MA NA : X → POVMIn A 𝒜) : ℝ :=
  ∑ x, μ x * ∑ a, M.stateSqNorm ((MA x).op a - (NA x).op a)

/-- **From POVM elements to generalized observables**, blueprint `lem:qld-povm-to-obs`: the
weighting costs a factor `|𝒜|`, from Cauchy--Schwarz over the outcome set. -/
theorem stateDist_obsOf_le {μ : X → ℝ} (hμ0 : ∀ x, 0 ≤ μ x) (MA NA : X → POVMIn A 𝒜)
    (α : A → ℂ) (hα : ∀ a, ‖α a‖ ≤ 1) :
    M.stateDist μ (fun x => pvmObs (MA x).op α) (fun x => pvmObs (NA x).op α)
      ≤ (Fintype.card A : ℝ) * M.povmStateDist μ MA NA := by
  classical
  rw [povmStateDist, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [← mul_assoc, mul_comm ((Fintype.card A : ℝ)) (μ x), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (hμ0 x)
  have hsub : pvmObs (MA x).op α - pvmObs (NA x).op α
      = ∑ a, α a • ((MA x).op a - (NA x).op a) := by
    rw [pvmObs, pvmObs, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => (smul_sub _ _ _).symm
  have htri : M.stateNorm (pvmObs (MA x).op α - pvmObs (NA x).op α)
      ≤ ∑ a, M.stateNorm ((MA x).op a - (NA x).op a) := by
    rw [hsub]
    refine (M.stateNorm_sum_le Finset.univ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [M.stateNorm_smul]
    calc ‖α a‖ * M.stateNorm _ ≤ 1 * M.stateNorm _ :=
          mul_le_mul_of_nonneg_right (hα a) (M.stateNorm_nonneg _)
      _ = M.stateNorm _ := one_mul _
  calc M.stateSqNorm (pvmObs (MA x).op α - pvmObs (NA x).op α)
      ≤ (∑ a, M.stateNorm ((MA x).op a - (NA x).op a)) ^ 2 :=
        pow_le_pow_left₀ (M.stateNorm_nonneg _) htri 2
    _ ≤ (Fintype.card A : ℝ) * ∑ a, M.stateNorm ((MA x).op a - (NA x).op a) ^ 2 :=
        sq_sum_le_card_mul_sum_sq _ (fun a => M.stateNorm_nonneg _)
    _ = (Fintype.card A : ℝ) * ∑ a, M.stateSqNorm ((MA x).op a - (NA x).op a) := rfl

end POVMs

/-- **Averaging preserves closeness**, blueprint `lem:qld-averaging`. -/
theorem stateSqNorm_avg_le {μ : X → ℝ} (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (A B : X → 𝒜) (α : X → ℂ) (hα : ∀ x, ‖α x‖ ≤ 1) :
    M.stateSqNorm ((∑ x, ((μ x : ℂ) * α x) • A x) - ∑ x, ((μ x : ℂ) * α x) • B x)
      ≤ M.stateDist μ A B := by
  classical
  have hsub : (∑ x, ((μ x : ℂ) * α x) • A x) - (∑ x, ((μ x : ℂ) * α x) • B x)
      = ∑ x, ((μ x : ℂ) * α x) • (A x - B x) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => (smul_sub _ _ _).symm
  have htri : M.stateNorm (∑ x, ((μ x : ℂ) * α x) • (A x - B x))
      ≤ ∑ x, μ x * M.stateNorm (A x - B x) := by
    refine (M.stateNorm_sum_le Finset.univ _).trans (Finset.sum_le_sum fun x _ => ?_)
    rw [M.stateNorm_smul]
    refine mul_le_mul_of_nonneg_right ?_ (M.stateNorm_nonneg _)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hμ0 x)]
    calc μ x * ‖α x‖ ≤ μ x * 1 := mul_le_mul_of_nonneg_left (hα x) (hμ0 x)
      _ = μ x := mul_one _
  have hjensen : ∑ x, μ x * M.stateNorm (A x - B x) ≤ Real.sqrt (M.stateDist μ A B) := by
    have h := sum_mul_sqrt_le (Finset.univ : Finset X) μ
      (fun x => M.stateSqNorm (A x - B x)) hμ0 (fun x => M.stateSqNorm_nonneg _)
    rw [hμ1, Real.sqrt_one, one_mul] at h
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun x _ => ?_)) h
    rw [M.sqrt_stateSqNorm]
  have hd : 0 ≤ M.stateDist μ A B := M.stateDist_nonneg hμ0 A B
  rw [hsub]
  calc M.stateSqNorm (∑ x, ((μ x : ℂ) * α x) • (A x - B x))
      ≤ Real.sqrt (M.stateDist μ A B) ^ 2 :=
        pow_le_pow_left₀ (M.stateNorm_nonneg _) (htri.trans hjensen) 2
    _ = M.stateDist μ A B := Real.sq_sqrt hd

end BipartiteModel

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

/-- **The matrix state norm is that of the tensor-product model.** -/
theorem stateNorm_eq_tensor [DecidableEq dA] (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) :
    stateNorm ψ M = (BipartiteModel.tensor ψ).stateNorm M :=
  rfl

theorem stateSqNorm_eq_tensor [DecidableEq dA] (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) :
    stateSqNorm ψ M = (BipartiteModel.tensor ψ).stateSqNorm M :=
  rfl

/-- **The squared norm is the blueprint's quadratic form**, as a complex number:
`⟨ψ| M† M ⊗ Id |ψ⟩` is real and equal to `stateSqNorm ψ M`. It is what makes the Lean definition
and `def:state-distance`'s spelling the same object rather than informally the same. The complex
form is what a positivity hypothesis on a linear functional wants. -/
theorem quadForm_eq (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) :
    star ψ ⬝ᵥ ((((Mᴴ * M) ⊗ₖ (1 : Matrix dB dB ℂ))) *ᵥ ψ) = (stateSqNorm ψ M : ℂ) := by
  classical
  rw [stateSqNorm_eq_tensor, ← (BipartiteModel.tensor ψ).inner_stateSqNorm M]
  show _ = (((Mᴴ * M) ⊗ₖ (1 : Matrix dB dB ℂ)) *ᵥ ψ) ⬝ᵥ star ψ
  rw [dotProduct_comm]

/-- The real form of `quadForm_eq`, which is how `def:state-distance` is written. -/
theorem stateSqNorm_eq (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) :
    stateSqNorm ψ M
      = (star ψ ⬝ᵥ ((((Mᴴ * M) ⊗ₖ (1 : Matrix dB dB ℂ))) *ᵥ ψ)).re := by
  rw [quadForm_eq, Complex.ofReal_re]

theorem stateSqNorm_nonneg (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) : 0 ≤ stateSqNorm ψ M := by
  classical
  exact (BipartiteModel.tensor ψ).stateSqNorm_nonneg M

/-- **The state-dependent distance** of two families of operators on Alice's factor, relative to
a question distribution `μ` and the state `ψ`: blueprint `def:state-distance`. -/
noncomputable def stateDist (μ : X → ℝ) (ψ : dA × dB → ℂ) (A B : X → Matrix dA dA ℂ) : ℝ :=
  ∑ x, μ x * stateSqNorm ψ (A x - B x)

/-- `A ≈_δ B` on `ψ`, relative to `μ`. -/
def IsStateClose (μ : X → ℝ) (ψ : dA × dB → ℂ) (δ : ℝ) (A B : X → Matrix dA dA ℂ) : Prop :=
  stateDist μ ψ A B ≤ δ

section POVMs

open scoped MatrixOrder

variable {A : Type*} [Fintype A] [DecidableEq A] [DecidableEq dA]

/-- **The same distance for families indexed by answers as well**, which is the form the
consistency statements take: the outcome sum is inside the question average. -/
noncomputable def povmStateDist (μ : X → ℝ) (ψ : dA × dB → ℂ) (M N : X → POVM A dA) : ℝ :=
  ∑ x, μ x * ∑ a, stateSqNorm ψ (((M x).mats a).val - ((N x).mats a).val)

/-- `M_a ≈_δ N_a` on `ψ`, relative to `μ`. -/
def IsPOVMStateClose (μ : X → ℝ) (ψ : dA × dB → ℂ) (δ : ℝ) (M N : X → POVM A dA) : Prop :=
  povmStateDist μ ψ M N ≤ δ

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
      ≤ (Fintype.card A : ℝ) * povmStateDist μ ψ M N :=
  (BipartiteModel.tensor ψ).stateDist_obsOf_le hμ0 (fun x => (M x).toIn) (fun x => (N x).toIn)
    α hα

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

/-- **Bob's norm is the first player's norm in the swapped tensor-product model.** -/
theorem norm_stateVecB_eq_tensor (ψ : dA × dB → ℂ) (N : Matrix dB dB ℂ) :
    ‖stateVecB ψ N‖ = (BipartiteModel.tensor ψ).swap.stateNorm N :=
  rfl

theorem normSq_stateVecB_eq_tensor (ψ : dA × dB → ℂ) (N : Matrix dB dB ℂ) :
    ‖stateVecB ψ N‖ ^ 2 = (BipartiteModel.tensor ψ).swap.stateSqNorm N :=
  rfl

omit [DecidableEq dB] in
@[simp] theorem stateVecB_smul (ψ : dA × dB → ℂ) (c : ℂ) (N : Matrix dB dB ℂ) :
    stateVecB ψ (c • N) = c • stateVecB ψ N := by
  show WithLp.toLp 2 _ = c • WithLp.toLp 2 _
  rw [Matrix.kronecker_smul, Matrix.smul_mulVec]
  rfl

omit [DecidableEq dB] in
theorem stateVecB_sum {ι : Type*} (ψ : dA × dB → ℂ) (t : Finset ι) (f : ι → Matrix dB dB ℂ) :
    stateVecB ψ (∑ i ∈ t, f i) = ∑ i ∈ t, stateVecB ψ (f i) := by
  classical
  induction t using Finset.induction with
  | empty => simp [stateVecB]
  | insert i t hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih, stateVecB, stateVecB, stateVecB,
        Matrix.kronecker_add, Matrix.add_mulVec]
      rfl

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
self-adjoint `Q`: the inner product of the two players' vectors in the tensor-product model. -/
theorem inner_stateVec_stateVecB (ψ : dA × dB → ℂ) {Q : Matrix dA dA ℂ} (hQ : Qᴴ = Q)
    (R : Matrix dB dB ℂ) :
    inner ℂ (stateVec ψ Q) (stateVecB ψ R) = star ψ ⬝ᵥ ((Q ⊗ₖ R) *ᵥ ψ) := by
  have h := (BipartiteModel.tensor ψ).inner_πA_πB (q := Q) hQ R
  refine h.trans ?_
  show ((aOp Q * bOp R) *ᵥ ψ) ⬝ᵥ star ψ = _
  rw [aOp, bOp, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul, dotProduct_comm]

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
  exact (BipartiteModel.tensor ψ).stateSqNorm_avg_le hμ0 hμ1 A B α hα

end MIPRE

end
