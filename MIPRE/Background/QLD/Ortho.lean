/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.StateDistance
import MIPRE.Background.Orthonormalization.Orthogonalization.FinDim.Main

/-!
# Orthonormalization in the vocabulary of the Pauli basis test

Blueprint `cor:ortho-from-consistency` turns bipartite consistency of two POVMs into closeness of
one of them to a *projective* measurement. It rests on `thm:orthonormalization`, which this
repository has through the vendored development, but it is not that theorem restated: the theorem
asks for strict near-projectivity in a normal state and what the appendix has is consistency.

This file is the first half: the **interface**, from near-projectivity in the reduced state to a
projective family close in the state-dependent distance of `def:state-distance`. Nothing in the
repository had called `Orthogonalization.povm_orthogonalization_finDim` before, so the bridge from
`MIPRE.POVM` (matrices) to its vocabulary (continuous linear maps on a Hilbert space) is here.

Three choices worth recording, all of which make the bridge cheaper than it looks:

* **The un-bridged form of the vendored theorem.** `Statement.lean`'s version wants a
  `NormalState` on a `VonNeumannAlgebra`, and Mathlib has no `⊤ : VonNeumannAlgebra H`.
  `FinDim/Main.lean`'s wants only a linear functional with `0 ≤ φ (star x * x)` and `φ 1 = 1`, so
  there is no algebra to construct and no weak-* continuity to prove.
* **Alice's space, not the tensor product.** The blueprint's proof text applies the theorem to the
  algebra `L(H_A) ⊗ Id` inside `L(H_A ⊗ H_B)`; the equivalent move that needs no algebra is to
  work on `H_A` with the *reduced* functional `x ↦ ⟨ψ| x ⊗ Id |ψ⟩`, whose projections then come
  out on `H_A` directly, which is where the conclusion wants them.
* **`quadForm_eq`** says `⟨ψ| M† M ⊗ Id |ψ⟩` *is* `stateSqNorm ψ M` as a complex number, so
  positivity of the functional is immediate and the conclusion translates without a second
  computation.

The second half --- deriving near-projectivity from consistency by the Cauchy--Schwarz step, which
is what makes this a corollary about *consistency* --- is `Consistency.lean`.
-/

namespace MIPRE.QLD

open Finset Matrix Kronecker MIPRE
open scoped ComplexOrder MatrixOrder

variable {A : Type*} [Fintype A] [DecidableEq A]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-! ## Alice's operators as matrices

`Matrix.toEuclideanCLM` is a star-algebra equivalence, so everything below is one of its
structural maps. They are named rather than used through `map_*` because `rw` cannot match a
higher-order pattern against a coercion, and every proof in this file is a rewrite. -/

/-- The matrix a continuous linear map of `EuclideanSpace ℂ dA` is. -/
noncomputable def ofCLM (x : EuclideanSpace ℂ dA →L[ℂ] EuclideanSpace ℂ dA) :
    Matrix dA dA ℂ :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm x

/-- The continuous linear map a matrix is. -/
noncomputable def toCLM (M : Matrix dA dA ℂ) :
    EuclideanSpace ℂ dA →L[ℂ] EuclideanSpace ℂ dA :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) M

@[simp] theorem ofCLM_toCLM (M : Matrix dA dA ℂ) : ofCLM (toCLM M) = M :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm_apply_apply M

theorem ofCLM_add (x y : EuclideanSpace ℂ dA →L[ℂ] EuclideanSpace ℂ dA) :
    ofCLM (x + y) = ofCLM x + ofCLM y := map_add _ _ _

theorem ofCLM_sub (x y : EuclideanSpace ℂ dA →L[ℂ] EuclideanSpace ℂ dA) :
    ofCLM (x - y) = ofCLM x - ofCLM y := map_sub _ _ _

theorem ofCLM_smul (c : ℂ) (x : EuclideanSpace ℂ dA →L[ℂ] EuclideanSpace ℂ dA) :
    ofCLM (c • x) = c • ofCLM x := map_smul _ _ _

theorem ofCLM_mul (x y : EuclideanSpace ℂ dA →L[ℂ] EuclideanSpace ℂ dA) :
    ofCLM (x * y) = ofCLM x * ofCLM y := map_mul _ _ _

theorem ofCLM_one : ofCLM (1 : EuclideanSpace ℂ dA →L[ℂ] EuclideanSpace ℂ dA) = 1 := map_one _

theorem ofCLM_star (x : EuclideanSpace ℂ dA →L[ℂ] EuclideanSpace ℂ dA) :
    ofCLM (star x) = (ofCLM x)ᴴ :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm.map_star' x

theorem ofCLM_sum {ι : Type*} (s : Finset ι)
    (f : ι → EuclideanSpace ℂ dA →L[ℂ] EuclideanSpace ℂ dA) :
    ofCLM (∑ i ∈ s, f i) = ∑ i ∈ s, ofCLM (f i) := map_sum _ _ _

theorem toCLM_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix dA dA ℂ) :
    toCLM (∑ i ∈ s, f i) = ∑ i ∈ s, toCLM (f i) := map_sum _ _ _

theorem toCLM_one : toCLM (1 : Matrix dA dA ℂ) = 1 := map_one _

/-- A positive semidefinite matrix is a positive operator: `toEuclideanCLM` is a star-algebra
equivalence of C*-algebras, so it preserves the order. -/
theorem toCLM_nonneg {M : Matrix dA dA ℂ} (hM : (0 : Matrix dA dA ℂ) ≤ M) :
    0 ≤ toCLM M :=
  map_nonneg _ hM

/-! ## The reduced state -/

/-- **The reduced state** `x ↦ ⟨ψ| x ⊗ Id |ψ⟩` on Alice's operators, as a `ℂ`-linear
functional. -/
noncomputable def redState (ψ : dA × dB → ℂ) :
    (EuclideanSpace ℂ dA →L[ℂ] EuclideanSpace ℂ dA) →ₗ[ℂ] ℂ where
  toFun x := star ψ ⬝ᵥ ((ofCLM x ⊗ₖ (1 : Matrix dB dB ℂ)) *ᵥ ψ)
  map_add' x y := by
    show star ψ ⬝ᵥ ((ofCLM (x + y) ⊗ₖ _) *ᵥ ψ) = _
    rw [ofCLM_add, Matrix.add_kronecker, Matrix.add_mulVec, dotProduct_add]
  map_smul' c x := by
    show star ψ ⬝ᵥ ((ofCLM (c • x) ⊗ₖ _) *ᵥ ψ) = _
    rw [ofCLM_smul, Matrix.smul_kronecker, Matrix.smul_mulVec, dotProduct_smul]
    rfl

@[simp] theorem redState_apply (ψ : dA × dB → ℂ)
    (x : EuclideanSpace ℂ dA →L[ℂ] EuclideanSpace ℂ dA) :
    redState ψ x = star ψ ⬝ᵥ ((ofCLM x ⊗ₖ (1 : Matrix dB dB ℂ)) *ᵥ ψ) := rfl

/-- The reduced state is normalized exactly when `ψ` is a unit vector. -/
theorem redState_one {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) :
    redState ψ 1 = 1 := by
  rw [redState_apply, ofCLM_one, Matrix.one_kronecker_one, Matrix.one_mulVec, hψ]

/-- **The reduced state on a square is the state-dependent squared norm.** -/
theorem redState_star_mul_self (ψ : dA × dB → ℂ)
    (x : EuclideanSpace ℂ dA →L[ℂ] EuclideanSpace ℂ dA) :
    redState ψ (star x * x) = (stateSqNorm ψ (ofCLM x) : ℂ) := by
  rw [redState_apply, ofCLM_mul, ofCLM_star, quadForm_eq]

/-- Hence the reduced state is positive. -/
theorem redState_nonneg (ψ : dA × dB → ℂ)
    (x : EuclideanSpace ℂ dA →L[ℂ] EuclideanSpace ℂ dA) :
    0 ≤ redState ψ (star x * x) := by
  rw [redState_star_mul_self]
  exact Complex.zero_le_real.mpr (stateSqNorm_nonneg ψ _)

/-- **The reduced state on the square of a self-adjoint operator**, which is the form the
vendored theorem's near-projectivity hypothesis takes. -/
theorem redState_mul_self (ψ : dA × dB → ℂ) {M : Matrix dA dA ℂ} (hM : Mᴴ = M) :
    redState ψ (toCLM M * toCLM M) = (stateSqNorm ψ M : ℂ) := by
  have hMM : M * M = Mᴴ * M := by rw [hM]
  rw [redState_apply, ofCLM_mul, ofCLM_toCLM, hMM]
  exact quadForm_eq ψ M

/-! ## The interface -/

omit [DecidableEq A] in
/-- **From near-projectivity to a projective measurement**, in the vocabulary of `MIPRE.POVM` and
`def:state-distance`. This is `thm:orthonormalization` applied on Alice's space with the reduced
state of `ψ`; the hypothesis is its `φ(∑ aᵢ²) > 1 − ε`, which here reads
`∑ₐ ‖(Qₐ ⊗ Id)|ψ⟩‖² > 1 − ε` because the POVM elements are self-adjoint. -/
theorem exists_projective_of_nearProjective {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (Q : POVM A dA) (ε : ℝ) (hε : 1 - ε < ∑ a, stateSqNorm ψ ((Q.mats a).val)) :
    ∃ P : A → Matrix dA dA ℂ,
      (∀ a, (P a)ᴴ = P a) ∧ (∀ a, P a * P a = P a) ∧ (∑ a, P a = 1) ∧
        ∑ a, stateSqNorm ψ ((Q.mats a).val - P a) < 9 * ε := by
  classical
  -- the POVM, as positive operators summing to one
  have hQnn : ∀ a, (0 : Matrix dA dA ℂ) ≤ (Q.mats a).val := fun a =>
    Subtype.coe_le_coe.mpr (Q.nonneg a)
  have ha0 : ∀ a, 0 ≤ toCLM ((Q.mats a).val) := fun a => toCLM_nonneg (hQnn a)
  have ha1 : ∑ a, toCLM ((Q.mats a).val) = 1 := by
    have hone : ∑ a, ((Q.mats a).val) = (1 : Matrix dA dA ℂ) := by
      rw [← AddSubmonoidClass.coe_finsetSum, Q.normalized]
      rfl
    rw [← toCLM_sum, hone, toCLM_one]
  -- each element is self-adjoint, so its square is what the hypothesis measures
  have hsq : ∀ a, redState ψ (toCLM ((Q.mats a).val) * toCLM ((Q.mats a).val))
      = (stateSqNorm ψ ((Q.mats a).val) : ℂ) := fun a =>
    redState_mul_self ψ ((Q.mats a).2 : star ((Q.mats a).val) = (Q.mats a).val)
  -- the hypothesis, in the vendored theorem's form
  have hε' : 1 - ε
      < (redState ψ (∑ a, toCLM ((Q.mats a).val) * toCLM ((Q.mats a).val))).re := by
    rw [map_sum (redState ψ), Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => hsq a,
      ← Complex.ofReal_sum, Complex.ofReal_re]
    exact hε
  obtain ⟨p, hp, hpsum, hbound⟩ := Orthogonalization.povm_orthogonalization_finDim
    (redState ψ) (redState_nonneg ψ) (redState_one hψ)
    (fun a => toCLM ((Q.mats a).val)) ha0 ha1 ε hε'
  refine ⟨fun a => ofCLM (p a), fun a => ?_, fun a => ?_, ?_, ?_⟩
  · have h : ofCLM (star (p a)) = (ofCLM (p a))ᴴ := ofCLM_star (p a)
    rw [show star (p a) = p a from (hp a).isSelfAdjoint] at h
    exact h.symm
  · have h : ofCLM (p a * p a) = ofCLM (p a) * ofCLM (p a) := ofCLM_mul _ _
    rw [show p a * p a = p a from (hp a).isIdempotentElem] at h
    exact h.symm
  · rw [← ofCLM_sum, hpsum, ofCLM_one]
  · refine lt_of_le_of_lt (le_of_eq ?_) hbound
    rw [map_sum (redState ψ), Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [redState_star_mul_self, Complex.ofReal_re, ofCLM_sub, ofCLM_toCLM]

end MIPRE.QLD
