/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import MIPRE.Tactics

@[expose] public section

/-!
# Matrices of operators on a finite direct sum of copies of a Hilbert space

For a complex Hilbert space `H` and a finite type `ι`, the `ℓ²` direct sum of `ι` copies of `H`
is the Hilbert space `H ⊗ ℂ^ι` (`OperatorMatrix.Ampl ι H`, the `ι`-fold *amplification* of
`H`). An `ι × ι` matrix of operators on `H` acts on it by `(M f) i = ∑ j, M i j (f j)`, and
this action is a unital `⋆`-algebra homomorphism from the matrices, with the conjugate
transpose, to the bounded operators, with the adjoint (`OperatorMatrix.toCLMStarAlgHom`). This
is what lets a construction written in the ring of operator matrices, where it is plain
algebra, be read as a statement about operators on a Hilbert space.

Three facts about the embedding of `H` as the `i₀`-th copy (`OperatorMatrix.emb`, the
embedding `ξ ↦ ξ ⊗ e_{i₀}` at a fixed unit vector of the ancilla `ℂ^ι`):

* it is isometric (`inner_emb_emb`, `norm_emb`);
* the compression of the operator of `M` to it is the entry `M i₀ i₀`
  (`inner_emb_toCLM_emb`);
* a diagonal matrix with constant entry `c` acts as `c ⊗ 1`, which the embedding intertwines
  with `c` (`toCLM_diagonal_emb`); such an operator is positive when `c` is
  (`isPositive_toCLM_diagonal`).

These are the finite ancillas of `planning/mipco-track.md` §5, Phase 1: `ι → H` with the
`PiLp 2` structure, in place of a tensor product of Hilbert spaces.
-/

namespace MIPRE

open scoped InnerProductSpace
open Matrix

namespace OperatorMatrix

variable (ι : Type*) (H : Type*)

/-- The `ℓ²` direct sum of `ι` copies of `H`, that is `H ⊗ ℂ^ι`. -/
abbrev Ampl : Type _ := PiLp 2 fun _ : ι => H

variable {ι H} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The operator of a matrix of operators: `(toCLM M f) i = ∑ j, M i j (f j)`. -/
noncomputable def toCLM (M : Matrix ι ι (H →L[ℂ] H)) : Ampl ι H →L[ℂ] Ampl ι H :=
  (PiLp.continuousLinearEquiv 2 ℂ fun _ : ι => H).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun i => ∑ j, M i j ∘L PiLp.proj 2 (fun _ : ι => H) j

omit [DecidableEq ι] [CompleteSpace H] in
@[simp]
theorem toCLM_apply (M : Matrix ι ι (H →L[ℂ] H)) (f : Ampl ι H) (i : ι) :
    toCLM M f i = ∑ j, M i j (f j) := by
  simp [toCLM]

omit [CompleteSpace H] in
theorem toCLM_diagonal_apply (d : ι → H →L[ℂ] H) (f : Ampl ι H) (i : ι) :
    toCLM (diagonal d) f i = d i (f i) := by
  rw [toCLM_apply, Finset.sum_eq_single i]
  · rw [diagonal_apply_eq]
  · intro j _ hj
    rw [diagonal_apply_ne _ (Ne.symm hj), _root_.zero_apply]
  · intro h
    exact absurd (Finset.mem_univ i) h

omit [CompleteSpace H] in
theorem toCLM_one : toCLM (1 : Matrix ι ι (H →L[ℂ] H)) = 1 := by
  ext f i
  rw [← diagonal_one, toCLM_diagonal_apply]
  rfl

omit [DecidableEq ι] [CompleteSpace H] in
theorem toCLM_mul (M N : Matrix ι ι (H →L[ℂ] H)) : toCLM (M * N) = toCLM M * toCLM N := by
  ext f i
  simp only [toCLM_apply, mul_apply_eq_comp, mul_apply, _root_.sum_apply, map_sum]
  exact Finset.sum_comm

omit [DecidableEq ι] [CompleteSpace H] in
theorem toCLM_add (M N : Matrix ι ι (H →L[ℂ] H)) : toCLM (M + N) = toCLM M + toCLM N := by
  ext f i
  simp [Finset.sum_add_distrib]

omit [DecidableEq ι] [CompleteSpace H] in
theorem toCLM_zero : toCLM (0 : Matrix ι ι (H →L[ℂ] H)) = 0 := by
  ext f i
  simp

omit [DecidableEq ι] in
/-- The operator of the conjugate transpose is the adjoint. -/
theorem toCLM_conjTranspose (M : Matrix ι ι (H →L[ℂ] H)) : toCLM Mᴴ = star (toCLM M) := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
  intro f g
  simp only [PiLp.inner_apply, toCLM_apply, conjTranspose_apply, sum_inner, inner_sum,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  exact Finset.sum_comm

omit [CompleteSpace H] in
theorem toCLM_algebraMap (r : ℂ) :
    toCLM (algebraMap ℂ (Matrix ι ι (H →L[ℂ] H)) r) =
      algebraMap ℂ (Ampl ι H →L[ℂ] Ampl ι H) r := by
  ext f i
  rw [algebraMap_eq_diagonal, toCLM_diagonal_apply]
  simp [Algebra.algebraMap_eq_smul_one]

/-- **The action of operator matrices, as a unital `⋆`-algebra homomorphism.** -/
noncomputable def toCLMStarAlgHom :
    Matrix ι ι (H →L[ℂ] H) →⋆ₐ[ℂ] (Ampl ι H →L[ℂ] Ampl ι H) where
  toFun := toCLM
  map_one' := toCLM_one
  map_mul' := toCLM_mul
  map_zero' := toCLM_zero
  map_add' := toCLM_add
  commutes' := toCLM_algebraMap
  map_star' M := by rw [star_eq_conjTranspose, toCLM_conjTranspose]

@[simp]
theorem toCLMStarAlgHom_apply (M : Matrix ι ι (H →L[ℂ] H)) :
    toCLMStarAlgHom (ι := ι) (H := H) M = toCLM M :=
  rfl

theorem toCLM_sum {κ : Type*} (s : Finset κ) (M : κ → Matrix ι ι (H →L[ℂ] H)) :
    toCLM (∑ k ∈ s, M k) = ∑ k ∈ s, toCLM (M k) :=
  map_sum (toCLMStarAlgHom (ι := ι) (H := H)) M s

/-- **The amplification `c ↦ c ⊗ 1`**, the diagonal action of an operator, as a unital
`⋆`-algebra homomorphism. -/
noncomputable def amplify : (H →L[ℂ] H) →⋆ₐ[ℂ] (Ampl ι H →L[ℂ] Ampl ι H) where
  toFun c := toCLM (diagonal fun _ : ι => c)
  map_one' := by rw [diagonal_one, toCLM_one]
  map_mul' c d := by rw [← toCLM_mul, diagonal_mul_diagonal]
  map_zero' := by rw [diagonal_zero, toCLM_zero]
  map_add' c d := by rw [← toCLM_add, diagonal_add]
  commutes' r := by rw [← toCLM_algebraMap, algebraMap_eq_diagonal]; rfl
  map_star' c := by rw [← toCLM_conjTranspose, diagonal_conjTranspose]; rfl

theorem amplify_apply (c : H →L[ℂ] H) :
    (amplify : (H →L[ℂ] H) →⋆ₐ[ℂ] (Ampl ι H →L[ℂ] Ampl ι H)) c =
      toCLM (diagonal fun _ : ι => c) :=
  rfl

/-- The operator of a star projection of matrices is a star projection. -/
theorem isStarProjection_toCLM {P : Matrix ι ι (H →L[ℂ] H)} (hP : IsStarProjection P) :
    IsStarProjection (toCLM P) :=
  hP.map (toCLMStarAlgHom (ι := ι) (H := H))

/-- The operator of a star projection of matrices is positive. -/
theorem isPositive_toCLM_of_isStarProjection {P : Matrix ι ι (H →L[ℂ] H)}
    (hP : IsStarProjection P) : (toCLM P).IsPositive :=
  ContinuousLinearMap.IsPositive.of_isStarProjection (isStarProjection_toCLM hP)

omit [CompleteSpace H] in
/-- The diagonal action of an idempotent operator is idempotent. -/
theorem isIdempotentElem_toCLM_diagonal {c : H →L[ℂ] H} (hc : IsIdempotentElem c) :
    IsIdempotentElem (toCLM (diagonal fun _ : ι => c)) := by
  rw [IsIdempotentElem, ← toCLM_mul, diagonal_mul_diagonal, hc.eq]

/-- The diagonal action `c ⊗ 1` of a positive operator is positive. -/
theorem isPositive_toCLM_diagonal {c : H →L[ℂ] H} (hc : c.IsPositive) :
    (toCLM (diagonal fun _ : ι => c)).IsPositive := by
  rw [ContinuousLinearMap.isPositive_def']
  refine ⟨?_, fun f => ?_⟩
  · rw [IsSelfAdjoint, ← toCLM_conjTranspose, diagonal_conjTranspose]
    congr 2
    funext _
    exact hc.isSelfAdjoint.star_eq
  · rw [ContinuousLinearMap.reApplyInnerSelf_apply, PiLp.inner_apply, map_sum]
    refine Finset.sum_nonneg fun i _ => ?_
    rw [toCLM_diagonal_apply]
    exact hc.re_inner_nonneg_left (f i)

/-! ## The embedding at a coordinate -/

/-- The embedding of `H` as the `i₀`-th copy, `ξ ↦ ξ ⊗ e_{i₀}`. -/
noncomputable def emb (i₀ : ι) : H →L[ℂ] Ampl ι H :=
  (PiLp.continuousLinearEquiv 2 ℂ fun _ : ι => H).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.single ℂ (fun _ : ι => H) i₀

omit [Fintype ι] [CompleteSpace H] in
theorem emb_eq_single (i₀ : ι) (ξ : H) : emb i₀ ξ = PiLp.single 2 i₀ ξ := rfl

omit [Fintype ι] [CompleteSpace H] in
@[simp]
theorem emb_apply_self (i₀ : ι) (ξ : H) : emb i₀ ξ i₀ = ξ := by
  rw [emb_eq_single, PiLp.single_eq_same]

omit [Fintype ι] [CompleteSpace H] in
@[simp]
theorem emb_apply_of_ne {i₀ i : ι} (h : i ≠ i₀) (ξ : H) : emb i₀ ξ i = 0 := by
  rw [emb_eq_single, PiLp.single_eq_of_ne (p := 2) h]

omit [CompleteSpace H] in
theorem inner_emb_emb (i₀ : ι) (ξ η : H) :
    ⟪emb i₀ ξ, emb i₀ η⟫_ℂ = ⟪ξ, η⟫_ℂ := by
  rw [PiLp.inner_apply, Finset.sum_eq_single i₀]
  · simp
  · intro i _ hi
    simp [emb_apply_of_ne hi]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

omit [CompleteSpace H] in
theorem norm_emb (i₀ : ι) (ξ : H) : ‖emb i₀ ξ‖ = ‖ξ‖ := by
  have h := inner_emb_emb i₀ ξ ξ
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h' : ‖emb i₀ ξ‖ ^ 2 = ‖ξ‖ ^ 2 := by exact_mod_cast h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h'

omit [CompleteSpace H] in
/-- The compression of the operator of `M` to the `i₀`-th copy is the entry `M i₀ i₀`. -/
theorem inner_emb_toCLM_emb (M : Matrix ι ι (H →L[ℂ] H)) (i₀ : ι) (ξ η : H) :
    ⟪emb i₀ ξ, toCLM M (emb i₀ η)⟫_ℂ = ⟪ξ, M i₀ i₀ η⟫_ℂ := by
  have hcol : ∀ i, toCLM M (emb i₀ η) i = M i i₀ η := by
    intro i
    rw [toCLM_apply, Finset.sum_eq_single i₀]
    · rw [emb_apply_self]
    · intro j _ hj
      rw [emb_apply_of_ne hj, map_zero]
    · intro h
      exact absurd (Finset.mem_univ i₀) h
  rw [PiLp.inner_apply, Finset.sum_eq_single i₀]
  · rw [hcol, emb_apply_self]
  · intro i _ hi
    rw [emb_apply_of_ne hi, inner_zero_left]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

omit [CompleteSpace H] in
/-- A constant diagonal matrix acts as `c ⊗ 1`, which the embedding intertwines with `c`. -/
theorem toCLM_diagonal_emb (c : H →L[ℂ] H) (i₀ : ι) (ξ : H) :
    toCLM (diagonal fun _ : ι => c) (emb i₀ ξ) = emb i₀ (c ξ) := by
  ext i
  rw [toCLM_diagonal_apply]
  by_cases h : i = i₀
  · subst h
    rw [emb_apply_self, emb_apply_self]
  · rw [emb_apply_of_ne h, emb_apply_of_ne h, map_zero]

end OperatorMatrix

end MIPRE

end
