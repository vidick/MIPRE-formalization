/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Basic/
QuantumState.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.Pasting

@[expose] public section

/-!
# The symmetric model: the state, the placements and the swap symmetry

This is the base file of the port of the vendored low-individual-degree test
(`MIPRE/Background/LIDT/MIPStarRE/LDT/`) from finite-dimensional matrices to a vector state on a
Hilbert space (`planning/c6b-plan.md`, milestone M0, and its section "Port conventions"). It is
the counterpart of `MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/QuantumState.lean`.

The vendored development works with a density matrix `ψ` on `ι × ι`, places a local operator
`A : Op ι` on the two tensor factors as `leftTensor A = A ⊗ 1` and `rightTensor A = 1 ⊗ A`, and
assumes, for its symmetric strategies, that `ψ` is fixed by the swap of the two factors. Here a
**symmetric model** `SymModel 𝔓 K` is

* a C*-algebra `𝔓` of local operators (the vendored `Op ι`), with its order;
* a Hilbert space `K` and a unit vector `Ψ ∈ K` (the state);
* a ⋆-homomorphism `L : 𝔓 →⋆ₐ[ℂ] (K →L[ℂ] K)`, the first player's placement (`leftTensor`);
* a self-inverse isometry `J` of `K` fixing `Ψ`, whose conjugation `flip` carries `L` to the
  second player's placement `R := flip ∘ L` (`rightTensor`), and such that the two placements
  commute.

Joint operators (the vendored `Op (ι × ι)`) are elements of `K →L[ℂ] K`, and the expectation is
`ev X = Re ⟪Ψ, X Ψ⟫ = Op.qform Ψ X` (`MIPRE/Foundations/OpCalculus.lean`), so the linearity,
monotonicity and positivity of the vendored `ev` are those of `Op.qform`.

The vendored swap symmetry (`PermInvState`, `swapDensity`, the `*_of_density_fixed` lemmas of
`LDT/Test/StrategyCore.lean`) is a hypothesis on a strategy there; here it is three theorems of
the structure (`reports/c6b-paper-proofs.md`, §4.1 and Theorem B):

* `ev_flip : ev (flip X) = ev X`, since `J` fixes `Ψ`;
* `ev_L_eq_ev_R : ev (L x) = ev (R x)`, the vendored `PermInvState.swap_ev`;
* `ev_L_mul_R_comm : ev (L x * R y) = ev (L y * R x)`, the vendored
  `ev_opTensor_swap_of_density_fixed`.

The model is a bipartite model of the repository (`toBipartite`, with `H := K`, `π := id`,
`πA := L`, `πB := R`), so the state calculus of `MIPRE/Foundations/` applies to it unchanged.

Every operator-positivity lemma of the port is proved here, in a file that imports only
Foundations and the Mathlib they import, and is applied downstream: positivity on `K →L[ℂ] K`
is the expensive part of elaboration, and it roughly doubles under the wholesale `import Mathlib`
of the vendored classical layer (`planning/c6b-plan.md`, §5).

## Translation

`QuantumState (ι × ι)` ψ ↦ `S : SymModel 𝔓 K`; `ev ψ X` ↦ `S.ev X`; `leftTensor A` ↦ `S.L A`;
`rightTensor A` ↦ `S.R A`; `opTensor A B` ↦ `S.opTensor A B = S.L A * S.R B`; `ᴴ` ↦ `star`;
`swapDensity` ↦ `S.flip`. Lemmas keep their vendored names, as `SymModel` lemmas
(`S.leftTensor_mul_leftTensor`, stated with `S.L`).

## Ported here from other vendored files

So that every positivity proof sits in this file, the following are ported here rather than in
the counterparts of their vendored files: from `LDT/Basic/OperatorExpectations.lean`, `ev_add`,
`ev_sub`, `ev_scale`, `ev_real_smul`, `ev_zero`, `ev_opTensor`, `ev_one_of_isNormalized`,
`ev_adjoint_self_nonneg`, `ev_finset_sum`, `ev_sum`, `ev_nonneg_of_psd`, `ev_mono`,
`ev_conjTranspose`, `ev_mul_comm_of_hermitian`, `ev_mul_comm_of_psd`,
`ev_conjTranspose_mul_comm`; from `LDT/Basic/TensorPlacement.lean`, `leftTensor_finset_sum`,
`rightTensor_finset_sum`, `leftTensor_nonneg`, `rightTensor_nonneg`, `leftTensor_le_one`,
`rightTensor_le_one`; from `LDT/Test/StrategyCore.lean`, `swapDensity_opTensor`,
`ev_swapDensity_of_density_fixed`, `ev_opTensor_swap_of_density_fixed`; from
`Quantum/FiniteMatrix/Order.lean`, `sq_le_self` (for any C*-algebra).

## Not ported

Matrix-only or density-only declarations of the vendored file, each replaced by the model:

- `QuantumState`: replaced by `SymModel`; the state is the vector `Ψ`, not a density matrix.
- `QuantumState.IsNormalized.nonempty`: supplies `Nonempty ι` to the normalized trace, which
  the model does not have; `K` contains the unit vector `Ψ`.
- `pureDensity`: the scaled rank-one density of a vector; the state is a vector here.
- `swapVector`: replaced by the field `J`.
- `swapVector_swapVector`: replaced by the field `J_J`.
- `PureState`: the state is a unit vector already (`Ψ`, `Ψ_norm`).
- `PureState.basis_unit`: a coordinate vector of `ι → ℂ`; no coordinates here.
- `PureState.basis`: a coordinate vector of `ι → ℂ`; no coordinates here.
- `PureState.density`: density of a vector; no density here.
- `PureState.density_psd`: density of a vector; no density here.
- `PureState.toQuantumState`: the coercion of a vector to a density; no density here.
- `PureState.coe_density`: the coercion of a vector to a density; no density here.
- `PureState.normalizedTrace_density`: normalized trace; replaced by `Ψ_norm` and
  `ev_one_of_isNormalized`.
- `PureState.toQuantumState_isNormalized`: replaced by `isNormalized`.
- `PureState.normalizedTrace_density_mul`: normalized trace of `ρ X`; replaced by
  `ev_eq_re_inner`, which holds by definition.
- `PureState.IsSwapInvariant`: replaced by the field `J_Ψ`.
- `leftTensor`: replaced by the field `L`.
- `rightTensor`: replaced by `R`.
- `normalizedTrace_opTensor`: the model has no trace.
- `QuantumState.tensor`: the tensor product of two states; the model has one state and no
  tensor product of Hilbert spaces.
- `QuantumState.tensor_density`: as `QuantumState.tensor`.
- `QuantumState.tensor_isNormalized`: as `QuantumState.tensor`.
-/

namespace MIPRE.LIDT.Co

open scoped InnerProductSpace

/-- **A symmetric model**: a unit vector `Ψ` in a Hilbert space `K`, a ⋆-homomorphism `L` from a
C*-algebra `𝔓` of local operators into the operators on `K` (the first player's placement), and
a self-inverse isometry `J` of `K` fixing `Ψ` whose conjugation carries `L` to an operator family
commuting with `L` (the second player's placement `R`). -/
structure SymModel (𝔓 : Type*) [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
    (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] where
  /-- The state. -/
  Ψ : K
  /-- The state is a unit vector (the vendored `QuantumState.IsNormalized`). -/
  Ψ_norm : ‖Ψ‖ = 1
  /-- The first player's placement (the vendored `leftTensor`). -/
  L : 𝔓 →⋆ₐ[ℂ] (K →L[ℂ] K)
  /-- The flip of the two players (the vendored `swapVector`). -/
  J : K ≃ₗᵢ[ℂ] K
  /-- The flip is an involution. -/
  J_J : ∀ v, J (J v) = v
  /-- The state is symmetric (the vendored `PureState.IsSwapInvariant`). -/
  J_Ψ : J Ψ = Ψ
  /-- The two placements commute. -/
  commute : ∀ x y : 𝔓, Commute (L x) (J.conjStarAlgEquiv (L y))

/-- An operator between `0` and `1` dominates its square: `X (1 - X)` is a product of commuting
positive elements. -/
theorem sq_le_self {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {X : A}
    (hX : 0 ≤ X) (hXle : X ≤ 1) : X * X ≤ X := by
  have hnonneg : 0 ≤ X * (1 - X) :=
    ((Commute.one_right X).sub_right (Commute.refl X)).mul_nonneg hX (sub_nonneg.2 hXle)
  rw [mul_sub, mul_one] at hnonneg
  exact sub_nonneg.1 hnonneg

namespace SymModel

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (S : SymModel 𝔓 K)

/-! ## The flip and the second placement -/

/-- The flip of the joint operators, `X ↦ J X J` (the vendored `swapDensity`). -/
noncomputable def flip : (K →L[ℂ] K) ≃⋆ₐ[ℂ] (K →L[ℂ] K) := S.J.conjStarAlgEquiv

/-- The second player's placement `R x = J (L x) J` (the vendored `rightTensor`). -/
noncomputable def R : 𝔓 →⋆ₐ[ℂ] (K →L[ℂ] K) := S.flip.toStarAlgHom.comp S.L

theorem R_apply (x : 𝔓) : S.R x = S.flip (S.L x) := rfl

theorem J_symm (v : K) : S.J.symm v = S.J v := by
  rw [LinearIsometryEquiv.symm_apply_eq, S.J_J]

theorem flip_apply (X : K →L[ℂ] K) (v : K) : S.flip X v = S.J (X (S.J v)) := by
  simp [flip, S.J_symm]

theorem flip_flip (X : K →L[ℂ] K) : S.flip (S.flip X) = X := by
  ext v
  simp [flip_apply, S.J_J]

theorem flip_L (x : 𝔓) : S.flip (S.L x) = S.R x := rfl

theorem flip_R (x : 𝔓) : S.flip (S.R x) = S.L x := by
  rw [R_apply, flip_flip]

/-- The two placements commute. -/
theorem L_comm_R (x y : 𝔓) : Commute (S.L x) (S.R y) := S.commute x y

/-! ## The expectation -/

/-- The expectation `Re ⟪Ψ, X Ψ⟫` of a joint operator (the vendored `ev ψ X = Re τ(ρ X)`). -/
noncomputable def ev (X : K →L[ℂ] K) : ℝ := Op.qform S.Ψ X

/-- The expectation is the real part of the inner product (the vendored
`PureState.ev_eq_re_inner`). -/
theorem ev_eq_re_inner (X : K →L[ℂ] K) : S.ev X = (⟪S.Ψ, X S.Ψ⟫_ℂ).re := rfl

/-- `ev` distributes over addition. -/
theorem ev_add (X Y : K →L[ℂ] K) : S.ev (X + Y) = S.ev X + S.ev Y := Op.qform_add _ X Y

/-- `ev` distributes over subtraction. -/
theorem ev_sub (X Y : K →L[ℂ] K) : S.ev (X - Y) = S.ev X - S.ev Y := Op.qform_sub _ X Y

/-- `ev` commutes with complex scalar multiplication by a real number. -/
theorem ev_scale (c : ℝ) (X : K →L[ℂ] K) : S.ev ((c : ℂ) • X) = c * S.ev X :=
  Op.qform_smul_real _ c X

/-- `ev` commutes with the real scalar action on operators. -/
theorem ev_real_smul (c : ℝ) (X : K →L[ℂ] K) : S.ev (c • X) = c * S.ev X := by
  rw [← Complex.coe_smul]
  exact S.ev_scale c X

/-- `ev` of the zero operator is zero. -/
theorem ev_zero : S.ev 0 = 0 := Op.qform_zero _

/-- `ev` distributes over finite sums. -/
theorem ev_finset_sum {α : Type*} (s : Finset α) (f : α → K →L[ℂ] K) :
    S.ev (∑ a ∈ s, f a) = ∑ a ∈ s, S.ev (f a) := Op.qform_sum _ s f

/-- `ev` distributes over univ sums. -/
theorem ev_sum {α : Type*} [Fintype α] (f : α → K →L[ℂ] K) :
    S.ev (∑ a, f a) = ∑ a, S.ev (f a) := S.ev_finset_sum Finset.univ f

/-- The state has unit expectation on the identity (the vendored `QuantumState.IsNormalized`,
`τ(ρ) = 1`). -/
def IsNormalized : Prop := S.ev 1 = 1

/-- A normalized state has unit expectation on the identity operator. -/
@[simp] theorem ev_one_of_isNormalized : S.ev 1 = 1 := Op.qform_one _ S.Ψ_norm

/-- The state of a symmetric model is normalized. -/
theorem isNormalized : S.IsNormalized := S.ev_one_of_isNormalized

/-- `ev` of a positive operator is nonnegative. -/
theorem ev_nonneg_of_psd (X : K →L[ℂ] K) (hX : 0 ≤ X) : 0 ≤ S.ev X :=
  Op.qform_nonneg_of_nonneg _ hX

/-- `ev` is monotone. -/
theorem ev_mono (X Y : K →L[ℂ] K) (h : X ≤ Y) : S.ev X ≤ S.ev Y := Op.qform_mono _ h

/-- `ev (M* M) = ‖M Ψ‖²`. -/
theorem ev_adjoint_self_eq_norm_sq (M : K →L[ℂ] K) : S.ev (star M * M) = ‖M S.Ψ‖ ^ 2 :=
  (Op.snorm_sq_eq_qform S.Ψ M).symm

/-- For any operator `M`, `ev (M* M) ≥ 0`. -/
theorem ev_adjoint_self_nonneg (M : K →L[ℂ] K) : 0 ≤ S.ev (star M * M) := by
  rw [ev_adjoint_self_eq_norm_sq]
  positivity

/-! ## The model as a bipartite model -/

/-- The symmetric model as a bipartite model of the repository: `H := K`, `π := id`,
`πA := L`, `πB := R`. -/
noncomputable def toBipartite : BipartiteModel (K →L[ℂ] K) 𝔓 𝔓 where
  H := K
  ψ := S.Ψ
  π := StarAlgHom.id ℂ (K →L[ℂ] K)
  πA := S.L
  πB := S.R
  commute := S.L_comm_R

@[simp] theorem toBipartite_ψ : S.toBipartite.ψ = S.Ψ := rfl

theorem toBipartite_ψ_norm : ‖S.toBipartite.ψ‖ = 1 := S.Ψ_norm

@[simp] theorem toBipartite_π (X : K →L[ℂ] K) : S.toBipartite.π X = X := rfl

@[simp] theorem toBipartite_πA (x : 𝔓) : S.toBipartite.πA x = S.L x := rfl

@[simp] theorem toBipartite_πB (x : 𝔓) : S.toBipartite.πB x = S.R x := rfl

/-- The quadratic form of the bipartite model is `ev`. -/
theorem toBipartite_qform (X : K →L[ℂ] K) : S.toBipartite.qform X = S.ev X := rfl

/-- The state norm of the bipartite model is `‖X Ψ‖`. -/
theorem toBipartite_snorm (X : K →L[ℂ] K) : S.toBipartite.snorm X = ‖X S.Ψ‖ := rfl

/-- Taking the adjoint does not change `ev`. -/
theorem ev_conjTranspose (X : K →L[ℂ] K) : S.ev (star X) = S.ev X :=
  S.toBipartite.qform_star X

/-- `ev (A B) = ev (B A)` for self-adjoint `A` and `B`. -/
theorem ev_mul_comm_of_hermitian (A B : K →L[ℂ] K) (hA : star A = A) (hB : star B = B) :
    S.ev (A * B) = S.ev (B * A) := by
  rw [← S.ev_conjTranspose (A * B), star_mul, hA, hB]

/-- `ev` commutes on positive operators. -/
theorem ev_mul_comm_of_psd (A B : K →L[ℂ] K) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    S.ev (A * B) = S.ev (B * A) :=
  S.ev_mul_comm_of_hermitian A B (IsSelfAdjoint.of_nonneg hA).star_eq
    (IsSelfAdjoint.of_nonneg hB).star_eq

/-- Cross-term identity: `ev (B* A) = ev (A* B)`. -/
theorem ev_conjTranspose_mul_comm (A B : K →L[ℂ] K) :
    S.ev (star B * A) = S.ev (star A * B) := by
  rw [← S.ev_conjTranspose (star A * B), star_mul, star_star]

/-! ## The swap symmetry -/

/-- **The flip fixes the state**: `ev (J X J) = ev X`. -/
theorem ev_flip (X : K →L[ℂ] K) : S.ev (S.flip X) = S.ev X := by
  rw [ev_eq_re_inner, ev_eq_re_inner, flip_apply, S.J_Ψ]
  have h : ⟪S.Ψ, S.J (X S.Ψ)⟫_ℂ = ⟪S.J S.Ψ, S.J (X S.Ψ)⟫_ℂ := by rw [S.J_Ψ]
  rw [h, LinearIsometryEquiv.inner_map_map]

/-- **The two placements have the same expectations** (the vendored `PermInvState.swap_ev`). -/
theorem ev_L_eq_ev_R (x : 𝔓) : S.ev (S.L x) = S.ev (S.R x) := by
  rw [← S.ev_flip (S.L x), flip_L]

/-- **The expectation of a product placement is symmetric** (the vendored
`ev_opTensor_swap_of_density_fixed`). -/
theorem ev_L_mul_R_comm (x y : 𝔓) : S.ev (S.L x * S.R y) = S.ev (S.L y * S.R x) := by
  rw [← S.ev_flip, map_mul, flip_L, flip_R, (S.L_comm_R y x).eq]

/-- The flip preserves `ev` (the vendored `ev_swapDensity_of_density_fixed`, where the fixed
density was a hypothesis). -/
theorem ev_swapDensity_of_density_fixed (Z : K →L[ℂ] K) : S.ev (S.flip Z) = S.ev Z :=
  S.ev_flip Z

/-! ## Tensor placement -/

/-- The product placement `A ⊗ B = L A * R B` (the vendored Kronecker product). -/
noncomputable abbrev opTensor (A B : 𝔓) : K →L[ℂ] K := S.L A * S.R B

/-- Expectation of a tensor product can be written using left/right placements. -/
theorem ev_opTensor (A B : 𝔓) : S.ev (S.opTensor A B) = S.ev (S.L A * S.R B) := rfl

/-- The flip exchanges the factors of a product placement. -/
theorem swapDensity_opTensor (X Y : 𝔓) : S.flip (S.opTensor X Y) = S.opTensor Y X := by
  rw [opTensor, map_mul, flip_L, flip_R]
  exact (S.L_comm_R Y X).eq.symm

/-- The expectation of a product placement is symmetric in its factors. -/
theorem ev_opTensor_swap_of_density_fixed (X Y : 𝔓) :
    S.ev (S.opTensor X Y) = S.ev (S.opTensor Y X) :=
  S.ev_L_mul_R_comm X Y

/-- Left placement of the identity is the identity. -/
theorem leftTensor_one : S.L 1 = 1 := map_one S.L

/-- Right placement of the identity is the identity. -/
theorem rightTensor_one : S.R 1 = 1 := map_one S.R

/-- Local placements multiply to the product placement. -/
theorem leftTensor_mul_rightTensor_eq_opTensor (A B : 𝔓) :
    S.L A * S.R B = S.opTensor A B := rfl

/-- `R B * L A = A ⊗ B`. -/
theorem rightTensor_mul_leftTensor_eq_opTensor (A B : 𝔓) :
    S.R B * S.L A = S.opTensor A B := (S.L_comm_R A B).eq.symm

/-- `L A * L B = L (A * B)`. -/
theorem leftTensor_mul_leftTensor (A B : 𝔓) : S.L A * S.L B = S.L (A * B) :=
  (map_mul S.L A B).symm

/-- `R A * R B = R (A * B)`. -/
theorem rightTensor_mul_rightTensor (A B : 𝔓) : S.R A * S.R B = S.R (A * B) :=
  (map_mul S.R A B).symm

/-- Multiplying a left placement into a product placement only affects the left factor. -/
theorem leftTensor_mul_opTensor (A B C : 𝔓) :
    S.L A * S.opTensor B C = S.opTensor (A * B) C :=
  (mul_assoc _ _ _).symm.trans (congrArg (· * S.R C) (S.L.map_mul A B).symm)

/-- Multiplying a product placement by a left placement only affects the left factor. -/
theorem opTensor_mul_leftTensor (A B C : 𝔓) :
    S.opTensor A C * S.L B = S.opTensor (A * B) C := by
  rw [opTensor, opTensor, mul_assoc, ← (S.L_comm_R B C).eq, ← mul_assoc,
    leftTensor_mul_leftTensor]

/-- Multiplying a right placement into a product placement only affects the right factor. -/
theorem rightTensor_mul_opTensor (A B C : 𝔓) :
    S.R A * S.opTensor B C = S.opTensor B (A * C) := by
  rw [opTensor, opTensor, ← mul_assoc, ← (S.L_comm_R B A).eq, mul_assoc,
    rightTensor_mul_rightTensor]

/-- Product placements multiply factorwise. -/
theorem opTensor_mul (A₁ A₂ B₁ B₂ : 𝔓) :
    S.opTensor A₁ B₁ * S.opTensor A₂ B₂ = S.opTensor (A₁ * A₂) (B₁ * B₂) :=
  S.toBipartite.πA_mul_πB_mul A₁ A₂ B₁ B₂

/-- Scalar multiplication commutes with left placement. -/
theorem leftTensor_smul (c : ℂ) (A : 𝔓) : c • S.L A = S.L (c • A) := (map_smul S.L c A).symm

/-- Powers commute with left placement. -/
theorem leftTensor_pow (A : 𝔓) (n : ℕ) : S.L A ^ n = S.L (A ^ n) := (map_pow S.L A n).symm

/-- The adjoint distributes over a product placement. -/
theorem conjTranspose_opTensor (A B : 𝔓) :
    star (S.opTensor A B) = S.opTensor (star A) (star B) :=
  S.toBipartite.star_πA_mul_πB A B

/-- The adjoint commutes with left placement. (The vendored `@[simp]` is dropped: it would loop
with `map_star`.) -/
theorem leftTensor_conjTranspose (A : 𝔓) : star (S.L A) = S.L (star A) := (map_star S.L A).symm

/-- The adjoint commutes with right placement. -/
theorem rightTensor_conjTranspose (B : 𝔓) : star (S.R B) = S.R (star B) :=
  (map_star S.R B).symm

/-- `opTensor` is linear in the left factor: subtraction. -/
theorem opTensor_sub_left (A B C : 𝔓) :
    S.opTensor A C - S.opTensor B C = S.opTensor (A - B) C :=
  (sub_mul _ _ _).symm.trans (congrArg (· * S.R C) (map_sub S.L A B).symm)

/-- Left placement commutes with subtraction. -/
theorem leftTensor_sub (A B : 𝔓) : S.L A - S.L B = S.L (A - B) := (map_sub S.L A B).symm

/-- Right placement commutes with subtraction. -/
theorem rightTensor_sub (A B : 𝔓) : S.R A - S.R B = S.R (A - B) := (map_sub S.R A B).symm

/-- `opTensor` is linear in the left factor: real scalar multiplication. -/
theorem opTensor_smul_left_error (c : ℝ) (A B : 𝔓) :
    S.opTensor (c • A) B = c • S.opTensor A B := by
  rw [← Complex.coe_smul, ← Complex.coe_smul, opTensor, opTensor, map_smul, smul_mul_assoc]

/-- `opTensor` is linear in the right factor: real scalar multiplication. -/
theorem opTensor_smul_right_error (c : ℝ) (A B : 𝔓) :
    S.opTensor A (c • B) = c • S.opTensor A B := by
  rw [← Complex.coe_smul, ← Complex.coe_smul, opTensor, opTensor, map_smul, mul_smul_comm]

/-- `opTensor` is additive in the left factor. -/
theorem opTensor_add_left_local (A B C : 𝔓) :
    S.opTensor (A + B) C = S.opTensor A C + S.opTensor B C :=
  (congrArg (· * S.R C) (S.L.map_add A B)).trans (add_mul _ _ _)

/-- `opTensor` is additive in the right factor. -/
theorem opTensor_add_right_local (A B C : 𝔓) :
    S.opTensor A (B + C) = S.opTensor A B + S.opTensor A C :=
  (congrArg (S.L A * ·) (S.R.map_add B C)).trans (mul_add _ _ _)

/-- Left placement commutes with finite sums. -/
theorem leftTensor_finset_sum {α : Type*} (s : Finset α) (f : α → 𝔓) :
    ∑ a ∈ s, S.L (f a) = S.L (∑ a ∈ s, f a) := (map_sum S.L f s).symm

/-- Right placement commutes with finite sums. -/
theorem rightTensor_finset_sum {α : Type*} (s : Finset α) (f : α → 𝔓) :
    ∑ a ∈ s, S.R (f a) = S.R (∑ a ∈ s, f a) := (map_sum S.R f s).symm

/-- Pull a finite sum out of the left factor of `opTensor`. -/
theorem opTensor_sum_left_finset {α : Type*} (s : Finset α) (f : α → 𝔓) (B : 𝔓) :
    S.opTensor (∑ a ∈ s, f a) B = ∑ a ∈ s, S.opTensor (f a) B :=
  (congrArg (· * S.R B) (map_sum S.L f s)).trans (Finset.sum_mul _ _ _)

/-- Pull a finite sum out of the right factor of `opTensor`. -/
theorem opTensor_sum_right_finset {α : Type*} (A : 𝔓) (s : Finset α) (f : α → 𝔓) :
    S.opTensor A (∑ a ∈ s, f a) = ∑ a ∈ s, S.opTensor A (f a) :=
  (congrArg (S.L A * ·) (map_sum S.R f s)).trans (Finset.mul_sum _ _ _)

/-- Pull an unindexed finite-type sum out of the left factor of `opTensor`. -/
theorem opTensor_sum_left_univ {α : Type*} [Fintype α] (f : α → 𝔓) (B : 𝔓) :
    S.opTensor (∑ a : α, f a) B = ∑ a : α, S.opTensor (f a) B :=
  S.opTensor_sum_left_finset Finset.univ f B

/-- Pull an unindexed finite-type sum out of the right factor of `opTensor`. -/
theorem opTensor_sum_right_univ {α : Type*} [Fintype α] (A : 𝔓) (f : α → 𝔓) :
    S.opTensor A (∑ a : α, f a) = ∑ a : α, S.opTensor A (f a) :=
  S.opTensor_sum_right_finset A Finset.univ f

/-! ## Positivity of the placements -/

/-- Left placement preserves positivity. -/
theorem leftTensor_nonneg {A : 𝔓} (hA : 0 ≤ A) : 0 ≤ S.L A := map_nonneg S.L hA

/-- Right placement preserves positivity. -/
theorem rightTensor_nonneg {A : 𝔓} (hA : 0 ≤ A) : 0 ≤ S.R A := map_nonneg S.R hA

/-- Left placement is monotone. -/
theorem leftTensor_mono {A₁ A₂ : 𝔓} (hA : A₁ ≤ A₂) : S.L A₁ ≤ S.L A₂ :=
  OrderHomClass.mono S.L hA

/-- Right placement is monotone. -/
theorem rightTensor_mono {B₁ B₂ : 𝔓} (hB : B₁ ≤ B₂) : S.R B₁ ≤ S.R B₂ :=
  OrderHomClass.mono S.R hB

/-- Left placement preserves the bound `≤ 1`. -/
theorem leftTensor_le_one {A : 𝔓} (hA : A ≤ 1) : S.L A ≤ 1 := by
  simpa using S.leftTensor_mono hA

/-- Right placement preserves the bound `≤ 1`. -/
theorem rightTensor_le_one {A : 𝔓} (hA : A ≤ 1) : S.R A ≤ 1 := by
  simpa using S.rightTensor_mono hA

/-- Positivity is preserved by `opTensor`: a product of commuting positive operators. -/
theorem opTensor_nonneg {A B : 𝔓} (hA : 0 ≤ A) (hB : 0 ≤ B) : 0 ≤ S.opTensor A B :=
  (S.L_comm_R A B).mul_nonneg (S.leftTensor_nonneg hA) (S.rightTensor_nonneg hB)

/-- `opTensor` is monotone in the left factor against a positive right factor. -/
theorem opTensor_mono_left {A₁ A₂ B : 𝔓} (hA : A₁ ≤ A₂) (hB : 0 ≤ B) :
    S.opTensor A₁ B ≤ S.opTensor A₂ B := by
  have h := S.opTensor_nonneg (sub_nonneg.2 hA) hB
  rw [← opTensor_sub_left] at h
  exact sub_nonneg.1 h

/-- `opTensor` is monotone in the right factor against a positive left factor. -/
theorem opTensor_mono_right {A B₁ B₂ : 𝔓} (hA : 0 ≤ A) (hB : B₁ ≤ B₂) :
    S.opTensor A B₁ ≤ S.opTensor A B₂ := by
  have h := S.opTensor_nonneg hA (sub_nonneg.2 hB)
  rw [opTensor, map_sub, mul_sub] at h
  exact sub_nonneg.1 h

/-- If `0 ≤ A` and `B ≤ 1`, then `A ⊗ B ≤ A ⊗ 1 = L A`. -/
theorem opTensor_le_leftTensor {A B : 𝔓} (hA : 0 ≤ A) (hB : B ≤ 1) :
    S.opTensor A B ≤ S.L A := by
  simpa [opTensor] using S.opTensor_mono_right hA hB

/-- A product placement of two effects is an effect: `A ⊗ B ≤ L A ≤ 1`. -/
theorem opTensor_le_one {A B : 𝔓} (hA0 : 0 ≤ A) (hA : A ≤ 1) (hB : B ≤ 1) :
    S.opTensor A B ≤ 1 :=
  (S.opTensor_le_leftTensor hA0 hB).trans (S.leftTensor_le_one hA)

end SymModel

end MIPRE.LIDT.Co

end
