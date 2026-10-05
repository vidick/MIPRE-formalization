/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Game
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.UnitaryGroup
public import MIPRE.Tactics

@[expose] public section

/-!
# Signed permutations

Paper II, §2.2 (II:1008–1069): the signed permutations of a finite set `Ω`, as combinatorial
data and as matrices.

* `SignedPerm Ω`: a permutation `σ` of `Ω` with a sign at each point, the permutation
  `±j ↦ ±(-1)^{s j} σ j` of the signed set `Ω_± = {±} × Ω`, which commutes with the sign flip
  (II:1043). They form a group, `Sym(Ω) ⋉ F₂^Ω` (II:1057); the sign flip `-Id` is `negOne`, the
  `±1` diagonals are `diag`, and the action on a product of signed sets is `prod` (II:3062).
* `SignedPerm.toMatrix`: the matrix of the action on the anti-symmetric functions in the basis
  `B^-` (II:1049), the signed permutation matrix `e_j ↦ (-1)^{s j} e_{σ j}`. It is an injective
  monoid homomorphism (`toMatrixHom`, `toMatrix_injective`): an identity between products of
  signed permutation matrices is an identity in the group, which is decidable.
* `IsSignedPerm`: the matrices of this form. They are unitary, with real entries, so an
  involutive one is self-adjoint (`IsSignedPerm.isHermitian`); a diagonal one is a `±1`
  diagonal (`IsSignedPerm.isDiag_iff`); they are closed under products, `-`, adjoints,
  Kronecker products and reindexing.
-/

namespace MIPRE.Tailored

open Matrix
open scoped Kronecker

/-! ## `(-1)^b` -/

@[simp] theorem bitSign_false : bitSign false = 1 := rfl

@[simp] theorem bitSign_true : bitSign true = -1 := rfl

theorem bitSign_mul_self (b : Bool) : bitSign b * bitSign b = 1 := by
  cases b <;> norm_num [bitSign]

theorem bitSign_xor (a b : Bool) : bitSign (xor a b) = bitSign a * bitSign b := by
  cases a <;> cases b <;> norm_num [bitSign]

theorem bitSign_not (b : Bool) : bitSign (!b) = -bitSign b := by
  cases b <;> norm_num [bitSign]

@[simp] theorem star_bitSign (b : Bool) : star (bitSign b) = bitSign b := by
  cases b <;> simp [bitSign]

theorem bitSign_ne_zero (b : Bool) : bitSign b ≠ 0 := by
  cases b <;> norm_num [bitSign]

theorem bitSign_injective : Function.Injective bitSign := by
  intro a b h
  revert h
  cases a <;> cases b <;> norm_num [bitSign]

/-! ## Signed permutation matrices -/

section Matrices

variable {Ω Ω' : Type*} [DecidableEq Ω] [DecidableEq Ω']

theorem signedPermMatrix_apply (σ : Equiv.Perm Ω) (s : Ω → Bool) (i j : Ω) :
    signedPermMatrix σ s i j = if σ j = i then bitSign (s j) else 0 := rfl

/-- The entry of column `j` in row `σ j`, its only nonzero entry. -/
theorem signedPermMatrix_apply_self (σ : Equiv.Perm Ω) (s : Ω → Bool) (j : Ω) :
    signedPermMatrix σ s (σ j) j = bitSign (s j) := by
  simp [signedPermMatrix_apply]

theorem signedPermMatrix_one_one : signedPermMatrix (1 : Equiv.Perm Ω) (fun _ => false) = 1 := by
  ext i j
  simp only [signedPermMatrix_apply, Equiv.Perm.coe_one, id_eq, bitSign_false, one_apply]
  exact if_congr eq_comm rfl rfl

/-- A signed permutation with trivial permutation is a `±1` diagonal. -/
theorem signedPermMatrix_one (s : Ω → Bool) :
    signedPermMatrix (1 : Equiv.Perm Ω) s = diagonal fun i => bitSign (s i) := by
  ext i j
  simp only [signedPermMatrix_apply, Equiv.Perm.coe_one, id_eq, diagonal_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

theorem neg_signedPermMatrix (σ : Equiv.Perm Ω) (s : Ω → Bool) :
    -signedPermMatrix σ s = signedPermMatrix σ fun j => !s j := by
  ext i j
  rw [Matrix.neg_apply, signedPermMatrix_apply, signedPermMatrix_apply, bitSign_not]
  split_ifs <;> simp

theorem signedPermMatrix_conjTranspose (σ : Equiv.Perm Ω) (s : Ω → Bool) :
    (signedPermMatrix σ s)ᴴ = signedPermMatrix σ⁻¹ fun i => s (σ⁻¹ i) := by
  ext i j
  rw [conjTranspose_apply, signedPermMatrix_apply, signedPermMatrix_apply]
  by_cases h : σ i = j
  · subst h
    simp
  · have h' : ¬σ⁻¹ j = i := by
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact fun h'' => h h''.symm
    rw [ite_eq_right h, ite_eq_right h', star_zero]

/-- Signed permutation matrices have real entries, so their adjoint is their transpose. -/
theorem signedPermMatrix_conjTranspose_eq_transpose (σ : Equiv.Perm Ω) (s : Ω → Bool) :
    (signedPermMatrix σ s)ᴴ = (signedPermMatrix σ s)ᵀ := by
  ext i j
  simp only [conjTranspose_apply, transpose_apply, signedPermMatrix_apply]
  split_ifs <;> simp

theorem signedPermMatrix_mul [Fintype Ω] (σ τ : Equiv.Perm Ω) (s t : Ω → Bool) :
    signedPermMatrix σ s * signedPermMatrix τ t =
      signedPermMatrix (σ * τ) fun j => xor (s (τ j)) (t j) := by
  ext i k
  simp only [mul_apply, signedPermMatrix_apply, Equiv.Perm.mul_apply, bitSign_xor]
  rw [Finset.sum_eq_single (τ k)]
  · by_cases h : σ (τ k) = i <;> simp [h]
  · intro j _ hj
    simp [Ne.symm hj]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem signedPermMatrix_kronecker (σ : Equiv.Perm Ω) (s : Ω → Bool) (τ : Equiv.Perm Ω')
    (t : Ω' → Bool) :
    signedPermMatrix σ s ⊗ₖ signedPermMatrix τ t =
      signedPermMatrix (σ.prodCongr τ) fun p => xor (s p.1) (t p.2) := by
  ext ⟨i, i'⟩ ⟨j, j'⟩
  simp only [kronecker_apply, signedPermMatrix_apply, Equiv.prodCongr_apply, Prod.map_apply,
    Prod.mk.injEq, bitSign_xor]
  by_cases h1 : σ j = i <;> by_cases h2 : τ j' = i' <;> simp [h1, h2]

theorem signedPermMatrix_reindex (e : Ω ≃ Ω') (σ : Equiv.Perm Ω) (s : Ω → Bool) :
    reindex e e (signedPermMatrix σ s) = signedPermMatrix (e.permCongr σ) (s ∘ e.symm) := by
  ext i j
  simp only [reindex_apply, submatrix_apply, signedPermMatrix_apply, Equiv.permCongr_apply,
    Function.comp_apply]
  exact if_congr ⟨fun h => by rw [h, Equiv.apply_symm_apply],
    fun h => by rw [← h, Equiv.symm_apply_apply]⟩ rfl rfl

/-- The diagonal signed permutation matrices are those with trivial permutation. -/
theorem isDiag_signedPermMatrix_iff (σ : Equiv.Perm Ω) (s : Ω → Bool) :
    (signedPermMatrix σ s).IsDiag ↔ σ = 1 := by
  constructor
  · intro h
    ext j
    by_contra hj
    have h2 : signedPermMatrix σ s (σ j) j = 0 := h (by simpa using hj)
    rw [signedPermMatrix_apply_self] at h2
    exact bitSign_ne_zero _ h2
  · rintro rfl
    rw [signedPermMatrix_one]
    exact isDiag_diagonal _

end Matrices

/-! ## Signed permutations as combinatorial data -/

/-- A signed permutation of `Ω` (II:1043): a permutation `perm` of `Ω` and a sign `(-1)^{sign j}`
at each point, the permutation `±j ↦ ±(-1)^{sign j} perm j` of `Ω_± = {±} × Ω`. -/
@[ext]
structure SignedPerm (Ω : Type*) where
  /-- The underlying permutation of `Ω`. -/
  perm : Equiv.Perm Ω
  /-- The signs, `true` for `-1`. -/
  sign : Ω → Bool

namespace SignedPerm

variable {Ω Ω' : Type*}

instance : Mul (SignedPerm Ω) :=
  ⟨fun g h => ⟨g.perm * h.perm, fun j => xor (g.sign (h.perm j)) (h.sign j)⟩⟩

instance : One (SignedPerm Ω) := ⟨⟨1, fun _ => false⟩⟩

instance : Inv (SignedPerm Ω) := ⟨fun g => ⟨g.perm⁻¹, fun i => g.sign (g.perm⁻¹ i)⟩⟩

@[simp] theorem mul_perm (g h : SignedPerm Ω) : (g * h).perm = g.perm * h.perm := rfl

@[simp] theorem mul_sign (g h : SignedPerm Ω) (j : Ω) :
    (g * h).sign j = xor (g.sign (h.perm j)) (h.sign j) := rfl

@[simp] theorem one_perm : (1 : SignedPerm Ω).perm = 1 := rfl

@[simp] theorem one_sign (j : Ω) : (1 : SignedPerm Ω).sign j = false := rfl

@[simp] theorem inv_perm (g : SignedPerm Ω) : g⁻¹.perm = g.perm⁻¹ := rfl

@[simp] theorem inv_sign (g : SignedPerm Ω) (i : Ω) : g⁻¹.sign i = g.sign (g.perm⁻¹ i) := rfl

/-- The signed permutations form a group, `Sym(Ω) ⋉ F₂^Ω` (II:1057). -/
instance : Group (SignedPerm Ω) where
  mul_assoc g h k := by
    ext j
    · rfl
    · simp
  one_mul g := by ext j <;> simp
  mul_one g := by ext j <;> simp
  inv_mul_cancel g := by ext j <;> simp

/-- The signed permutations of `Ω` as pairs. -/
def equivProd : SignedPerm Ω ≃ Equiv.Perm Ω × (Ω → Bool) where
  toFun g := (g.perm, g.sign)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Fintype Ω] [DecidableEq Ω] : Fintype (SignedPerm Ω) :=
  Fintype.ofEquiv _ equivProd.symm

instance [Fintype Ω] [DecidableEq Ω] : DecidableEq (SignedPerm Ω) :=
  equivProd.decidableEq

/-- The sign flip `-Id` (II:1029). -/
def negOne : SignedPerm Ω := ⟨1, fun _ => true⟩

/-- The `±1` diagonal with signs `s`. -/
def diag (s : Ω → Bool) : SignedPerm Ω := ⟨1, s⟩

/-- The action on a product of signed sets (II:3062–3069), whose matrix is the Kronecker
product. -/
def prod (g : SignedPerm Ω) (h : SignedPerm Ω') : SignedPerm (Ω × Ω') :=
  ⟨g.perm.prodCongr h.perm, fun p => xor (g.sign p.1) (h.sign p.2)⟩

/-- Transport along a bijection of the underlying sets. -/
def map (e : Ω ≃ Ω') (g : SignedPerm Ω) : SignedPerm Ω' := ⟨e.permCongr g.perm, g.sign ∘ e.symm⟩

theorem negOne_mul (g : SignedPerm Ω) : negOne * g = ⟨g.perm, fun j => !g.sign j⟩ := by
  ext j
  · rfl
  · simp [negOne]

/-- The sign flip is central. -/
theorem negOne_comm (g : SignedPerm Ω) : negOne * g = g * negOne := by
  ext j
  · simp [negOne]
  · simp [negOne]

/-- The matrix of a signed permutation: of its action on the anti-symmetric functions, in the
basis `B^-` (II:1049). -/
def toMatrix [DecidableEq Ω] (g : SignedPerm Ω) : Matrix Ω Ω ℂ := signedPermMatrix g.perm g.sign

section Matrix

variable [DecidableEq Ω] [DecidableEq Ω']

theorem toMatrix_apply (g : SignedPerm Ω) (i j : Ω) :
    g.toMatrix i j = if g.perm j = i then bitSign (g.sign j) else 0 := rfl

theorem toMatrix_one [Fintype Ω] : (1 : SignedPerm Ω).toMatrix = 1 := signedPermMatrix_one_one

theorem toMatrix_mul [Fintype Ω] (g h : SignedPerm Ω) :
    (g * h).toMatrix = g.toMatrix * h.toMatrix :=
  (signedPermMatrix_mul _ _ _ _).symm

/-- The matrix interpretation, a monoid homomorphism (II:1043–1053). -/
def toMatrixHom [Fintype Ω] : SignedPerm Ω →* Matrix Ω Ω ℂ where
  toFun := toMatrix
  map_one' := toMatrix_one
  map_mul' := toMatrix_mul

@[simp] theorem toMatrixHom_apply [Fintype Ω] (g : SignedPerm Ω) : toMatrixHom g = g.toMatrix :=
  rfl

/-- A signed permutation is determined by its matrix. -/
theorem toMatrix_injective : Function.Injective (toMatrix : SignedPerm Ω → Matrix Ω Ω ℂ) := by
  intro g h hgh
  have key : ∀ j, h.perm j = g.perm j ∧ h.sign j = g.sign j := by
    intro j
    have := congrFun (congrFun hgh (g.perm j)) j
    rw [toMatrix_apply, toMatrix_apply, ite_eq_left rfl] at this
    by_cases hj : h.perm j = g.perm j
    · rw [ite_eq_left hj] at this
      exact ⟨hj, bitSign_injective this.symm⟩
    · rw [ite_eq_right hj] at this
      exact absurd this (bitSign_ne_zero _)
  ext j
  · exact (key j).1.symm
  · exact (key j).2.symm

theorem toMatrix_inj {g h : SignedPerm Ω} : g.toMatrix = h.toMatrix ↔ g = h :=
  toMatrix_injective.eq_iff

theorem toMatrix_inv (g : SignedPerm Ω) : g⁻¹.toMatrix = g.toMatrixᴴ :=
  (signedPermMatrix_conjTranspose _ _).symm

theorem toMatrix_negOne : (negOne : SignedPerm Ω).toMatrix = -1 := by
  rw [show (negOne : SignedPerm Ω).toMatrix = signedPermMatrix 1 (fun _ => true) from rfl,
    signedPermMatrix_one, ← diagonal_one, diagonal_neg]
  congr 1

theorem toMatrix_diag (s : Ω → Bool) : (diag s).toMatrix = diagonal fun i => bitSign (s i) :=
  signedPermMatrix_one s

theorem toMatrix_prod (g : SignedPerm Ω) (h : SignedPerm Ω') :
    (g.prod h).toMatrix = g.toMatrix ⊗ₖ h.toMatrix :=
  (signedPermMatrix_kronecker _ _ _ _).symm

theorem toMatrix_map (e : Ω ≃ Ω') (g : SignedPerm Ω) :
    (g.map e).toMatrix = reindex e e g.toMatrix :=
  (signedPermMatrix_reindex _ _ _).symm

theorem toMatrix_mul_conjTranspose [Fintype Ω] (g : SignedPerm Ω) :
    g.toMatrix * g.toMatrixᴴ = 1 := by
  rw [← toMatrix_inv, ← toMatrix_mul, mul_inv_cancel, toMatrix_one]

theorem toMatrix_conjTranspose_mul [Fintype Ω] (g : SignedPerm Ω) :
    g.toMatrixᴴ * g.toMatrix = 1 := by
  rw [← toMatrix_inv, ← toMatrix_mul, inv_mul_cancel, toMatrix_one]

theorem toMatrix_mem_unitaryGroup [Fintype Ω] (g : SignedPerm Ω) :
    g.toMatrix ∈ Matrix.unitaryGroup Ω ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  exact g.toMatrix_mul_conjTranspose

theorem isDiag_toMatrix_iff (g : SignedPerm Ω) : g.toMatrix.IsDiag ↔ g.perm = 1 :=
  isDiag_signedPermMatrix_iff _ _

end Matrix

end SignedPerm

/-! ## Signed permutation matrices, as a property -/

section IsSignedPerm

variable {Ω Ω' : Type*} [DecidableEq Ω] [DecidableEq Ω'] {M N : Matrix Ω Ω ℂ}

theorem isSignedPerm_iff : IsSignedPerm M ↔ ∃ g : SignedPerm Ω, g.toMatrix = M :=
  ⟨fun ⟨σ, s, h⟩ => ⟨⟨σ, s⟩, h.symm⟩, fun ⟨g, h⟩ => ⟨g.perm, g.sign, h.symm⟩⟩

theorem SignedPerm.isSignedPerm_toMatrix (g : SignedPerm Ω) : IsSignedPerm g.toMatrix :=
  isSignedPerm_iff.2 ⟨g, rfl⟩

namespace IsSignedPerm

theorem one [Fintype Ω] : IsSignedPerm (1 : Matrix Ω Ω ℂ) :=
  isSignedPerm_iff.2 ⟨1, SignedPerm.toMatrix_one⟩

theorem mul [Fintype Ω] (hM : IsSignedPerm M) (hN : IsSignedPerm N) : IsSignedPerm (M * N) := by
  obtain ⟨g, rfl⟩ := isSignedPerm_iff.1 hM
  obtain ⟨h, rfl⟩ := isSignedPerm_iff.1 hN
  exact isSignedPerm_iff.2 ⟨g * h, SignedPerm.toMatrix_mul g h⟩

theorem neg (hM : IsSignedPerm M) : IsSignedPerm (-M) := by
  obtain ⟨σ, s, rfl⟩ := hM
  exact ⟨σ, _, neg_signedPermMatrix σ s⟩

theorem neg_one [Fintype Ω] : IsSignedPerm (-1 : Matrix Ω Ω ℂ) := one.neg

theorem conjTranspose (hM : IsSignedPerm M) : IsSignedPerm Mᴴ := by
  obtain ⟨σ, s, rfl⟩ := hM
  exact ⟨σ⁻¹, _, signedPermMatrix_conjTranspose σ s⟩

theorem conjTranspose_eq_transpose (hM : IsSignedPerm M) : Mᴴ = Mᵀ := by
  obtain ⟨σ, s, rfl⟩ := hM
  exact signedPermMatrix_conjTranspose_eq_transpose σ s

theorem transpose (hM : IsSignedPerm M) : IsSignedPerm Mᵀ :=
  hM.conjTranspose_eq_transpose ▸ hM.conjTranspose

theorem diagonal (s : Ω → Bool) : IsSignedPerm (diagonal fun i => bitSign (s i)) :=
  ⟨1, s, (signedPermMatrix_one s).symm⟩

theorem kronecker {M' : Matrix Ω' Ω' ℂ} (hM : IsSignedPerm M) (hM' : IsSignedPerm M') :
    IsSignedPerm (M ⊗ₖ M') := by
  obtain ⟨σ, s, rfl⟩ := hM
  obtain ⟨τ, t, rfl⟩ := hM'
  exact ⟨_, _, signedPermMatrix_kronecker σ s τ t⟩

theorem reindex (e : Ω ≃ Ω') (hM : IsSignedPerm M) : IsSignedPerm (Matrix.reindex e e M) := by
  obtain ⟨σ, s, rfl⟩ := hM
  exact ⟨_, _, signedPermMatrix_reindex e σ s⟩

theorem conjTranspose_mul_self [Fintype Ω] (hM : IsSignedPerm M) : Mᴴ * M = 1 := by
  obtain ⟨g, rfl⟩ := isSignedPerm_iff.1 hM
  exact g.toMatrix_conjTranspose_mul

theorem mul_conjTranspose_self [Fintype Ω] (hM : IsSignedPerm M) : M * Mᴴ = 1 := by
  obtain ⟨g, rfl⟩ := isSignedPerm_iff.1 hM
  exact g.toMatrix_mul_conjTranspose

theorem mem_unitaryGroup [Fintype Ω] (hM : IsSignedPerm M) : M ∈ Matrix.unitaryGroup Ω ℂ :=
  Matrix.mem_unitaryGroup_iff.2 hM.mul_conjTranspose_self

/-- **An involutive signed permutation matrix is self-adjoint**: it is unitary and its own
inverse. -/
theorem isHermitian [Fintype Ω] (hM : IsSignedPerm M) (h : M * M = 1) : M.IsHermitian := by
  change Mᴴ = M
  calc Mᴴ = Mᴴ * (M * M) := by rw [h, Matrix.mul_one]
    _ = (Mᴴ * M) * M := (Matrix.mul_assoc _ _ _).symm
    _ = M := by rw [hM.conjTranspose_mul_self, Matrix.one_mul]

/-- A diagonal signed permutation matrix is a `±1` diagonal. -/
theorem isDiag_iff (hM : IsSignedPerm M) :
    M.IsDiag ↔ ∃ s : Ω → Bool, M = Matrix.diagonal fun i => bitSign (s i) := by
  obtain ⟨σ, s, rfl⟩ := hM
  rw [isDiag_signedPermMatrix_iff]
  constructor
  · rintro rfl
    exact ⟨s, signedPermMatrix_one s⟩
  · rintro ⟨t, ht⟩
    rw [← signedPermMatrix_one] at ht
    have := @SignedPerm.toMatrix_injective Ω _ ⟨σ, s⟩ ⟨1, t⟩ ht
    exact congrArg SignedPerm.perm this

end IsSignedPerm

end IsSignedPerm

end MIPRE.Tailored

end
