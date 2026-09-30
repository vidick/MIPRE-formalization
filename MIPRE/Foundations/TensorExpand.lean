/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.AncillaIsometry
public import MIPRE.Foundations.Expanded

@[expose] public section

/-!
# The ancilla extension of a tensor-product model

The extension of the tensor-product model of `ξ` on `ℂ^{dA × dB}` by registers `α` and `β` in
the vector `e` (`BipartiteModel.expand`) is the tensor-product model of the expanded vector
`expVec e ξ` on `ℂ^{(α × dA) × (β × dB)}`, the register first: its block matrices of matrices are
the matrices on the products of the indices (`Matrix.comp`), and its `ℓ²` sum of copies of
`ℂ^{dA × dB}` is `ℂ^{(α × dA) × (β × dB)}` (`BipartiteModel.tensorExpand`, carrying the state
exactly). This is the bridge between the register model of `MIPRE/Foundations/Introspection/
RegisterModel.lean`, in which the introspection analysis is stated, and the matrix states
`MIPRE.Introspection.registerState I ξ = expVec (registerEPR I) ξ` of the tensor-product proof and
of the Pauli basis test.
-/

noncomputable section

namespace MIPRE

open scoped InnerProductSpace Kronecker
open Matrix OperatorMatrix

namespace BipartiteModel

variable {dA dB α β : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The flattening of `ℂ^{dA × dB} ⊗ ℂ^{α × β}` onto `ℂ^{(α × dA) × (β × dB)}`. -/
def flattenIsometry (ξ : dA × dB → ℂ) (e : α × β → ℂ) :
    ((tensor ξ).expand e).H →ₗᵢ[ℂ] (tensor (expVec e ξ)).H :=
  (amplReindex (H := ℂ) (Equiv.prodProdProdComm α dA β dB)).comp
    ((amplUncurry (ι := α × β) (κ := dA × dB) (H := ℂ)).comp ((tensor ξ).ampl e).toLinearIsometry)

theorem flattenIsometry_apply (ξ : dA × dB → ℂ) (e : α × β → ℂ) (v : ((tensor ξ).expand e).H)
    (q : (α × dA) × (β × dB)) :
    WithLp.ofLp (flattenIsometry ξ e v) q =
      WithLp.ofLp ((tensor ξ).ampl e v (q.1.1, q.2.1)) (q.1.2, q.2.2) := rfl

/-- The action of the tensor-product model's matrices, entrywise. -/
theorem tensor_π_apply {N N' : Type*} [Fintype N] [DecidableEq N] [Fintype N'] [DecidableEq N']
    (v : N × N' → ℂ) (T : Matrix (N × N') (N × N') ℂ) (w : (tensor v).H) (i : N × N') :
    WithLp.ofLp ((tensor v).π T w) i = ∑ j, T i j * WithLp.ofLp w j :=
  rfl

/-- The Hilbert space of the tensor-product model is `ℂ^{dA × dB}`. -/
def euclid {N N' : Type*} [Fintype N] [DecidableEq N] [Fintype N'] [DecidableEq N']
    (v : N × N' → ℂ) : (tensor v).H ≃ₗᵢ[ℂ] EuclideanSpace ℂ (N × N') :=
  LinearIsometryEquiv.refl ℂ _

/-- The components of a sum of vectors of the tensor-product model. -/
theorem tensor_ofLp_sum {N N' : Type*} [Fintype N] [DecidableEq N] [Fintype N'] [DecidableEq N']
    (v : N × N' → ℂ) {ι : Type*} (s : Finset ι) (f : ι → (tensor v).H) (i : N × N') :
    WithLp.ofLp ((∑ a ∈ s, f a : (tensor v).H)) i = ∑ a ∈ s, WithLp.ofLp (f a) i := by
  show WithLp.ofLp (euclid v (∑ a ∈ s, f a : (tensor v).H)) i = _
  rw [map_sum, WithLp.ofLp_sum, Finset.sum_apply]
  rfl

/-- **The extension of a tensor-product model is the tensor-product model of the expanded
vector**: a local isometry carrying the state to the state, the players' block matrices of
matrices read as matrices on the products of the indices. -/
def tensorExpand (ξ : dA × dB → ℂ) (e : α × β → ℂ) :
    LocalIsometry ((tensor ξ).expand e) (tensor (expVec e ξ)) where
  W := flattenIsometry ξ e
  ΦA := compHom
  ΦB := compHom
  intertwineA X v := by
    refine PiLp.ext fun q => ?_
    show WithLp.ofLp ((tensor (expVec e ξ)).π ((tensor (expVec e ξ)).πA (compHom X))
      (flattenIsometry ξ e v)) q = WithLp.ofLp (flattenIsometry ξ e
        (((tensor ξ).expand e).π (((tensor ξ).expand e).πA X) v)) q
    rw [tensor_π_apply, tensor_πA, flattenIsometry_apply, expand_π_πA_apply, tensor_ofLp_sum]
    simp only [tensor_π_apply, tensor_πA, flattenIsometry_apply, aOp, kroneckerMap_apply,
      compHom_apply, one_apply, Fintype.sum_prod_type, mul_ite, mul_one, mul_zero, Prod.ext_iff,
      ite_and, ite_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  intertwineB Y v := by
    refine PiLp.ext fun q => ?_
    show WithLp.ofLp ((tensor (expVec e ξ)).π ((tensor (expVec e ξ)).πB (compHom Y))
      (flattenIsometry ξ e v)) q = WithLp.ofLp (flattenIsometry ξ e
        (((tensor ξ).expand e).π (((tensor ξ).expand e).πB Y) v)) q
    rw [tensor_π_apply, tensor_πB, flattenIsometry_apply, expand_π_πB_apply, tensor_ofLp_sum]
    simp only [tensor_π_apply, tensor_πB, flattenIsometry_apply, bOp, kroneckerMap_apply,
      compHom_apply, one_apply, Fintype.sum_prod_type, ite_mul, one_mul, zero_mul, Prod.ext_iff,
      ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]

theorem tensorExpand_W_ψ (ξ : dA × dB → ℂ) (e : α × β → ℂ) :
    (tensorExpand ξ e).W ((tensor ξ).expand e).ψ = (tensor (expVec e ξ)).ψ := by
  refine PiLp.ext fun q => ?_
  show WithLp.ofLp (flattenIsometry ξ e ((tensor ξ).expand e).ψ) q = expVec e ξ q
  rw [flattenIsometry_apply, expand_ψ_apply]
  rfl

@[simp]
theorem tensorExpand_ΦA (ξ : dA × dB → ℂ) (e : α × β → ℂ) (X : Matrix α α (Matrix dA dA ℂ)) :
    (tensorExpand ξ e).ΦA X = compHom X := rfl

@[simp]
theorem tensorExpand_ΦB (ξ : dA × dB → ℂ) (e : α × β → ℂ) (Y : Matrix β β (Matrix dB dB ℂ)) :
    (tensorExpand ξ e).ΦB Y = compHom Y := rfl

/-! ## The inverse of the flattening -/

/-- Matrices on the products of the indices as block matrices of matrices (`Matrix.comp`
inverted), as a `⋆`-homomorphism. -/
def compSymmHom {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] :
    Matrix (α × dA) (α × dA) R →⋆ₙₐ[ℂ] Matrix α α (Matrix dA dA R) where
  toFun X := (comp α α dA dA R).symm X
  map_smul' c X := by
    ext a a' h h'
    rfl
  map_zero' := by
    ext a a' h h'
    rfl
  map_add' X Y := by
    ext a a' h h'
    rfl
  map_mul' X Y := ((compRingEquiv α dA R).symm.map_mul X Y)
  map_star' X := by
    ext a a' h h'
    rfl

omit [DecidableEq dA] [DecidableEq α] in
@[simp]
theorem compSymmHom_apply {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
    (X : Matrix (α × dA) (α × dA) R) (a a' : α) (h h' : dA) :
    compSymmHom X a a' h h' = X (a, h) (a', h') := rfl

omit [DecidableEq dA] [DecidableEq α] in
theorem compHom_compSymmHom {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
    (X : Matrix (α × dA) (α × dA) R) : compHom (compSymmHom X) = X := by
  ext p q
  rfl

/-- The inverse of the flattening. -/
def unflattenIsometry (ξ : dA × dB → ℂ) (e : α × β → ℂ) :
    (tensor (expVec e ξ)).H →ₗᵢ[ℂ] ((tensor ξ).expand e).H :=
  ((tensor ξ).ampl e).symm.toLinearIsometry.comp
    ((amplCurry (ι := α × β) (κ := dA × dB) (H := ℂ)).comp
      (amplReindex (H := ℂ) (Equiv.prodProdProdComm α dA β dB).symm))

theorem flattenIsometry_unflattenIsometry (ξ : dA × dB → ℂ) (e : α × β → ℂ)
    (v : (tensor (expVec e ξ)).H) : flattenIsometry ξ e (unflattenIsometry ξ e v) = v := by
  refine PiLp.ext fun q => ?_
  rfl

/-- **The tensor-product model of an expanded vector is the extension of the tensor-product
model**: the inverse of `tensorExpand`. -/
def tensorUnexpand (ξ : dA × dB → ℂ) (e : α × β → ℂ) :
    LocalIsometry (tensor (expVec e ξ)) ((tensor ξ).expand e) :=
  (tensorExpand ξ e).symm (unflattenIsometry ξ e) (flattenIsometry_unflattenIsometry ξ e)
    compSymmHom compHom_compSymmHom compSymmHom compHom_compSymmHom

theorem tensorUnexpand_W_ψ (ξ : dA × dB → ℂ) (e : α × β → ℂ) :
    (tensorUnexpand ξ e).W (tensor (expVec e ξ)).ψ = ((tensor ξ).expand e).ψ :=
  LocalIsometry.symm_W_ψ _ _ _ _ _ _ _ (tensorExpand_W_ψ ξ e)

@[simp]
theorem tensorUnexpand_ΦA (ξ : dA × dB → ℂ) (e : α × β → ℂ) (X : Matrix (α × dA) (α × dA) ℂ) :
    (tensorUnexpand ξ e).ΦA X = compSymmHom X := rfl

@[simp]
theorem tensorUnexpand_ΦB (ξ : dA × dB → ℂ) (e : α × β → ℂ) (Y : Matrix (β × dB) (β × dB) ℂ) :
    (tensorUnexpand ξ e).ΦB Y = compSymmHom Y := rfl

omit [DecidableEq α] in
/-- A register operator acting as `P ⊗ 1` on the flat space is `smulKron 1 P` in blocks. -/
theorem compSymmHom_kronecker_one (P : Matrix α α ℂ) :
    compSymmHom (P ⊗ₖ (1 : Matrix dA dA ℂ)) = smulKron (1 : Matrix dA dA ℂ) P := by
  ext a a' h h'
  simp only [compSymmHom_apply, kroneckerMap_apply, smulKron_apply, Matrix.smul_apply,
    smul_eq_mul]

end BipartiteModel

/-! ## Local isometries of tensor-product models given by matrices -/

section MatrixIsometry

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- **A matrix with orthonormal columns as an isometry** of the Euclidean spaces. -/
def matrixIsometry (V : Matrix m n ℂ) (hV : Vᴴ * V = 1) :
    EuclideanSpace ℂ n →ₗᵢ[ℂ] EuclideanSpace ℂ m where
  toLinearMap := (Matrix.toEuclideanLin V)
  norm_map' v := by
    obtain ⟨v⟩ := v
    show ‖evec (V *ᵥ v)‖ = ‖evec v‖
    exact norm_evec_mulVec_eq hV v

omit [DecidableEq m] in
theorem matrixIsometry_apply (V : Matrix m n ℂ) (hV : Vᴴ * V = 1) (v : EuclideanSpace ℂ n) :
    WithLp.ofLp (matrixIsometry V hV v) = V *ᵥ WithLp.ofLp v := rfl

/-- **Conjugation by a matrix with orthonormal columns**, `X ↦ V X Vᴴ`, a `⋆`-homomorphism. -/
def conjHom (V : Matrix m n ℂ) (hV : Vᴴ * V = 1) : Matrix n n ℂ →⋆ₙₐ[ℂ] Matrix m m ℂ where
  toFun X := V * X * Vᴴ
  map_smul' c X := by simp only [Matrix.mul_smul, Matrix.smul_mul, MonoidHom.id_apply]
  map_zero' := by simp only [Matrix.mul_zero, Matrix.zero_mul]
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_mul' X Y := by
    show V * (X * Y) * Vᴴ = V * X * Vᴴ * (V * Y * Vᴴ)
    calc V * (X * Y) * Vᴴ = V * X * (Vᴴ * V) * Y * Vᴴ := by
          rw [hV, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = V * X * Vᴴ * (V * Y * Vᴴ) := by simp only [Matrix.mul_assoc]
  map_star' X := by
    show V * star X * Vᴴ = star (V * X * Vᴴ)
    simp only [star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose,
      Matrix.mul_assoc]

omit [DecidableEq m] in
@[simp]
theorem conjHom_apply (V : Matrix m n ℂ) (hV : Vᴴ * V = 1) (X : Matrix n n ℂ) :
    conjHom V hV X = V * X * Vᴴ := rfl

end MatrixIsometry

namespace BipartiteModel

variable {dA dB R S : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]

/-- **The local isometry of two tensor-product models given by matrix isometries** `V_A` and
`V_B`: the space moved by `V_A ⊗ V_B`, the players' operators by `X ↦ V_A X V_Aᴴ` and
`Y ↦ V_B Y V_Bᴴ`. The states of the two models play no part. -/
def tensorIsometry (ψ : dA × dB → ℂ) (ψ' : R × S → ℂ) (VA : Matrix R dA ℂ) (VB : Matrix S dB ℂ)
    (hA : VAᴴ * VA = 1) (hB : VBᴴ * VB = 1) : LocalIsometry (tensor ψ) (tensor ψ') where
  W := matrixIsometry (VA ⊗ₖ VB) (by
    rw [conjTranspose_kronecker, ← mul_kronecker_mul, hA, hB, one_kronecker_one])
  ΦA := conjHom VA hA
  ΦB := conjHom VB hB
  intertwineA X v := by
    refine PiLp.ext fun q => ?_
    show WithLp.ofLp ((tensor ψ').π (aOp (VA * X * VAᴴ)) (matrixIsometry (VA ⊗ₖ VB) _ v)) q =
      WithLp.ofLp (matrixIsometry (VA ⊗ₖ VB) _ ((tensor ψ).π (aOp X) v)) q
    have h : aOp (VA * X * VAᴴ) * (VA ⊗ₖ VB) = (VA ⊗ₖ VB) * aOp X := by
      calc aOp (VA * X * VAᴴ) * (VA ⊗ₖ VB) = (VA * X * VAᴴ * VA) ⊗ₖ ((1 : Matrix S S ℂ) * VB) :=
            (Matrix.mul_kronecker_mul _ _ _ _).symm
        _ = (VA * X) ⊗ₖ (VB * (1 : Matrix dB dB ℂ)) := by
            rw [Matrix.mul_assoc (VA * X), hA, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]
        _ = (VA ⊗ₖ VB) * aOp X := Matrix.mul_kronecker_mul _ _ _ _
    show (aOp (VA * X * VAᴴ) *ᵥ ((VA ⊗ₖ VB) *ᵥ WithLp.ofLp v)) q =
      ((VA ⊗ₖ VB) *ᵥ (aOp X *ᵥ WithLp.ofLp v)) q
    rw [mulVec_mulVec, mulVec_mulVec]
    exact congrFun (congrArg (· *ᵥ WithLp.ofLp v) h) q
  intertwineB Y v := by
    refine PiLp.ext fun q => ?_
    have h : bOp (VB * Y * VBᴴ) * (VA ⊗ₖ VB) = (VA ⊗ₖ VB) * bOp Y := by
      calc bOp (VB * Y * VBᴴ) * (VA ⊗ₖ VB) = ((1 : Matrix R R ℂ) * VA) ⊗ₖ (VB * Y * VBᴴ * VB) :=
            (Matrix.mul_kronecker_mul _ _ _ _).symm
        _ = (VA * (1 : Matrix dA dA ℂ)) ⊗ₖ (VB * Y) := by
            rw [Matrix.mul_assoc (VB * Y), hB, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]
        _ = (VA ⊗ₖ VB) * bOp Y := Matrix.mul_kronecker_mul _ _ _ _
    show (bOp (VB * Y * VBᴴ) *ᵥ ((VA ⊗ₖ VB) *ᵥ WithLp.ofLp v)) q =
      ((VA ⊗ₖ VB) *ᵥ (bOp Y *ᵥ WithLp.ofLp v)) q
    rw [mulVec_mulVec, mulVec_mulVec]
    exact congrFun (congrArg (· *ᵥ WithLp.ofLp v) h) q

theorem tensorIsometry_W (ψ : dA × dB → ℂ) (ψ' : R × S → ℂ) (VA : Matrix R dA ℂ)
    (VB : Matrix S dB ℂ) (hA : VAᴴ * VA = 1) (hB : VBᴴ * VB = 1) (v : (tensor ψ).H) :
    WithLp.ofLp ((tensorIsometry ψ ψ' VA VB hA hB).W v) = (VA ⊗ₖ VB) *ᵥ WithLp.ofLp v := rfl

@[simp]
theorem tensorIsometry_ΦA (ψ : dA × dB → ℂ) (ψ' : R × S → ℂ) (VA : Matrix R dA ℂ)
    (VB : Matrix S dB ℂ) (hA : VAᴴ * VA = 1) (hB : VBᴴ * VB = 1) (X : Matrix dA dA ℂ) :
    (tensorIsometry ψ ψ' VA VB hA hB).ΦA X = VA * X * VAᴴ := rfl

@[simp]
theorem tensorIsometry_ΦB (ψ : dA × dB → ℂ) (ψ' : R × S → ℂ) (VA : Matrix R dA ℂ)
    (VB : Matrix S dB ℂ) (hA : VAᴴ * VA = 1) (hB : VBᴴ * VB = 1) (Y : Matrix dB dB ℂ) :
    (tensorIsometry ψ ψ' VA VB hA hB).ΦB Y = VB * Y * VBᴴ := rfl

end BipartiteModel

end MIPRE

end
