/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.OperatorMatrix
public import MIPRE.Foundations.StateDistance
public import MIPRE.Foundations.BlockOrder

@[expose] public section

/-!
# The ancilla extension of a bipartite model

A finite ancilla adjoined to a bipartite model: a register `α` for the first player and a
register `β` for the second, in a joint state `e : α × β → ℂ`. The Hilbert space becomes
`H ⊗ ℂ^{α × β}`, the `ℓ²` sum `OperatorMatrix.Ampl (α × β) H` of `ι → H` of Phase 1(a); the first
player's algebra becomes the `α × α` matrices over `𝒜`, acting as `X ⊗ 1_β`, and the second's the
`β × β` matrices over `ℬ`, acting as `1_α ⊗ Y` (`BipartiteModel.expand`). These are the finite
ancillas of `planning/mipco-track.md` §5, and the expanded state of the Pauli appendix
(`def:expanded-state`) in any model.

An element `X` of a player's algebra tensored with a matrix `P` of scalars on the register is the
matrix `smulKron X P` with entries `P a b • X`. Three facts carry every use of the construction.

* **The Born probability of a measurement of product form factorizes** into the model's and the
  ancilla's (`bornProb_expand_smulKron`), as soon as the ancilla's two operators are positive,
  which makes the ancilla's quadratic form real.
* So an operator with an **inert ancilla**, `X ⊗ 1`, has the state norm it had before the
  expansion, scaled by the norm of `e` (`stateSqNorm_expand_smulKron_one`); and the norm of the
  state is the product of the norms (`norm_expand_state`).
* A product of projective measurements is projective (`IsPVMIn.smulKron`).

The matrix expanded state `expVec` of `MIPRE/Foundations/Expanded.lean` is this construction at
the tensor-product model, through the bridge `bornProb_expVec_eq` there.
-/

noncomputable section

namespace MIPRE

open scoped InnerProductSpace Kronecker ComplexOrder
open Matrix OperatorMatrix

/-! ## An element tensored with a matrix of scalars -/

section SmulKron

variable {R α : Type*} [Ring R] [Algebra ℂ R]

/-- `X ⊗ P` as an `α × α` matrix over `R`: the entry `(a, b)` is `P a b • X`. -/
def smulKron (X : R) (P : Matrix α α ℂ) : Matrix α α R := P.map (· • X)

@[simp]
theorem smulKron_apply (X : R) (P : Matrix α α ℂ) (a b : α) : smulKron X P a b = P a b • X :=
  rfl

theorem smulKron_zero_left (P : Matrix α α ℂ) : smulKron (0 : R) P = 0 := by
  ext a b
  simp

theorem smulKron_zero_right (X : R) : smulKron X (0 : Matrix α α ℂ) = 0 := by
  ext a b
  simp

theorem smulKron_sum_left {ι : Type*} (s : Finset ι) (X : ι → R) (P : Matrix α α ℂ) :
    smulKron (∑ i ∈ s, X i) P = ∑ i ∈ s, smulKron (X i) P := by
  ext a b
  simp only [smulKron_apply, Finset.smul_sum, Matrix.sum_apply]

theorem smulKron_sum_right {ι : Type*} (X : R) (s : Finset ι) (P : ι → Matrix α α ℂ) :
    smulKron X (∑ i ∈ s, P i) = ∑ i ∈ s, smulKron X (P i) := by
  ext a b
  simp only [smulKron_apply, Matrix.sum_apply, Finset.sum_smul]

/-- The adjoint of `X ⊗ P` is `X* ⊗ P*`. -/
theorem star_smulKron [StarRing R] [StarModule ℂ R] (X : R) (P : Matrix α α ℂ) :
    star (smulKron X P) = smulKron (star X) Pᴴ := by
  ext a b
  simp only [star_apply, smulKron_apply, conjTranspose_apply, star_smul]

theorem smulKron_mul [Fintype α] (X Y : R) (P Q : Matrix α α ℂ) :
    smulKron X P * smulKron Y Q = smulKron (X * Y) (P * Q) := by
  ext a b
  simp only [smulKron_apply, mul_apply, smul_mul_smul_comm, Finset.sum_smul]

theorem smulKron_add_left (X Y : R) (P : Matrix α α ℂ) :
    smulKron (X + Y) P = smulKron X P + smulKron Y P := by
  ext a b
  simp only [smulKron_apply, Matrix.add_apply, smul_add]

theorem smulKron_sub_left (X Y : R) (P : Matrix α α ℂ) :
    smulKron X P - smulKron Y P = smulKron (X - Y) P := by
  ext a b
  simp only [smulKron_apply, Matrix.sub_apply, smul_sub]

theorem smulKron_add_right (X : R) (P Q : Matrix α α ℂ) :
    smulKron X (P + Q) = smulKron X P + smulKron X Q := by
  ext a b
  simp only [smulKron_apply, Matrix.add_apply, add_smul]

theorem smulKron_sub_right (X : R) (P Q : Matrix α α ℂ) :
    smulKron X (P - Q) = smulKron X P - smulKron X Q := by
  ext a b
  simp only [smulKron_apply, Matrix.sub_apply, sub_smul]

theorem smulKron_smul_right (X : R) (c : ℂ) (P : Matrix α α ℂ) :
    smulKron X (c • P) = c • smulKron X P := by
  ext a b
  simp only [smulKron_apply, Matrix.smul_apply, smul_eq_mul, mul_smul]

variable [DecidableEq α]

theorem smulKron_one_one : smulKron (1 : R) (1 : Matrix α α ℂ) = 1 := by
  ext a b
  by_cases h : a = b
  · subst h
    simp
  · simp [one_apply_ne h]

/-- The adjoint of `X ⊗ 1` is `X* ⊗ 1`, in any `⋆`-ring. -/
theorem star_smulKron_one [StarRing R] (X : R) :
    star (smulKron X (1 : Matrix α α ℂ)) = smulKron (star X) 1 := by
  ext a b
  rw [star_apply, smulKron_apply, smulKron_apply]
  by_cases h : a = b
  · subst h
    simp
  · simp [one_apply_ne h, one_apply_ne (Ne.symm h)]

variable [Fintype α]

omit [DecidableEq α] in
/-- **A nonnegative element times a projection of the register is nonnegative**, in the order of
the matrices over a proper ordered `⋆`-ring (`MIPRE.MatrixStar.instPartialOrderStar`):
`z⋆ z ⊗ P = (z ⊗ P)⋆ (z ⊗ P)` when `Pᴴ P = P`. -/
theorem smulKron_nonneg_of_proj [StarRing R] [StarModule ℂ R] [PartialOrder R]
    [StarOrderedRing R] [StarProper R] {X : R} (hX : 0 ≤ X) {P : Matrix α α ℂ}
    (hP : Pᴴ * P = P) : 0 ≤ smulKron X P := by
  rw [StarOrderedRing.nonneg_iff] at hX
  induction hX using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨z, rfl⟩ := hx
    have h : smulKron (star z * z) P = star (smulKron z P) * smulKron z P := by
      rw [star_smulKron, smulKron_mul, hP]
    rw [h]
    exact star_mul_self_nonneg _
  | zero => rw [smulKron_zero_left]
  | add x y _ _ hx hy => rw [smulKron_add_left]; exact add_nonneg hx hy

/-- **A product of projective measurements is projective**: the first in `R`, the second of
scalar matrices on the register. -/
theorem IsPVMIn.smulKron [StarRing R] [StarModule ℂ R] {ι κ : Type*} [Fintype ι] [Fintype κ]
    {P : ι → R} {Q : κ → Matrix α α ℂ} (hP : IsPVMIn P) (hQ : IsPVMIn Q) :
    IsPVMIn (fun p : ι × κ => MIPRE.smulKron (P p.1) (Q p.2)) where
  star_eq p := by
    rw [star_smulKron, hP.star_eq, ← star_eq_conjTranspose, hQ.star_eq]
  idem p := by
    rw [smulKron_mul, hP.idem, hQ.idem]
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← smulKron_sum_right, hQ.sum_eq_one, ← smulKron_sum_left, hP.sum_eq_one,
      smulKron_one_one]
  orthogonal {p q} hpq := by
    rw [smulKron_mul]
    by_cases h1 : p.1 = q.1
    · have h2 : p.2 ≠ q.2 := fun h2 => hpq (Prod.ext h1 h2)
      rw [hQ.orthogonal h2, smulKron_zero_right]
    · rw [hP.orthogonal h1, smulKron_zero_left]

/-- **A projective measurement of the register is projective in the matrices over `R`**, as
`P ↦ 1 ⊗ P`. -/
theorem IsPVMIn.smulKron_one [StarRing R] [StarModule ℂ R] {ι : Type*} [Fintype ι]
    {P : ι → Matrix α α ℂ} (hP : IsPVMIn P) : IsPVMIn fun i => MIPRE.smulKron (1 : R) (P i) where
  star_eq i := by rw [star_smulKron, star_one, ← star_eq_conjTranspose, hP.star_eq]
  idem i := by rw [smulKron_mul, one_mul, hP.idem]
  sum_eq_one := by rw [← smulKron_sum_right, hP.sum_eq_one, smulKron_one_one]
  orthogonal hij := by rw [smulKron_mul, hP.orthogonal hij, smulKron_zero_right]

end SmulKron

/-! ## The two registers of a pair -/

section Lift

variable {R α β : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β]

/-- The first register's matrices acting on the pair of registers, `X ↦ X ⊗ 1_β`. -/
def liftLeft : Matrix α α R →⋆ₐ[ℂ] Matrix (α × β) (α × β) R where
  toFun X := blockDiagonal fun _ : β => X
  map_one' := blockDiagonal_one (m := α) (o := β) (α := R)
  map_mul' X Y := blockDiagonal_mul (fun _ : β => X) (fun _ : β => Y)
  map_zero' := blockDiagonal_zero (m := α) (n := α) (o := β) (α := R)
  map_add' X Y := blockDiagonal_add (fun _ : β => X) (fun _ : β => Y)
  commutes' r := by
    simp only [algebraMap_eq_diagonal]
    rw [blockDiagonal_diagonal]
    rfl
  map_star' X := by
    simp only [star_eq_conjTranspose]
    exact (blockDiagonal_conjTranspose (fun _ : β => X)).symm

theorem liftLeft_apply (X : Matrix α α R) (p q : α × β) :
    liftLeft (β := β) X p q = if p.2 = q.2 then X p.1 q.1 else 0 := by
  show blockDiagonal (fun _ : β => X) p q = _
  exact blockDiagonal_apply _ _ _

/-- The second register's matrices acting on the pair of registers, `Y ↦ 1_α ⊗ Y`: the first
register's lift with the two registers exchanged. -/
def liftRight : Matrix β β R →⋆ₐ[ℂ] Matrix (α × β) (α × β) R where
  toAlgHom := (reindexAlgEquiv ℂ R (Equiv.prodComm β α)).toAlgHom.comp
    (liftLeft (β := α)).toAlgHom
  map_star' Y := by
    show reindex _ _ (liftLeft (star Y)) = star (reindex _ _ (liftLeft Y))
    rw [map_star, star_eq_conjTranspose, star_eq_conjTranspose, conjTranspose_reindex]

theorem liftRight_apply (Y : Matrix β β R) (p q : α × β) :
    liftRight (α := α) Y p q = if p.1 = q.1 then Y p.2 q.2 else 0 := by
  show liftLeft (β := α) Y (Prod.swap p) (Prod.swap q) = _
  exact liftLeft_apply _ _ _

/-- The two registers' matrices multiply entrywise. -/
theorem liftLeft_mul_liftRight (X : Matrix α α R) (Y : Matrix β β R) (p q : α × β) :
    (liftLeft (β := β) X * liftRight (α := α) Y) p q = X p.1 q.1 * Y p.2 q.2 := by
  rw [mul_apply, Finset.sum_eq_single (q.1, p.2)]
  · rw [liftLeft_apply, liftRight_apply, ite_eq_left rfl, ite_eq_left rfl]
  · intro r _ hr
    rw [liftLeft_apply, liftRight_apply]
    by_cases h2 : p.2 = r.2
    · have h1 : r.1 ≠ q.1 := fun h1 => hr (Prod.ext h1 h2.symm)
      rw [ite_eq_right h1, mul_zero]
    · rw [ite_eq_right h2, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem liftRight_mul_liftLeft (X : Matrix α α R) (Y : Matrix β β R) (p q : α × β) :
    (liftRight (α := α) Y * liftLeft (β := β) X) p q = Y p.2 q.2 * X p.1 q.1 := by
  rw [mul_apply, Finset.sum_eq_single (p.1, q.2)]
  · rw [liftLeft_apply, liftRight_apply, ite_eq_left rfl, ite_eq_left rfl]
  · intro r _ hr
    rw [liftLeft_apply, liftRight_apply]
    by_cases h1 : p.1 = r.1
    · have h2 : r.2 ≠ q.2 := fun h2 => hr (Prod.ext h1.symm h2)
      rw [ite_eq_right h2, mul_zero]
    · rw [ite_eq_right h1, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Lift

/-- A `⋆`-algebra homomorphism, applied entrywise to square matrices. -/
def mapMatrixStarAlgHom {A B n : Type*} [Fintype n] [DecidableEq n] [Ring A] [StarRing A]
    [Algebra ℂ A] [Ring B] [StarRing B] [Algebra ℂ B] (f : A →⋆ₐ[ℂ] B) :
    Matrix n n A →⋆ₐ[ℂ] Matrix n n B where
  toAlgHom := (f : A →ₐ[ℂ] B).mapMatrix
  map_star' X := by
    show (star X).map f = star (X.map f)
    simp only [star_eq_conjTranspose]
    exact conjTranspose_map _ fun a => map_star f a

@[simp]
theorem mapMatrixStarAlgHom_apply {A B n : Type*} [Fintype n] [DecidableEq n] [Ring A]
    [StarRing A] [Algebra ℂ A] [Ring B] [StarRing B] [Algebra ℂ B] (f : A →⋆ₐ[ℂ] B)
    (X : Matrix n n A) : mapMatrixStarAlgHom f X = X.map f :=
  rfl

/-- The quadratic form of the identity is the squared norm of the state. -/
theorem StateModel.qform_one_eq_norm_sq {𝒞 : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞]
    (M : StateModel 𝒞) : M.qform 1 = ‖M.ψ‖ ^ 2 := by
  rw [StateModel.qform, map_one]
  exact Op.qform_one_eq _

/-! ## The extension -/

namespace BipartiteModel

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- **The ancilla extension** of a bipartite model by a register `α` for the first player and a
register `β` for the second, in the joint state `e`: the space `H ⊗ ℂ^{α × β}`, the state
`ψ ⊗ e`, the first player's `α × α` matrices over `𝒜` acting as `X ⊗ 1_β` and the second's
`β × β` matrices over `ℬ` acting as `1_α ⊗ Y`. -/
def expand (M : BipartiteModel 𝒞 𝒜 ℬ) (e : α × β → ℂ) :
    BipartiteModel (Matrix (α × β) (α × β) 𝒞) (Matrix α α 𝒜) (Matrix β β ℬ) where
  H := Ampl (α × β) M.H
  ψ := WithLp.toLp 2 fun p => e p • M.ψ
  π := toCLMStarAlgHom.comp (mapMatrixStarAlgHom M.π)
  πA := liftLeft.comp (mapMatrixStarAlgHom M.πA)
  πB := liftRight.comp (mapMatrixStarAlgHom M.πB)
  commute X Y := by
    show _ * _ = _ * _
    ext p q
    simp only [StarAlgHom.comp_apply, mapMatrixStarAlgHom_apply]
    rw [liftLeft_mul_liftRight, liftRight_mul_liftLeft]
    exact (M.commute _ _).eq

variable (M : BipartiteModel 𝒞 𝒜 ℬ) (e : α × β → ℂ)

theorem expand_ψ : (M.expand e).ψ = WithLp.toLp 2 (fun p => e p • M.ψ) :=
  rfl

theorem expand_π_apply (Z : Matrix (α × β) (α × β) 𝒞) :
    (M.expand e).π Z = toCLM (Z.map M.π) :=
  rfl

theorem expand_πA_smulKron (X : 𝒜) (P : Matrix α α ℂ) :
    (M.expand e).πA (smulKron X P) = liftLeft (smulKron (M.πA X) P) := by
  show liftLeft ((smulKron X P).map M.πA) = _
  congr 1
  ext a b
  simp [map_smul]

theorem expand_πB_smulKron (Y : ℬ) (Q : Matrix β β ℂ) :
    (M.expand e).πB (smulKron Y Q) = liftRight (smulKron (M.πB Y) Q) := by
  show liftRight ((smulKron Y Q).map M.πB) = _
  congr 1
  ext a b
  simp [map_smul]

/-- The action of a product operator on a product vector of the amplified space: entrywise, the
model's operator on the model's vector and the scalar Kronecker product on the ancilla's. -/
theorem toCLM_liftLeft_mul_liftRight_smulKron {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (π : 𝒞 →⋆ₐ[ℂ] (H →L[ℂ] H)) (a b : 𝒞)
    (P : Matrix α α ℂ) (Q : Matrix β β ℂ) (ξ : H) :
    toCLM ((liftLeft (smulKron a P) * liftRight (smulKron b Q)).map π)
        (WithLp.toLp 2 fun p => e p • ξ : Ampl (α × β) H)
      = WithLp.toLp 2 (fun p => ((P ⊗ₖ Q) *ᵥ e) p • π (a * b) ξ) := by
  ext p
  rw [toCLM_apply, PiLp.toLp_apply, mulVec, dotProduct, Finset.sum_smul]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_apply, liftLeft_mul_liftRight, smulKron_apply, smulKron_apply, smul_mul_smul_comm,
    kronecker_apply]
  show π ((P p.1 q.1 * Q p.2 q.2) • (a * b)) (e q • ξ) = _
  rw [map_smul, map_smul, _root_.smul_apply, smul_smul, mul_comm (e q)]

omit [DecidableEq α] [DecidableEq β] in
/-- The inner product of two product vectors of the amplified space. -/
theorem inner_toLp_smul {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (c : α × β → ℂ) (ξ η : H) :
    ⟪(WithLp.toLp 2 fun p => e p • ξ : Ampl (α × β) H), WithLp.toLp 2 fun p => c p • η⟫_ℂ
      = (star e ⬝ᵥ c) * ⟪ξ, η⟫_ℂ := by
  rw [PiLp.inner_apply, dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [PiLp.toLp_apply, PiLp.toLp_apply, inner_smul_left, inner_smul_right, Pi.star_apply,
    RCLike.star_def]
  ring

/-- **An operator of product form acts on the extended state factor by factor**: on the model's
state as the model's operator, and on the ancilla's as the Kronecker product of the two scalar
matrices. -/
theorem expand_π_smulKron_ψ (X : 𝒜) (Y : ℬ) (P : Matrix α α ℂ) (Q : Matrix β β ℂ) :
    (M.expand e).π ((M.expand e).πA (smulKron X P) * (M.expand e).πB (smulKron Y Q))
        (M.expand e).ψ
      = WithLp.toLp 2 (fun p => ((P ⊗ₖ Q) *ᵥ e) p • M.π (M.πA X * M.πB Y) M.ψ) := by
  rw [expand_πA_smulKron, expand_πB_smulKron, expand_π_apply, expand_ψ]
  exact toCLM_liftLeft_mul_liftRight_smulKron e M.π _ _ P Q M.ψ

/-- **The quadratic form of a product operator on the extended state**, before real parts. -/
theorem inner_expand_smulKron (X : 𝒜) (Y : ℬ) (P : Matrix α α ℂ) (Q : Matrix β β ℂ) :
    ⟪(M.expand e).ψ, (M.expand e).π ((M.expand e).πA (smulKron X P)
        * (M.expand e).πB (smulKron Y Q)) (M.expand e).ψ⟫_ℂ
      = (star e ⬝ᵥ ((P ⊗ₖ Q) *ᵥ e)) * ⟪M.ψ, M.π (M.πA X * M.πB Y) M.ψ⟫_ℂ := by
  rw [expand_π_smulKron_ψ, expand_ψ]
  exact inner_toLp_smul e _ M.ψ _

/-- The Born probability of a product measurement on the extended state, before the ancilla's
factor is known to be real. -/
theorem bornProb_expand_smulKron_eq (X : 𝒜) (Y : ℬ) (P : Matrix α α ℂ) (Q : Matrix β β ℂ) :
    (M.expand e).bornProb (smulKron X P) (smulKron Y Q)
      = ((star e ⬝ᵥ ((P ⊗ₖ Q) *ᵥ e)) * ⟪M.ψ, M.π (M.πA X * M.πB Y) M.ψ⟫_ℂ).re :=
  congrArg Complex.re (M.inner_expand_smulKron e X Y P Q)

/-- **The Born probability of a product measurement on the extended state factorizes**: the
model's Born probability times the ancilla's. Only the ancilla's two operators need to be
positive: that is what makes their quadratic form real, which is what lets the real part of the
product split. -/
theorem bornProb_expand_smulKron (X : 𝒜) (Y : ℬ) {P : Matrix α α ℂ} {Q : Matrix β β ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    (M.expand e).bornProb (smulKron X P) (smulKron Y Q)
      = MIPRE.bornProb e P Q * M.bornProb X Y := by
  have hre : (star e ⬝ᵥ ((P ⊗ₖ Q) *ᵥ e)).im = 0 :=
    ((Complex.nonneg_iff.mp ((hP.kronecker hQ).dotProduct_mulVec_nonneg e)).2).symm
  rw [bornProb_expand_smulKron_eq, Complex.mul_re, hre, zero_mul, sub_zero]
  rfl

/-- The model's Born probability against the identity is its first player's squared norm. -/
theorem stateSqNorm_eq_bornProb_one (N : BipartiteModel 𝒞 𝒜 ℬ) (a : 𝒜) :
    N.stateSqNorm a = N.bornProb (star a * a) 1 := by
  rw [N.stateSqNorm_eq, bornProb, map_one, mul_one]

/-- **An inert ancilla changes nothing**: the first player's operator `X ⊗ 1` has, on the
extended state, the squared norm `‖e‖²` times the one `X` has on the model's state. -/
theorem stateSqNorm_expand_smulKron_one (X : 𝒜) :
    (M.expand e).stateSqNorm (smulKron X 1) = ‖evec e‖ ^ 2 * M.stateSqNorm X := by
  rw [stateSqNorm_eq_bornProb_one, star_smulKron_one, smulKron_mul, one_mul,
    ← smulKron_one_one (R := ℬ), bornProb_expand_smulKron M e _ _ PosSemidef.one PosSemidef.one,
    stateSqNorm_eq_bornProb_one, norm_evec_sq, MIPRE.bornProb, Matrix.one_kronecker_one,
    Matrix.one_mulVec]

/-- The same for the second player. -/
theorem swap_stateSqNorm_expand_smulKron_one (Y : ℬ) :
    (M.expand e).swap.stateSqNorm (smulKron Y 1) = ‖evec e‖ ^ 2 * M.swap.stateSqNorm Y := by
  rw [stateSqNorm_eq_bornProb_one, bornProb_swap, star_smulKron_one, smulKron_mul, one_mul,
    ← smulKron_one_one (R := 𝒜), bornProb_expand_smulKron M e _ _ PosSemidef.one PosSemidef.one,
    stateSqNorm_eq_bornProb_one, bornProb_swap, norm_evec_sq, MIPRE.bornProb,
    Matrix.one_kronecker_one, Matrix.one_mulVec]

/-- **The norm of the extended state is the product of the norms.** -/
theorem norm_expand_state : ‖(M.expand e).ψ‖ = ‖evec e‖ * ‖M.ψ‖ := by
  have h3 := M.bornProb_expand_smulKron e 1 1 PosSemidef.one PosSemidef.one
  rw [smulKron_one_one, smulKron_one_one] at h3
  have h : ‖(M.expand e).ψ‖ ^ 2 = (‖evec e‖ * ‖M.ψ‖) ^ 2 := by
    rw [← (M.expand e).qform_one_eq_norm_sq, mul_pow, ← M.qform_one_eq_norm_sq,
      show (M.expand e).qform 1 = (M.expand e).bornProb 1 1 by
        rw [BipartiteModel.bornProb, map_one, map_one, mul_one], h3,
      show M.bornProb 1 1 = M.qform 1 by rw [BipartiteModel.bornProb, map_one, map_one, mul_one],
      norm_evec_sq, MIPRE.bornProb, Matrix.one_kronecker_one, Matrix.one_mulVec]
  exact (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).1 h

end BipartiteModel

end MIPRE

end
