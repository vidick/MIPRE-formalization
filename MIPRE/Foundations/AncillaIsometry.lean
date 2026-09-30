/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.AncillaModel
public import MIPRE.Foundations.LocalIsometry

@[expose] public section

/-!
# Local isometries between ancilla extensions

The introspection analysis moves a strategy between extensions of one bipartite model by finite
registers (`BipartiteModel.expand`): it splits a register into two, relabels one, adjoins one on
which the strategy does nothing, reads a register on the other player's side, and adjoins the
answer register of a Naimark dilation. In the tensor-product model each of these is a
permutation of computational basis labels of `ℂ^{register} ⊗ ℂ^{d}`
(`MIPRE.Introspection.registerOp`, `registerParty`, `registerExtend`). In a bipartite model each
is a local isometry (`BipartiteModel.LocalIsometry`) carrying the state of one extension exactly
to the state of the other, so that it carries every Born probability and state norm over
(`LocalIsometry.bornProb_of_W_ψ`, `LocalIsometry.stateSqNorm_of_W_ψ`). Four of them generate the
rest:

* **an inert ancilla** (`BipartiteModel.inert`): `M` into `M.expand e` for a unit vector `e`,
  the players' operators acting as `X ⊗ 1`;
* **a relabelling of the registers** (`BipartiteModel.relabel`);
* **associativity** (`BipartiteModel.assoc`): an extension of an extension is an extension by
  the product registers, the players' block matrices of block matrices becoming block matrices
  (`Matrix.comp`);
* **the exchange of the players** (`BipartiteModel.swapExpand`): the extension of the exchanged
  model is the exchanged extension.

The entrywise action of an extension's operators (`expand_π_πA_apply`, `expand_π_πB_apply`) is
what every intertwining identity here reduces to.
-/

noncomputable section

namespace MIPRE

open scoped InnerProductSpace
open Matrix OperatorMatrix

/-! ## Isometries of `ℓ²` sums -/

namespace OperatorMatrix

variable {ι κ H : Type*} [Fintype ι] [Fintype κ] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The isometry of `ℓ²` sums induced by a bijection of the index sets: `(v ↦ v ∘ e)`. -/
def amplReindex (e : κ ≃ ι) : Ampl ι H →ₗᵢ[ℂ] Ampl κ H :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ H e.symm).toLinearIsometry

@[simp]
theorem amplReindex_apply (e : κ ≃ ι) (v : Ampl ι H) (k : κ) : amplReindex e v k = v (e k) := by
  simp [amplReindex, Equiv.piCongrLeft']

/-- The `ℓ²` sum of `ℓ²` sums, as one `ℓ²` sum over the pairs of indices. -/
def amplUncurry : Ampl ι (Ampl κ H) →ₗᵢ[ℂ] Ampl (ι × κ) H where
  toFun v := WithLp.toLp 2 fun q => v q.1 q.2
  map_add' v w := by
    ext q
    simp only [PiLp.add_apply]
  map_smul' c v := by
    ext q
    simp only [PiLp.smul_apply, RingHom.id_apply]
  norm_map' v := by
    have h : ‖(WithLp.toLp 2 fun q : ι × κ => v q.1 q.2 : Ampl (ι × κ) H)‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [PiLp.norm_sq_eq_of_L2]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

@[simp]
theorem amplUncurry_apply (v : Ampl ι (Ampl κ H)) (q : ι × κ) :
    amplUncurry v q = v q.1 q.2 := rfl

end OperatorMatrix

/-! ## Matrices over a star ring as `⋆`-homomorphisms -/

section Hom

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
variable {α α' : Type*} [Fintype α] [DecidableEq α] [Fintype α'] [DecidableEq α']

/-- The constant diagonal `X ↦ X ⊗ 1`, as a `⋆`-homomorphism. -/
def diagHom : R →⋆ₙₐ[ℂ] Matrix α α R where
  toFun X := diagonal fun _ => X
  map_smul' c X := by
    ext i j
    by_cases h : i = j
    · subst h
      simp only [diagonal_apply_eq, MonoidHom.id_apply, Matrix.smul_apply]
    · simp only [diagonal_apply_ne _ h, MonoidHom.id_apply, Matrix.smul_apply, smul_zero]
  map_zero' := diagonal_zero
  map_add' X Y := (diagonal_add _ _).symm
  map_mul' X Y := (diagonal_mul_diagonal _ _).symm
  map_star' X := by
    show diagonal (fun _ => star X) = star (diagonal fun _ => X)
    rw [star_eq_conjTranspose, diagonal_conjTranspose]
    rfl

@[simp]
theorem diagHom_apply (X : R) : diagHom (α := α) X = diagonal fun _ => X := rfl

theorem diagHom_one : diagHom (α := α) (1 : R) = 1 := diagonal_one

/-- Relabelling the rows and columns of a square matrix along a bijection, as a
`⋆`-homomorphism. -/
def submatrixHom (f : α' ≃ α) : Matrix α α R →⋆ₙₐ[ℂ] Matrix α' α' R where
  toFun X := X.submatrix f f
  map_smul' c X := by
    ext i j
    simp only [submatrix_apply, Matrix.smul_apply, MonoidHom.id_apply]
  map_zero' := by
    ext i j
    simp only [submatrix_apply, Matrix.zero_apply]
  map_add' X Y := by
    ext i j
    simp only [submatrix_apply, Matrix.add_apply]
  map_mul' X Y := (submatrix_mul_equiv X Y f f f).symm
  map_star' X := by
    show (star X).submatrix f f = star (X.submatrix f f)
    rw [star_eq_conjTranspose, star_eq_conjTranspose, conjTranspose_submatrix]

omit [DecidableEq α] [DecidableEq α'] in
@[simp]
theorem submatrixHom_apply (f : α' ≃ α) (X : Matrix α α R) :
    submatrixHom f X = X.submatrix f f := rfl

theorem submatrixHom_one (f : α' ≃ α) : submatrixHom f (1 : Matrix α α R) = 1 :=
  submatrix_one_equiv f

/-- Block matrices of block matrices as block matrices over the pairs (`Matrix.comp`), as a
`⋆`-homomorphism. -/
def compHom : Matrix α' α' (Matrix α α R) →⋆ₙₐ[ℂ] Matrix (α' × α) (α' × α) R where
  toFun X := comp α' α' α α R X
  map_smul' c X := by
    ext p q
    simp only [comp_apply, Matrix.smul_apply, MonoidHom.id_apply]
  map_zero' := by
    ext p q
    simp only [comp_apply, Matrix.zero_apply]
  map_add' X Y := by
    ext p q
    simp only [comp_apply, Matrix.add_apply]
  map_mul' X Y := (compRingEquiv α' α R).map_mul X Y
  map_star' X := by
    ext p q
    simp only [comp_apply, Matrix.star_apply]

omit [DecidableEq α] [DecidableEq α'] in
@[simp]
theorem compHom_apply (X : Matrix α' α' (Matrix α α R)) (p q : α' × α) :
    compHom X p q = X p.1 q.1 p.2 q.2 := rfl

theorem compHom_one : compHom (1 : Matrix α' α' (Matrix α α R)) = 1 := comp_one

end Hom

namespace BipartiteModel

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] (M : BipartiteModel 𝒞 𝒜 ℬ)
variable {α β α' β' α'' β'' : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype α'] [DecidableEq α'] [Fintype β'] [DecidableEq β'] [Fintype α''] [DecidableEq α'']
  [Fintype β''] [DecidableEq β'']

/-! ## The action of an extension, entry by entry

A vector of an extension is a vector of the `ℓ²` sum `Ampl (α × β) M.H`, definitionally but not
syntactically; `BipartiteModel.ampl` is that identification, as an isometry, so that the
components of a vector of an extension can be read and rewritten. -/

/-- The Hilbert space of an extension is the `ℓ²` sum. -/
def ampl (e : α × β → ℂ) : (M.expand e).H ≃ₗᵢ[ℂ] Ampl (α × β) M.H :=
  LinearIsometryEquiv.refl ℂ (Ampl (α × β) M.H)

/-- Two vectors of an extension are equal if their components are. -/
theorem expand_ext (e : α × β → ℂ) {v w : (M.expand e).H}
    (h : ∀ p, M.ampl e v p = M.ampl e w p) : v = w :=
  (M.ampl e).injective (PiLp.ext h)

/-- The first player's operators of an extension act on the first register. -/
theorem expand_π_πA_apply (e : α × β → ℂ) (X : Matrix α α 𝒜) (v : (M.expand e).H)
    (p : α × β) :
    M.ampl e ((M.expand e).π ((M.expand e).πA X) v) p =
      ∑ a, M.π (M.πA (X p.1 a)) (M.ampl e v (a, p.2)) := by
  show toCLM ((liftLeft (X.map M.πA)).map M.π) (M.ampl e v) p = _
  rw [toCLM_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single p.2]
  · rw [map_apply, liftLeft_apply, ite_eq_left rfl, map_apply]
  · intro b _ hb
    rw [map_apply, liftLeft_apply, ite_eq_right (Ne.symm hb), map_zero, _root_.zero_apply]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The second player's operators of an extension act on the second register. -/
theorem expand_π_πB_apply (e : α × β → ℂ) (Y : Matrix β β ℬ) (v : (M.expand e).H)
    (p : α × β) :
    M.ampl e ((M.expand e).π ((M.expand e).πB Y) v) p =
      ∑ b, M.π (M.πB (Y p.2 b)) (M.ampl e v (p.1, b)) := by
  show toCLM ((liftRight (Y.map M.πB)).map M.π) (M.ampl e v) p = _
  rw [toCLM_apply, Fintype.sum_prod_type, Finset.sum_eq_single p.1]
  · refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_apply, liftRight_apply, ite_eq_left rfl, map_apply]
  · intro a _ ha
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [map_apply, liftRight_apply, ite_eq_right (Ne.symm ha), map_zero, _root_.zero_apply]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem expand_ψ_apply (e : α × β → ℂ) (p : α × β) :
    M.ampl e (M.expand e).ψ p = e p • M.ψ := rfl

/-! ## An inert ancilla -/

/-- The vector `e ⊗ v` of the `ℓ²` sum. -/
def tensorLeft (e : α × β → ℂ) : M.H →ₗ[ℂ] Ampl (α × β) M.H where
  toFun v := WithLp.toLp 2 fun p => e p • v
  map_add' v w := by
    ext p
    simp only [PiLp.add_apply, smul_add]
  map_smul' c v := by
    ext p
    simp only [PiLp.smul_apply, RingHom.id_apply, smul_comm (e p) c v]

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
@[simp]
theorem tensorLeft_apply (e : α × β → ℂ) (v : M.H) (p : α × β) :
    M.tensorLeft e v p = e p • v := rfl

omit [DecidableEq α] [DecidableEq β] in
theorem norm_tensorLeft (e : α × β → ℂ) (v : M.H) : ‖M.tensorLeft e v‖ = ‖evec e‖ * ‖v‖ := by
  have h : ‖M.tensorLeft e v‖ ^ 2 = (‖evec e‖ * ‖v‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, mul_pow, evec, EuclideanSpace.norm_eq,
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [tensorLeft_apply, norm_smul, mul_pow]
  exact (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).1 h

/-- `v ↦ e ⊗ v`, an isometry into the extension for a unit vector `e`. -/
def ancillaIsometry (e : α × β → ℂ) (he : ‖evec e‖ = 1) : M.H →ₗᵢ[ℂ] (M.expand e).H :=
  (M.ampl e).symm.toLinearIsometry.comp
    { toLinearMap := M.tensorLeft e
      norm_map' := fun v => by
        show ‖M.tensorLeft e v‖ = ‖v‖
        rw [norm_tensorLeft, he, one_mul] }

@[simp]
theorem ampl_ancillaIsometry (e : α × β → ℂ) (he : ‖evec e‖ = 1) (v : M.H) :
    M.ampl e (M.ancillaIsometry e he v) = M.tensorLeft e v := rfl

/-- **An inert ancilla** in the unit vector `e`: `M` into its extension, the players' operators
acting as `X ⊗ 1`. It carries the state of `M` to the state of the extension. -/
def inert (e : α × β → ℂ) (he : ‖evec e‖ = 1) : LocalIsometry M (M.expand e) where
  W := M.ancillaIsometry e he
  ΦA := diagHom
  ΦB := diagHom
  intertwineA a v := by
    refine M.expand_ext e fun p => ?_
    rw [diagHom_apply, expand_π_πA_apply, ampl_ancillaIsometry, Finset.sum_eq_single p.1]
    · rw [diagonal_apply_eq, tensorLeft_apply, ampl_ancillaIsometry, tensorLeft_apply, map_smul]
    · intro a' _ ha'
      rw [diagonal_apply_ne _ (Ne.symm ha'), map_zero, map_zero, _root_.zero_apply]
    · intro h
      exact absurd (Finset.mem_univ _) h
  intertwineB b v := by
    refine M.expand_ext e fun p => ?_
    rw [diagHom_apply, expand_π_πB_apply, ampl_ancillaIsometry, Finset.sum_eq_single p.2]
    · rw [diagonal_apply_eq, tensorLeft_apply, ampl_ancillaIsometry, tensorLeft_apply, map_smul]
    · intro b' _ hb'
      rw [diagonal_apply_ne _ (Ne.symm hb'), map_zero, map_zero, _root_.zero_apply]
    · intro h
      exact absurd (Finset.mem_univ _) h

theorem inert_W_ψ (e : α × β → ℂ) (he : ‖evec e‖ = 1) :
    (M.inert e he).W M.ψ = (M.expand e).ψ := rfl

@[simp]
theorem inert_ΦA (e : α × β → ℂ) (he : ‖evec e‖ = 1) (a : 𝒜) :
    (M.inert e he).ΦA a = diagonal fun _ => a := rfl

@[simp]
theorem inert_ΦB (e : α × β → ℂ) (he : ‖evec e‖ = 1) (b : ℬ) :
    (M.inert e he).ΦB b = diagonal fun _ => b := rfl

/-! ## Relabelling the registers -/

/-- The isometry of the extensions relabelling the registers along `f` and `g`. -/
def relabelIsometry (e : α × β → ℂ) (e' : α' × β' → ℂ) (f : α' ≃ α) (g : β' ≃ β) :
    (M.expand e).H →ₗᵢ[ℂ] (M.expand e').H :=
  (M.ampl e').symm.toLinearIsometry.comp
    ((amplReindex (H := M.H) (f.prodCongr g)).comp (M.ampl e).toLinearIsometry)

@[simp]
theorem ampl_relabelIsometry (e : α × β → ℂ) (e' : α' × β' → ℂ) (f : α' ≃ α) (g : β' ≃ β)
    (v : (M.expand e).H) (p : α' × β') :
    M.ampl e' (M.relabelIsometry e e' f g v) p = M.ampl e v (f p.1, g p.2) := rfl

/-- **A relabelling of the registers**, along bijections `f` and `g`, from the extension in `e`
to the extension in the relabelled vector `e'`. -/
def relabel (e : α × β → ℂ) (e' : α' × β' → ℂ) (f : α' ≃ α) (g : β' ≃ β) :
    LocalIsometry (M.expand e) (M.expand e') where
  W := M.relabelIsometry e e' f g
  ΦA := submatrixHom f
  ΦB := submatrixHom g
  intertwineA a v := by
    refine M.expand_ext e' fun p => ?_
    rw [submatrixHom_apply, expand_π_πA_apply, ampl_relabelIsometry, expand_π_πA_apply]
    exact Fintype.sum_equiv f _ _ fun a' => by
      rw [submatrix_apply, ampl_relabelIsometry]
  intertwineB b v := by
    refine M.expand_ext e' fun p => ?_
    rw [submatrixHom_apply, expand_π_πB_apply, ampl_relabelIsometry, expand_π_πB_apply]
    exact Fintype.sum_equiv g _ _ fun b' => by
      rw [submatrix_apply, ampl_relabelIsometry]

theorem relabel_W_ψ (e : α × β → ℂ) (e' : α' × β' → ℂ) (f : α' ≃ α) (g : β' ≃ β)
    (he : ∀ p, e' p = e (f p.1, g p.2)) :
    (M.relabel e e' f g).W (M.expand e).ψ = (M.expand e').ψ := by
  refine M.expand_ext e' fun p => ?_
  show M.ampl e' (M.relabelIsometry e e' f g (M.expand e).ψ) p = _
  rw [ampl_relabelIsometry, expand_ψ_apply, expand_ψ_apply, he]

@[simp]
theorem relabel_ΦA (e : α × β → ℂ) (e' : α' × β' → ℂ) (f : α' ≃ α) (g : β' ≃ β)
    (a : Matrix α α 𝒜) : (M.relabel e e' f g).ΦA a = a.submatrix f f := rfl

@[simp]
theorem relabel_ΦB (e : α × β → ℂ) (e' : α' × β' → ℂ) (f : α' ≃ α) (g : β' ≃ β)
    (b : Matrix β β ℬ) : (M.relabel e e' f g).ΦB b = b.submatrix g g := rfl

/-! ## Associativity -/

/-- The isometry of an extension of an extension onto the extension by the product
registers. -/
def assocIsometry (e : α × β → ℂ) (e' : α' × β' → ℂ) (e'' : (α' × α) × (β' × β) → ℂ) :
    ((M.expand e).expand e').H →ₗᵢ[ℂ] (M.expand e'').H :=
  (M.ampl e'').symm.toLinearIsometry.comp
    ((amplReindex (H := M.H) (Equiv.prodProdProdComm α' α β' β)).comp
      ((amplUncurry (ι := α' × β') (κ := α × β) (H := M.H)).comp
        ((LinearIsometryEquiv.piLpCongrRight 2 fun _ : α' × β' => M.ampl e).toLinearIsometry.comp
          ((M.expand e).ampl e').toLinearIsometry)))

@[simp]
theorem ampl_assocIsometry (e : α × β → ℂ) (e' : α' × β' → ℂ) (e'' : (α' × α) × (β' × β) → ℂ)
    (v : ((M.expand e).expand e').H) (q : (α' × α) × (β' × β)) :
    M.ampl e'' (M.assocIsometry e e' e'' v) q =
      M.ampl e ((M.expand e).ampl e' v (q.1.1, q.2.1)) (q.1.2, q.2.2) := rfl

/-- **Associativity**: the extension in `e'` of the extension in `e` into the extension by the
product registers, in any vector `e''` that is the product of the two. -/
def assoc (e : α × β → ℂ) (e' : α' × β' → ℂ) (e'' : (α' × α) × (β' × β) → ℂ) :
    LocalIsometry ((M.expand e).expand e') (M.expand e'') where
  W := M.assocIsometry e e' e''
  ΦA := compHom
  ΦB := compHom
  intertwineA a v := by
    refine M.expand_ext e'' fun q => ?_
    rw [expand_π_πA_apply, ampl_assocIsometry, (M.expand e).expand_π_πA_apply e' a v,
      map_sum, WithLp.ofLp_sum, Finset.sum_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [expand_π_πA_apply]
    rfl
  intertwineB b v := by
    refine M.expand_ext e'' fun q => ?_
    rw [expand_π_πB_apply, ampl_assocIsometry, (M.expand e).expand_π_πB_apply e' b v,
      map_sum, WithLp.ofLp_sum, Finset.sum_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [expand_π_πB_apply]
    rfl

theorem assoc_W_ψ (e : α × β → ℂ) (e' : α' × β' → ℂ) (e'' : (α' × α) × (β' × β) → ℂ)
    (he : ∀ q, e'' q = e' (q.1.1, q.2.1) * e (q.1.2, q.2.2)) :
    (M.assoc e e' e'').W ((M.expand e).expand e').ψ = (M.expand e'').ψ := by
  refine M.expand_ext e'' fun q => ?_
  show M.ampl e'' (M.assocIsometry e e' e'' ((M.expand e).expand e').ψ) q = _
  rw [ampl_assocIsometry, expand_ψ_apply, map_smul, PiLp.smul_apply, expand_ψ_apply,
    expand_ψ_apply, he, mul_smul]

@[simp]
theorem assoc_ΦA (e : α × β → ℂ) (e' : α' × β' → ℂ) (e'' : (α' × α) × (β' × β) → ℂ)
    (a : Matrix α' α' (Matrix α α 𝒜)) : (M.assoc e e' e'').ΦA a = compHom a := rfl

@[simp]
theorem assoc_ΦB (e : α × β → ℂ) (e' : α' × β' → ℂ) (e'' : (α' × α) × (β' × β) → ℂ)
    (b : Matrix β' β' (Matrix β β ℬ)) : (M.assoc e e' e'').ΦB b = compHom b := rfl

/-! ## Exchanging the players -/

/-- The isometry of the exchanged extension onto the extension of the exchanged model. -/
def swapIsometry (e : α × β → ℂ) (e' : β × α → ℂ) :
    (M.expand e).swap.H →ₗᵢ[ℂ] (M.swap.expand e').H :=
  (M.swap.ampl e').symm.toLinearIsometry.comp
    ((amplReindex (H := M.H) (Equiv.prodComm β α)).comp (M.ampl e).toLinearIsometry)

@[simp]
theorem ampl_swapIsometry (e : α × β → ℂ) (e' : β × α → ℂ) (v : (M.expand e).swap.H)
    (p : β × α) : M.swap.ampl e' (M.swapIsometry e e' v) p = M.ampl e v p.swap := rfl

/-- **The exchange of the players**: the exchanged extension into the extension of the exchanged
model, in the exchanged vector. -/
def swapExpand (e : α × β → ℂ) (e' : β × α → ℂ) :
    LocalIsometry (M.expand e).swap (M.swap.expand e') where
  W := M.swapIsometry e e'
  ΦA := NonUnitalStarAlgHom.id ℂ _
  ΦB := NonUnitalStarAlgHom.id ℂ _
  intertwineA b v := by
    refine M.swap.expand_ext e' fun p => ?_
    show M.swap.ampl e' ((M.swap.expand e').π ((M.swap.expand e').πA b)
        (M.swapIsometry e e' v)) p =
      M.swap.ampl e' (M.swapIsometry e e' ((M.expand e).π ((M.expand e).πB b) v)) p
    rw [expand_π_πA_apply]
    exact (M.expand_π_πB_apply e b v p.swap).symm
  intertwineB a v := by
    refine M.swap.expand_ext e' fun p => ?_
    show M.swap.ampl e' ((M.swap.expand e').π ((M.swap.expand e').πB a)
        (M.swapIsometry e e' v)) p =
      M.swap.ampl e' (M.swapIsometry e e' ((M.expand e).π ((M.expand e).πA a) v)) p
    rw [expand_π_πB_apply]
    exact (M.expand_π_πA_apply e a v p.swap).symm

theorem swapExpand_W_ψ (e : α × β → ℂ) (e' : β × α → ℂ) (he : ∀ p, e' p = e p.swap) :
    (M.swapExpand e e').W (M.expand e).swap.ψ = (M.swap.expand e').ψ := by
  refine M.swap.expand_ext e' fun p => ?_
  show M.ampl e (M.expand e).ψ p.swap = M.swap.ampl e' (M.swap.expand e').ψ p
  rw [expand_ψ_apply, expand_ψ_apply, he]
  rfl

end BipartiteModel

end MIPRE

end
