/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.ModelIso

@[expose] public section

/-!
# Readings of an extended model along a regrouping of its registers

An extension `M.expand e` of a bipartite model by a register `α` for the first player and a
register `β` for the second (`MIPRE/Foundations/AncillaModel.lean`) fixes which registers each
player holds. The soundness analysis of the Pauli basis test reads one state along several such
assignments, its *cuts*: a register handed across the cut is read by the other player, and nothing
happens to the state. New in Phase 5 of `planning/mipco-track.md`, where the analysis is stated in
a bipartite model; this file is the model form of the matrix regroupings of the registers
(`Matrix.reindex` along `Equiv.prodAssoc` and its relatives) of that analysis.

* **A reading** (`BipartiteModel.recut`): along a bijection `σ : α × β ≃ α' × β'`, the state model
  of `M.expand e`, its space, state and representation unchanged, with the first player's
  `α' × α'` matrices and the second's `β' × β'` matrices acting through `σ`. What is computed in
  the state model (state norms, quadratic forms) is shared by all the readings of one extension.
  The entries of a reading are those of the extension read through `σ` (`recut_πA_apply`,
  `recut_πB_apply`; for the extension itself `expand_πA_apply`, `expand_πB_apply`,
  `expand_πA_mul_πB_apply`).
* **Handing the first player's outer register to the second player** (`moveEquiv`): the operators
  of that reading are operators of the extension (`recut_move_πA`, `recut_move_πB`), so an
  operator of one cut that is a product on the moved register is a product of the two players'
  operators of the other. With `smulKron_eq_diagonal_mul` and `compHom_smulKron_one`, these two
  lemmas are every change of cut the analysis makes.
* **A reading is isomorphic to the extension along the regrouped registers**
  (`BipartiteModel.recutIso`, from the local isometry `BipartiteModel.recutIsom`): the reindexing of
  the `ℓ²` sum, the players' algebras unchanged.
* **The two-sided compression** (`BipartiteModel.bornProb_expand_basisVec`): on the extension at a
  product basis vector (`basisVec`), a Born probability is the Born probability of the two
  reference entries.
-/

noncomputable section

namespace MIPRE

open Matrix OperatorMatrix
open scoped InnerProductSpace Kronecker

/-! ## Reindexing square matrices over a `⋆`-algebra -/

section Reindex

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] {n n' : Type*} [Fintype n]
  [DecidableEq n] [Fintype n'] [DecidableEq n']

/-- `Matrix.reindex` over a `⋆`-algebra, as a unital `⋆`-algebra homomorphism: the homomorphism
underlying `submatrixStarAlgEquiv σ.symm` (`MIPRE/Foundations/ModelIso.lean`), as `πA` and `πB`
of a model are unital. -/
def reindexStarAlgHomR (σ : n ≃ n') : Matrix n n R →⋆ₐ[ℂ] Matrix n' n' R where
  toAlgHom := (Matrix.reindexAlgEquiv ℂ R σ).toAlgHom
  map_star' X := by
    show Matrix.reindex σ σ (star X) = star (Matrix.reindex σ σ X)
    rw [star_eq_conjTranspose, star_eq_conjTranspose, conjTranspose_reindex]

@[simp]
theorem reindexStarAlgHomR_apply (σ : n ≃ n') (X : Matrix n n R) (i j : n') :
    reindexStarAlgHomR σ X i j = X (σ.symm i) (σ.symm j) := rfl

end Reindex

/-! ## Register operators as block matrices -/

section SmulKron

variable {R : Type*} [Ring R] [Algebra ℂ R] {α α' : Type*} [Fintype α] [DecidableEq α]
  [Fintype α']

/-- `X ⊗ P` is `(X ⊗ 1)(1 ⊗ P)`: the element on the diagonal, times the register operator. -/
theorem smulKron_eq_diagonal_mul (X : R) (P : Matrix α α ℂ) :
    smulKron X P = diagonal (fun _ => X) * smulKron 1 P := by
  ext a b
  rw [diagonal_mul, smulKron_apply, smulKron_apply, mul_smul_comm, mul_one]

variable [StarRing R]

/-- A register operator of the outer register, tensored with an element and a register operator of
the inner one, is one register operator of the pair of registers (`Matrix.comp`). -/
theorem compHom_smulKron_smulKron (X : R) (P : Matrix α α ℂ) (Q : Matrix α' α' ℂ) :
    compHom (smulKron (smulKron X P) Q) = smulKron X (Q ⊗ₖ P) := by
  ext p q
  rw [compHom_apply, smulKron_apply, Matrix.smul_apply, smulKron_apply, smul_smul,
    smulKron_apply, kronecker_apply]

/-- **A register operator of the outer register is a register operator of the pair**, acting as
the identity on the inner register. -/
theorem compHom_smulKron_one (Q : Matrix α' α' ℂ) :
    compHom (smulKron (1 : Matrix α α R) Q) = smulKron (1 : R) (Q ⊗ₖ (1 : Matrix α α ℂ)) := by
  rw [← compHom_smulKron_smulKron]
  congr 2
  exact (smulKron_one_one (R := R) (α := α)).symm

end SmulKron

/-! ## Moving a register across the cut, and product basis vectors -/

/-- The regrouping of registers handing the first player's outer register `γ` to the second
player: `((c, a), b) ↦ (a, (c, b))`. -/
def moveEquiv (γ α₀ β : Type*) : (γ × α₀) × β ≃ α₀ × (γ × β) where
  toFun p := (p.1.2, (p.1.1, p.2))
  invFun q := ((q.2.1, q.1), q.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem moveEquiv_apply (γ α₀ β : Type*) (p : (γ × α₀) × β) :
    moveEquiv γ α₀ β p = (p.1.2, (p.1.1, p.2)) := rfl

@[simp]
theorem moveEquiv_symm_apply (γ α₀ β : Type*) (q : α₀ × (γ × β)) :
    (moveEquiv γ α₀ β).symm q = ((q.2.1, q.1), q.2.2) := rfl

section BasisVec

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- The basis vector `|a₀⟩ ⊗ |b₀⟩` of a pair of registers. -/
def basisVec (a₀ : α) (b₀ : β) : α × β → ℂ := fun p => if p = (a₀, b₀) then 1 else 0

theorem basisVec_apply (a₀ : α) (b₀ : β) (p : α × β) :
    basisVec a₀ b₀ p = if p = (a₀, b₀) then 1 else 0 := rfl

/-- Exchanging the two registers exchanges the two reference points. -/
theorem basisVec_swap (a₀ : α) (b₀ : β) (p : β × α) : basisVec a₀ b₀ p.swap = basisVec b₀ a₀ p := by
  simp only [basisVec_apply, Prod.swap_eq_iff_eq_swap, Prod.swap_prod_mk]

/-- A product basis vector is a unit vector. -/
theorem norm_basisVec [Fintype α] [Fintype β] {a₀ : α} {b₀ : β} : ‖evec (basisVec a₀ b₀)‖ = 1 := by
  rw [evec, EuclideanSpace.norm_eq, Finset.sum_eq_single (a₀, b₀)]
  · simp [basisVec_apply]
  · intro p _ hp
    simp [basisVec_apply, hp]
  · intro h
    exact absurd (Finset.mem_univ _) h

end BasisVec

namespace BipartiteModel

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]
variable {α β α' β' : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype α'] [DecidableEq α'] [Fintype β'] [DecidableEq β']

/-! ## Readings of an extension -/

/-- **The reading of an extension along a regrouping of its registers**: the state model of
`M.expand e` (its space, state and representation), with the first player's `α' × α'` matrices and
the second player's `β' × β'` matrices acting through the bijection `σ : α × β ≃ α' × β'`. Two
readings of one extension differ only in their players' representations. -/
def recut (M : BipartiteModel 𝒞 𝒜 ℬ) (e : α × β → ℂ) (σ : α × β ≃ α' × β') :
    BipartiteModel (Matrix (α × β) (α × β) 𝒞) (Matrix α' α' 𝒜) (Matrix β' β' ℬ) where
  toStateModel := (M.expand e).toStateModel
  πA := (reindexStarAlgHomR σ.symm).comp (liftLeft.comp (mapMatrixStarAlgHom M.πA))
  πB := (reindexStarAlgHomR σ.symm).comp (liftRight.comp (mapMatrixStarAlgHom M.πB))
  commute X Y := by
    have h := (M.expand (e ∘ σ.symm)).commute X Y
    show _ * _ = _ * _
    simp only [StarAlgHom.comp_apply]
    rw [← map_mul, ← map_mul]
    exact congrArg _ h.eq

variable (M : BipartiteModel 𝒞 𝒜 ℬ)

/-- Every reading of an extension has the extension's state model. -/
@[simp]
theorem recut_toStateModel (e : α × β → ℂ) (σ : α × β ≃ α' × β') :
    (M.recut e σ).toStateModel = (M.expand e).toStateModel := rfl

/-- The first player's operators of a reading, entry by entry. -/
theorem recut_πA_apply (e : α × β → ℂ) (σ : α × β ≃ α' × β') (X : Matrix α' α' 𝒜)
    (p q : α × β) : (M.recut e σ).πA X p q
      = if (σ p).2 = (σ q).2 then M.πA (X (σ p).1 (σ q).1) else 0 := by
  show liftLeft (X.map M.πA) (σ p) (σ q) = _
  rw [liftLeft_apply, Matrix.map_apply]

/-- The second player's operators of a reading, entry by entry. -/
theorem recut_πB_apply (e : α × β → ℂ) (σ : α × β ≃ α' × β') (Y : Matrix β' β' ℬ)
    (p q : α × β) : (M.recut e σ).πB Y p q
      = if (σ p).1 = (σ q).1 then M.πB (Y (σ p).2 (σ q).2) else 0 := by
  show liftRight (Y.map M.πB) (σ p) (σ q) = _
  rw [liftRight_apply, Matrix.map_apply]

/-- The first player's operators of an extension, entry by entry. -/
theorem expand_πA_apply (e : α × β → ℂ) (X : Matrix α α 𝒜) (p q : α × β) :
    (M.expand e).πA X p q = if p.2 = q.2 then M.πA (X p.1 q.1) else 0 := by
  show liftLeft (X.map M.πA) p q = _
  rw [liftLeft_apply, Matrix.map_apply]

/-- The second player's operators of an extension, entry by entry. -/
theorem expand_πB_apply (e : α × β → ℂ) (Y : Matrix β β ℬ) (p q : α × β) :
    (M.expand e).πB Y p q = if p.1 = q.1 then M.πB (Y p.2 q.2) else 0 := by
  show liftRight (Y.map M.πB) p q = _
  rw [liftRight_apply, Matrix.map_apply]

/-- A product of the two players' operators of an extension, entry by entry. -/
theorem expand_πA_mul_πB_apply (e : α × β → ℂ) (X : Matrix α α 𝒜) (Y : Matrix β β ℬ)
    (p q : α × β) :
    ((M.expand e).πA X * (M.expand e).πB Y) p q = M.πA (X p.1 q.1) * M.πB (Y p.2 q.2) := by
  show (((liftLeft (β := β) (X.map M.πA) * liftRight (α := α) (Y.map M.πB) :
    Matrix (α × β) (α × β) 𝒞)) p q) = _
  rw [liftLeft_mul_liftRight, Matrix.map_apply, Matrix.map_apply]

/-! ## Moving the first player's outer register to the second player -/

variable {γ α₀ : Type*} [Fintype γ] [DecidableEq γ] [Fintype α₀] [DecidableEq α₀]

/-- **Reading lemma for the first player**: once the first player's outer register `γ` is handed
to the second player, an operator `X` of the first player's remaining register `α₀` is the
extension's operator `1_γ ⊗ X`. -/
theorem recut_move_πA (e : (γ × α₀) × β → ℂ) (X : Matrix α₀ α₀ 𝒜) :
    (M.recut e (moveEquiv γ α₀ β)).πA X
      = (M.expand e).πA (compHom (diagonal fun _ : γ => X)) := by
  ext ⟨⟨c, a⟩, b⟩ ⟨⟨c', a'⟩, b'⟩
  rw [recut_πA_apply, expand_πA_apply]
  simp only [moveEquiv, Equiv.coe_fn_mk, compHom_apply, Prod.mk.injEq]
  by_cases hc : c = c' <;> by_cases hb : b = b' <;> simp [hc, hb]

/-- **Reading lemma for the second player**: once the first player's outer register `γ` is handed
to the second player, an operator of the second player that is a product `Q ⊗ Y` of a register
operator `Q` of `γ` and an operator `Y` of the second player's own registers is the product of the
extension's first-player operator `Q ⊗ 1` and second-player operator `Y`. -/
theorem recut_move_πB (e : (γ × α₀) × β → ℂ) (Y : Matrix β β ℬ) (Q : Matrix γ γ ℂ) :
    (M.recut e (moveEquiv γ α₀ β)).πB (compHom (smulKron Y Q))
      = (M.expand e).πA (compHom (smulKron (1 : Matrix α₀ α₀ 𝒜) Q)) * (M.expand e).πB Y := by
  ext ⟨⟨c, a⟩, b⟩ ⟨⟨c', a'⟩, b'⟩
  rw [recut_πB_apply, expand_πA_mul_πB_apply]
  simp only [moveEquiv, Equiv.coe_fn_mk, compHom_apply, smulKron_apply]
  by_cases hc : c = c'
  · subst hc
    by_cases ha : a = a'
    · subst ha
      simp [map_smul]
    · simp [ha]
  · by_cases ha : a = a'
    · subst ha
      simp [map_smul]
    · simp [ha]

/-! ## A reading is isomorphic to the extension along the regrouped registers -/

section RecutIso

/-- The Hilbert space of a reading is the `ℓ²` sum (as for the extension, `BipartiteModel.ampl`). -/
def recutAmpl (e : α × β → ℂ) (σ : α × β ≃ α' × β') :
    (M.recut e σ).H ≃ₗᵢ[ℂ] OperatorMatrix.Ampl (α × β) M.H :=
  LinearIsometryEquiv.refl ℂ _

theorem recutAmpl_apply (e : α × β → ℂ) (σ : α × β ≃ α' × β') (v : (M.recut e σ).H)
    (p : α × β) : M.recutAmpl e σ v p = M.ampl e v p := rfl

/-- **The change of cut as a local isometry**: the extension along the regrouped registers onto
the reading of the original extension, by the reindexing of the `ℓ²` sum, the players' algebras
unchanged. -/
def recutIsom (e : α × β → ℂ) (σ : α × β ≃ α' × β') :
    LocalIsometry (M.expand (e ∘ σ.symm)) (M.recut e σ) where
  W := (M.recutAmpl e σ).symm.toLinearIsometry.comp
    ((OperatorMatrix.amplReindex (H := M.H) σ).comp (M.ampl (e ∘ σ.symm)).toLinearIsometry)
  ΦA := NonUnitalStarAlgHom.id ℂ _
  ΦB := NonUnitalStarAlgHom.id ℂ _
  intertwineA X v := by
    refine (M.recutAmpl e σ).injective (PiLp.ext fun p => ?_)
    show (OperatorMatrix.toCLM (((M.recut e σ).πA X).map M.π)
        (OperatorMatrix.amplReindex σ (M.ampl (e ∘ σ.symm) v))) p =
      OperatorMatrix.amplReindex σ (M.ampl (e ∘ σ.symm)
        ((M.expand (e ∘ σ.symm)).π ((M.expand (e ∘ σ.symm)).πA X) v)) p
    rw [OperatorMatrix.toCLM_apply, OperatorMatrix.amplReindex_apply, expand_π_πA_apply]
    rw [← Equiv.sum_comp σ.symm]
    simp only [Matrix.map_apply, recut_πA_apply, OperatorMatrix.amplReindex_apply,
      Equiv.apply_symm_apply]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single (σ p).2]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · intro h
      exact absurd (Finset.mem_univ _) h
  intertwineB Y v := by
    refine (M.recutAmpl e σ).injective (PiLp.ext fun p => ?_)
    show (OperatorMatrix.toCLM (((M.recut e σ).πB Y).map M.π)
        (OperatorMatrix.amplReindex σ (M.ampl (e ∘ σ.symm) v))) p =
      OperatorMatrix.amplReindex σ (M.ampl (e ∘ σ.symm)
        ((M.expand (e ∘ σ.symm)).π ((M.expand (e ∘ σ.symm)).πB Y) v)) p
    rw [OperatorMatrix.toCLM_apply, OperatorMatrix.amplReindex_apply, expand_π_πB_apply]
    rw [← Equiv.sum_comp σ.symm]
    simp only [Matrix.map_apply, recut_πB_apply, OperatorMatrix.amplReindex_apply,
      Equiv.apply_symm_apply]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single (σ p).1]
    · refine Finset.sum_congr rfl fun b _ => ?_
      simp
    · intro a _ ha
      refine Finset.sum_eq_zero fun b _ => ?_
      simp [Ne.symm ha]
    · intro h
      exact absurd (Finset.mem_univ _) h

theorem recutAmpl_recutIsom_W (e : α × β → ℂ) (σ : α × β ≃ α' × β')
    (v : (M.expand (e ∘ σ.symm)).H) (p : α × β) :
    M.recutAmpl e σ ((M.recutIsom e σ).W v) p = M.ampl (e ∘ σ.symm) v (σ p) :=
  OperatorMatrix.amplReindex_apply σ _ p

@[simp]
theorem recutIsom_ΦA (e : α × β → ℂ) (σ : α × β ≃ α' × β') (X : Matrix α' α' 𝒜) :
    (M.recutIsom e σ).ΦA X = X := rfl

@[simp]
theorem recutIsom_ΦB (e : α × β → ℂ) (σ : α × β ≃ α' × β') (Y : Matrix β' β' ℬ) :
    (M.recutIsom e σ).ΦB Y = Y := rfl

/-- The change of cut carries the state to the state. -/
theorem recutIsom_W_ψ (e : α × β → ℂ) (σ : α × β ≃ α' × β') :
    (M.recutIsom e σ).W (M.expand (e ∘ σ.symm)).ψ = (M.recut e σ).ψ := by
  refine (M.recutAmpl e σ).injective (PiLp.ext fun p => ?_)
  show OperatorMatrix.amplReindex σ (M.ampl (e ∘ σ.symm) (M.expand (e ∘ σ.symm)).ψ) p = e p • M.ψ
  rw [OperatorMatrix.amplReindex_apply, expand_ψ_apply, Function.comp_apply,
    Equiv.symm_apply_apply]

/-- **A reading of an extension is isomorphic to the extension along the regrouped registers**:
the reindexing of the `ℓ²` sum, with the players' algebras unchanged (`recutIsom`). -/
def recutIso (e : α × β → ℂ) (σ : α × β ≃ α' × β') :
    Iso (M.expand (e ∘ σ.symm)) (M.recut e σ) :=
  Iso.ofLocalIsometry (M.recutIsom e σ) (M.recutIsom_W_ψ e σ)
    (fun w => (M.ampl (e ∘ σ.symm)).symm
      (OperatorMatrix.amplReindex (H := M.H) σ.symm (M.recutAmpl e σ w)))
    (fun w => (M.recutAmpl e σ).injective (PiLp.ext fun p => by
      rw [recutAmpl_recutIsom_W]
      show OperatorMatrix.amplReindex (H := M.H) σ.symm (M.recutAmpl e σ w) (σ p) = _
      rw [OperatorMatrix.amplReindex_apply, Equiv.symm_apply_apply]))
    id (fun _ => rfl) (fun _ => rfl) id (fun _ => rfl) (fun _ => rfl)

@[simp]
theorem recutIso_ΦA (e : α × β → ℂ) (σ : α × β ≃ α' × β') (X : Matrix α' α' 𝒜) :
    (M.recutIso e σ).ΦA X = X := rfl

@[simp]
theorem recutIso_ΦB (e : α × β → ℂ) (σ : α × β ≃ α' × β') (Y : Matrix β' β' ℬ) :
    (M.recutIso e σ).ΦB Y = Y := rfl

@[simp]
theorem recutIso_toLocalIsometry (e : α × β → ℂ) (σ : α × β ≃ α' × β') :
    (M.recutIso e σ).toLocalIsometry = M.recutIsom e σ := rfl

end RecutIso

/-! ## The two-sided compression at a product basis vector -/

/-- **The two-sided compression**: on the extension at a product basis vector `|a₀⟩ ⊗ |b₀⟩`, a
Born probability is the Born probability of the two reference entries. -/
theorem bornProb_expand_basisVec (a₀ : α) (b₀ : β) (X : Matrix α α 𝒜) (Y : Matrix β β ℬ) :
    (M.expand (basisVec a₀ b₀)).bornProb X Y = M.bornProb (X a₀ a₀) (Y b₀ b₀) := by
  have hψ : ∀ p : α × β, M.ampl (basisVec a₀ b₀) (M.expand (basisVec a₀ b₀)).ψ p
      = if p = (a₀, b₀) then M.ψ else 0 := fun p => by
    rw [expand_ψ_apply, basisVec]
    split_ifs <;> simp
  have hv : ∀ p : α × β,
      M.ampl (basisVec a₀ b₀) ((M.expand (basisVec a₀ b₀)).π
        ((M.expand (basisVec a₀ b₀)).πA X * (M.expand (basisVec a₀ b₀)).πB Y)
          (M.expand (basisVec a₀ b₀)).ψ) p
        = M.π (M.πA (X p.1 a₀) * M.πB (Y p.2 b₀)) M.ψ := by
    intro p
    rw [map_mul, mul_apply_eq_comp, expand_π_πA_apply]
    rw [Finset.sum_eq_single a₀]
    · rw [expand_π_πB_apply, Finset.sum_eq_single b₀]
      · rw [hψ, ite_eq_left rfl, map_mul, mul_apply_eq_comp]
      · intro b _ hb
        rw [hψ, ite_eq_right (by simp [hb]), map_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · intro a _ ha
      rw [expand_π_πB_apply, Finset.sum_eq_zero, map_zero]
      intro b _
      rw [hψ, ite_eq_right (by simp [ha]), map_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  show (⟪(M.expand (basisVec a₀ b₀)).ψ, (M.expand (basisVec a₀ b₀)).π
      ((M.expand (basisVec a₀ b₀)).πA X * (M.expand (basisVec a₀ b₀)).πB Y)
        (M.expand (basisVec a₀ b₀)).ψ⟫_ℂ).re =
    (⟪M.ψ, M.π (M.πA (X a₀ a₀) * M.πB (Y b₀ b₀)) M.ψ⟫_ℂ).re
  rw [← LinearIsometryEquiv.inner_map_map (M.ampl (basisVec a₀ b₀)), PiLp.inner_apply,
    Finset.sum_eq_single (a₀, b₀)]
  · rw [hv, hψ, ite_eq_left rfl]
  · intro p _ hp
    rw [hψ, ite_eq_right hp, inner_zero_left]
  · intro h
    exact absurd (Finset.mem_univ _) h

end BipartiteModel

end MIPRE

end

end
