/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.AncillaIsometry
public import MIPRE.Foundations.KrausDilation

@[expose] public section

/-!
# A one-sided ancilla, and the fixed-state dilation in a bipartite model

Introspection's adaptive inductions replace a measurement of the first player by a projective one
acting on the old space and a fresh ancilla, prepared in one fixed state for every question
(`MIPRE.Introspection.extVecA` in the matrix analysis). In a bipartite model
(Phase 4 of `planning/mipco-track.md`):

* **The one-sided extension** `BipartiteModel.expandA M t₀`: the first player's register `T`,
  in the basis state `t₀`; the first player's algebra becomes the `T × T` matrices over `𝒜`, the
  second player's is unchanged, acting as `1 ⊗ b`. The state is `M.ψ ⊗ e_{t₀}`
  (`OperatorMatrix.emb`), so a quadratic form, a Born probability or a squared state norm on the
  extension is the one of the `(t₀, t₀)` entry, or of the `t₀`-th column
  (`qform_expandA`, `bornProb_expandA`, `stateSqNorm_expandA`).
* **The inert embedding** `BipartiteModel.inertA M t₀`, a local isometry `M → M.expandA t₀`
  carrying the state to the state, with the first player's operator `a` becoming `a ⊗ 1`.
* **Local isometries extend along registers** (`LocalIsometry.expand`), so the inert embedding
  of the ancilla is one of the register models too.

The fixed-state dilation itself is `MIPRE.exists_pvm_dilation`
(`MIPRE/Foundations/KrausDilation.lean`), in the first player's algebra.
-/

noncomputable section

namespace MIPRE

open Matrix OperatorMatrix
open scoped InnerProductSpace

section Hom

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The constant diagonal `X ↦ X ⊗ 1`, as a unital `⋆`-homomorphism. -/
def diagStarAlgHom : R →⋆ₐ[ℂ] Matrix α α R where
  toFun X := diagonal fun _ => X
  map_one' := diagonal_one
  map_mul' X Y := (diagonal_mul_diagonal _ _).symm
  map_zero' := diagonal_zero
  map_add' X Y := (diagonal_add _ _).symm
  commutes' r := by
    rw [Matrix.algebraMap_eq_diagonal]
    rfl
  map_star' X := by
    show diagonal (fun _ => star X) = star (diagonal fun _ => X)
    rw [star_eq_conjTranspose, diagonal_conjTranspose]
    rfl

@[simp]
theorem diagStarAlgHom_apply (X : R) : diagStarAlgHom (α := α) X = diagonal fun _ => X := rfl

end Hom

namespace BipartiteModel

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]
variable {T : Type*} [Fintype T] [DecidableEq T]

/-- **The one-sided ancilla extension**: a register `T` for the first player only, in the basis
state `t₀`. The space is `H ⊗ ℂ^T`, the state `ψ ⊗ e_{t₀}`, the first player's operators the
`T × T` matrices over `𝒜`, and the second player's `b` acts as `1 ⊗ b`. -/
def expandA (M : BipartiteModel 𝒞 𝒜 ℬ) (t₀ : T) :
    BipartiteModel (Matrix T T 𝒞) (Matrix T T 𝒜) ℬ where
  H := Ampl T M.H
  ψ := emb t₀ M.ψ
  π := toCLMStarAlgHom.comp (mapMatrixStarAlgHom M.π)
  πA := mapMatrixStarAlgHom M.πA
  πB := diagStarAlgHom.comp M.πB
  commute X b := by
    show _ * _ = _ * _
    ext t s
    simp only [mapMatrixStarAlgHom_apply, StarAlgHom.comp_apply, diagStarAlgHom_apply,
      mul_diagonal, diagonal_mul, map_apply]
    exact (M.commute _ _).eq

variable (M : BipartiteModel 𝒞 𝒜 ℬ) (t₀ : T)

theorem expandA_ψ : (M.expandA t₀).ψ = emb t₀ M.ψ := rfl

theorem expandA_π_apply (Z : Matrix T T 𝒞) : (M.expandA t₀).π Z = toCLM (Z.map M.π) := rfl

theorem expandA_πA (X : Matrix T T 𝒜) : (M.expandA t₀).πA X = X.map M.πA := rfl

theorem expandA_πB (b : ℬ) : (M.expandA t₀).πB b = diagonal fun _ => M.πB b := rfl

/-- The norm of the extended state is the norm of the state. -/
theorem norm_expandA_ψ : ‖(M.expandA t₀).ψ‖ = ‖M.ψ‖ := norm_emb t₀ M.ψ

/-- An operator matrix on an embedded vector: its `t₀`-th column. -/
theorem toCLM_emb_apply {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (N : Matrix T T (H →L[ℂ] H)) (ξ : H) (t : T) :
    (toCLM N (emb t₀ ξ) : Ampl T H) t = N t t₀ ξ := by
  rw [toCLM_apply, Finset.sum_eq_single t₀]
  · rw [emb_apply_self]
  · intro s _ hs
    rw [emb_apply_of_ne hs, map_zero]
  · intro h
    exact absurd (Finset.mem_univ t₀) h

/-- **The quadratic form of the extension is that of the `(t₀, t₀)` entry.** -/
theorem qform_expandA (Z : Matrix T T 𝒞) : (M.expandA t₀).qform Z = M.qform (Z t₀ t₀) := by
  show (⟪emb t₀ M.ψ, toCLM (Z.map M.π) (emb t₀ M.ψ)⟫_ℂ).re = (⟪M.ψ, M.π (Z t₀ t₀) M.ψ⟫_ℂ).re
  rw [inner_emb_toCLM_emb, map_apply]

/-- **The squared state norm of the extension is that of the `t₀`-th column.** -/
theorem snorm_sq_expandA (Z : Matrix T T 𝒞) :
    (M.expandA t₀).snorm Z ^ 2 = ∑ t, M.snorm (Z t t₀) ^ 2 := by
  show ‖(toCLM (Z.map M.π) (emb t₀ M.ψ) : Ampl T M.H)‖ ^ 2 = ∑ t, ‖M.π (Z t t₀) M.ψ‖ ^ 2
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_congr rfl fun t _ => by rw [toCLM_emb_apply, map_apply]

/-- **A Born probability on the extension is that of the `(t₀, t₀)` entry.** -/
theorem bornProb_expandA (X : Matrix T T 𝒜) (b : ℬ) :
    (M.expandA t₀).bornProb X b = M.bornProb (X t₀ t₀) b := by
  rw [bornProb, qform_expandA, bornProb]
  congr 1
  rw [expandA_πA, expandA_πB, mul_diagonal, map_apply]

/-- **The first player's squared state norm on the extension**: that of the `t₀`-th column. -/
theorem stateSqNorm_expandA (X : Matrix T T 𝒜) :
    (M.expandA t₀).stateSqNorm X = ∑ t, M.stateSqNorm (X t t₀) := by
  rw [stateSqNorm, stateNorm, snorm_sq_expandA]
  rfl

/-! ## Components -/

/-- The Hilbert space of a one-sided extension is the `ℓ²` sum. -/
def amplA : (M.expandA t₀).H ≃ₗᵢ[ℂ] Ampl T M.H := LinearIsometryEquiv.refl ℂ (Ampl T M.H)

/-- Two vectors of a one-sided extension are equal if their components are. -/
theorem expandA_ext {v w : (M.expandA t₀).H} (h : ∀ t, M.amplA t₀ v t = M.amplA t₀ w t) :
    v = w :=
  (M.amplA t₀).injective (PiLp.ext h)

theorem expandA_π_πA_apply (X : Matrix T T 𝒜) (v : (M.expandA t₀).H) (t : T) :
    M.amplA t₀ ((M.expandA t₀).π ((M.expandA t₀).πA X) v) t =
      ∑ s, M.π (M.πA (X t s)) (M.amplA t₀ v s) := by
  show toCLM ((X.map M.πA).map M.π) (M.amplA t₀ v) t = _
  rw [toCLM_apply]
  rfl

theorem expandA_π_πB_apply (b : ℬ) (v : (M.expandA t₀).H) (t : T) :
    M.amplA t₀ ((M.expandA t₀).π ((M.expandA t₀).πB b) v) t = M.π (M.πB b) (M.amplA t₀ v t) := by
  show toCLM ((diagonal fun _ : T => M.πB b).map M.π) (M.amplA t₀ v) t = _
  rw [diagonal_map (map_zero _), toCLM_diagonal_apply]

theorem expandA_ψ_apply (t : T) :
    M.amplA t₀ (M.expandA t₀).ψ t = if t = t₀ then M.ψ else 0 := by
  show emb t₀ M.ψ t = _
  by_cases h : t = t₀
  · subst h
    rw [emb_apply_self, ite_eq_left rfl]
  · rw [emb_apply_of_ne h, ite_eq_right h]

/-! ## The inert embedding -/

/-- **The inert embedding** of a model into its one-sided extension: the state goes to
`ψ ⊗ e_{t₀}`, the first player's operator `a` to `a ⊗ 1`, the second player's are unchanged. -/
def inertA : LocalIsometry M (M.expandA t₀) where
  W := { toLinearMap := (emb t₀ : M.H →L[ℂ] Ampl T M.H).toLinearMap
         norm_map' := norm_emb t₀ }
  ΦA := diagHom
  ΦB := NonUnitalStarAlgHom.id ℂ ℬ
  intertwineA a v := by
    show toCLM ((diagonal fun _ : T => a).map M.πA |>.map M.π) (emb t₀ v) = emb t₀ _
    rw [diagonal_map (map_zero _), diagonal_map (map_zero _)]
    exact toCLM_diagonal_emb _ t₀ v
  intertwineB b v := by
    show toCLM ((diagonal fun _ : T => M.πB b).map M.π) (emb t₀ v) = emb t₀ _
    rw [diagonal_map (map_zero _)]
    exact toCLM_diagonal_emb _ t₀ v

theorem inertA_W_ψ : (M.inertA t₀).W M.ψ = (M.expandA t₀).ψ := rfl

@[simp]
theorem inertA_ΦA (a : 𝒜) : (M.inertA t₀).ΦA a = diagonal fun _ => a := rfl

@[simp]
theorem inertA_ΦB (b : ℬ) : (M.inertA t₀).ΦB b = b := rfl

/-! ## Local isometries extend along registers -/

section ExtendAlong

variable {M}
variable {𝒞' 𝒜' ℬ' : Type*} [Ring 𝒞'] [StarRing 𝒞'] [Algebra ℂ 𝒞'] [Ring 𝒜'] [StarRing 𝒜']
  [Algebra ℂ 𝒜'] [Ring ℬ'] [StarRing ℬ'] [Algebra ℂ ℬ']
  {M' : BipartiteModel 𝒞' 𝒜' ℬ'}
  {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The entrywise image of a matrix under a non-unital `⋆`-homomorphism, as one. -/
def mapMatrixHom {R S : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [Ring S] [StarRing S]
    [Algebra ℂ S] (f : R →⋆ₙₐ[ℂ] S) : Matrix α α R →⋆ₙₐ[ℂ] Matrix α α S where
  toFun X := X.map f
  map_smul' c X := by
    ext i j
    simp only [map_apply, Matrix.smul_apply, map_smul, MonoidHom.id_apply]
  map_zero' := by
    ext i j
    simp only [map_apply, Matrix.zero_apply, map_zero]
  map_add' X Y := by
    ext i j
    simp only [map_apply, Matrix.add_apply, map_add]
  map_mul' X Y := by
    ext i j
    simp only [map_apply, Matrix.mul_apply, map_sum, map_mul]
  map_star' X := by
    ext i j
    simp only [map_apply, Matrix.star_apply, map_star]

omit [DecidableEq α] in
@[simp]
theorem mapMatrixHom_apply {R S : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [Ring S]
    [StarRing S] [Algebra ℂ S] (f : R →⋆ₙₐ[ℂ] S) (X : Matrix α α R) :
    mapMatrixHom f X = X.map f := rfl

/-- A linear isometry applied in each component of an `ℓ²` sum. -/
def amplMap {ι H H' : Type*} [Fintype ι] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (W : H →ₗᵢ[ℂ] H') :
    Ampl ι H →ₗᵢ[ℂ] Ampl ι H' where
  toFun v := WithLp.toLp 2 fun i => W (v i)
  map_add' v w := by
    ext i
    simp only [PiLp.add_apply, map_add]
  map_smul' c v := by
    ext i
    simp only [PiLp.smul_apply, map_smul, RingHom.id_apply]
  norm_map' v := by
    have h : ‖(WithLp.toLp 2 fun i => W (v i) : Ampl ι H')‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
      exact Finset.sum_congr rfl fun i _ => by rw [PiLp.toLp_apply, LinearIsometry.norm_map]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- The isometry of the extensions by the same register, componentwise. -/
def LocalIsometry.expandW (Φ : LocalIsometry M M') (e : α × β → ℂ) :
    (M.expand e).H →ₗᵢ[ℂ] (M'.expand e).H :=
  (M'.ampl e).symm.toLinearIsometry.comp ((amplMap Φ.W).comp (M.ampl e).toLinearIsometry)

theorem LocalIsometry.ampl_expandW (Φ : LocalIsometry M M') (e : α × β → ℂ)
    (v : (M.expand e).H) (p : α × β) :
    M'.ampl e (Φ.expandW e v) p = Φ.W (M.ampl e v p) := rfl

/-- **A local isometry extends along a register**: the extensions of the two models by the same
registers in the same state, with the players' block matrices mapped entrywise. -/
def LocalIsometry.expand (Φ : LocalIsometry M M') (e : α × β → ℂ) :
    LocalIsometry (M.expand e) (M'.expand e) where
  W := Φ.expandW e
  ΦA := mapMatrixHom Φ.ΦA
  ΦB := mapMatrixHom Φ.ΦB
  intertwineA X v := by
    refine M'.expand_ext e fun p => ?_
    rw [expand_π_πA_apply, Φ.ampl_expandW, expand_π_πA_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mapMatrixHom_apply, map_apply, Φ.ampl_expandW, Φ.intertwineA]
  intertwineB Y v := by
    refine M'.expand_ext e fun p => ?_
    rw [expand_π_πB_apply, Φ.ampl_expandW, expand_π_πB_apply, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [mapMatrixHom_apply, map_apply, Φ.ampl_expandW, Φ.intertwineB]

@[simp]
theorem LocalIsometry.expand_ΦA (Φ : LocalIsometry M M') (e : α × β → ℂ) (X : Matrix α α 𝒜) :
    (Φ.expand e).ΦA X = X.map Φ.ΦA := rfl

@[simp]
theorem LocalIsometry.expand_ΦB (Φ : LocalIsometry M M') (e : α × β → ℂ) (Y : Matrix β β ℬ) :
    (Φ.expand e).ΦB Y = Y.map Φ.ΦB := rfl

/-- The extension carries the state to the state when the local isometry does. -/
theorem LocalIsometry.expand_W_ψ {Φ : LocalIsometry M M'} (h : Φ.W M.ψ = M'.ψ)
    (e : α × β → ℂ) : (Φ.expand e).W (M.expand e).ψ = (M'.expand e).ψ := by
  refine M'.expand_ext e fun p => ?_
  show Φ.W (M.ampl e (M.expand e).ψ p) = M'.ampl e (M'.expand e).ψ p
  rw [expand_ψ_apply, expand_ψ_apply, map_smul, h]

end ExtendAlong

/-! ## Exchanging an ancilla with a register -/

section Exchange

variable {M}
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The exchange of the two layers of a block matrix of block matrices, as a `⋆`-homomorphism:
`X t t' a a'` becomes the entry `(a, a') (t, t')`. -/
def layerSwap {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] :
    Matrix T T (Matrix α α R) →⋆ₙₐ[ℂ] Matrix α α (Matrix T T R) :=
  uncompHom.comp ((submatrixHom (Equiv.prodComm α T)).comp compHom)

omit [DecidableEq T] [DecidableEq α] in
@[simp]
theorem layerSwap_apply {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
    (X : Matrix T T (Matrix α α R)) (a a' : α) (t t' : T) :
    layerSwap X a a' t t' = X t t' a a' := rfl

theorem layerSwap_one {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] :
    layerSwap (T := T) (α := α) (1 : Matrix T T (Matrix α α R)) = 1 := by
  simp only [layerSwap, NonUnitalStarAlgHom.comp_apply, compHom_one, submatrixHom_one,
    uncompHom_one]

/-- The isometry exchanging the ancilla and the register coordinates. -/
def exchangeIsometry (e : α × β → ℂ) :
    ((M.expand e).expandA t₀).H →ₗᵢ[ℂ] ((M.expandA t₀).expand e).H :=
  ((M.expandA t₀).ampl e).symm.toLinearIsometry.comp
    ((LinearIsometryEquiv.piLpCongrRight 2 fun _ : α × β => (M.amplA t₀).symm).toLinearIsometry.comp
      ((amplCurry (ι := α × β) (κ := T) (H := M.H)).comp
        ((amplReindex (H := M.H) (Equiv.prodComm (α × β) T)).comp
          ((amplUncurry (ι := T) (κ := α × β) (H := M.H)).comp
            ((LinearIsometryEquiv.piLpCongrRight 2 fun _ : T => M.ampl e).toLinearIsometry.comp
              ((M.expand e).amplA t₀).toLinearIsometry)))))

theorem ampl_exchangeIsometry (e : α × β → ℂ) (v : ((M.expand e).expandA t₀).H) (p : α × β)
    (t : T) :
    M.amplA t₀ ((M.expandA t₀).ampl e (M.exchangeIsometry t₀ e v) p) t =
      M.ampl e ((M.expand e).amplA t₀ v t) p := rfl

/-- **The exchange of a one-sided ancilla with a register**: the one-sided extension of an
extension into the extension of the one-sided extension, the first player's block matrices of
block matrices exchanged layer for layer (`layerSwap`), the second player's unchanged. -/
def exchange (e : α × β → ℂ) :
    LocalIsometry ((M.expand e).expandA t₀) ((M.expandA t₀).expand e) where
  W := M.exchangeIsometry t₀ e
  ΦA := layerSwap
  ΦB := NonUnitalStarAlgHom.id ℂ _
  intertwineA X v := by
    refine (M.expandA t₀).expand_ext e fun p => ?_
    refine M.expandA_ext t₀ fun t => ?_
    rw [expand_π_πA_apply, ampl_exchangeIsometry, expandA_π_πA_apply (M.expand e), map_sum,
      map_sum, WithLp.ofLp_sum, WithLp.ofLp_sum, Finset.sum_apply, Finset.sum_apply]
    simp only [expandA_π_πA_apply, expand_π_πA_apply, ampl_exchangeIsometry]
    rw [Finset.sum_comm]
    rfl
  intertwineB Y v := by
    refine (M.expandA t₀).expand_ext e fun p => ?_
    refine M.expandA_ext t₀ fun t => ?_
    rw [expand_π_πB_apply, ampl_exchangeIsometry, map_sum, WithLp.ofLp_sum, Finset.sum_apply]
    simp only [expandA_π_πB_apply, ampl_exchangeIsometry]
    rw [expand_π_πB_apply]
    rfl

theorem exchange_W_ψ (e : α × β → ℂ) :
    (M.exchange t₀ e).W ((M.expand e).expandA t₀).ψ = ((M.expandA t₀).expand e).ψ := by
  refine (M.expandA t₀).expand_ext e fun p => ?_
  refine M.expandA_ext t₀ fun t => ?_
  show M.amplA t₀ ((M.expandA t₀).ampl e (M.exchangeIsometry t₀ e _) p) t = _
  rw [ampl_exchangeIsometry, expandA_ψ_apply, expand_ψ_apply, map_smul, PiLp.smul_apply,
    expandA_ψ_apply]
  by_cases h : t = t₀
  · rw [ite_eq_left h, ite_eq_left h, expand_ψ_apply]
  · rw [ite_eq_right h, ite_eq_right h, smul_zero]
    rfl

@[simp]
theorem exchange_ΦA (e : α × β → ℂ) (X : Matrix T T (Matrix α α 𝒜)) :
    (M.exchange t₀ e).ΦA X = layerSwap X := rfl

@[simp]
theorem exchange_ΦB (e : α × β → ℂ) (Y : Matrix β β ℬ) : (M.exchange t₀ e).ΦB Y = Y := rfl

end Exchange

end BipartiteModel

end MIPRE

end
