/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.DyadicPair

@[expose] public section

/-!
# Block-diagonal operators on `H ⊕ H`

The doubling of a finite pair (`reports/c6b-paper-proofs.md`, §4; built in
`MIPRE/Background/LIDT/Co/Doubling/`) acts on `H ⊕ H = Ampl (Fin 2) H`, the first player by the
block-diagonal operators `u ⊕ v` and the second by `v ⊕ u`, with the state `(ψ, ψ)/√2` and the flip
`(ξ, η) ↦ (η, ξ)` exchanging them. This file collects the facts about these operators that name
no model:

* **Diagonal operators** of any finite amplification: `toCLM (diagonal d)` acts on the `i`-th copy
  by `d i` (`toCLM_diagonal_emb_apply`), is positive exactly when every `d i` is
  (`toCLM_diagonal_nonneg_iff`), and determines `d` (`toCLM_diagonal_inj`); an operator commutes
  with it exactly when its entries intertwine the `d i` (`commute_toCLM_diagonal_iff`).
* **The pair embedding** `diag2 : (H →L[ℂ] H) × (H →L[ℂ] H) →⋆ₐ[ℂ] B(H ⊕ H)`,
  `(u, v) ↦ u ⊕ v`, a unital `⋆`-homomorphism (`diag2_apply`), injective.
* **The flip** `flip2` of the two copies, a self-inverse isometry, which conjugates `u ⊕ v` to
  `v ⊕ u` (`flip2_diag2_flip2`).
* **The half vector** `halfVec ψ = (ψ, ψ)/√2`, fixed by the flip, of the norm of `ψ`, at which a
  block-diagonal operator has the average of its blocks' expectations
  (`inner_halfVec_toCLM_diagonal`, Lemma 2 of the report).
* **Traces** (`VecTrace.diag2`): faithful tracial vector functionals `τ` on `s` and `σ` on `t` give
  one on the block-diagonal operators `u ⊕ v` with `u ∈ s`, `v ∈ t`, namely
  `½ (τ(u) + σ(v))` (`VecTrace.tr_diag2`), from the vectors `(gₖ, 0)/√2` and `(0, hₗ)/√2`
  (Lemma 9).
* **No abelian projections** (`NoAbelianProj`, `noAbelianProj_diag2Set_iff`): the hypothesis
  `hII` of the orthonormalization tier `povm_orthogonalization_finitePair` holds for the
  block-diagonal operators over `s` and `t` exactly when it holds for both (Lemma 11, Theorem F);
  both algebras of a dyadic pair satisfy it (`IsDyadicPair.noAbelianProj_opsA`, `_opsB`).
-/

namespace MIPRE

open scoped InnerProductSpace
open Matrix

namespace OperatorMatrix

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## Diagonal operators of an amplification -/

section Diagonal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [CompleteSpace H] in
/-- A diagonal matrix acts on the `i₀`-th copy by its `i₀`-th entry. -/
theorem toCLM_diagonal_emb_apply (d : ι → H →L[ℂ] H) (i₀ : ι) (ξ : H) :
    toCLM (diagonal d) (emb i₀ ξ) = emb i₀ (d i₀ ξ) := by
  ext i
  rw [toCLM_diagonal_apply]
  by_cases h : i = i₀
  · subst h
    rw [emb_apply_self, emb_apply_self]
  · rw [emb_apply_of_ne h, emb_apply_of_ne h, map_zero]

omit [Fintype ι] [CompleteSpace H] in
/-- The embedding of a copy is injective. -/
theorem emb_injective (i₀ : ι) : Function.Injective (emb (H := H) i₀) := fun ξ η h => by
  rw [← emb_apply_self i₀ ξ, h, emb_apply_self]

omit [CompleteSpace H] in
/-- **A diagonal operator is positive exactly when its entries are.** -/
theorem toCLM_diagonal_nonneg_iff (d : ι → H →L[ℂ] H) :
    0 ≤ toCLM (diagonal d) ↔ ∀ i, 0 ≤ d i := by
  simp only [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_def]
  constructor
  · rintro ⟨hsymm, hpos⟩ i
    refine ⟨fun ξ η => ?_, fun ξ => ?_⟩
    · have := hsymm (emb i ξ) (emb i η)
      simp only [ContinuousLinearMap.coe_coe, toCLM_diagonal_emb_apply, inner_emb_emb] at this
      exact this
    · have := hpos (emb i ξ)
      rwa [ContinuousLinearMap.reApplyInnerSelf_apply, toCLM_diagonal_emb_apply,
        inner_emb_emb] at this
  · intro hd
    refine ⟨fun f g => ?_, fun f => ?_⟩
    · simp only [ContinuousLinearMap.coe_coe, PiLp.inner_apply, toCLM_diagonal_apply]
      exact Finset.sum_congr rfl fun i _ => (hd i).1 (f i) (g i)
    · rw [ContinuousLinearMap.reApplyInnerSelf_apply, PiLp.inner_apply, map_sum]
      refine Finset.sum_nonneg fun i _ => ?_
      rw [toCLM_diagonal_apply]
      exact (hd i).2 (f i)

omit [CompleteSpace H] in
/-- **A diagonal operator determines its entries.** -/
theorem toCLM_diagonal_inj {d d' : ι → H →L[ℂ] H} :
    toCLM (diagonal d) = toCLM (diagonal d') ↔ d = d' :=
  ⟨fun h => diagonal_injective (toCLM_injective h), fun h => h ▸ rfl⟩

omit [CompleteSpace H] in
/-- **An operator commutes with a diagonal operator** exactly when its entries intertwine the
diagonal's: `Tᵢⱼ dⱼ = dᵢ Tᵢⱼ`. -/
theorem commute_toCLM_diagonal_iff (T : Ampl ι H →L[ℂ] Ampl ι H) (d : ι → H →L[ℂ] H) :
    Commute T (toCLM (diagonal d)) ↔ ∀ i j, entries T i j * d j = d i * entries T i j := by
  rw [commute_toCLM_iff, Commute, SemiconjBy]
  constructor
  · intro h i j
    have := congrFun (congrFun h i) j
    rwa [mul_diagonal, diagonal_mul] at this
  · intro h
    ext1 i j
    rw [mul_diagonal, diagonal_mul]
    exact h i j

end Diagonal

/-! ## Two copies: the pair embedding and the flip -/

section Two

/-- `(u, v) ↦ diag(u, v)`, as a unital `⋆`-algebra homomorphism into the `2 × 2` matrices. -/
noncomputable def pairDiag {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] :
    R × R →⋆ₐ[ℂ] Matrix (Fin 2) (Fin 2) R where
  toFun c := diagonal ![c.1, c.2]
  map_one' := by
    rw [← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> rfl
  map_mul' c c' := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> rfl
  map_zero' := by
    rw [← diagonal_zero]
    congr 1
    funext i
    fin_cases i <;> rfl
  map_add' c c' := by
    rw [diagonal_add]
    congr 1
    funext i
    fin_cases i <;> rfl
  commutes' r := by
    rw [algebraMap_eq_diagonal]
    congr 1
    funext i
    fin_cases i <;> rfl
  map_star' c := by
    rw [star_eq_conjTranspose, diagonal_conjTranspose]
    congr 1
    funext i
    fin_cases i <;> rfl

/-- **The pair embedding** `(u, v) ↦ u ⊕ v` of two operators on `H` as a block-diagonal operator
on `H ⊕ H`, a unital `⋆`-algebra homomorphism. -/
noncomputable def diag2 : (H →L[ℂ] H) × (H →L[ℂ] H) →⋆ₐ[ℂ] (Ampl (Fin 2) H →L[ℂ] Ampl (Fin 2) H) :=
  toCLMStarAlgHom.comp pairDiag

/-- The pair embedding is the operator of the diagonal matrix of the pair. -/
theorem diag2_apply (c : (H →L[ℂ] H) × (H →L[ℂ] H)) :
    diag2 (H := H) c = toCLM (diagonal ![c.1, c.2]) :=
  rfl

/-- The pair embedding is injective. -/
theorem diag2_injective : Function.Injective (diag2 (H := H)) := fun c c' h => by
  rw [diag2_apply, diag2_apply, toCLM_diagonal_inj] at h
  exact Prod.ext (congrFun h 0) (congrFun h 1)

/-- A block-diagonal operator is positive exactly when both blocks are. -/
theorem diag2_nonneg_iff (c : (H →L[ℂ] H) × (H →L[ℂ] H)) :
    0 ≤ diag2 (H := H) c ↔ 0 ≤ c.1 ∧ 0 ≤ c.2 := by
  rw [diag2_apply, toCLM_diagonal_nonneg_iff, Fin.forall_fin_two]
  rfl

/-- **The flip** `(ξ, η) ↦ (η, ξ)` of the two copies of `H`. -/
noncomputable def flip2 : Ampl (Fin 2) H ≃ₗᵢ[ℂ] Ampl (Fin 2) H :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ H (Equiv.swap 0 1)

omit [CompleteSpace H] in
/-- The first coordinate of the flip is the second coordinate. -/
theorem flip2_apply_zero (f : Ampl (Fin 2) H) : flip2 f 0 = f 1 :=
  rfl

omit [CompleteSpace H] in
/-- The second coordinate of the flip is the first coordinate. -/
theorem flip2_apply_one (f : Ampl (Fin 2) H) : flip2 f 1 = f 0 :=
  rfl

omit [CompleteSpace H] in
/-- The flip is an involution. -/
theorem flip2_flip2 (f : Ampl (Fin 2) H) : flip2 (flip2 f) = f := by
  ext i
  fin_cases i <;> rfl

/-- **The flip exchanges the blocks** of a block-diagonal operator. -/
theorem flip2_diag2_flip2 (c : (H →L[ℂ] H) × (H →L[ℂ] H)) (f : Ampl (Fin 2) H) :
    flip2 (diag2 (H := H) c (flip2 f)) = diag2 (H := H) c.swap f := by
  ext i
  fin_cases i <;> simp [flip2_apply_zero, flip2_apply_one, diag2_apply]

omit [CompleteSpace H] in
/-- The flip is its own inverse. -/
theorem flip2_symm_apply (f : Ampl (Fin 2) H) : flip2.symm f = flip2 f := by
  rw [LinearIsometryEquiv.symm_apply_eq, flip2_flip2]

/-- **Conjugation by the flip exchanges the blocks**: `J (u ⊕ v) J = v ⊕ u`. -/
theorem conjStarAlgEquiv_flip2_diag2 (c : (H →L[ℂ] H) × (H →L[ℂ] H)) :
    flip2.conjStarAlgEquiv (diag2 (H := H) c) = diag2 (H := H) c.swap := by
  ext f : 1
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, flip2_symm_apply, flip2_diag2_flip2]

/-! ## Operators commuting with block-diagonal operators -/

/-- **An operator commuting with `1 ⊕ 0` is block diagonal**, with its diagonal entries as
blocks. -/
theorem eq_diag2_of_commute {T : Ampl (Fin 2) H →L[ℂ] Ampl (Fin 2) H}
    (h : Commute T (diag2 (H := H) (1, 0))) :
    T = diag2 (H := H) (entries T 0 0, entries T 1 1) := by
  rw [diag2_apply, commute_toCLM_diagonal_iff] at h
  conv_lhs => rw [← toCLM_entries T]
  rw [diag2_apply]
  congr 1
  ext1 i j
  fin_cases i <;> fin_cases j
  · simp
  · simpa using (h 0 1).symm
  · simpa using h 1 0
  · simp

/-- An operator commuting with `u ⊕ 0` has its first diagonal entry commuting with `u`. -/
theorem commute_entries_zero {T : Ampl (Fin 2) H →L[ℂ] Ampl (Fin 2) H} {u : H →L[ℂ] H}
    (h : Commute T (diag2 (H := H) (u, 0))) : Commute (entries T 0 0) u := by
  rw [diag2_apply, commute_toCLM_diagonal_iff] at h
  show _ * _ = _ * _
  simpa using h 0 0

/-- An operator commuting with `0 ⊕ v` has its second diagonal entry commuting with `v`. -/
theorem commute_entries_one {T : Ampl (Fin 2) H →L[ℂ] Ampl (Fin 2) H} {v : H →L[ℂ] H}
    (h : Commute T (diag2 (H := H) (0, v))) : Commute (entries T 1 1) v := by
  rw [diag2_apply, commute_toCLM_diagonal_iff] at h
  show _ * _ = _ * _
  simpa using h 1 1

/-! ## The half vector -/

/-- `(√2)⁻¹ * (√2)⁻¹ = ½`, as complex numbers. -/
theorem ofReal_inv_sqrt_two_mul_self :
    (((√2)⁻¹ : ℝ) : ℂ) * (((√2)⁻¹ : ℝ) : ℂ) = 2⁻¹ := by
  rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt zero_le_two]
  push_cast
  rfl

/-- **The half vector** `(ψ, ψ)/√2` of `H ⊕ H`. -/
noncomputable def halfVec (ψ : H) : Ampl (Fin 2) H :=
  WithLp.toLp 2 fun _ => (((√2)⁻¹ : ℝ) : ℂ) • ψ

omit [CompleteSpace H] in
/-- Both coordinates of the half vector are `ψ/√2`. -/
theorem halfVec_apply (ψ : H) (i : Fin 2) : halfVec ψ i = (((√2)⁻¹ : ℝ) : ℂ) • ψ :=
  rfl

omit [CompleteSpace H] in
/-- The half vector has the norm of `ψ`. -/
theorem norm_halfVec (ψ : H) : ‖halfVec ψ‖ = ‖ψ‖ := by
  have h : ‖halfVec ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two, halfVec_apply, halfVec_apply, norm_smul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_pow, inv_pow,
      Real.sq_sqrt zero_le_two]
    ring
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

omit [CompleteSpace H] in
/-- The flip fixes the half vector. -/
theorem flip2_halfVec (ψ : H) : flip2 (halfVec ψ) = halfVec ψ := by
  ext i
  fin_cases i <;> rfl

omit [CompleteSpace H] in
/-- **The expectation of a block-diagonal operator at the half vector is the average of its
blocks' expectations** (Lemma 2 of `reports/c6b-paper-proofs.md`, §4.3). -/
theorem inner_halfVec_toCLM_diagonal (ψ : H) (d : Fin 2 → H →L[ℂ] H) :
    ⟪halfVec ψ, toCLM (diagonal d) (halfVec ψ)⟫_ℂ = 2⁻¹ * (⟪ψ, d 0 ψ⟫_ℂ + ⟪ψ, d 1 ψ⟫_ℂ) := by
  rw [PiLp.inner_apply, Fin.sum_univ_two, toCLM_diagonal_apply, toCLM_diagonal_apply,
    halfVec_apply, halfVec_apply, map_smul, map_smul, inner_smul_left, inner_smul_right,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc, ← mul_assoc,
    ofReal_inv_sqrt_two_mul_self, mul_add]

/-- **The expectation of a block-diagonal operator at the half vector**, for the pair
embedding. -/
theorem inner_halfVec_diag2 (ψ : H) (c : (H →L[ℂ] H) × (H →L[ℂ] H)) :
    ⟪halfVec ψ, diag2 (H := H) c (halfVec ψ)⟫_ℂ = 2⁻¹ * (⟪ψ, c.1 ψ⟫_ℂ + ⟪ψ, c.2 ψ⟫_ℂ) :=
  inner_halfVec_toCLM_diagonal ψ _

omit [CompleteSpace H] in
/-- A scaled embedded vector, `c • emb i ξ` with `c = (√2)⁻¹`, gives half the expectation of the
`i`-th entry of a diagonal operator. -/
theorem inner_smul_emb_toCLM_diagonal (d : Fin 2 → H →L[ℂ] H) (i : Fin 2) (ξ : H) :
    ⟪(((√2)⁻¹ : ℝ) : ℂ) • emb i ξ, toCLM (diagonal d) ((((√2)⁻¹ : ℝ) : ℂ) • emb i ξ)⟫_ℂ =
      2⁻¹ * ⟪ξ, d i ξ⟫_ℂ := by
  rw [map_smul, toCLM_diagonal_emb_apply, inner_smul_left, inner_smul_right, inner_emb_emb,
    Complex.conj_ofReal, ← mul_assoc, ofReal_inv_sqrt_two_mul_self]

end Two

end OperatorMatrix

open OperatorMatrix

/-! ## Traces of block-diagonal operators -/

namespace VecTrace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {s t : Set (H →L[ℂ] H)}

/-- The block-diagonal operators `u ⊕ v` with `u ∈ s` and `v ∈ t`. -/
def diag2Set (s t : Set (H →L[ℂ] H)) : Set (Ampl (Fin 2) H →L[ℂ] Ampl (Fin 2) H) :=
  Set.image2 (fun u v => diag2 (H := H) (u, v)) s t

/-- The vectors of the doubled trace: `(gₖ, 0)/√2` and `(0, hₗ)/√2`. -/
noncomputable def diag2Vec (τ : VecTrace s) (σ : VecTrace t) :
    Fin τ.n ⊕ Fin σ.n → Ampl (Fin 2) H
  | .inl k => (((√2)⁻¹ : ℝ) : ℂ) • emb 0 (τ.g k)
  | .inr l => (((√2)⁻¹ : ℝ) : ℂ) • emb 1 (σ.g l)

/-- The doubled functional of a block-diagonal operator is the average of the two functionals. -/
theorem sum_inner_diag2Vec (τ : VecTrace s) (σ : VecTrace t) (u v : H →L[ℂ] H) :
    ∑ m, ⟪diag2Vec τ σ m, diag2 (H := H) (u, v) (diag2Vec τ σ m)⟫_ℂ = 2⁻¹ * (τ.tr u + σ.tr v) := by
  rw [Fintype.sum_sum_type, mul_add, tr, tr]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Finset.mul_sum, diag2Vec, diag2_apply,
    inner_smul_emb_toCLM_diagonal]
  rfl

/-- **The doubled trace** (Lemma 9 of `reports/c6b-paper-proofs.md`, §4.3): faithful tracial
vector functionals `τ` on `s` and `σ` on `t` give the faithful tracial vector functional
`u ⊕ v ↦ ½ (τ(u) + σ(v))` on the block-diagonal operators over `s` and `t`. -/
noncomputable def diag2 (τ : VecTrace s) (σ : VecTrace t) : VecTrace (diag2Set s t) :=
  ofFintype (diag2Vec τ σ)
    (by
      have hc : ‖(((√2)⁻¹ : ℝ) : ℂ)‖ ^ 2 = 2⁻¹ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_pow,
          Real.sq_sqrt zero_le_two]
      simp only [Fintype.sum_sum_type, diag2Vec, norm_smul, norm_emb, mul_pow, hc,
        ← Finset.mul_sum, τ.norm_sq_sum, σ.norm_sq_sum]
      norm_num)
    (by
      rintro _ ⟨u, hu, v, hv, rfl⟩ _ ⟨u', hu', v', hv', rfl⟩
      rw [← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, sum_inner_diag2Vec,
        sum_inner_diag2Vec, τ.tr_mul_comm hu hu', σ.tr_mul_comm hv hv'])
    (by
      rintro _ ⟨u, hu, v, hv, rfl⟩ h
      beta_reduce at h
      have hc : (((√2)⁻¹ : ℝ) : ℂ) ≠ 0 := by
        rw [Complex.ofReal_ne_zero]
        positivity
      have hu0 : u = 0 := τ.separating u hu fun k => by
        have := h (.inl k)
        rw [diag2Vec, map_smul, diag2_apply, toCLM_diagonal_emb_apply, smul_eq_zero,
          or_iff_right hc] at this
        exact emb_injective 0 (this.trans (map_zero _).symm)
      have hv0 : v = 0 := σ.separating v hv fun l => by
        have := h (.inr l)
        rw [diag2Vec, map_smul, diag2_apply, toCLM_diagonal_emb_apply, smul_eq_zero,
          or_iff_right hc] at this
        exact emb_injective 1 (this.trans (map_zero _).symm)
      show OperatorMatrix.diag2 (H := H) (u, v) = 0
      rw [hu0, hv0, Prod.mk_zero_zero, map_zero])

/-- **The functional of the doubled trace** is the average of the two functionals:
`tr(u ⊕ v) = ½ (τ(u) + σ(v))`. -/
theorem tr_diag2 (τ : VecTrace s) (σ : VecTrace t) (u v : H →L[ℂ] H) :
    (τ.diag2 σ).tr (OperatorMatrix.diag2 (H := H) (u, v)) = 2⁻¹ * (τ.tr u + σ.tr v) := by
  rw [← sum_inner_diag2Vec]
  exact (Fintype.equivFin _).symm.sum_comp
    fun m => ⟪diag2Vec τ σ m, OperatorMatrix.diag2 (H := H) (u, v) (diag2Vec τ σ m)⟫_ℂ

end VecTrace

/-! ## Abelian projections -/

section Abelian

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **No nonzero abelian projection** in a set `s` of operators: a self-adjoint idempotent `r ∈ s`
whose corner `r s r` is commutative vanishes. This is the hypothesis `hII` of the
orthonormalization tier `povm_orthogonalization_finitePair` at `s = M.opsA`. -/
def NoAbelianProj (s : Set (H →L[ℂ] H)) : Prop :=
  ∀ r ∈ s, IsStarProjection r →
    (∀ x ∈ s, ∀ y ∈ s, r * x * r * (r * y * r) = r * y * r * (r * x * r)) → r = 0

/-- A block-diagonal star projection has star-projection blocks. -/
private theorem isStarProjection_of_diag2 {c : (H →L[ℂ] H) × (H →L[ℂ] H)}
    (h : IsStarProjection (diag2 (H := H) c)) : IsStarProjection c.1 ∧ IsStarProjection c.2 := by
  have hidem : c * c = c := diag2_injective (by rw [map_mul]; exact h.isIdempotentElem.eq)
  have hstar : star c = c := diag2_injective (by rw [map_star]; exact h.isSelfAdjoint.star_eq)
  exact ⟨⟨congrArg Prod.fst hidem, congrArg Prod.fst hstar⟩,
    ⟨congrArg Prod.snd hidem, congrArg Prod.snd hstar⟩⟩

/-- A pair of star projections gives a block-diagonal star projection. -/
private theorem isStarProjection_diag2 {p q : H →L[ℂ] H} (hp : IsStarProjection p)
    (hq : IsStarProjection q) : IsStarProjection (diag2 (H := H) (p, q)) :=
  IsStarProjection.map (f := diag2) ⟨Prod.ext hp.isIdempotentElem.eq hq.isIdempotentElem.eq,
    Prod.ext hp.isSelfAdjoint.star_eq hq.isSelfAdjoint.star_eq⟩

/-- The corner of a block-diagonal operator is computed blockwise. -/
private theorem diag2_corner (c x y : (H →L[ℂ] H) × (H →L[ℂ] H)) :
    diag2 (H := H) c * diag2 (H := H) x * diag2 (H := H) c *
        (diag2 (H := H) c * diag2 (H := H) y * diag2 (H := H) c) =
      diag2 (H := H) (c * x * c * (c * y * c)) := by
  simp only [map_mul]

/-- **No abelian projections in a block-diagonal algebra** (Lemma 11, Theorem F of
`reports/c6b-paper-proofs.md`, §4.3): for sets `s`, `t` containing `0`, the block-diagonal
operators over `s` and `t` have no nonzero abelian projection exactly when neither `s` nor `t`
has. -/
theorem noAbelianProj_diag2Set_iff {s t : Set (H →L[ℂ] H)} (hs : 0 ∈ s) (ht : 0 ∈ t) :
    NoAbelianProj (VecTrace.diag2Set s t) ↔ NoAbelianProj s ∧ NoAbelianProj t := by
  constructor
  · intro h
    refine ⟨fun p hp hpP hab => ?_, fun q hq hqP hab => ?_⟩
    · have := h (diag2 (H := H) (p, 0)) ⟨p, hp, 0, ht, rfl⟩ (isStarProjection_diag2 hpP (.zero _))
        (by
          rintro _ ⟨u, hu, v, hv, rfl⟩ _ ⟨u', hu', v', hv', rfl⟩
          rw [diag2_corner, diag2_corner]
          congr 1
          refine Prod.ext ?_ (by simp)
          exact hab u hu u' hu')
      exact congrArg Prod.fst (diag2_injective (this.trans (map_zero _).symm))
    · have := h (diag2 (H := H) (0, q)) ⟨0, hs, q, hq, rfl⟩ (isStarProjection_diag2 (.zero _) hqP)
        (by
          rintro _ ⟨u, hu, v, hv, rfl⟩ _ ⟨u', hu', v', hv', rfl⟩
          rw [diag2_corner, diag2_corner]
          congr 1
          refine Prod.ext (by simp) ?_
          exact hab v hv v' hv')
      exact congrArg Prod.snd (diag2_injective (this.trans (map_zero _).symm))
  · rintro ⟨hS, hT⟩ _ ⟨p, hp, q, hq, rfl⟩ hr hab
    obtain ⟨hpP, hqP⟩ := isStarProjection_of_diag2 hr
    have hblock : ∀ x x' : (H →L[ℂ] H) × (H →L[ℂ] H), diag2 (H := H) x ∈ VecTrace.diag2Set s t →
        diag2 (H := H) x' ∈ VecTrace.diag2Set s t →
        (p, q) * x * (p, q) * ((p, q) * x' * (p, q)) =
          (p, q) * x' * (p, q) * ((p, q) * x * (p, q)) := fun x x' hx hx' =>
      diag2_injective (by rw [← diag2_corner, ← diag2_corner]; exact hab _ hx _ hx')
    have hp0 : p = 0 := hS p hp hpP fun u hu u' hu' =>
      congrArg Prod.fst (hblock (u, 0) (u', 0) ⟨u, hu, 0, ht, rfl⟩ ⟨u', hu', 0, ht, rfl⟩)
    have hq0 : q = 0 := hT q hq hqP fun v hv v' hv' =>
      congrArg Prod.snd (hblock (0, v) (0, v') ⟨0, hs, v, hv, rfl⟩ ⟨0, hs, v', hv', rfl⟩)
    rw [hp0, hq0]
    exact map_zero (diag2 (H := H))

/-- **A dyadic pair's first player's operators have no nonzero abelian projection**
(`IsDyadicPair.eq_zero_of_abelianA`, in the form `NoAbelianProj`). -/
theorem BipartiteModel.IsDyadicPair.noAbelianProj_opsA {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞]
    [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]
    {M : BipartiteModel 𝒞 𝒜 ℬ} (h : M.IsDyadicPair) : NoAbelianProj M.opsA :=
  fun _ hr hrP hab => h.eq_zero_of_abelianA hr hrP hab

/-- **A dyadic pair's second player's operators have no nonzero abelian projection**
(`IsDyadicPair.eq_zero_of_abelianB`, in the form `NoAbelianProj`). -/
theorem BipartiteModel.IsDyadicPair.noAbelianProj_opsB {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞]
    [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]
    {M : BipartiteModel 𝒞 𝒜 ℬ} (h : M.IsDyadicPair) : NoAbelianProj M.opsB :=
  fun _ hr hrP hab => h.eq_zero_of_abelianB hr hrP hab

end Abelian

end MIPRE

end
