/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Doubling.Model

@[expose] public section

/-!
# The doubled model of a finite pair is a finite pair

Theorem A items 3 and 4 and Theorem F of `reports/c6b-paper-proofs.md`, §4, for the doubled model
`Doubling.model hM hψ` of `Co/Doubling/Model.lean`, stated on its bipartite model `toBipartite`
(`π = id`, `πA = L`, `πB = R`):

* **The players' operators** (`opsA_model`, `opsB_model`): the first player's operators of the
  doubled model are the block-diagonal operators `u ⊕ v` with `u` the first player's operator of `M`
  and `v` the second's, and the second player's are `v ⊕ u`.
* **A finite pair** (`isFinitePair`, Lemmas 6–9 of the report): the placements are injective; an
  operator commuting with every `R y` commutes with `1 ⊕ 0`, so is block diagonal, and its blocks
  commute with the two players' commutants, so it is an `L x` (and symmetrically); the traces are
  the averages `½ (τ_𝒜 + τ_ℬ)` (`VecTrace.diag2`, `tr_diag2_L`, `tr_diag2_R`).
* **Dyadic pairs** (`isDyadicPair`): the doubled model of a dyadic pair is a dyadic pair, its local
  algebra having the componentwise units (`HasDyadicUnits.prod`).
* **Order agreement** (Theorem A.4, Lemma 10): `0 ≤ x ↔ 0 ≤ L x ↔ 0 ≤ R x` (`L_nonneg_iff`,
  `R_nonneg_iff`); with the order agreement of `M` itself (`IsFinitePair.nonneg_iff_A`,
  `MIPRE/Foundations/FinitePairOrder.lean`), the translation `Doubling.equiv : 𝒜 × ℬ ≃⋆ₐ Loc M` of
  the report's local algebra `𝒩 = 𝒜 × ℬ` preserves and reflects the order
  (`equiv_nonneg_iff`, `L_equiv_nonneg_iff`).
* **No abelian projections** (Theorem F, Lemma 11; `noAbelianProj_iff`): the two algebras of the
  doubled model have no nonzero abelian projection exactly when the two algebras of `M` have none.
-/

namespace MIPRE.LIDT.Co.Doubling

open scoped InnerProductSpace
open MIPRE.OperatorMatrix

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] {M : BipartiteModel 𝒞 𝒜 ℬ}
  (hM : M.IsFinitePair) (hψ : ‖M.ψ‖ = 1)

/-! ## The players' operators -/

/-- **The first player's operators of the doubled model** are the block-diagonal operators
`u ⊕ v` over the first and the second player's operators of `M`. -/
theorem opsA_model :
    (model hM hψ).toBipartite.opsA = VecTrace.diag2Set M.opsA M.opsB := by
  ext T
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, hM.mem_opsA x.1, _, hM.mem_opsB x.2, rfl⟩
  · rintro ⟨u, hu, v, hv, rfl⟩
    exact ⟨(⟨u, M.opsA_subset_centralizer hu⟩, ⟨v, M.opsB_subset_centralizer hv⟩), rfl⟩

/-- **The second player's operators of the doubled model** are the block-diagonal operators
`v ⊕ u` over the second and the first player's operators of `M`. -/
theorem opsB_model :
    (model hM hψ).toBipartite.opsB = VecTrace.diag2Set M.opsB M.opsA := by
  ext T
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, hM.mem_opsB x.2, _, hM.mem_opsA x.1, (model_R hM hψ x).symm⟩
  · rintro ⟨v, hv, u, hu, rfl⟩
    exact ⟨(⟨u, M.opsA_subset_centralizer hu⟩, ⟨v, M.opsB_subset_centralizer hv⟩),
      model_R hM hψ _⟩

/-! ## Traces

The traces are stated on the block-diagonal operators `VecTrace.diag2Set`, which are the players'
operators of the doubled model by `opsA_model` and `opsB_model`, rather than on
`(model hM hψ).toBipartite.opsA`: instance synthesis on the space `(model hM hψ).toBipartite.H`,
which is `Ampl (Fin 2) M.H` only after unfolding `SymModel.toBipartite`, exceeds the synthesis
budget, and every functional applied to an operator of that type needs it. -/

/-- **The doubled trace of the first algebra is the average** (Lemma 9 of the report): with vector
traces `τ` of the first player's operators of `M` and `σ` of the second's,
`τ_D(L x) = ½ (τ(x₁) + σ(x₂))`, where `τ_D = τ.diag2 σ` is a vector trace of the first player's
operators of the doubled model (`opsA_model`). -/
theorem tr_diag2_L (τ : VecTrace M.opsA) (σ : VecTrace M.opsB) (x : Loc M) :
    (τ.diag2 σ).tr ((model hM hψ).L x) =
      2⁻¹ * (τ.tr (x.1 : M.H →L[ℂ] M.H) + σ.tr (x.2 : M.H →L[ℂ] M.H)) :=
  VecTrace.tr_diag2 τ σ _ _

/-- **The doubled trace of the second algebra is the average**: `τ_D(R x) = ½ (σ(x₂) + τ(x₁))`,
where `τ_D = σ.diag2 τ` is a vector trace of the second player's operators of the doubled model
(`opsB_model`). -/
theorem tr_diag2_R (τ : VecTrace M.opsA) (σ : VecTrace M.opsB) (x : Loc M) :
    (σ.diag2 τ).tr ((model hM hψ).R x) =
      2⁻¹ * (σ.tr (x.2 : M.H →L[ℂ] M.H) + τ.tr (x.1 : M.H →L[ℂ] M.H)) := by
  rw [model_R]
  exact VecTrace.tr_diag2 σ τ _ _

/-! ## The doubled model is a finite pair -/

/-- An operator commuting with every `R y` is an `L x`. -/
private theorem mem_opsA_of_commute {T : Ampl (Fin 2) M.H →L[ℂ] Ampl (Fin 2) M.H}
    (hT : ∀ y : Loc M, Commute T ((model hM hψ).R y)) : T ∈ (model hM hψ).toBipartite.opsA := by
  have hR : ∀ y : Loc M, Commute T (diag2 (H := M.H) ((y.2 : M.H →L[ℂ] M.H), y.1)) :=
    fun y => model_R hM hψ y ▸ hT y
  have hdiag := eq_diag2_of_commute (by simpa using hR (0, 1))
  have h0 : ∀ b : LocB M, Commute (entries T 0 0) b := fun b =>
    commute_entries_zero (by simpa using hR (0, b))
  have h1 : ∀ a : LocA M, Commute (entries T 1 1) a := fun a =>
    commute_entries_one (by simpa using hR (a, 0))
  refine ⟨(⟨entries T 0 0, ?_⟩, ⟨entries T 1 1, ?_⟩), hdiag.symm⟩
  · refine (StarSubalgebra.mem_centralizer_iff ℂ).2 fun g hg => ⟨?_, ?_⟩
    · exact (h0 ⟨g, M.opsB_subset_centralizer hg⟩).eq.symm
    · exact (h0 (star ⟨g, M.opsB_subset_centralizer hg⟩)).eq.symm
  · refine (StarSubalgebra.mem_centralizer_iff ℂ).2 fun g hg => ⟨?_, ?_⟩
    · exact (h1 ⟨g, M.opsA_subset_centralizer hg⟩).eq.symm
    · exact (h1 (star ⟨g, M.opsA_subset_centralizer hg⟩)).eq.symm

/-- An operator commuting with every `L x` is an `R y`. -/
private theorem mem_opsB_of_commute {T : Ampl (Fin 2) M.H →L[ℂ] Ampl (Fin 2) M.H}
    (hT : ∀ x : Loc M, Commute T ((model hM hψ).L x)) : T ∈ (model hM hψ).toBipartite.opsB := by
  have hL : ∀ x : Loc M, Commute T (diag2 (H := M.H) ((x.1 : M.H →L[ℂ] M.H), x.2)) := hT
  have hdiag := eq_diag2_of_commute (by simpa using hL (1, 0))
  have h0 : ∀ a : LocA M, Commute (entries T 0 0) a := fun a =>
    commute_entries_zero (by simpa using hL (a, 0))
  have h1 : ∀ b : LocB M, Commute (entries T 1 1) b := fun b =>
    commute_entries_one (by simpa using hL (0, b))
  refine ⟨(⟨entries T 1 1, ?_⟩, ⟨entries T 0 0, ?_⟩), (model_R hM hψ _).trans hdiag.symm⟩
  · refine (StarSubalgebra.mem_centralizer_iff ℂ).2 fun g hg => ⟨?_, ?_⟩
    · exact (h1 ⟨g, M.opsB_subset_centralizer hg⟩).eq.symm
    · exact (h1 (star ⟨g, M.opsB_subset_centralizer hg⟩)).eq.symm
  · refine (StarSubalgebra.mem_centralizer_iff ℂ).2 fun g hg => ⟨?_, ?_⟩
    · exact (h0 ⟨g, M.opsA_subset_centralizer hg⟩).eq.symm
    · exact (h0 (star ⟨g, M.opsA_subset_centralizer hg⟩)).eq.symm

/-- **The doubled model of a finite pair is a finite pair** (Theorem A.3 of
`reports/c6b-paper-proofs.md`, §4; Lemmas 6–9): the placements are injective, each player's
operators are the commutant of the other's, and both carry the averaged vector traces. -/
theorem isFinitePair : (model hM hψ).toBipartite.IsFinitePair where
  injA x y h := by
    have := diag2_injective (H := M.H) h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst this)) (Subtype.ext (congrArg Prod.snd this))
  injB x y h := by
    have := diag2_injective (H := M.H) ((model_R hM hψ x).symm.trans (h.trans (model_R hM hψ y)))
    exact Prod.ext (Subtype.ext (congrArg Prod.snd this)) (Subtype.ext (congrArg Prod.fst this))
  commutantA _ hT := mem_opsA_of_commute hM hψ hT
  commutantB _ hT := mem_opsB_of_commute hM hψ hT
  traceA := by
    obtain ⟨τ⟩ := hM.traceA
    obtain ⟨σ⟩ := hM.traceB
    exact ⟨(τ.diag2 σ).mono fun T hT => opsA_model hM hψ ▸ hT⟩
  traceB := by
    obtain ⟨τ⟩ := hM.traceA
    obtain ⟨σ⟩ := hM.traceB
    exact ⟨(σ.diag2 τ).mono fun T hT => opsB_model hM hψ ▸ hT⟩

/-! ## Order agreement -/

/-- **Order agreement in the doubled model, first placement** (Theorem A.4): `0 ≤ L x ↔ 0 ≤ x`. -/
theorem L_nonneg_iff (x : Loc M) : 0 ≤ (model hM hψ).L x ↔ 0 ≤ x := by
  rw [model_L, diag2_nonneg_iff, Prod.le_def]
  exact Iff.rfl

/-- **Order agreement in the doubled model, second placement** (Theorem A.4): `0 ≤ R x ↔ 0 ≤ x`. -/
theorem R_nonneg_iff (x : Loc M) : 0 ≤ (model hM hψ).R x ↔ 0 ≤ x := by
  rw [model_R, diag2_nonneg_iff, Prod.le_def, and_comm]
  exact Iff.rfl

/-! ## The report's local algebra `𝒜 × ℬ` -/

/-- The translation `(a, b) ↦ (π (πA a), π (πB b))`, as a `⋆`-homomorphism. -/
noncomputable def equivHom : 𝒜 × ℬ →⋆ₐ[ℂ] Loc M :=
  (hM.equivA.toStarAlgHom.comp (StarAlgHom.fst ℂ 𝒜 ℬ)).prod
    (hM.equivB.toStarAlgHom.comp (StarAlgHom.snd ℂ 𝒜 ℬ))

/-- The inverse translation, as a `⋆`-homomorphism. -/
noncomputable def equivInv : Loc M →⋆ₐ[ℂ] 𝒜 × ℬ :=
  (hM.equivA.symm.toStarAlgHom.comp (StarAlgHom.fst ℂ (LocA M) (LocB M))).prod
    (hM.equivB.symm.toStarAlgHom.comp (StarAlgHom.snd ℂ (LocA M) (LocB M)))

/-- **The translation of the report's local algebra** `𝒩 = 𝒜 × ℬ` to the doubled model's,
`(a, b) ↦ (π (πA a), π (πB b))`, a `⋆`-isomorphism (`IsFinitePair.equivA`, `.equivB`). -/
noncomputable def equiv : 𝒜 × ℬ ≃⋆ₐ[ℂ] Loc M :=
  StarAlgEquiv.ofStarAlgHom (equivHom hM) (equivInv hM)
    (StarAlgHom.ext fun n => Prod.ext (hM.equivA.symm_apply_apply n.1)
      (hM.equivB.symm_apply_apply n.2))
    (StarAlgHom.ext fun x => Prod.ext (hM.equivA.apply_symm_apply x.1)
      (hM.equivB.apply_symm_apply x.2))

/-- The translation of `(a, b)` is the pair of its operators. -/
@[simp]
theorem equiv_apply (n : 𝒜 × ℬ) : equiv hM n = (hM.equivA n.1, hM.equivB n.2) :=
  rfl

/-- The first placement of a translated element: `L (a, b) = π (πA a) ⊕ π (πB b)`. -/
theorem model_L_equiv (n : 𝒜 × ℬ) :
    (model hM hψ).L (equiv hM n) = diag2 (H := M.H) (M.π (M.πA n.1), M.π (M.πB n.2)) :=
  rfl

/-- The second placement of a translated element: `R (a, b) = π (πB b) ⊕ π (πA a)`. -/
theorem model_R_equiv (n : 𝒜 × ℬ) :
    (model hM hψ).R (equiv hM n) = diag2 (H := M.H) (M.π (M.πB n.2), M.π (M.πA n.1)) :=
  model_R hM hψ _

/-- The doubled trace of a translated element, in the vocabulary of `M`:
`τ_D(L (a, b)) = ½ (τ(π (πA a)) + σ(π (πB b)))`. -/
theorem tr_diag2_L_equiv (τ : VecTrace M.opsA) (σ : VecTrace M.opsB) (n : 𝒜 × ℬ) :
    (τ.diag2 σ).tr ((model hM hψ).L (equiv hM n)) =
      2⁻¹ * (τ.tr (M.π (M.πA n.1)) + σ.tr (M.π (M.πB n.2))) :=
  tr_diag2_L hM hψ τ σ _

section Order

variable [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- **The translation preserves and reflects the order.** -/
theorem equiv_nonneg_iff (n : 𝒜 × ℬ) : 0 ≤ equiv hM n ↔ 0 ≤ n := by
  rw [equiv_apply, Prod.le_def, Prod.le_def]
  exact and_congr hM.nonneg_iff_A hM.nonneg_iff_B

/-- **Order agreement for the report's local algebra** (Theorem A.4):
`0 ≤ L (a, b) ↔ 0 ≤ (a, b)`. -/
theorem L_equiv_nonneg_iff (n : 𝒜 × ℬ) : 0 ≤ (model hM hψ).L (equiv hM n) ↔ 0 ≤ n :=
  (L_nonneg_iff hM hψ _).trans (equiv_nonneg_iff hM n)

/-- **Order agreement for the report's local algebra** (Theorem A.4):
`0 ≤ R (a, b) ↔ 0 ≤ (a, b)`. -/
theorem R_equiv_nonneg_iff (n : 𝒜 × ℬ) : 0 ≤ (model hM hψ).R (equiv hM n) ↔ 0 ≤ n :=
  (R_nonneg_iff hM hψ _).trans (equiv_nonneg_iff hM n)

end Order

/-! ## Dyadic pairs -/

/-- **The doubled model of a dyadic pair is a dyadic pair**: a finite pair, and its local algebra
has the componentwise unital dyadic matrix units (`HasDyadicUnits.prod`). -/
theorem isDyadicPair (h : M.IsDyadicPair) (hψ : ‖M.ψ‖ = 1) :
    (model h.isFinitePair hψ).toBipartite.IsDyadicPair :=
  have hU : HasDyadicUnits (Loc M) :=
    (h.unitsA.map h.isFinitePair.equivA).prod (h.unitsB.map h.isFinitePair.equivB)
  ⟨isFinitePair h.isFinitePair hψ, hU, hU⟩

/-! ## Abelian projections -/

/-- **No abelian projections in the doubled model** (Theorem F of `reports/c6b-paper-proofs.md`,
§4; Lemma 11): the two algebras of the doubled model have no nonzero abelian projection exactly
when the two algebras of `M` have none. -/
theorem noAbelianProj_iff :
    NoAbelianProj (model hM hψ).toBipartite.opsA ∧ NoAbelianProj (model hM hψ).toBipartite.opsB ↔
      NoAbelianProj M.opsA ∧ NoAbelianProj M.opsB := by
  have hA : (0 : M.H →L[ℂ] M.H) ∈ M.opsA := ⟨0, by simp⟩
  have hB : (0 : M.H →L[ℂ] M.H) ∈ M.opsB := ⟨0, by simp⟩
  -- the sets are compared through `Ampl (Fin 2) M.H`, whose instances unify with those of
  -- `(model hM hψ).toBipartite.H` only up to unfolding
  have e1 := (congrArg (fun s => NoAbelianProj (H := Ampl (Fin 2) M.H) s)
    (opsA_model hM hψ)).to_iff.trans (noAbelianProj_diag2Set_iff hA hB)
  have e2 := (congrArg (fun s => NoAbelianProj (H := Ampl (Fin 2) M.H) s)
    (opsB_model hM hψ)).to_iff.trans (noAbelianProj_diag2Set_iff hB hA)
  exact ⟨fun h => e1.1 h.1, fun h => ⟨e1.2 h, e2.2 h.symm⟩⟩

/-- **The doubled model of a dyadic pair has no abelian projections**, in its first algebra, the
one the orthonormalization tier `povm_orthogonalization_finitePair` is applied to (report §4,
Theorem G, step 4). -/
theorem noAbelianProj_opsA_of_isDyadicPair (h : M.IsDyadicPair) (hψ : ‖M.ψ‖ = 1) :
    NoAbelianProj (model h.isFinitePair hψ).toBipartite.opsA :=
  ((noAbelianProj_iff h.isFinitePair hψ).2 ⟨h.noAbelianProj_opsA, h.noAbelianProj_opsB⟩).1

/-- **The doubled model of a dyadic pair has no abelian projections**, in its second algebra. -/
theorem noAbelianProj_opsB_of_isDyadicPair (h : M.IsDyadicPair) (hψ : ‖M.ψ‖ = 1) :
    NoAbelianProj (model h.isFinitePair hψ).toBipartite.opsB :=
  ((noAbelianProj_iff h.isFinitePair hψ).2 ⟨h.noAbelianProj_opsA, h.noAbelianProj_opsB⟩).2

end MIPRE.LIDT.Co.Doubling

end
