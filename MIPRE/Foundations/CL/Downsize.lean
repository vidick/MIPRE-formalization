/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.CL.Closure
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Downsizing conditionally linear functions, and reindexing

Paper `linear.tex`, `def:cl-downsize`, `lem:cl-downsize` and `lem:downsize-cl-dist`; blueprint
`lem:cl-downsize`. The CL functions of the pipeline are native to `𝔽_{2^t}` (the low-degree
tests, the introspection sampler), while samplers of normal form verifiers are over `𝔽₂`
(`def:sampler`). *Downsizing* bridges the two: a basis `b` of a field `F` over a subfield `K`
gives the `K`-linear bijection `↓ : F^ι ≃ K^{ι × κ}` reading off coordinates entry by entry
(`downsizeEquiv`), and `L ↦ ↓ ∘ L ∘ ↓⁻¹` carries `ℓ`-level CL functions on `F^ι` to `ℓ`-level CL
functions on `K^{ι × κ}` — on presentations, `CLFun.downsize`, whose decomposition data are
the downsized data of the original: register subspaces `S` become `S × κ`, stage maps are
conjugated by `↓`, and the marginals, factor spaces and stage maps of `lem:cl-kth` correspond
(`eval_truncate_downsize`, `factorOfPrefix_downsize`, `mapOfPrefix_downsize`). Exactness is
preserved, and the CL distribution is pushed forward along `↓` (`clDist_downsize`).

The paper states this for admissible field sizes `q = 2^t`, `t` odd, with the self-dual
normal basis of blueprint `lem:self-dual-basis`. Nothing here depends on the choice of basis:
the self-duality matters for the *arithmetic* of `𝔽_{2^t}` to be computable from `𝔽₂`-data
by the programs that use it, which is a matter for the efficient-computability toolkit. The
paper's downsized *sampler* (`def:downsize_sampler`), a machine wrapping a sampler over
`𝔽_{2^t}`, has no counterpart: samplers are over `𝔽₂` by definition, and a construction native
to `𝔽_{2^t}` is to present the downsized CL functions directly.

The second half of the file is the transport of presentations along a bijection of
coordinates `e : ι ≃ ι'` (`reindexEquiv`, `CLFun.reindex`), with the same list of lemmas; it is
the identification `K^{ι × κ} = K^{|ι| · |κ|}` the paper leaves implicit, and it is what puts a
downsized presentation on the coordinates `Fin (s · t)` of a sampler.
-/

namespace MIPRE.CL

variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {ι ι' : Type*} {κ : Type*} [Fintype κ]

/-! ## The downsize map, and the transport along a bijection of coordinates -/

/-- The downsize map of a basis `b` of `F` over `K`, on vectors: `F^ι ≃ K^{ι × κ}`, sending
`v` to the coordinates of its entries, `↓v (i, j) = (b.repr (v i)) j`. -/
noncomputable def downsizeEquiv (b : Module.Basis κ K F) : (ι → F) ≃ₗ[K] (ι × κ → K) where
  toFun x p := b.repr (x p.1) p.2
  invFun y i := b.repr.symm (Finsupp.equivFunOnFinite.symm fun j => y (i, j))
  map_add' x y := by ext p; simp
  map_smul' c x := by ext p; simp
  left_inv x := by
    funext i
    simp only
    rw [Finsupp.equivFunOnFinite_symm_coe, LinearEquiv.symm_apply_apply]
  right_inv y := by
    funext p
    simp only
    rw [LinearEquiv.apply_symm_apply]
    rfl

@[simp] theorem downsizeEquiv_apply (b : Module.Basis κ K F) (x : ι → F) (p : ι × κ) :
    downsizeEquiv b x p = b.repr (x p.1) p.2 := rfl

/-- Transport of vectors along a bijection of coordinates, `x ↦ x ∘ e.symm`: the identification
`K^{ι} = K^{ι'}` (for instance `K^{ι × κ} = K^{|ι| · |κ|}`, the paper's `𝔽_2^{nt}`). -/
def reindexEquiv (e : ι ≃ ι') : (ι → F) ≃ₗ[F] (ι' → F) where
  toFun x := x ∘ e.symm
  invFun y := y ∘ e
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by funext i; simp
  right_inv y := by funext i; simp

@[simp] theorem reindexEquiv_apply (e : ι ≃ ι') (x : ι → F) (i : ι') :
    reindexEquiv e x i = x (e.symm i) := rfl

@[simp] theorem reindexEquiv_symm_apply (e : ι ≃ ι') (y : ι' → F) (i : ι) :
    (reindexEquiv e).symm y i = y (e i) := rfl

variable [DecidableEq ι] [DecidableEq κ]

theorem downsizeEquiv_proj (b : Module.Basis κ K F) (S : Finset ι) (x : ι → F) :
    downsizeEquiv b (proj S x) = proj (S ×ˢ Finset.univ) (downsizeEquiv b x) := by
  ext ⟨i, j⟩
  simp only [downsizeEquiv_apply, proj_apply, Finset.mem_product, Finset.mem_univ, and_true]
  split_ifs <;> simp

theorem downsizeEquiv_symm_proj (b : Module.Basis κ K F) (S : Finset ι) (y : ι × κ → K) :
    (downsizeEquiv b).symm (proj (S ×ˢ Finset.univ) y) = proj S ((downsizeEquiv b).symm y) := by
  conv_lhs => rw [← (downsizeEquiv b).apply_symm_apply y]
  rw [← downsizeEquiv_proj, LinearEquiv.symm_apply_apply]

theorem sdiff_product_univ (S T : Finset ι) :
    (T ×ˢ (Finset.univ : Finset κ)) \ (S ×ˢ Finset.univ) = (T \ S) ×ˢ Finset.univ := by
  ext ⟨i, j⟩; simp

namespace RegLinear

variable {S : Finset ι}

/-- The downsized linear map `↓ ∘ L ∘ ↓⁻¹` of a map on `V_S`: a map on `V_{S × κ}` over `K`. -/
noncomputable def downsize (b : Module.Basis κ K F) (L : RegLinear F S) :
    RegLinear K (S ×ˢ (Finset.univ : Finset κ)) where
  toLinearMap := (downsizeEquiv (ι := ι) b).toLinearMap ∘ₗ
    (L.toLinearMap.restrictScalars K) ∘ₗ (downsizeEquiv (ι := ι) b).symm.toLinearMap
  proj_comp_proj' y := by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.restrictScalars_apply,
      toLinearMap_apply, downsizeEquiv_symm_proj, apply_proj, ← downsizeEquiv_proj, proj_apply]

@[simp] theorem downsize_apply (b : Module.Basis κ K F) (L : RegLinear F S) (y : ι × κ → K) :
    L.downsize b y = downsizeEquiv b (L ((downsizeEquiv b).symm y)) := rfl

@[simp] theorem downsize_zero (b : Module.Basis κ K F) :
    (0 : RegLinear F S).downsize b = 0 := by
  ext y; simp

end RegLinear

namespace CLFun

variable {ℓ : ℕ}

/-- The downsized presentation `L^↓` (paper `def:cl-downsize`): register subspaces `S` become
`S × κ`, the linear maps are conjugated by the downsize map, and the continuations are selected
through it. -/
noncomputable def downsize (b : Module.Basis κ K F) : {ℓ : ℕ} → CLFun F ι ℓ → CLFun K (ι × κ) ℓ
  | _, zero => zero
  | _, cons S L₁ next =>
    cons (S ×ˢ (Finset.univ : Finset κ)) (L₁.downsize b)
      fun v => (next ((downsizeEquiv b).symm v)).downsize b

@[simp] theorem downsize_zero (b : Module.Basis κ K F) :
    (zero : CLFun F ι 0).downsize b = zero := rfl

@[simp] theorem downsize_cons (b : Module.Basis κ K F) {S : Finset ι} (L₁ : RegLinear F S)
    (next : (ι → F) → CLFun F ι ℓ) :
    (cons S L₁ next).downsize b =
      cons (S ×ˢ (Finset.univ : Finset κ)) (L₁.downsize b)
        fun v => (next ((downsizeEquiv b).symm v)).downsize b := rfl

theorem SupportedOn.downsize (b : Module.Basis κ K F) {P : CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) : (P.downsize b).SupportedOn (T ×ˢ Finset.univ) := by
  induction P generalizing T with
  | zero => trivial
  | cons S L₁ next ih =>
    obtain ⟨hS, hnext⟩ := hP
    refine ⟨Finset.product_subset_product hS (Finset.Subset.refl _), fun v => ?_⟩
    rw [sdiff_product_univ]
    exact ih _ (hnext _)

theorem ExactlyOn.downsize (b : Module.Basis κ K F) {P : CLFun F ι ℓ} {T : Finset ι}
    (hP : P.ExactlyOn T) : (P.downsize b).ExactlyOn (T ×ˢ Finset.univ) := by
  induction P generalizing T with
  | zero =>
    have hT : T = ∅ := hP
    show T ×ˢ Finset.univ = ∅
    rw [hT, Finset.empty_product]
  | cons S L₁ next ih =>
    obtain ⟨hS, hnext⟩ := hP
    refine ⟨Finset.product_subset_product hS (Finset.Subset.refl _), fun v => ?_⟩
    rw [sdiff_product_univ]
    exact ih _ (hnext _)

theorem lift_downsize (b : Module.Basis κ K F) (T : Finset ι) (P : CLFun F ι ℓ) :
    (P.lift T).downsize b = (P.downsize b).lift (T ×ˢ Finset.univ) := by
  induction P generalizing T with
  | zero => simp [lift]
  | cons S L₁ next ih =>
    simp only [lift, downsize_cons]
    congr 1
    funext v
    rw [ih, sdiff_product_univ]

theorem truncate_downsize (b : Module.Basis κ K F) (k : ℕ) (P : CLFun F ι ℓ) :
    (P.downsize b).truncate k = (P.truncate k).downsize b := by
  induction k generalizing ℓ P with
  | zero => simp
  | succ k ih =>
    cases P with
    | zero =>
      rw [downsize_zero, truncate_succ_zero, truncate_succ_zero, lift_downsize, ← ih,
        downsize_zero, Finset.empty_product]
    | cons S L₁ next =>
      rw [downsize_cons, truncate_succ_cons, truncate_succ_cons, downsize_cons]
      congr 1
      funext v
      exact ih _

end CLFun

/-! ## Reindexing coordinates -/

section Reindex

variable [DecidableEq ι']

theorem reindexEquiv_proj (e : ι ≃ ι') (S : Finset ι) (x : ι → F) :
    reindexEquiv e (proj S x) = proj (S.map e.toEmbedding) (reindexEquiv e x) := by
  ext i
  simp [Finset.mem_map_equiv]

theorem reindexEquiv_symm_proj (e : ι ≃ ι') (S : Finset ι) (y : ι' → F) :
    (reindexEquiv e).symm (proj (S.map e.toEmbedding) y) = proj S ((reindexEquiv e).symm y) := by
  conv_lhs => rw [← (reindexEquiv e).apply_symm_apply y]
  rw [← reindexEquiv_proj, LinearEquiv.symm_apply_apply]

theorem map_sdiff' (e : ι ≃ ι') (S T : Finset ι) :
    T.map e.toEmbedding \ S.map e.toEmbedding = (T \ S).map e.toEmbedding := by
  ext i; simp [Finset.mem_map_equiv]

/-- A map on `V_S`, transported along `e`. -/
def RegLinear.reindex (e : ι ≃ ι') {S : Finset ι} (L : RegLinear F S) :
    RegLinear F (S.map e.toEmbedding) where
  toLinearMap := (reindexEquiv e).toLinearMap ∘ₗ L.toLinearMap ∘ₗ (reindexEquiv e).symm.toLinearMap
  proj_comp_proj' y := by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, RegLinear.toLinearMap_apply,
      reindexEquiv_symm_proj, RegLinear.apply_proj, ← reindexEquiv_proj, RegLinear.proj_apply]

@[simp] theorem RegLinear.reindex_apply (e : ι ≃ ι') {S : Finset ι} (L : RegLinear F S)
    (y : ι' → F) : L.reindex e y = reindexEquiv e (L ((reindexEquiv e).symm y)) := rfl

@[simp] theorem RegLinear.reindex_zero (e : ι ≃ ι') {S : Finset ι} :
    (0 : RegLinear F S).reindex e = 0 := by
  ext y; simp

namespace CLFun

variable {ℓ : ℕ}

/-- A presentation, transported along a bijection of coordinates. -/
def reindex (e : ι ≃ ι') : {ℓ : ℕ} → CLFun F ι ℓ → CLFun F ι' ℓ
  | _, zero => zero
  | _, cons S L₁ next =>
    cons (S.map e.toEmbedding) (L₁.reindex e) fun v => (next ((reindexEquiv e).symm v)).reindex e

@[simp] theorem reindex_zero (e : ι ≃ ι') : (zero : CLFun F ι 0).reindex e = zero := rfl

@[simp] theorem reindex_cons (e : ι ≃ ι') {S : Finset ι} (L₁ : RegLinear F S)
    (next : (ι → F) → CLFun F ι ℓ) :
    (cons S L₁ next).reindex e =
      cons (S.map e.toEmbedding) (L₁.reindex e)
        fun v => (next ((reindexEquiv e).symm v)).reindex e := rfl

theorem SupportedOn.reindex (e : ι ≃ ι') {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.SupportedOn T) :
    (P.reindex e).SupportedOn (T.map e.toEmbedding) := by
  induction P generalizing T with
  | zero => trivial
  | cons S L₁ next ih =>
    obtain ⟨hS, hnext⟩ := hP
    refine ⟨Finset.map_subset_map.mpr hS, fun v => ?_⟩
    rw [map_sdiff']
    exact ih _ (hnext _)

theorem ExactlyOn.reindex (e : ι ≃ ι') {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.ExactlyOn T) :
    (P.reindex e).ExactlyOn (T.map e.toEmbedding) := by
  induction P generalizing T with
  | zero =>
    have hT : T = ∅ := hP
    show T.map e.toEmbedding = ∅
    rw [hT, Finset.map_empty]
  | cons S L₁ next ih =>
    obtain ⟨hS, hnext⟩ := hP
    refine ⟨Finset.map_subset_map.mpr hS, fun v => ?_⟩
    rw [map_sdiff']
    exact ih _ (hnext _)

theorem lift_reindex (e : ι ≃ ι') (T : Finset ι) (P : CLFun F ι ℓ) :
    (P.lift T).reindex e = (P.reindex e).lift (T.map e.toEmbedding) := by
  induction P generalizing T with
  | zero => simp [lift]
  | cons S L₁ next ih =>
    simp only [lift, reindex_cons]
    congr 1
    funext v
    rw [ih, map_sdiff']

theorem truncate_reindex (e : ι ≃ ι') (k : ℕ) (P : CLFun F ι ℓ) :
    (P.reindex e).truncate k = (P.truncate k).reindex e := by
  induction k generalizing ℓ P with
  | zero => simp
  | succ k ih =>
    cases P with
    | zero =>
      rw [reindex_zero, truncate_succ_zero, truncate_succ_zero, lift_reindex, ← ih, reindex_zero,
        Finset.map_empty]
    | cons S L₁ next =>
      rw [reindex_cons, truncate_succ_cons, truncate_succ_cons, reindex_cons]
      congr 1
      funext v
      exact ih _

end CLFun

end Reindex

/-! ## Evaluation, and the data of `lem:cl-kth` -/

variable [Fintype ι]

namespace CLFun

variable {ℓ : ℕ}

theorem compl_product_univ (S : Finset ι) :
    (S ×ˢ (Finset.univ : Finset κ))ᶜ = Sᶜ ×ˢ Finset.univ := by
  ext ⟨i, j⟩; simp

/-- `L^↓ = ↓ ∘ L ∘ ↓⁻¹`. -/
theorem eval_downsize (b : Module.Basis κ K F) (P : CLFun F ι ℓ) (x : ι → F) :
    (P.downsize b).eval (downsizeEquiv b x) = downsizeEquiv b (P.eval x) := by
  induction P generalizing x with
  | zero => simp
  | cons S L₁ next ih =>
    rw [downsize_cons, eval_cons, eval_cons, RegLinear.downsize_apply,
      LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, compl_product_univ,
      ← downsizeEquiv_proj, ih, map_add]

theorem eval_downsize' (b : Module.Basis κ K F) (P : CLFun F ι ℓ) (y : ι × κ → K) :
    (P.downsize b).eval y = downsizeEquiv b (P.eval ((downsizeEquiv b).symm y)) := by
  conv_lhs => rw [← (downsizeEquiv b).apply_symm_apply y]
  rw [eval_downsize]

/-- Item 1 of `lem:cl-downsize`: the marginals of `L^↓` are the downsized marginals of `L`. -/
theorem eval_truncate_downsize (b : Module.Basis κ K F) (k : ℕ) (P : CLFun F ι ℓ) (x : ι → F) :
    ((P.downsize b).truncate k).eval (downsizeEquiv b x) =
      downsizeEquiv b ((P.truncate k).eval x) := by
  rw [truncate_downsize, eval_downsize]

/-- Item 2 of `lem:cl-downsize`, factor spaces: `V^↓_{k, ↓u} = V_{k,u} × κ`. -/
theorem factorOfPrefix_downsize (b : Module.Basis κ K F) (P : CLFun F ι ℓ) (k : ℕ)
    (u : ι → F) :
    (P.downsize b).factorOfPrefix k (downsizeEquiv b u) =
      P.factorOfPrefix k u ×ˢ Finset.univ := by
  induction P generalizing k u with
  | zero => simp
  | cons S L₁ next ih =>
    cases k with
    | zero => rfl
    | succ k =>
      rw [downsize_cons, factorOfPrefix_cons_succ, factorOfPrefix_cons_succ, compl_product_univ,
        ← downsizeEquiv_proj, ← downsizeEquiv_proj, LinearEquiv.symm_apply_apply, ih]

/-- Item 2 of `lem:cl-downsize`, linear maps: `L^↓_{k, ↓u} = ↓ ∘ L_{k,u} ∘ ↓⁻¹`. -/
theorem mapOfPrefix_downsize (b : Module.Basis κ K F) (P : CLFun F ι ℓ) (k : ℕ) (u : ι → F) :
    (P.downsize b).mapOfPrefix k (downsizeEquiv b u) =
      (downsizeEquiv (ι := ι) b).toLinearMap ∘ₗ (P.mapOfPrefix k u).restrictScalars K ∘ₗ
        (downsizeEquiv (ι := ι) b).symm.toLinearMap := by
  induction P generalizing k u with
  | zero => ext y; simp
  | cons S L₁ next ih =>
    cases k with
    | zero => rfl
    | succ k =>
      rw [downsize_cons, mapOfPrefix_cons_succ, mapOfPrefix_cons_succ, compl_product_univ,
        ← downsizeEquiv_proj, ← downsizeEquiv_proj, LinearEquiv.symm_apply_apply, ih]

end CLFun

/-- `lem:cl-downsize` for functions: `↓ ∘ f ∘ ↓⁻¹` is an `ℓ`-level CL function on `V_{T × κ}`
over `K` whenever `f` is one on `V_T` over `F`. -/
theorem IsCLFun.downsize (b : Module.Basis κ K F) {ℓ : ℕ} {T : Finset ι}
    {f : (ι → F) → (ι → F)} (hf : IsCLFun ℓ T f) :
    IsCLFun ℓ (T ×ˢ Finset.univ) (downsizeEquiv b ∘ f ∘ (downsizeEquiv b).symm) := by
  obtain ⟨P, hP, rfl⟩ := hf
  exact ⟨P.downsize b, hP.downsize b, funext fun y => P.eval_downsize' b y⟩

section Reindex

variable [DecidableEq ι'] [Fintype ι']

namespace CLFun

variable {ℓ : ℕ}

theorem map_compl (e : ι ≃ ι') (S : Finset ι) : (S.map e.toEmbedding)ᶜ = Sᶜ.map e.toEmbedding := by
  ext i; simp [Finset.mem_map_equiv]

theorem eval_reindex (e : ι ≃ ι') (P : CLFun F ι ℓ) (x : ι → F) :
    (P.reindex e).eval (reindexEquiv e x) = reindexEquiv e (P.eval x) := by
  induction P generalizing x with
  | zero => simp
  | cons S L₁ next ih =>
    rw [reindex_cons, eval_cons, eval_cons, RegLinear.reindex_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply, map_compl, ← reindexEquiv_proj, ih, map_add]

theorem eval_reindex' (e : ι ≃ ι') (P : CLFun F ι ℓ) (y : ι' → F) :
    (P.reindex e).eval y = reindexEquiv e (P.eval ((reindexEquiv e).symm y)) := by
  conv_lhs => rw [← (reindexEquiv e).apply_symm_apply y]
  rw [eval_reindex]

theorem factorOfPrefix_reindex (e : ι ≃ ι') (P : CLFun F ι ℓ) (k : ℕ) (u : ι → F) :
    (P.reindex e).factorOfPrefix k (reindexEquiv e u) =
      (P.factorOfPrefix k u).map e.toEmbedding := by
  induction P generalizing k u with
  | zero => simp
  | cons S L₁ next ih =>
    cases k with
    | zero => rfl
    | succ k =>
      rw [reindex_cons, factorOfPrefix_cons_succ, factorOfPrefix_cons_succ, map_compl,
        ← reindexEquiv_proj, ← reindexEquiv_proj, LinearEquiv.symm_apply_apply, ih]

theorem mapOfPrefix_reindex (e : ι ≃ ι') (P : CLFun F ι ℓ) (k : ℕ) (u : ι → F) :
    (P.reindex e).mapOfPrefix k (reindexEquiv e u) =
      (reindexEquiv e).toLinearMap ∘ₗ P.mapOfPrefix k u ∘ₗ (reindexEquiv e).symm.toLinearMap := by
  induction P generalizing k u with
  | zero => ext y; simp
  | cons S L₁ next ih =>
    cases k with
    | zero => rfl
    | succ k =>
      rw [reindex_cons, mapOfPrefix_cons_succ, mapOfPrefix_cons_succ, map_compl,
        ← reindexEquiv_proj, ← reindexEquiv_proj, LinearEquiv.symm_apply_apply, ih]

end CLFun

/-- Reindexing, for functions. -/
theorem IsCLFun.reindex (e : ι ≃ ι') {ℓ : ℕ} {T : Finset ι} {f : (ι → F) → (ι → F)}
    (hf : IsCLFun ℓ T f) :
    IsCLFun ℓ (T.map e.toEmbedding) (reindexEquiv e ∘ f ∘ (reindexEquiv e).symm) := by
  obtain ⟨P, hP, rfl⟩ := hf
  exact ⟨P.reindex e, hP.reindex e, funext fun y => P.eval_reindex' e y⟩

end Reindex

section Distribution

variable [Fintype K] [DecidableEq K] [Fintype F] [DecidableEq F]

/-- `lem:downsize-cl-dist`: the CL distribution of the downsized functions is the image of the
CL distribution under `↓`. -/
theorem clDist_downsize (b : Module.Basis κ K F) (L R : (ι → F) → (ι → F)) (a c : ι → F) :
    clDist (downsizeEquiv b ∘ L ∘ (downsizeEquiv b).symm)
      (downsizeEquiv b ∘ R ∘ (downsizeEquiv b).symm) (downsizeEquiv b a) (downsizeEquiv b c) =
      clDist L R a c := by
  unfold clDist
  have hcard : Fintype.card (ι × κ → K) = Fintype.card (ι → F) :=
    Fintype.card_congr (downsizeEquiv b).toEquiv.symm
  rw [hcard]
  congr 2
  rw [← Finset.map_univ_equiv (downsizeEquiv b).toEquiv, Finset.filter_map, Finset.card_map]
  congr 1
  ext x
  simp [Function.comp, (downsizeEquiv b).injective.eq_iff]

end Distribution

end MIPRE.CL
