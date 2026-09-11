/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/BlockOperators.lean
-/
/-
# Block operators on `H^κ` and the lift into the matrix amplification

For a finite index type `κ` and the GNS space `H = L²(M)`, the block Hilbert
space `𝐇 = H^κ` (with the ℓ²-norm) carries coordinate embeddings and
projections, and every operator `T` on `𝐇` has entries
`entry T r r' = proj r ∘ T ∘ embed r'`. The **block algebra** `blockAlg M κ` is
the closed star subalgebra of operators all of whose entries lie in the
concrete von Neumann algebra `vnAlg M` (`VN/ConcreteVN.lean`); it is
isomorphic to `Matrix κ κ (vnAlg M)`, and `lift` sends it into the matrix
amplification `amplify (vnModel M) d`, `d = card κ`, as a star algebra
homomorphism with `τ (lift T) = d⁻¹ ∑ᵣ φ(entry T r r)`. The corner copy
`E s T = embed s ∘ T ∘ proj s` of `vnAlg M` at a coordinate `s` is the
"source corner" of the resolver construction (node 1.2.6). Infrastructure
only; no manuscript statement.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.ConcreteVN
import MIPRE.Background.Repetition.CommutingRepetition.VN.Amplify

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace Block

open scoped BigOperators InnerProductSpace
open StdTracialAlgebra

set_option linter.unusedSectionVars false

universe u

variable (M : StdTracialAlgebra.{u}) (κ : Type) [Fintype κ] [DecidableEq κ]

/-- The block Hilbert space `H^κ`. -/
abbrev BH : Type u := PiLp 2 (fun _ : κ => M.H)

/-! ## Coordinate embeddings and projections -/

/-- Coordinate embedding `v ↦ (0, …, v, …, 0)`. -/
noncomputable def embed (r : κ) : M.H →L[ℂ] BH M κ :=
  ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : κ => M.H)).symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.pi fun r' : κ =>
      if r' = r then ContinuousLinearMap.id ℂ M.H else 0)

/-- Coordinate projection. -/
noncomputable def proj (r : κ) : BH M κ →L[ℂ] M.H := PiLp.proj 2 (fun _ : κ => M.H) r

theorem embed_apply (r r' : κ) (v : M.H) : embed M κ r v r' = if r' = r then v else 0 := by
  unfold embed
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, PiLp.coe_symm_continuousLinearEquiv]
  show (ContinuousLinearMap.pi fun r' : κ =>
      if r' = r then ContinuousLinearMap.id ℂ M.H else 0) v r' = _
  rw [ContinuousLinearMap.pi_apply]
  split_ifs <;> rfl

theorem proj_apply (r : κ) (w : BH M κ) : proj M κ r w = w r := rfl

theorem proj_embed (r r' : κ) (v : M.H) :
    proj M κ r (embed M κ r' v) = if r = r' then v else 0 := by
  rw [proj_apply, embed_apply]

theorem proj_comp_embed_same (r : κ) : (proj M κ r).comp (embed M κ r) = ContinuousLinearMap.id ℂ M.H := by
  ext v
  simp [proj_embed]

theorem proj_comp_embed_ne {r r' : κ} (h : r ≠ r') : (proj M κ r).comp (embed M κ r') = 0 := by
  ext v
  simp [proj_embed, h]

theorem inner_embed_left (r : κ) (v : M.H) (w : BH M κ) :
    ⟪embed M κ r v, w⟫_ℂ = ⟪v, w r⟫_ℂ := by
  rw [PiLp.inner_apply]
  simp only [embed_apply]
  rw [Finset.sum_eq_single r]
  · simp
  · intro r' _ hr'
    simp [hr']
  · intro h
    exact absurd (Finset.mem_univ r) h

theorem adjoint_embed (r : κ) : ContinuousLinearMap.adjoint (embed M κ r) = proj M κ r := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro w v
  rw [proj_apply]
  conv_rhs => rw [← inner_conj_symm, inner_embed_left, inner_conj_symm]

theorem adjoint_proj (r : κ) : ContinuousLinearMap.adjoint (proj M κ r) = embed M κ r := by
  rw [← adjoint_embed, ContinuousLinearMap.adjoint_adjoint]

theorem sumA {ι : Type*} (s : Finset ι) (f : ι → BH M κ) (r : κ) :
    (∑ i ∈ s, f i) r = ∑ i ∈ s, f i r := by
  show WithLp.ofLp (∑ i ∈ s, f i) r = ∑ i ∈ s, WithLp.ofLp (f i) r
  rw [WithLp.ofLp_sum, Finset.sum_apply]

theorem sumCLM {ι : Type*} {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F] (s : Finset ι) (f : ι → E →L[ℂ] F) (v : E) :
    (∑ i ∈ s, f i) v = ∑ i ∈ s, f i v := by
  rw [ContinuousLinearMap.coe_sum', Finset.sum_apply]

theorem sum_embed_proj_apply (w : BH M κ) : ∑ r, embed M κ r (proj M κ r w) = w := by
  ext r'
  rw [sumA]
  simp only [embed_apply, proj_apply]
  rw [Finset.sum_ite_eq Finset.univ r']
  simp

/-! ## Entries -/

/-- The `(r, r')` entry of a block operator. -/
noncomputable def entry (T : BH M κ →L[ℂ] BH M κ) (r r' : κ) : M.H →L[ℂ] M.H :=
  (proj M κ r).comp (T.comp (embed M κ r'))

theorem entry_apply (T : BH M κ →L[ℂ] BH M κ) (r r' : κ) (v : M.H) :
    entry M κ T r r' v = proj M κ r (T (embed M κ r' v)) := rfl

theorem entry_add (T T' : BH M κ →L[ℂ] BH M κ) (r r' : κ) :
    entry M κ (T + T') r r' = entry M κ T r r' + entry M κ T' r r' := by
  ext v; simp [entry_apply]

theorem entry_sub (T T' : BH M κ →L[ℂ] BH M κ) (r r' : κ) :
    entry M κ (T - T') r r' = entry M κ T r r' - entry M κ T' r r' := by
  ext v; simp [entry_apply]

theorem entry_smul (c : ℂ) (T : BH M κ →L[ℂ] BH M κ) (r r' : κ) :
    entry M κ (c • T) r r' = c • entry M κ T r r' := by
  ext v; simp [entry_apply]

theorem entry_zero (r r' : κ) : entry M κ (0 : BH M κ →L[ℂ] BH M κ) r r' = 0 := by
  ext v; simp [entry_apply]

theorem entry_one (r r' : κ) :
    entry M κ (1 : BH M κ →L[ℂ] BH M κ) r r' = if r = r' then 1 else 0 := by
  ext v
  rw [entry_apply, ContinuousLinearMap.one_apply, proj_embed]
  split_ifs <;> rfl

theorem entry_mul (T T' : BH M κ →L[ℂ] BH M κ) (r r' : κ) :
    entry M κ (T * T') r r' = ∑ k, entry M κ T r k * entry M κ T' k r' := by
  ext v
  rw [sumCLM, entry_apply]
  show proj M κ r (T (T' (embed M κ r' v))) = _
  conv_lhs => rw [← sum_embed_proj_apply M κ (T' (embed M κ r' v))]
  rw [map_sum, map_sum]
  rfl

theorem entry_star (T : BH M κ →L[ℂ] BH M κ) (r r' : κ) :
    entry M κ (star T) r r' = star (entry M κ T r' r) := by
  unfold entry
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, adjoint_embed, adjoint_proj,
    ContinuousLinearMap.comp_assoc]

theorem continuous_entry (r r' : κ) : Continuous fun T : BH M κ →L[ℂ] BH M κ => entry M κ T r r' :=
  continuous_const.clm_comp (continuous_id.clm_comp continuous_const)

/-- Block decomposition `T = ∑ r r', embed r ∘ entry T r r' ∘ proj r'`. -/
theorem block_decomp (T : BH M κ →L[ℂ] BH M κ) :
    T = ∑ r, ∑ r', (embed M κ r).comp ((entry M κ T r r').comp (proj M κ r')) := by
  ext w
  rw [sumCLM]
  have h1 : ∀ r, (∑ r', (embed M κ r).comp ((entry M κ T r r').comp (proj M κ r'))) w
      = embed M κ r (proj M κ r (T w)) := by
    intro r
    rw [sumCLM]
    simp only [ContinuousLinearMap.comp_apply, entry_apply]
    rw [← map_sum, ← map_sum, ← map_sum, sum_embed_proj_apply]
  rw [Finset.sum_congr rfl fun r _ => h1 r, sum_embed_proj_apply]

/-! ## The block algebra -/

/-- Block operators with all entries in the concrete von Neumann algebra. -/
noncomputable def blockAlg : StarSubalgebra ℂ (BH M κ →L[ℂ] BH M κ) where
  carrier := {T | ∀ r r', entry M κ T r r' ∈ M.vnAlg}
  mul_mem' := by
    intro T T' hT hT' r r'
    rw [entry_mul]
    exact sum_mem fun k _ => mul_mem (hT r k) (hT' k r')
  one_mem' := by
    intro r r'
    rw [entry_one]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  add_mem' := by
    intro T T' hT hT' r r'
    rw [entry_add]
    exact add_mem (hT r r') (hT' r r')
  zero_mem' := by
    intro r r'
    rw [entry_zero]
    exact zero_mem _
  algebraMap_mem' := by
    intro c r r'
    rw [Algebra.algebraMap_eq_smul_one, entry_smul, entry_one]
    split_ifs
    · exact SMulMemClass.smul_mem c (one_mem _)
    · rw [smul_zero]; exact zero_mem _
  star_mem' := by
    intro T hT r r'
    rw [entry_star]
    exact star_mem (hT r' r)

theorem mem_blockAlg_iff {T : BH M κ →L[ℂ] BH M κ} :
    T ∈ blockAlg M κ ↔ ∀ r r', entry M κ T r r' ∈ M.vnAlg := Iff.rfl

theorem isClosed_blockAlg : IsClosed (blockAlg M κ : Set (BH M κ →L[ℂ] BH M κ)) := by
  have : (blockAlg M κ : Set (BH M κ →L[ℂ] BH M κ))
      = ⋂ r, ⋂ r', (fun T => entry M κ T r r') ⁻¹' (M.vnAlg : Set _) := by
    ext T
    simp only [SetLike.mem_coe, mem_blockAlg_iff, Set.mem_iInter, Set.mem_preimage]
  rw [this]
  exact isClosed_iInter fun r => isClosed_iInter fun r' =>
    M.isClosed_vnAlg.preimage (continuous_entry M κ r r')

/-! ## The lift into the amplification -/

/-- The amplification dimension. -/
abbrev dim : ℕ := Fintype.card κ

variable [Nonempty κ]

instance : NeZero (dim κ) := ⟨Fintype.card_ne_zero⟩

/-- The target algebra `M_d(vnAlg M)` as a standard tracial algebra. -/
noncomputable abbrev N : StdTracialAlgebra.{u} := amplify M.vnModel (dim κ)

/-- The index equivalence. -/
noncomputable abbrev eκ : κ ≃ Fin (dim κ) := Fintype.equivFin κ

/-- The entry matrix of a block-algebra element, reindexed to `Fin d`. -/
noncomputable def liftFun (T : ↥(blockAlg M κ)) :
    Matrix (Fin (dim κ)) (Fin (dim κ)) M.vnModel.A :=
  Matrix.of fun p q : Fin (dim κ) =>
    (⟨entry M κ T.1 ((eκ κ).symm p) ((eκ κ).symm q), T.2 _ _⟩ : ↥M.vnAlg)

theorem liftFun_apply (T : ↥(blockAlg M κ)) (p q : Fin (dim κ)) :
    Subtype.val (liftFun M κ T p q : ↥M.vnAlg)
      = entry M κ T.1 ((eκ κ).symm p) ((eκ κ).symm q) := rfl

theorem liftFun_one : liftFun M κ 1 = 1 := by
  refine Matrix.ext fun p q => ?_
  rw [Matrix.one_apply]
  apply Subtype.ext
  rw [liftFun_apply]
  show entry M κ (1 : BH M κ →L[ℂ] BH M κ) _ _ = _
  rw [entry_one]
  by_cases h : p = q
  · subst h
    rw [if_pos rfl, if_pos rfl]
    rfl
  · have h' : (eκ κ).symm p ≠ (eκ κ).symm q := fun e => h ((eκ κ).symm.injective e)
    rw [if_neg h, if_neg h']
    rfl

theorem liftFun_mul (T T' : ↥(blockAlg M κ)) :
    liftFun M κ (T * T') = liftFun M κ T * liftFun M κ T' := by
  refine Matrix.ext fun p q => ?_
  rw [Matrix.mul_apply]
  apply Subtype.ext
  have key : ∀ f : Fin (dim κ) → ↥M.vnAlg,
      Subtype.val (∑ j, f j) = ∑ j, Subtype.val (f j) := fun f =>
    map_sum M.vnAlg.subtype f Finset.univ
  show entry M κ (T.1 * T'.1) _ _
    = Subtype.val (∑ j, (liftFun M κ T p j : ↥M.vnAlg) * (liftFun M κ T' j q : ↥M.vnAlg))
  refine Eq.trans ?_ (key _).symm
  refine (entry_mul M κ T.1 T'.1 _ _).trans ?_
  refine (Equiv.sum_comp (eκ κ).symm _).symm.trans ?_
  rfl

theorem liftFun_add (T T' : ↥(blockAlg M κ)) :
    liftFun M κ (T + T') = liftFun M κ T + liftFun M κ T' := by
  refine Matrix.ext fun p q => ?_
  apply Subtype.ext
  rw [Matrix.add_apply]
  show entry M κ (T.1 + T'.1) _ _ = entry M κ T.1 _ _ + entry M κ T'.1 _ _
  rw [entry_add]

theorem liftFun_zero : liftFun M κ 0 = 0 := by
  refine Matrix.ext fun p q => ?_
  apply Subtype.ext
  show entry M κ (0 : BH M κ →L[ℂ] BH M κ) _ _ = (0 : M.H →L[ℂ] M.H)
  rw [entry_zero]

theorem liftFun_smul (c : ℂ) (T : ↥(blockAlg M κ)) :
    liftFun M κ (c • T) = c • liftFun M κ T := by
  refine Matrix.ext fun p q => ?_
  apply Subtype.ext
  rw [Matrix.smul_apply]
  show entry M κ (c • T.1) _ _ = c • entry M κ T.1 _ _
  rw [entry_smul]

theorem liftFun_star (T : ↥(blockAlg M κ)) : liftFun M κ (star T) = star (liftFun M κ T) := by
  refine Matrix.ext fun p q => ?_
  apply Subtype.ext
  rw [Matrix.star_apply]
  show entry M κ (star T.1) _ _ = star (entry M κ T.1 _ _)
  rw [entry_star]

/-- **The lift** `blockAlg M κ →⋆ₐ[ℂ] M_d(vnAlg M)`. -/
noncomputable def lift : ↥(blockAlg M κ) →⋆ₐ[ℂ] (N M κ).A where
  toFun := liftFun M κ
  map_one' := liftFun_one M κ
  map_mul' := liftFun_mul M κ
  map_zero' := liftFun_zero M κ
  map_add' := liftFun_add M κ
  commutes' := fun c => by
    rw [Algebra.algebraMap_eq_smul_one, liftFun_smul, liftFun_one, Algebra.algebraMap_eq_smul_one]
    rfl
  map_star' := liftFun_star M κ

theorem lift_apply (T : ↥(blockAlg M κ)) (p q : Fin (dim κ)) :
    Subtype.val (lift M κ T p q : ↥M.vnAlg)
      = entry M κ T.1 ((eκ κ).symm p) ((eκ κ).symm q) := rfl

/-- The amplified trace of a lifted block operator: `d⁻¹ ∑ᵣ φ(entry T r r)`. -/
theorem τ_lift (T : ↥(blockAlg M κ)) :
    (N M κ).τ (lift M κ T) = ((dim κ : ℂ))⁻¹ * ∑ r, M.traceState (entry M κ T.1 r r) := by
  have h : (N M κ).τ (lift M κ T) = ((dim κ : ℂ))⁻¹ * ∑ i : Fin (dim κ),
      M.vnModel.τ ((lift M κ T : Matrix (Fin (dim κ)) (Fin (dim κ)) M.vnModel.A) i i) :=
    ampτ_apply M.vnModel (dim κ) (lift M κ T)
  rw [h]
  congr 1
  rw [← Equiv.sum_comp (eκ κ).symm]
  rfl

/-! ## The corner copy of `vnAlg M` -/

variable (s : κ)

theorem entry_corner (T : M.H →L[ℂ] M.H) (r r' : κ) :
    entry M κ ((embed M κ s).comp (T.comp (proj M κ s))) r r'
      = if r = s ∧ r' = s then T else 0 := by
  ext v
  rw [entry_apply]
  simp only [ContinuousLinearMap.comp_apply]
  rw [proj_embed, proj_embed]
  by_cases hr : r = s
  · by_cases hr' : r' = s
    · subst hr; subst hr'; simp
    · simp [hr, hr', Ne.symm hr']
  · simp [hr]

theorem corner_mem (T : ↥M.vnAlg) :
    (embed M κ s).comp (T.1.comp (proj M κ s)) ∈ blockAlg M κ := by
  intro r r'
  rw [entry_corner]
  split_ifs
  · exact T.2
  · exact zero_mem _

/-- The corner copy `E s T = embed s ∘ T ∘ proj s`. -/
noncomputable def E (T : ↥M.vnAlg) : ↥(blockAlg M κ) :=
  ⟨(embed M κ s).comp (T.1.comp (proj M κ s)), corner_mem M κ s T⟩

theorem E_val (T : ↥M.vnAlg) : (E M κ s T).1 = (embed M κ s).comp (T.1.comp (proj M κ s)) := rfl

theorem E_mul (T T' : ↥M.vnAlg) : E M κ s (T * T') = E M κ s T * E M κ s T' := by
  apply Subtype.ext
  rw [E_val]
  show _ = (E M κ s T).1.comp (E M κ s T').1
  rw [E_val, E_val]
  ext v
  simp [proj_embed]

theorem E_star (T : ↥M.vnAlg) : E M κ s (star T) = star (E M κ s T) := by
  apply Subtype.ext
  rw [E_val]
  show _ = star (E M κ s T).1
  rw [E_val, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_comp, adjoint_embed, adjoint_proj, ContinuousLinearMap.comp_assoc]
  rfl

theorem E_add (T T' : ↥M.vnAlg) : E M κ s (T + T') = E M κ s T + E M κ s T' := by
  apply Subtype.ext
  rw [E_val]
  show _ = (E M κ s T).1 + (E M κ s T').1
  rw [E_val, E_val]
  ext v
  simp

theorem E_sub (T T' : ↥M.vnAlg) : E M κ s (T - T') = E M κ s T - E M κ s T' := by
  apply Subtype.ext
  rw [E_val]
  show _ = (E M κ s T).1 - (E M κ s T').1
  rw [E_val, E_val]
  ext v
  simp

theorem E_smul (c : ℂ) (T : ↥M.vnAlg) : E M κ s (c • T) = c • E M κ s T := by
  apply Subtype.ext
  rw [E_val]
  show _ = c • (E M κ s T).1
  rw [E_val]
  ext v
  simp

theorem E_zero : E M κ s 0 = 0 := by
  apply Subtype.ext
  rw [E_val]
  show _ = (0 : BH M κ →L[ℂ] BH M κ)
  ext v; simp

/-- The corner copy as an additive monoid homomorphism. -/
noncomputable def Eadd : ↥M.vnAlg →+ ↥(blockAlg M κ) where
  toFun := E M κ s
  map_zero' := E_zero M κ s
  map_add' := E_add M κ s

theorem E_sum {ι : Type*} (t : Finset ι) (f : ι → ↥M.vnAlg) :
    E M κ s (∑ x ∈ t, f x) = ∑ x ∈ t, E M κ s (f x) :=
  map_sum (Eadd M κ s) f t

/-- `τ_N (lift (E s T)) = d⁻¹ φ(T)`. -/
theorem τ_lift_E (T : ↥M.vnAlg) :
    (N M κ).τ (lift M κ (E M κ s T)) = ((dim κ : ℂ))⁻¹ * M.traceState T.1 := by
  rw [τ_lift]
  congr 1
  rw [Finset.sum_eq_single s]
  · rw [E_val, entry_corner]; simp
  · intro r _ hr
    rw [E_val, entry_corner]
    simp [hr, StdTracialAlgebra.traceState]
  · intro h
    exact absurd (Finset.mem_univ s) h

/-! ## Placement, matrix units and the block-diagonal right action -/

section Place

/-- `X ↦ embed r ∘ X ∘ proj r'` as a continuous linear map. -/
noncomputable def place (r r' : κ) :
    (M.H →L[ℂ] M.H) →L[ℂ] (BH M κ →L[ℂ] BH M κ) :=
  (ContinuousLinearMap.compL ℂ (BH M κ) M.H (BH M κ) (embed M κ r)).comp
    ((ContinuousLinearMap.compL ℂ (BH M κ) M.H M.H).flip (proj M κ r'))

theorem place_apply (r r' : κ) (X : M.H →L[ℂ] M.H) :
    place M κ r r' X = (embed M κ r).comp (X.comp (proj M κ r')) := rfl

theorem place_apply_vec (r r' : κ) (X : M.H →L[ℂ] M.H) (w : BH M κ) :
    place M κ r r' X w = embed M κ r (X (w r')) := rfl

theorem entry_place (r r' : κ) (X : M.H →L[ℂ] M.H) (q q' : κ) :
    entry M κ (place M κ r r' X) q q' = if q = r ∧ q' = r' then X else 0 := by
  ext v
  rw [entry_apply, place_apply_vec, embed_apply, proj_embed]
  by_cases hq : q = r
  · by_cases hq' : q' = r'
    · subst hq; subst hq'; simp
    · simp [hq, hq', Ne.symm hq']
  · simp [hq]

theorem place_mem (r r' : κ) {T : M.H →L[ℂ] M.H} (hT : T ∈ M.vnAlg) :
    place M κ r r' T ∈ blockAlg M κ := by
  intro q q'
  rw [entry_place]
  split_ifs
  · exact hT
  · exact zero_mem _

theorem entry_sum {ι : Type*} (s : Finset ι) (T : ι → BH M κ →L[ℂ] BH M κ) (r r' : κ) :
    entry M κ (∑ i ∈ s, T i) r r' = ∑ i ∈ s, entry M κ (T i) r r' := by
  ext v
  rw [sumCLM, entry_apply, sumCLM, map_sum]
  rfl

/-- Two block operators with the same entries are equal. -/
theorem ext_entry {T T' : BH M κ →L[ℂ] BH M κ}
    (h : ∀ r r', entry M κ T r r' = entry M κ T' r r') : T = T' := by
  rw [block_decomp M κ T, block_decomp M κ T']
  simp only [h]

theorem place_mul_place (r r' q q' : κ) (X Y : M.H →L[ℂ] M.H) :
    place M κ r r' X * place M κ q q' Y = if r' = q then place M κ r q' (X * Y) else 0 := by
  refine ContinuousLinearMap.ext fun w => ?_
  show embed M κ r (X (embed M κ q (Y (w q')) r')) = _
  rw [embed_apply]
  split_ifs with h1
  · subst h1; rfl
  · simp

theorem star_place (r r' : κ) (X : M.H →L[ℂ] M.H) :
    star (place M κ r r' X) = place M κ r' r (star X) := by
  rw [place_apply, place_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_comp, adjoint_embed, adjoint_proj, ContinuousLinearMap.comp_assoc]

theorem place_one_mul_mul_place_one (s r r' s' : κ) (W : BH M κ →L[ℂ] BH M κ) :
    place M κ s r 1 * W * place M κ r' s' 1 = place M κ s s' (entry M κ W r r') := by
  ext w
  rfl

/-- The block-diagonal right action `diag (R b)`. -/
noncomputable def Rt (b : M.A) : BH M κ →L[ℂ] BH M κ := ∑ r, place M κ r r (M.Rop b)

theorem entry_Rt (b : M.A) (r r' : κ) :
    entry M κ (Rt M κ b) r r' = if r = r' then M.Rop b else 0 := by
  unfold Rt
  rw [entry_sum]
  simp only [entry_place]
  rw [Finset.sum_eq_single r]
  · by_cases h : r = r'
    · subst h; simp
    · simp [h, Ne.symm h]
  · intro q _ hq
    simp [Ne.symm hq]
  · intro h
    exact absurd (Finset.mem_univ r) h

theorem entry_mul_Rt (T : BH M κ →L[ℂ] BH M κ) (b : M.A) (r r' : κ) :
    entry M κ (T * Rt M κ b) r r' = entry M κ T r r' * M.Rop b := by
  rw [entry_mul]
  simp only [entry_Rt, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ r']
  simp

theorem entry_Rt_mul (T : BH M κ →L[ℂ] BH M κ) (b : M.A) (r r' : κ) :
    entry M κ (Rt M κ b * T) r r' = M.Rop b * entry M κ T r r' := by
  rw [entry_mul]
  simp only [entry_Rt, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq Finset.univ r]
  simp

theorem star_Rt (b : M.A) : star (Rt M κ b) = Rt M κ (star b) := by
  refine ext_entry M κ fun r r' => ?_
  rw [entry_star, entry_Rt, entry_Rt]
  by_cases h : r = r'
  · subst h; simp [M.star_Rop]
  · simp [h, Ne.symm h]

/-- Membership in the block algebra is commutation with the block-diagonal right action. -/
theorem mem_blockAlg_iff_comm {T : BH M κ →L[ℂ] BH M κ} :
    T ∈ blockAlg M κ ↔ ∀ b : M.A, Rt M κ b * T = T * Rt M κ b := by
  constructor
  · intro hT b
    refine ext_entry M κ fun r r' => ?_
    rw [entry_Rt_mul, entry_mul_Rt]
    exact (M.mem_vnAlg_iff.mp (hT r r') b)
  · intro h r r'
    rw [M.mem_vnAlg_iff]
    intro b
    have := congrArg (fun T => entry M κ T r r') (h b)
    simp only [entry_Rt_mul, entry_mul_Rt] at this
    exact this

end Place

end Block

end CommutingRepetition
