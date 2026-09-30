/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.AncillaIsometry
public import MIPRE.Foundations.Expanded
public import MIPRE.Foundations.WeylEPR

@[expose] public section

/-!
# The EPR register in a bipartite model

Introspection's soundness analysis runs on a state `|EPR_I⟩ ⊗ |ξ⟩`: a maximally entangled
register `I`, shared by the two players, next to whatever else they hold. In the tensor-product
model `ξ` is a vector of `ℂ^{H} ⊗ ℂ^{K}` and the players' operators are matrices on
`ℂ^{I} ⊗ ℂ^{H}` and `ℂ^{I} ⊗ ℂ^{K}` (`MIPRE.Introspection.registerState`). Phase 4 of
`planning/mipco-track.md` keeps the register and abstracts the rest: `ξ` becomes a bipartite model
`N`, and the state `|EPR_I⟩ ⊗ |ξ⟩` its extension by the register (`BipartiteModel.reg`, the
ancilla extension of `MIPRE/Foundations/AncillaModel.lean` in the vector `registerEPR I`). The
first player's operators are then the `I × I` matrices over the first player's algebra of `N`,
the second's over the second's; a matrix `P` on the register acting as `P ⊗ 1` is `smulKron 1 P`.

* **The mirror identity** (`reg_mirror`, `reg_mirror_smulKron`): an operator `P` on the first
  player's register acts on the state as its transpose on the second player's. This is the
  switching trick of the analysis, and it is exact in any model, the register being a matrix
  factor.
* **The register is carried along bijections** (`regRelabel`), **split** into two registers
  (`regSplit`), and **extended** by one on which nothing acts (`regExtend`), each by a local
  isometry carrying the state exactly (`MIPRE/Foundations/AncillaIsometry.lean`); and the players
  are exchanged (`regSwap`).
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix
open scoped Kronecker

variable {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype R] [DecidableEq R]

/-- The maximally entangled state, indexed by an arbitrary finite basis. -/
def registerEPR (I : Type*) [Fintype I] [DecidableEq I] : I × I → ℂ :=
  fun p => if p.1 = p.2 then (((Real.sqrt (Fintype.card I))⁻¹ : ℝ) : ℂ) else 0

/-- The finite-basis EPR definition agrees literally with the Weyl-register definition. -/
theorem registerEPR_eq_weyl {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F] {ι : Type*} [Fintype ι] [DecidableEq ι] :
    registerEPR (ι → F) = Weyl.epr (F := F) (n := ι) := rfl

/-- Simultaneous relabelling of both EPR halves leaves the state unchanged. -/
theorem registerEPR_equiv (e : I ≃ J) :
    registerEPR J ∘ e.prodCongr e = registerEPR I := by
  funext p
  simp only [Function.comp_apply, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
    registerEPR, e.injective.eq_iff,
    Fintype.card_congr e]

/-- EPR on a product basis factors exactly into the two EPR states. -/
theorem registerEPR_prod :
    registerEPR (I × J) = expVec (registerEPR I) (registerEPR J) := by
  funext p
  obtain ⟨⟨i, j⟩, ⟨i', j'⟩⟩ := p
  simp only [registerEPR, expVec, Prod.mk.injEq, Fintype.card_prod, Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg _), _root_.mul_inv_rev, Complex.ofReal_mul]
  by_cases hi : i = i' <;> by_cases hj : j = j' <;> simp [hi, hj, mul_comm]

/-- Unit normalization for a nonempty finite EPR basis. -/
theorem registerEPR_norm [Nonempty I] : ‖evec (registerEPR I)‖ = 1 := by
  have hc : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hs : Real.sqrt (Fintype.card I) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hc)
  rw [evec, EuclideanSpace.norm_eq]
  simp only [registerEPR, Fintype.sum_prod_type]
  simp only [apply_ite norm, norm_zero, zero_pow (by decide : 2 ≠ 0),
    ite_pow, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_inv, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt hc.le]
  rw [mul_inv_cancel₀ hc.ne', Real.sqrt_one]

/-- The EPR state is symmetric under the exchange of its halves. -/
theorem registerEPR_swap (p : I × I) : registerEPR I p.swap = registerEPR I p := by
  simp only [registerEPR, Prod.fst_swap, Prod.snd_swap, eq_comm]

/-- **The mirror identity of the EPR state**: an operator on the first half acts on the state as
its transpose on the second half. -/
theorem kron_one_mulVec_registerEPR (P : Matrix I I ℂ) :
    (P ⊗ₖ (1 : Matrix I I ℂ)) *ᵥ registerEPR I = ((1 : Matrix I I ℂ) ⊗ₖ Pᵀ) *ᵥ registerEPR I := by
  funext p
  obtain ⟨i, j⟩ := p
  simp only [mulVec, dotProduct, Fintype.sum_prod_type, kroneckerMap_apply, one_apply,
    transpose_apply, registerEPR, mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

end MIPRE.Introspection

namespace MIPRE.BipartiteModel

open Introspection OperatorMatrix Matrix
open scoped Kronecker

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] (N : BipartiteModel 𝒞 𝒜 ℬ)
variable {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype R] [DecidableEq R]

/-- **The register model**: `N` with an EPR register `I` adjoined for the two players, in the
state `|EPR_I⟩ ⊗ ψ`. The first player's operators are the `I × I` matrices over the first
player's algebra of `N`, the second's over the second's. -/
abbrev reg (I : Type*) [Fintype I] [DecidableEq I] :
    BipartiteModel (Matrix (I × I) (I × I) 𝒞) (Matrix I I 𝒜) (Matrix I I ℬ) :=
  N.expand (registerEPR I)

/-- The state of the register model has the norm of the state of `N`. -/
theorem norm_reg_ψ [Nonempty I] : ‖(N.reg I).ψ‖ = ‖N.ψ‖ := by
  rw [norm_expand_state, registerEPR_norm, one_mul]

/-- **The mirror identity in the register model**: the first player's register operator
`X ⊗ P` acts on the state as `X ⊗ 1` for the first player times `1 ⊗ Pᵀ` for the second. -/
theorem reg_mirror_smulKron (X : 𝒜) (P : Matrix I I ℂ) :
    (N.reg I).π ((N.reg I).πA (smulKron X P)) (N.reg I).ψ =
      (N.reg I).π ((N.reg I).πA (smulKron X 1) * (N.reg I).πB (smulKron 1 Pᵀ)) (N.reg I).ψ := by
  have h1 : (N.reg I).πA (smulKron X P) =
      (N.reg I).πA (smulKron X P) * (N.reg I).πB (smulKron (1 : ℬ) (1 : Matrix I I ℂ)) := by
    rw [smulKron_one_one, map_one, mul_one]
  rw [h1, expand_π_smulKron_ψ, expand_π_smulKron_ψ, kron_one_mulVec_registerEPR]

/-- **The mirror identity**: a matrix `P` on the first player's register acts on the state as
its transpose on the second player's. -/
theorem reg_mirror (P : Matrix I I ℂ) :
    (N.reg I).π ((N.reg I).πA (smulKron 1 P)) (N.reg I).ψ =
      (N.reg I).π ((N.reg I).πB (smulKron 1 Pᵀ)) (N.reg I).ψ := by
  rw [reg_mirror_smulKron, smulKron_one_one, map_one, one_mul]

/-! ## Moving the register -/

/-- **Relabelling the register** along a bijection `f : I ≃ J`: the register model on `J` into
the register model on `I`, the players' operators relabelled by `f`. -/
def regRelabel (f : I ≃ J) : LocalIsometry (N.reg J) (N.reg I) :=
  N.relabel (registerEPR J) (registerEPR I) f f

theorem regRelabel_W_ψ (f : I ≃ J) : (N.regRelabel f).W (N.reg J).ψ = (N.reg I).ψ :=
  N.relabel_W_ψ _ _ f f fun p => (congrFun (registerEPR_equiv f) p).symm

@[simp]
theorem regRelabel_ΦA (f : I ≃ J) (X : Matrix J J 𝒜) :
    (N.regRelabel f).ΦA X = X.submatrix f f := rfl

@[simp]
theorem regRelabel_ΦB (f : I ≃ J) (Y : Matrix J J ℬ) :
    (N.regRelabel f).ΦB Y = Y.submatrix f f := rfl

/-- **Splitting the register** along `e : I ≃ J × R`: the register model on `J` over the register
model on `R` into the register model on `I`, the players' block matrices of block matrices read
as block matrices along `e`. -/
def regSplit (e : I ≃ J × R) : LocalIsometry ((N.reg R).reg J) (N.reg I) :=
  (N.relabel (registerEPR (J × R)) (registerEPR I) e e).comp
    (N.assoc (registerEPR R) (registerEPR J) (registerEPR (J × R)))

theorem regSplit_W_ψ (e : I ≃ J × R) : (N.regSplit e).W ((N.reg R).reg J).ψ = (N.reg I).ψ :=
  LocalIsometry.comp_W_ψ
    (N.assoc_W_ψ _ _ _ fun q => by rw [registerEPR_prod]; rfl)
    (N.relabel_W_ψ _ _ e e fun p => (congrFun (registerEPR_equiv e) p).symm)

theorem regSplit_ΦA (e : I ≃ J × R) (X : Matrix J J (Matrix R R 𝒜)) (i i' : I) :
    (N.regSplit e).ΦA X i i' = X (e i).1 (e i').1 (e i).2 (e i').2 := rfl

theorem regSplit_ΦB (e : I ≃ J × R) (Y : Matrix J J (Matrix R R ℬ)) (i i' : I) :
    (N.regSplit e).ΦB Y i i' = Y (e i).1 (e i').1 (e i).2 (e i').2 := rfl

/-- **Extending the register** along `e : I ≃ J × R` by a register `R` on which nothing acts: the
register model on `J` into the register model on `I`, an operator `X` on `J` becoming `X ⊗ 1_R`
read along `e`. -/
def regExtend [Nonempty R] (e : I ≃ J × R) : LocalIsometry (N.reg J) (N.reg I) :=
  (N.relabel (registerEPR (R × J)) (registerEPR I) (e.trans (Equiv.prodComm J R))
      (e.trans (Equiv.prodComm J R))).comp
    ((N.assoc (registerEPR J) (registerEPR R) (registerEPR (R × J))).comp
      ((N.reg J).inert (registerEPR R) registerEPR_norm))

theorem regExtend_W_ψ [Nonempty R] (e : I ≃ J × R) :
    (N.regExtend e).W (N.reg J).ψ = (N.reg I).ψ :=
  LocalIsometry.comp_W_ψ
    (LocalIsometry.comp_W_ψ ((N.reg J).inert_W_ψ _ _)
      (N.assoc_W_ψ _ _ _ fun q => by rw [registerEPR_prod]; rfl))
    (N.relabel_W_ψ _ _ _ _ fun p =>
      (congrFun (registerEPR_equiv (e.trans (Equiv.prodComm J R))) p).symm)

theorem regExtend_ΦA [Nonempty R] (e : I ≃ J × R) (X : Matrix J J 𝒜) (i i' : I) :
    (N.regExtend e).ΦA X i i' = if (e i).2 = (e i').2 then X (e i).1 (e i').1 else 0 := by
  show (diagonal fun _ : R => X) (e i).2 (e i').2 (e i).1 (e i').1 = _
  by_cases h : (e i).2 = (e i').2
  · rw [h, diagonal_apply_eq, ite_eq_left rfl]
  · rw [diagonal_apply_ne _ h, ite_eq_right h, Matrix.zero_apply]

theorem regExtend_ΦB [Nonempty R] (e : I ≃ J × R) (Y : Matrix J J ℬ) (i i' : I) :
    (N.regExtend e).ΦB Y i i' = if (e i).2 = (e i').2 then Y (e i).1 (e i').1 else 0 := by
  show (diagonal fun _ : R => Y) (e i).2 (e i').2 (e i).1 (e i').1 = _
  by_cases h : (e i).2 = (e i').2
  · rw [h, diagonal_apply_eq, ite_eq_left rfl]
  · rw [diagonal_apply_ne _ h, ite_eq_right h, Matrix.zero_apply]

/-- **Exchanging the players** of the register model. -/
def regSwap : LocalIsometry (N.reg I).swap (N.swap.reg I) :=
  N.swapExpand (registerEPR I) (registerEPR I)

theorem regSwap_W_ψ : (N.regSwap (I := I)).W (N.reg I).swap.ψ = (N.swap.reg I).ψ :=
  N.swapExpand_W_ψ _ _ fun p => (registerEPR_swap p).symm

@[simp]
theorem regSwap_ΦA (Y : Matrix I I ℬ) : (N.regSwap (I := I)).ΦA Y = Y := rfl

@[simp]
theorem regSwap_ΦB (X : Matrix I I 𝒜) : (N.regSwap (I := I)).ΦB X = X := rfl

end MIPRE.BipartiteModel

end
