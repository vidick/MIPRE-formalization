/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.StrategyReplacementRegister

@[expose] public section

/-! # Conditional Naimark projectors in adaptive register coordinates

A residual dilation is pulled back through the actual coordinate split.
Compression and reassociation are exact, and the next linear-map readout is
retained as an explicit tensor factor of the new projective measurement.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the coordinate split is the
local isometry `regSplit e` extended along the one-sided ancilla (`LocalIsometry.expandA`), the
compression is the entry at the fixed ancilla state, and the reassociation is `regExchange`.
-/

noncomputable section
namespace MIPRE

open Finset Matrix Classical
set_option linter.unusedSectionVars false

/-! ## Local isometries extend along a one-sided ancilla -/

namespace BipartiteModel

variable {𝒞 𝒜 ℬ 𝒞' 𝒜' ℬ' : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [Ring 𝒞'] [StarRing 𝒞'] [Algebra ℂ 𝒞']
  [Ring 𝒜'] [StarRing 𝒜'] [Algebra ℂ 𝒜'] [Ring ℬ'] [StarRing ℬ'] [Algebra ℂ ℬ']
  {M : BipartiteModel 𝒞 𝒜 ℬ} {M' : BipartiteModel 𝒞' 𝒜' ℬ'}
  {T : Type*} [Fintype T] [DecidableEq T]

/-- The isometry of the one-sided extensions, componentwise. -/
def LocalIsometry.expandAW (Φ : LocalIsometry M M') (t₀ : T) :
    (M.expandA t₀).H →ₗᵢ[ℂ] (M'.expandA t₀).H :=
  (M'.amplA t₀).symm.toLinearIsometry.comp ((amplMap Φ.W).comp (M.amplA t₀).toLinearIsometry)

theorem LocalIsometry.amplA_expandAW (Φ : LocalIsometry M M') (t₀ : T)
    (v : (M.expandA t₀).H) (t : T) : M'.amplA t₀ (Φ.expandAW t₀ v) t = Φ.W (M.amplA t₀ v t) :=
  rfl

/-- **A local isometry extends along a one-sided ancilla**: the first player's block matrices are
mapped entrywise, the second player's operators as before. -/
def LocalIsometry.expandA (Φ : LocalIsometry M M') (t₀ : T) :
    LocalIsometry (M.expandA t₀) (M'.expandA t₀) where
  W := Φ.expandAW t₀
  ΦA := mapMatrixHom Φ.ΦA
  ΦB := Φ.ΦB
  intertwineA X v := by
    refine M'.expandA_ext t₀ fun t => ?_
    rw [expandA_π_πA_apply, Φ.amplA_expandAW, expandA_π_πA_apply, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [mapMatrixHom_apply, map_apply, Φ.amplA_expandAW, Φ.intertwineA]
  intertwineB b v := by
    refine M'.expandA_ext t₀ fun t => ?_
    rw [expandA_π_πB_apply, Φ.amplA_expandAW, Φ.amplA_expandAW, expandA_π_πB_apply,
      Φ.intertwineB]

@[simp]
theorem LocalIsometry.expandA_ΦA (Φ : LocalIsometry M M') (t₀ : T) (X : Matrix T T 𝒜) :
    (Φ.expandA t₀).ΦA X = X.map Φ.ΦA := rfl

@[simp]
theorem LocalIsometry.expandA_ΦB (Φ : LocalIsometry M M') (t₀ : T) (b : ℬ) :
    (Φ.expandA t₀).ΦB b = Φ.ΦB b := rfl

/-- The extension carries the state to the state when the local isometry does. -/
theorem LocalIsometry.expandA_W_ψ {Φ : LocalIsometry M M'} (h : Φ.W M.ψ = M'.ψ) (t₀ : T) :
    (Φ.expandA t₀).W (M.expandA t₀).ψ = (M'.expandA t₀).ψ := by
  refine M'.expandA_ext t₀ fun t => ?_
  show Φ.W (M.amplA t₀ (M.expandA t₀).ψ t) = M'.amplA t₀ (M'.expandA t₀).ψ t
  rw [expandA_ψ_apply, expandA_ψ_apply]
  split_ifs
  · exact h
  · exact map_zero _

end BipartiteModel

namespace Introspection

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [StarModule ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]
variable {V I R Y A T : Type*}
  [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
  [Fintype R] [DecidableEq R] [Fintype Y] [DecidableEq Y]
  [Fintype A] [DecidableEq A] [Fintype T] [DecidableEq T]

theorem map_regSplitHom_one (e : V ≃ I × R) :
    (1 : Matrix T T (Matrix I I (Matrix R R 𝒜))).map (regSplitHom e) = 1 :=
  Matrix.map_one _ (map_zero _) (regSplitHom_one e)

/-- The conditional joint PVM on the original remaining register plus one
fixed ancilla. -/
def transportedConditionalDilation (e : V ≃ I × R) (Z : Y → Matrix I I ℂ)
    (P : Y → A → Matrix T T (Matrix R R 𝒜)) (p : Y × A) : Matrix T T (Matrix V V 𝒜) :=
  (conditionalDilationOp Z P p).map (regSplitHom e)

theorem transportedConditionalDilation_isPVM (e : V ≃ I × R)
    (Z : Y → Matrix I I ℂ) (hZ : IsPVM Z)
    (P : Y → A → Matrix T T (Matrix R R 𝒜))
    (hP : ∀ y, IsPVMIn (P y)) : IsPVMIn (transportedConditionalDilation e Z P) := by
  have h1 : BipartiteModel.mapMatrixHom (regSplitHom e)
      (1 : Matrix T T (Matrix I I (Matrix R R 𝒜))) = 1 := map_regSplitHom_one e
  exact (conditionalDilationOp_isPVM Z hZ P hP).pushforward h1

theorem transportedConditionalDilation_compress (e : V ≃ I × R) (t₀ : T)
    (Z : Y → Matrix I I ℂ) (P : Y → A → Matrix T T (Matrix R R 𝒜)) (Q : Y → A → Matrix R R 𝒜)
    (hk : ∀ y a, P y a t₀ t₀ = Q y a) (p : Y × A) :
    transportedConditionalDilation e Z P p t₀ t₀ = regSplitHom e (smulKron (Q p.1 p.2) (Z p.1)) := by
  rw [transportedConditionalDilation, map_apply, conditionalDilationOp_compress t₀ Z P Q hk]

/-- The same PVM with the fresh ancilla absorbed into the auxiliary register. -/
def reassociatedConditionalDilation (e : V ≃ I × R) (Z : Y → Matrix I I ℂ)
    (P : Y → A → Matrix T T (Matrix R R 𝒜)) (p : Y × A) : Matrix V V (Matrix T T 𝒜) :=
  BipartiteModel.layerSwap (transportedConditionalDilation e Z P p)

theorem reassociatedConditionalDilation_isPVM (e : V ≃ I × R)
    (Z : Y → Matrix I I ℂ) (hZ : IsPVM Z)
    (P : Y → A → Matrix T T (Matrix R R 𝒜))
    (hP : ∀ y, IsPVMIn (P y)) : IsPVMIn (reassociatedConditionalDilation e Z P) :=
  (transportedConditionalDilation_isPVM e Z hZ P hP).pushforward BipartiteModel.layerSwap_one

/-- The new readout remains an exact tensor factor. The second factor is
the dilated residual operator on precisely the remaining coordinates. -/
theorem reassociatedConditionalDilation_factor (e : V ≃ I × R)
    (Z : Y → Matrix I I ℂ)
    (P : Y → A → Matrix T T (Matrix R R 𝒜)) (p : Y × A) :
    reassociatedConditionalDilation e Z P p =
      regSplitHom e (smulKron (BipartiteModel.layerSwap (P p.1 p.2)) (Z p.1)) := by
  ext v v' t t'
  rfl

variable [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜] [PartialOrder ℬ]
  [StarOrderedRing ℬ] [StarModule ℂ ℬ] [StarProper ℬ] (Ξ : BipartiteModel 𝒞 𝒜 ℬ)

/-- The coordinate split transports squared errors exactly along the one-sided ancilla. -/
theorem stateSqNorm_transported (e : V ≃ I × R) (t₀ : T)
    (X : Matrix T T (Matrix I I (Matrix R R 𝒜))) :
    ((Ξ.reg V).expandA t₀).stateSqNorm (X.map (regSplitHom e)) =
      (((Ξ.reg R).reg I).expandA t₀).stateSqNorm X :=
  BipartiteModel.LocalIsometry.stateSqNorm_of_W_ψ
    (BipartiteModel.LocalIsometry.expandA_W_ψ (Ξ.regSplit_W_ψ e) t₀) X

/-- Reassociation transports the squared error exactly to the new register
state, with no state replacement or dimension factor. -/
theorem stateSqNorm_reassociated_extVecA (t₀ : T) (M : Matrix T T (Matrix V V 𝒜)) :
    ((Ξ.expandA t₀).reg V).stateSqNorm (BipartiteModel.layerSwap M) =
      ((Ξ.reg V).expandA t₀).stateSqNorm M :=
  BipartiteModel.LocalIsometry.stateSqNorm_of_W_ψ (regExchange_W_ψ Ξ t₀) M

end Introspection

end MIPRE
end

end
