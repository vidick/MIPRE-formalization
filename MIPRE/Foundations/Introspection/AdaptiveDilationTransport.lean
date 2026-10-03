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

variable [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜] [PartialOrder ℬ]
  [StarOrderedRing ℬ] [StarModule ℂ ℬ] [StarProper ℬ] (Ξ : BipartiteModel 𝒞 𝒜 ℬ)

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
