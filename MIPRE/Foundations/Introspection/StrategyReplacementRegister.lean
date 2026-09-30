/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.StrategyReplacement

@[expose] public section

/-! # Reassembly in the original EPR-register ordering

The added register belongs to Alice's auxiliary space. The shared state is
exactly the original EPR factor tensored with that extended auxiliary state.
These definitions construct the actual strategy on finite registers and
preserve all nonselected measurements under the displayed reassociation.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the replacement lives on the
one-sided extension `(Ξ.reg I).expandA t₀` of the register model, and the reassociation is the
local isometry `regExchange` onto `(Ξ.expandA t₀).reg I`, which exchanges the fresh ancilla with
the register on the first player's side (`BipartiteModel.exchange`).
-/

noncomputable section
namespace MIPRE.Introspection

open Finset Matrix Classical
set_option linter.unusedSectionVars false

/-- Pushing a POVM forward along the identity changes nothing. -/
theorem POVMIn.pushforward_id {X R : Type*} [Fintype X] [Ring R] [StarRing R] [Algebra ℂ R]
    [PartialOrder R] [StarOrderedRing R] (M : POVMIn X R) :
    M.pushforward (NonUnitalStarAlgHom.id ℂ R) rfl = M :=
  POVMIn.ext' fun _ => rfl

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [StarModule ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜]
  [StarOrderedRing 𝒜] [StarProper 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ] [StarModule ℂ ℬ]
  [StarProper ℬ]
  (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
variable {X Y A B C I T : Type*}
  [Fintype X] [DecidableEq X] [Fintype Y]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]
  [Fintype I] [DecidableEq I]
  [Fintype T] [DecidableEq T]

/-- The reassociation: the fresh ancilla of the register model, exchanged with the register, is
an ancilla of the auxiliary model. -/
abbrev regExchange (t₀ : T) : BipartiteModel.LocalIsometry ((Ξ.reg I).expandA t₀) ((Ξ.expandA t₀).reg I) :=
  Ξ.exchange t₀ (registerEPR I)

/-- Reassociation places the fresh fixed ancilla entirely in the auxiliary
state and leaves the EPR factor literally unchanged. -/
theorem regExchange_W_ψ (t₀ : T) :
    (regExchange (I := I) Ξ t₀).W ((Ξ.reg I).expandA t₀).ψ = ((Ξ.expandA t₀).reg I).ψ :=
  Ξ.exchange_W_ψ t₀ (registerEPR I)

/-- The new actual question-indexed family in the original register-first
ordering. -/
def registeredReplacement (MA : X → POVMIn A (Matrix I I 𝒜)) (q : X)
    (R : POVMIn A (Matrix T T (Matrix I I 𝒜))) : X → POVMIn A (Matrix I I (Matrix T T 𝒜)) :=
  fun x => (replaceExtended MA q R x).pushforward BipartiteModel.layerSwap BipartiteModel.layerSwap_one

@[simp] theorem registeredReplacement_at (MA : X → POVMIn A (Matrix I I 𝒜)) (q : X)
    (R : POVMIn A (Matrix T T (Matrix I I 𝒜))) :
    registeredReplacement MA q R q = R.pushforward BipartiteModel.layerSwap BipartiteModel.layerSwap_one := by
  simp only [registeredReplacement, replaceExtended_at]

theorem registeredReplacement_other (MA : X → POVMIn A (Matrix I I 𝒜)) (q x : X)
    (R : POVMIn A (Matrix T T (Matrix I I 𝒜))) (hx : x ≠ q) :
    registeredReplacement MA q R x =
      (POVMIn.ampA (T := T) (MA x)).pushforward BipartiteModel.layerSwap BipartiteModel.layerSwap_one := by
  simp only [registeredReplacement, replaceExtended_other MA q x R hx]

theorem registeredReplacement_isPVM (MA : X → POVMIn A (Matrix I I 𝒜)) (q : X)
    (R : POVMIn A (Matrix T T (Matrix I I 𝒜)))
    (hMA : ∀ x, IsPVMIn (MA x).op) (hR : IsPVMIn R.op) (x : X) :
    IsPVMIn (registeredReplacement MA q R x).op :=
  POVMIn.isPVMIn_pushforward _ _ (replaceExtended_isPVM MA q R hMA hR x)

/-- The registered replacement and its unreassociated version have exactly
the same value, for every game. -/
theorem registeredReplacement_value_eq (G : Game X Y A B) (t₀ : T)
    (MA : X → POVMIn A (Matrix I I 𝒜)) (MB : Y → POVMIn B (Matrix I I ℬ)) (q : X)
    (R : POVMIn A (Matrix T T (Matrix I I 𝒜))) :
    ((Ξ.expandA t₀).reg I).povmValue G (registeredReplacement MA q R) MB =
      ((Ξ.reg I).expandA t₀).povmValue G (replaceExtended MA q R) MB := by
  have h := BipartiteModel.LocalIsometry.povmValue_pushforward (regExchange_W_ψ Ξ t₀)
    BipartiteModel.layerSwap_one rfl G (replaceExtended MA q R) MB
  refine Eq.trans ?_ h
  congr 1

variable [Nonempty I]

/-- The fixed auxiliary extension is normalized, hence gives the actual
normalized EPR-plus-auxiliary state of the next strategy. -/
theorem norm_reg_expandA_ψ (hΞ : ‖Ξ.ψ‖ = 1) (t₀ : T) : ‖((Ξ.expandA t₀).reg I).ψ‖ = 1 := by
  rw [BipartiteModel.norm_reg_ψ, BipartiteModel.norm_expandA_ψ, hΞ]

/-- A concrete legal strategy on the new register state. -/
def registeredReplacementStrategy (G : Game X Y A B) (hΞ : ‖Ξ.ψ‖ = 1) (t₀ : T)
    (MA : X → POVMIn A (Matrix I I 𝒜)) (MB : Y → POVMIn B (Matrix I I ℬ)) (q : X)
    (R : POVMIn A (Matrix T T (Matrix I I 𝒜)))
    (hMA : ∀ x, IsPVMIn (MA x).op) (hMB : ∀ y, IsPVMIn (MB y).op) (hR : IsPVMIn R.op) :
    ((Ξ.expandA t₀).reg I).ProjStrat G where
  PA := registeredReplacement MA q R
  PB := MB
  projA := registeredReplacement_isPVM MA q R hMA hR
  projB := hMB
  ψ_unit := norm_reg_expandA_ψ Ξ hΞ t₀

theorem registeredReplacementStrategy_value (G : Game X Y A B) (hΞ : ‖Ξ.ψ‖ = 1) (t₀ : T)
    (MA : X → POVMIn A (Matrix I I 𝒜)) (MB : Y → POVMIn B (Matrix I I ℬ)) (q : X)
    (R : POVMIn A (Matrix T T (Matrix I I 𝒜)))
    (hMA : ∀ x, IsPVMIn (MA x).op) (hMB : ∀ y, IsPVMIn (MB y).op) (hR : IsPVMIn R.op) :
    (registeredReplacementStrategy Ξ G hΞ t₀ MA MB q R hMA hMB hR).value =
      ((Ξ.reg I).expandA t₀).povmValue G (replaceExtended MA q R) MB :=
  registeredReplacement_value_eq Ξ G t₀ MA MB q R

/-- Quantitative value preservation of the actual registered strategy,
including its finite-dimensional packaging. -/
theorem registeredReplacementStrategy_value_loss (G : Game X Y A B) (hΞ : ‖Ξ.ψ‖ = 1) (t₀ : T)
    (MA : X → POVMIn A (Matrix I I 𝒜)) (MB : Y → POVMIn B (Matrix I I ℬ)) (q : X)
    (M : POVMIn C (Matrix I I 𝒜)) (R : POVMIn C (Matrix T T (Matrix I I 𝒜))) (f : C → A)
    (hMA : ∀ x, IsPVMIn (MA x).op) (hMB : ∀ y, IsPVMIn (MB y).op)
    (hselected : MA q = M.map f) (hM : IsPVMIn M.op) (hR : IsPVMIn R.op) {δ : ℝ}
    (hd : ∑ c, ((Ξ.reg I).expandA t₀).stateSqNorm ((diagonal fun _ => M.op c) - R.op c) ≤ δ) :
    |(Ξ.reg I).povmValue G MA MB -
      (registeredReplacementStrategy Ξ G hΞ t₀ MA MB q (R.map f) hMA hMB
        (POVMIn.isPVMIn_map hR f)).value| ≤ 2*Real.sqrt δ := by
  rw [registeredReplacementStrategy_value]
  exact replaceExtended_value (Ξ.reg I) G (by rw [BipartiteModel.norm_reg_ψ, hΞ]) t₀ MA MB q
    M R f hselected hM hR hMB hd

end MIPRE.Introspection
end

end
