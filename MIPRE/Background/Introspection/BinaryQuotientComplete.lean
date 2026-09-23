/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.ExplicitStrategy
import MIPRE.Foundations.Introspection.TypedQuotientGame
import MIPRE.Foundations.Introspection.HonestPrefixSupport
import MIPRE.Foundations.Introspection.HonestIntrospectSupport

/-! # Honest binary completeness with the supports required by executable guards -/

noncomputable section
namespace MIPRE.Introspection.BinaryComplete
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] {m t d ℓ : ℕ} [NeZero m]
  (L : Bool → CL.CLFun (ZMod 2) (Coord m t) ℓ)
  (D : Seed m t → Seed m t → A → A → Bool)
  (R : SyncStrategy (Honest.sourceGame L D).doubled)
  (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (hL : ∀ w, (L w).SupportedOn univ)

theorem strategy_nonzero_prefixGuard (q : Bool × Question m t ℓ)
    (a : Answer F A m t d) (ha : (strategy L D R hm b hL).P.M q a ≠ 0) :
    PrefixGuard.holds L q.2.1 a := by
  have hop : op L D R hm b hL q.2 a ≠ 0 := by
    intro hz
    apply ha
    change registerOp _ (op L D R hm b hL q.2 a) = 0
    rw [hz]
    rfl
  rcases q with ⟨side,q,payload⟩
  cases q with
  | inl p => cases a <;> trivial
  | inr p =>
    apply Honest.auxOp_nonzero_prefixGuard L D R hL p a
    intro hz
    apply hop
    change aOp (HB := Fin 2) (Honest.auxOp L D R hL p a) = 0
    rw [hz, aOp_zero]

theorem strategy_nonzero_introspect (side w : Bool)
    (payload : Fin ((3*m+3)*t) → ZMod 2) (y : Seed m t) (a : A)
    (ha : (strategy (F := F) (d := d) L D R hm b hL).P.M
      (side, .inr (.introspect,w), payload) (.pair y a) ≠ 0) :
    ∃ x, (L w).eval x = y := by
  apply Honest.auxOp_introspect_output_attained (PA := QLD.Answer F m d) L D R hL w y a
  intro hz
  apply ha
  change registerOp _ (aOp (HB := Fin 2)
    (Honest.auxOp L D R hL (.introspect,w) (.pair y a : Answer F A m t d))) = 0
  rw [hz, aOp_zero]
  rfl

variable (χ : F → Fin m) (π : F ≃ F)

abbrev explicitHonest : SyncStrategy
    (ExplicitGame.game hm χ π b L (project (d := d) b) D).doubled :=
  ExplicitGame.pccToExplicit hm χ π b L (project b) D (strategy L D R hm b hL)

theorem explicitHonest_prefixGuard (q : Bool × Question m t ℓ)
    (a : Answer F A m t d) (ha : (explicitHonest L D R hm b hL χ π).P.M q a ≠ 0) :
    PrefixGuard.holds L q.2.1 a :=
  strategy_nonzero_prefixGuard L D R hm b hL
    ((Equiv.refl Bool).prodCongr (ExplicitGame.questionEquiv π b) q) a ha

theorem explicitHonest_introspect (side w : Bool)
    (payload : Fin ((3*m+3)*t) → ZMod 2) (y : Seed m t) (a : A)
    (ha : (explicitHonest (d := d) L D R hm b hL χ π).P.M
      (side, .inr (.introspect,w), payload) (.pair y a) ≠ 0) :
    ∃ x, (L w).eval x = y :=
  strategy_nonzero_introspect L D R hm b hL side w payload y a ha

abbrev explicitQuotientGame := AuxiliaryQuotient.game QLD.adj (.pauli .X) (.pauli .Z)
  (QLD.PauliCL.ExplicitSeed.binaryPresentation χ b) L (project (d := d) b) D
  (ExplicitGame.pauliCheck hm π b)

abbrev quotientHonest : SyncStrategy (explicitQuotientGame (d := d) L D hm b χ π).doubled :=
  AuxiliaryQuotient.copiedPCC QLD.adj (.pauli .X) (.pauli .Z)
    (QLD.PauliCL.ExplicitSeed.binaryPresentation χ b) L (project (d := d) b) D
    (ExplicitGame.pauliCheck hm π b) (explicitHonest L D R hm b hL χ π)

theorem quotientHonest_prefixGuard (q : Bool × Question m t ℓ)
    (a : Answer F A m t d) (ha : (quotientHonest L D R hm b hL χ π).P.M q a ≠ 0) :
    PrefixGuard.holds L q.2.1 a := explicitHonest_prefixGuard L D R hm b hL χ π q a ha

theorem quotientHonest_introspect (side w : Bool)
    (payload : Fin ((3*m+3)*t) → ZMod 2) (y : Seed m t) (a : A)
    (ha : (quotientHonest (d := d) L D R hm b hL χ π).P.M
      (side, .inr (.introspect,w), payload) (.pair y a) ≠ 0) :
    ∃ x, (L w).eval x = y := explicitHonest_introspect L D R hm b hL χ π side w payload y a ha

theorem quotientHonest_isPCC (hb : LowDegree.IsSelfDualBasis b)
    (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s) (hR : R.IsPCC) :
    (quotientHonest (d := d) L D R hm b hL χ π).IsPCC :=
  AuxiliaryQuotient.copiedPCC_isPCC _ _ _ _ _ _ _ _ _
    (ExplicitGame.pccToExplicit_isPCC hm χ π hχ b L (project b) D _
      (strategy_isPCC L D R hm b hb hL hR))

theorem quotientHonest_value (hb : LowDegree.IsSelfDualBasis b)
    (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s) (hd : 1 ≤ d)
    (hR : R.IsPCC) (hv : R.value = 1) :
    (quotientHonest (d := d) L D R hm b hL χ π).value = 1 := by
  apply AuxiliaryQuotient.copiedPCC_value_eq_one _ _ _ _ _ _ _ _ hL
  exact (ExplicitGame.pccToExplicit_value hm χ π hχ b L (project b) D _).trans
    (strategy_value L D R hm b hb hd hL hR hv)

theorem quotientHonest_dimension :
    (quotientHonest (d := d) L D R hm b hL χ π).d =
      2 * Fintype.card (Seed m t) * R.d := by
  change Fintype.card (Space L D R) = _
  simp only [Space, Fintype.card_prod, Fintype.card_fin]
  ring

end MIPRE.Introspection.BinaryComplete
end
