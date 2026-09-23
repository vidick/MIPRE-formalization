/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.HonestCore
import MIPRE.Foundations.CL.Downsize
import MIPRE.Foundations.GameTransport

/-! # Source-game transport along a concrete coordinate bijection -/

noncomputable section
namespace MIPRE.Introspection.SourceReindex
open Finset CL Classical
set_option linter.unusedSectionVars false
variable {F ι κ A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype A] [DecidableEq A] {ℓ : ℕ}
  (e : ι ≃ κ) (L : Bool → CLFun F ι ℓ)
  (D : (ι → F) → (ι → F) → A → A → Bool)

def family (w : Bool) : CLFun F κ ℓ := (L w).reindex e
def decider (x y : κ → F) : A → A → Bool :=
  D ((reindexEquiv e).symm x) ((reindexEquiv e).symm y)

theorem exactlyOn (hL : ∀ w, (L w).ExactlyOn univ) (w : Bool) :
    (family e L w).ExactlyOn univ := by
  simpa only [family, Finset.map_univ_equiv] using (hL w).reindex e

theorem game_mu (x y : κ → F) :
    (Honest.sourceGame (family e L) (decider e D)).μ x y =
      (Honest.sourceGame L D).μ ((reindexEquiv e).symm x) ((reindexEquiv e).symm y) := by
  change SampledGame.dist _ _ _ _ = SampledGame.dist _ _ _ _
  unfold SampledGame.dist
  rw [← Fintype.card_congr (reindexEquiv (F := F) e).toEquiv]
  congr 1
  refine Fintype.sum_equiv (reindexEquiv e).symm.toEquiv _ _ fun z => ?_
  simp only [family, CLFun.eval_reindex', Prod.mk.injEq, LinearEquiv.coe_toEquiv]
  simp only [LinearEquiv.eq_symm_apply]

theorem quantumValue_eq :
    quantumValue (Honest.sourceGame (family e L) (decider e D)) =
      quantumValue (Honest.sourceGame L D) :=
  quantumValue_eq_of_equiv _ _ (reindexEquiv e).symm.toEquiv (reindexEquiv e).symm.toEquiv
    (.refl _) (.refl _) (game_mu e L D) (fun _ _ _ _ => rfl)

abbrev strategy (R : SyncStrategy (Honest.sourceGame L D).doubled) :
    SyncStrategy (Honest.sourceGame (family e L) (decider e D)).doubled :=
  R.relabel _ ((Equiv.refl Bool).prodCongr (reindexEquiv e).symm.toEquiv) (.refl _)

theorem strategy_isPCC (R : SyncStrategy (Honest.sourceGame L D).doubled) (hR : R.IsPCC) :
    (strategy e L D R).IsPCC := by
  apply SyncStrategy.isPCC_relabel hR
  intro x y
  simp only [Game.doubled_μ, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply, game_mu,
    LinearEquiv.coe_toEquiv]

theorem strategy_value (R : SyncStrategy (Honest.sourceGame L D).doubled) :
    (strategy e L D R).value = R.value := by
  apply R.value_relabel _ ((Equiv.refl Bool).prodCongr (reindexEquiv e).symm.toEquiv) (.refl _)
  · intro x y
    simp only [Game.doubled_μ, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply, game_mu,
      LinearEquiv.coe_toEquiv]
  · intro x y a b
    rfl

@[simp] theorem strategy_dimension (R : SyncStrategy (Honest.sourceGame L D).doubled) :
    (strategy e L D R).d = R.d := rfl

end MIPRE.Introspection.SourceReindex
end
