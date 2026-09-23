/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.PrefixGuard
import MIPRE.Foundations.GameTransport
import MIPRE.Foundations.GameDouble

/-! # Adding honest prefix guards preserves completeness

Changing a predicate only on zero measurement effects preserves its value.
Applying this observation to the local prefix guards keeps the honest state,
dimension and PCC property, while guard rejection can only reduce arbitrary
strategies' success.
-/

noncomputable section
namespace MIPRE
open Classical
set_option linter.unusedSectionVars false

namespace SyncStrategy
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
  {G : SynchronousGame X A}

/-- Predicate agreement is needed only on nonzero measurement effects. -/
theorem value_copy_of_nonzero (S : SyncStrategy G) (G' : SynchronousGame X A)
    (hμ : ∀ x y, G'.μ x y = G.μ x y)
    (hD : ∀ x y a b, S.P.M x a ≠ 0 → S.P.M y b ≠ 0 →
      G'.D x y a b = G.D x y a b) : (S.copy G').value = S.value := by
  rw [value_eq, value_eq]
  change (∑ x, ∑ y, ∑ a, ∑ b, G'.μ x y * (if G'.D x y a b then 1 else 0) *
      ((S.P.M x a * S.P.M y b).trace.re / (S.d : ℝ))) =
    ∑ x, ∑ y, ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) *
      ((S.P.M x a * S.P.M y b).trace.re / (S.d : ℝ))
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hμ]
  by_cases hx : S.P.M x a = 0
  · simp [hx]
  by_cases hy : S.P.M y b = 0
  · simp [hy]
  rw [hD x y a b hx hy]

end SyncStrategy

namespace Introspection.PrefixGuard
variable {F ι A PA P Q : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]
  [Fintype PA] [DecidableEq PA] [Fintype Q] {ℓ : ℕ}
  (L : Bool → CL.CLFun F ι ℓ) (type : Q → QuestionType P ℓ)
  (G : Game Q Q (ParsedAnswer (ι → F) A PA) (ParsedAnswer (ι → F) A PA))

/-- Retain the question law and add both local prefix checks. Raw question
payloads remain available to the original predicate. -/
def game : Game Q Q (ParsedAnswer (ι → F) A PA) (ParsedAnswer (ι → F) A PA) :=
  { G with D := fun q r a b => check L (type q) a && check L (type r) b && G.D q r a b }

@[simp] theorem game_mu (q r : Q) : (game L type G).μ q r = G.μ q r := rfl

theorem game_accepts_iff (q r : Q) (a b : ParsedAnswer (ι → F) A PA) :
    (game L type G).D q r a b = true ↔
      holds L (type q) a ∧ holds L (type r) b ∧ G.D q r a b = true := by
  simp [game, and_assoc]

/-- Guarding cannot increase the game's quantum value. -/
theorem quantumValue_le : quantumValue (game L type G) ≤ quantumValue G := by
  apply quantumValue_mono (game L type G) G (fun _ _ => rfl)
  intro q r a b h
  exact ((game_accepts_iff L type G q r a b).mp h).2.2

/-- Any strategy whose nonzero effects satisfy the guard retains its exact
value, without requiring perfection as an intermediate premise. -/
theorem copied_value (S : SyncStrategy G.doubled)
    (hS : ∀ q a, S.P.M q a ≠ 0 → holds L (type q.2) a) :
    (S.copy (game L type G).doubled).value = S.value := by
  apply S.value_copy_of_nonzero (game L type G).doubled (fun _ _ => rfl)
  intro q r a b ha hb
  have hqa := hS q a ha
  have hrb := hS r b hb
  simp [Game.doubled_D, game, check, hqa, hrb]

theorem copied_value_eq_one (S : SyncStrategy G.doubled)
    (hS : ∀ q a, S.P.M q a ≠ 0 → holds L (type q.2) a) (hv : S.value = 1) :
    (S.copy (game L type G).doubled).value = 1 :=
  (copied_value L type G S hS).trans hv

theorem copied_isPCC (S : SyncStrategy G.doubled) (hS : S.IsPCC) :
    (S.copy (game L type G).doubled).IsPCC :=
  SyncStrategy.isPCC_copy hS _ (fun _ _ => rfl)

@[simp] theorem copied_dimension (S : SyncStrategy G.doubled) :
    (S.copy (game L type G).doubled).d = S.d := rfl

end Introspection.PrefixGuard
end MIPRE
