/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.GameTransport

/-!
# The doubled question set

A game description denotes a *synchronous* game by construction: `GameData.game` rejects
unequal answers at equal questions whatever its acceptance table holds, while a verifier's
game does no such thing. So a description can match `𝒱_n` only where `𝒱_n` happens to be
synchronous (`MIPRE.Verifier.isSynchronousAt_of_game_matches`), and membership in the class
`B` of the halting reduction does not ask for synchronicity — which is exactly the seam
blueprint `lem:halting-semidecider` records, the semidecider needing the tabulation's value
to equal `val*` at every bounded string.

`Game.doubled` closes it, and does so without weakening anything. The doubled game plays on
`Bool × X`: Alice is asked a question tagged `false`, Bob one tagged `true`, and every other
pair — the diagonal included — carries no weight and is rejected outright. Two consequences,
and both are what make this cheap:

* it is a `SynchronousGame` for *any* game, its `synchronous` field holding for free, since
  `p = q` forces equal tags and so fails the tag test. The description's veto is no longer a
  constraint on the verifier; it is implied by the distribution.
* because the decision predicate also rejects off the tag block, a description matching the
  doubled game matches it *totally*, on every question pair including the diagonal. So
  `quantumValue_eq_of_equiv` and `SyncStrategy.isPCC_relabel` apply unchanged, and no
  support-restricted version of either is needed.

The value is untouched in both senses that the halting reduction uses:

* `quantumValue_doubled`, by a two-sided `iSup` argument on `TensorProductStrategy.double`
  and `undouble` — a strategy for the doubled game restricts to Alice's `(false, ·)` and
  Bob's `(true, ·)` measurements, and one for the original ignores the tag;
* `SyncStrategy.double` with `value_double` and `isPCC_double`, which is the direction
  completeness needs. The doubling adds no commutation obligation: `IsPCC` is quantified
  over the support of `μ`, and the doubled support maps into the original one.

`Game.sum_doubled` is the one computation, strategy-agnostic so that it serves both values.
-/

namespace MIPRE

open Matrix Kronecker
open scoped ComplexOrder

variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]

namespace Game

/-- **The doubled game.** Alice's questions carry the tag `false` and Bob's the tag `true`;
every other pair carries no weight and is rejected. Synchronous for free. -/
def doubled (G : Game X X A A) : SynchronousGame (Bool × X) A where
  μ p q := if p.1 = false ∧ q.1 = true then G.μ p.2 q.2 else 0
  μ_nonneg p q := by split_ifs; exacts [G.μ_nonneg _ _, le_rfl]
  μ_sum_one := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    simp [G.μ_sum_one]
  D p q a b := if p.1 = false ∧ q.1 = true then G.D p.2 q.2 a b else false
  synchronous p a b _ := by
    rcases p with ⟨t, x⟩
    cases t <;> simp

@[simp] theorem doubled_μ (G : Game X X A A) (p q : Bool × X) :
    G.doubled.μ p q = if p.1 = false ∧ q.1 = true then G.μ p.2 q.2 else 0 := rfl

@[simp] theorem doubled_D (G : Game X X A A) (p q : Bool × X) (a b : A) :
    G.doubled.D p q a b = if p.1 = false ∧ q.1 = true then G.D p.2 q.2 a b else false := rfl

/-- The one computation the doubling needs, in a form independent of what kind of strategy is
being summed: the four-fold sum over the doubled alphabets collapses to the original one, the
three blocks other than `(false, ·), (true, ·)` contributing zero. -/
theorem sum_doubled (G : Game X X A A) (f : (Bool × X) → (Bool × X) → A → A → ℝ) :
    (∑ p, ∑ q, ∑ a, ∑ b,
        G.doubled.μ p q * (if G.doubled.D p q a b then 1 else 0) * f p q a b)
      = ∑ x, ∑ y, ∑ a, ∑ b,
          G.μ x y * (if G.D x y a b then 1 else 0) * f (false, x) (true, y) a b := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, doubled_μ, doubled_D]
  simp

end Game

/-! ## Tensor-product strategies through the doubling -/

namespace TensorProductStrategy

/-- A strategy for the doubled game, read on the original: Alice keeps her measurements at
`(false, ·)`, Bob his at `(true, ·)`. -/
def undouble {G : Game X X A A} (S : TensorProductStrategy G.doubled.toGame) :
    TensorProductStrategy G :=
  S.relabel G (fun x => (false, x)) (fun y => (true, y)) (Equiv.refl A) (Equiv.refl A)

/-- A strategy for the original game, read on the doubled one: both players ignore the tag. -/
def double {G : Game X X A A} (S : TensorProductStrategy G) :
    TensorProductStrategy G.doubled.toGame :=
  S.relabel G.doubled.toGame (fun p => p.2) (fun q => q.2) (Equiv.refl A) (Equiv.refl A)

theorem value_undouble {G : Game X X A A} (S : TensorProductStrategy G.doubled.toGame) :
    S.undouble.value = S.value := by
  rw [show S.value = ∑ p, ∑ q, ∑ a, ∑ b, G.doubled.μ p q *
      (if G.doubled.D p q a b then 1 else 0) *
      (star S.ψ ⬝ᵥ ((S.PA.M p a ⊗ₖ S.PB.M q b) *ᵥ S.ψ)).re from rfl,
    Game.sum_doubled]
  rfl

theorem value_double {G : Game X X A A} (S : TensorProductStrategy G) :
    S.double.value = S.value := by
  rw [show S.double.value = ∑ p, ∑ q, ∑ a, ∑ b, G.doubled.μ p q *
      (if G.doubled.D p q a b then 1 else 0) *
      (star S.ψ ⬝ᵥ ((S.PA.M p.2 a ⊗ₖ S.PB.M q.2 b) *ᵥ S.ψ)).re from rfl,
    Game.sum_doubled]
  rfl

end TensorProductStrategy

/-- **The doubling preserves the quantum value.** Each direction is one strategy transported
and one `le_ciSup`; `TensorProductStrategy` carries no field mentioning the game, so `relabel`
is a bijection of the two index types of the supremum. -/
theorem quantumValue_doubled (G : Game X X A A) :
    quantumValue G.doubled.toGame = quantumValue G := by
  apply le_antisymm
  · refine Real.iSup_le (fun S => ?_) (quantumValue_nonneg _)
    rw [← S.value_undouble]
    exact le_ciSup (TensorProductStrategy.bddAbove_range_value G) S.undouble
  · refine Real.iSup_le (fun S => ?_) (quantumValue_nonneg _)
    rw [← S.value_double]
    exact le_ciSup (TensorProductStrategy.bddAbove_range_value G.doubled.toGame) S.double

/-! ## Synchronous strategies through the doubling -/

namespace SyncStrategy

variable {G : SynchronousGame X A}

/-- A synchronous strategy played on the doubled game: the same measurement at `(b, x)` for
both tags. -/
def double (S : SyncStrategy G) : SyncStrategy G.toGame.doubled :=
  S.relabel G.toGame.doubled (fun p => p.2) (Equiv.refl A)

theorem value_double (S : SyncStrategy G) : S.double.value = S.value := by
  rw [value_eq, value_eq,
    show (∑ p, ∑ q, ∑ a, ∑ b, G.toGame.doubled.μ p q *
        (if G.toGame.doubled.D p q a b then 1 else 0) *
        ((S.double.P.M p a * S.double.P.M q b).trace.re / (S.double.d : ℝ)))
      = ∑ p, ∑ q, ∑ a, ∑ b, G.toGame.doubled.μ p q *
        (if G.toGame.doubled.D p q a b then 1 else 0) *
        ((S.P.M p.2 a * S.P.M q.2 b).trace.re / (S.d : ℝ)) from rfl,
    Game.sum_doubled]
  rfl

/-- **The doubled strategy is PCC.** The worry is the right one and the answer is no: a
question pair of the doubled game carries weight only when it is `((false, x), (true, y))`
with `(x, y)` carrying weight in the original, so the doubled support maps *into* the original
one and no commutation obligation is added. -/
theorem isPCC_double {S : SyncStrategy G} (hS : S.IsPCC) : S.double.IsPCC := by
  intro p q hpq a b
  refine hS p.2 q.2 ?_ a b
  rw [Game.doubled_μ] at hpq
  split_ifs at hpq with h
  · exact hpq
  · exact absurd hpq (lt_irrefl 0)

/-- The support-restricted `SyncStrategy.isPCC_relabel`: the commutation condition is
quantified over the support of `μ`, so a relabeling that only shrinks the support transports
it. `isPCC_relabel` is the case of a total `hμ`. Not used by the doubling — whose relabelings
are total — and kept because it is the general statement. -/
theorem isPCC_relabel_of_support {X' A' : Type*} [Fintype X'] [Fintype A'] [DecidableEq A']
    {S : SyncStrategy G} (hS : S.IsPCC) (G' : SynchronousGame X' A') (eX : X' → X)
    (eA : A' ≃ A) (hμ : ∀ x' y', 0 < G'.μ x' y' → 0 < G.μ (eX x') (eX y')) :
    (S.relabel G' eX eA).IsPCC :=
  fun x' y' hxy _ _ => hS _ _ (hμ x' y' hxy) _ _

end SyncStrategy

/-- **The doubling preserves the synchronous value from below**, which is the direction
completeness needs: a value-`1` PCC strategy of `G` is one of `G.toGame.doubled`. -/
theorem exists_perfectPCC_doubled {G : SynchronousGame X A} {S : SyncStrategy G}
    (hS : S.IsPCC) (hval : S.value = 1) :
    ∃ S' : SyncStrategy G.toGame.doubled, S'.IsPCC ∧ S'.value = 1 :=
  ⟨S.double, SyncStrategy.isPCC_double hS, by rw [SyncStrategy.value_double, hval]⟩

end MIPRE
