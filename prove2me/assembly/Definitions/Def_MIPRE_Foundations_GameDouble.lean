/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/GameDouble.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport

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

end TensorProductStrategy

/-! ## Synchronous strategies through the doubling -/

namespace SyncStrategy

variable {G : SynchronousGame X A}

end SyncStrategy

end MIPRE
