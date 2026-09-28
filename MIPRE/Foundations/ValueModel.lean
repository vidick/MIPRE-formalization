/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import Mathlib.Computability.Halting
import MIPRE.Foundations.CommutingTransport
import MIPRE.Foundations.GameDescription

/-!
# Value models: one interface for the tensor-product and the commuting-operator value

The halting reduction of `MIP* = RE` and the one of `MIP^co = coRE` (`planning/mipco-track.md`)
are the same argument in two values: `val*` (`MIPRE.quantumValue`) and the bipartite
commuting-operator value `ω_co` (`MIPRE.commutingOperatorValue`). What the argument uses of
the value is a short list — it is at most `1`, it dominates the tensor-product value, and it is
invariant under the presentations of a verifier's game that the reduction moves between:
relabeling of the alphabets, padding of the answers by always-rejected ones, the doubled
question set, and the frozen verifier — and the only place the two differ is the direction in
which the value is semidecidable: `val*` from below (`lem:value-lower-approx`), `ω_co` from
above (`lem:valco-upper-re`). `ValueModel` is that list, and the whole reduction is written
once against it:

* `ValueModel`: a value functional on finite games with the transport properties, and its two
  instances `ValueModel.tensor` (`val*`) and `ValueModel.commuting` (`ω_co`), whose fields are
  the transport lemmas of `GameTransport.lean` and `CommutingTransport.lean`. The values are
  definitionally `quantumValue` and `commutingOperatorValue` (`tensor_val`, `commuting_val`),
  so the tensor-product statements of the reduction are the generic ones at `tensor`.
* `ValueModel.LowerRE`, `ValueModel.UpperRE`: the value is recursively enumerable from below,
  respectively from above, in the threshold encoding of `lem:value-lower-approx` (a pair
  `(p, q)` stands for `p / q`, with `p / 0 = 0`). `ValueModel.tensor_lowerRE`
  (`ClassMIPStar.lean`) and `ValueModel.commuting_upperRE` (`Tsirelson/UpperRE.lean`) are the
  two facts; neither model has the other direction, by the two theorems themselves.
* `ValueModel.HaltingReductionRE`, `ValueModel.HaltingReductionCoRE`: the two shapes of a
  halting reduction to the value — `1` on halting machines and at most `1/2` on the others,
  and the reverse — as propositions, which `Halting/CompressorProgram.lean` proves from a gap
  compression sound in the model and `Halting/Corollaries.lean` turns into `RE ⊆ MIPClass ω`,
  respectively `coRE ⊆ MIPClass ω`.

The universe of the alphabets is `Type`: the games of a verifier, their doubled forms and the
tabulated games all live there, and the fields need no more.
-/

namespace MIPRE

open HaltingGameValue (GameData HaltsOnEmptyInput)

section ExtendAnswers

variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- Enlarging the answer alphabets can only raise the quantum value: a strategy extends by zero
operators on the new answers. -/
theorem quantumValue_le_extendAnswers {A' B' : Type*} [Fintype A'] [Fintype B']
    (G : Game X Y A B) (G' : Game X Y A' B') (ιA : A ↪ A') (ιB : B ↪ B')
    (hμ : ∀ x y, G'.μ x y = G.μ x y) (hD : ∀ x y a b, G'.D x y (ιA a) (ιB b) = G.D x y a b) :
    quantumValue G ≤ quantumValue G' := by
  refine Real.iSup_le (fun S => ?_) (quantumValue_nonneg _)
  rw [← S.value_extendAnswers G' ιA ιB hμ hD]
  exact le_ciSup (TensorProductStrategy.bddAbove_range_value G') _

/-- Enlarging the answer alphabets can only raise the commuting-operator value. -/
theorem commutingOperatorValue_le_extendAnswers {A' B' : Type*} [Fintype A']
    [Fintype B'] (G : Game X Y A B) (G' : Game X Y A' B') (ιA : A ↪ A') (ιB : B ↪ B')
    (hμ : ∀ x y, G'.μ x y = G.μ x y) (hD : ∀ x y a b, G'.D x y (ιA a) (ιB b) = G.D x y a b) :
    commutingOperatorValue G ≤ commutingOperatorValue G' := by
  refine Real.iSup_le (fun S => ?_) (commutingOperatorValue_nonneg _)
  rw [← S.value_extendAnswers ιA ιB G G' hμ hD]
  exact (S.extendAnswers ιA ιB).value_le_commutingOperatorValue G'

end ExtendAnswers

/-- **A value model**: a value functional `val` on finite games — for `val*` and for `ω_co`,
the supremum of the value of a strategy over a class of strategies — together with the
properties of it that the halting reduction uses. The value is at most `1` and dominates the
tensor-product value (every model contains the tensor-product strategies), and it is invariant
under relabeling of the alphabets, monotone in the decision predicate, `0` on a game that
rejects everything, unchanged by padding the answer alphabets with always-rejected answers, and
unchanged by the doubling of the question set. -/
structure ValueModel where
  /-- The value of a game. -/
  val : ∀ {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B], Game X Y A B → ℝ
  /-- The value is at most one. -/
  le_one : ∀ {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B), val G ≤ 1
  /-- The value dominates the tensor-product value. -/
  quantumValue_le : ∀ {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B), quantumValue G ≤ val G
  /-- Games related by equivalences of their alphabets, with matching distribution and
  decision predicate, have the same value. -/
  eq_of_equiv : ∀ {X Y A B X' Y' A' B' : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B'] (G : Game X Y A B) (G' : Game X' Y' A' B')
    (eX : X' ≃ X) (eY : Y' ≃ Y) (eA : A' ≃ A) (eB : B' ≃ B),
    (∀ x' y', G'.μ x' y' = G.μ (eX x') (eY y')) →
    (∀ x' y' a' b', G'.D x' y' a' b' = G.D (eX x') (eY y') (eA a') (eB b')) → val G' = val G
  /-- Accepting more answer tuples, on the same alphabets and distribution, raises the value. -/
  mono : ∀ {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B] (G G' : Game X Y A B),
    (∀ x y, G'.μ x y = G.μ x y) → (∀ x y a b, G.D x y a b = true → G'.D x y a b = true) →
    val G ≤ val G'
  /-- A game whose decision predicate rejects everything has value `0`. -/
  eq_zero_of_reject : ∀ {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B), (∀ x y a b, G.D x y a b = false) → val G = 0
  /-- Enlarging the answer alphabets can only raise the value, whatever the decision predicate
  does on the new answers. -/
  le_extendAnswers : ∀ {X Y A B A' B' : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype A'] [Fintype B'] (G : Game X Y A B) (G' : Game X Y A' B') (ιA : A ↪ A') (ιB : B ↪ B'),
    (∀ x y, G'.μ x y = G.μ x y) → (∀ x y a b, G'.D x y (ιA a) (ιB b) = G.D x y a b) →
    val G ≤ val G'
  /-- Enlarging the answer alphabets by always-rejected answers does not change the value. -/
  extendAnswers : ∀ {X Y A B A' B' : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype A'] [Fintype B'] [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (G : Game X Y A B) (G' : Game X Y A' B') (ιA : A ↪ A') (ιB : B ↪ B'),
    (∀ x y, G'.μ x y = G.μ x y) → (∀ x y a b, G'.D x y (ιA a) (ιB b) = G.D x y a b) →
    (∀ x y a' b', G'.D x y a' b' = true → (∃ a, ιA a = a') ∧ (∃ b, ιB b = b')) →
    val G' = val G
  /-- The doubled game has the value of the game it doubles. -/
  doubled : ∀ {X A : Type} [Fintype X] [Fintype A] [DecidableEq A] (G : Game X X A A),
    val G.doubled.toGame = val G

namespace ValueModel

variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The value is nonnegative: it dominates the tensor-product value. -/
theorem nonneg (ω : ValueModel) (G : Game X Y A B) : 0 ≤ ω.val G :=
  (quantumValue_nonneg G).trans (ω.quantumValue_le G)

/-! ## The two models -/

/-- **The tensor-product model**: `val*`, the quantum value. -/
noncomputable def tensor : ValueModel where
  val G := quantumValue G
  le_one G := quantumValue_le_one G
  quantumValue_le _ := le_rfl
  eq_of_equiv G G' eX eY eA eB hμ hD := quantumValue_eq_of_equiv G G' eX eY eA eB hμ hD
  mono G G' hμ hD := quantumValue_mono G G' hμ hD
  eq_zero_of_reject G hD := quantumValue_eq_zero_of_reject G hD
  le_extendAnswers G G' ιA ιB hμ hD := quantumValue_le_extendAnswers G G' ιA ιB hμ hD
  extendAnswers G G' ιA ιB hμ hD hD' := quantumValue_extendAnswers G G' ιA ιB hμ hD hD'
  doubled G := quantumValue_doubled G

@[simp] theorem tensor_val (G : Game X Y A B) : tensor.val G = quantumValue G := rfl

/-- **The commuting-operator model**: `ω_co`, the bipartite commuting-operator value. -/
noncomputable def commuting : ValueModel where
  val G := commutingOperatorValue G
  le_one G := commutingOperatorValue_le_one G
  quantumValue_le G := quantumValue_le_commutingOperatorValue G
  eq_of_equiv G G' eX eY eA eB hμ hD := commutingOperatorValue_eq_of_equiv G G' eX eY eA eB hμ hD
  mono G G' hμ hD := commutingOperatorValue_mono G G' hμ hD
  eq_zero_of_reject G hD := commutingOperatorValue_eq_zero_of_reject G hD
  le_extendAnswers G G' ιA ιB hμ hD := commutingOperatorValue_le_extendAnswers G G' ιA ιB hμ hD
  extendAnswers G G' ιA ιB hμ hD hD' := commutingOperatorValue_extendAnswers G G' ιA ιB hμ hD hD'
  doubled G := commutingOperatorValue_doubled G

@[simp] theorem commuting_val (G : Game X Y A B) : commuting.val G = commutingOperatorValue G :=
  rfl

/-! ## Semidecidability of the value, and the two shapes of a halting reduction -/

/-- **The value is r.e. from below**: the triples `(d, p, q)` with `p / q < val(G_d)` form an
r.e. set, in the threshold encoding of `lem:value-lower-approx` (`p / 0 = 0`). The
tensor-product model has it (`ValueModel.tensor_lowerRE`); the commuting-operator model does
not, by `MIP^co = coRE` itself. -/
def LowerRE (ω : ValueModel) : Prop :=
  REPred fun x : GameData × ℕ × ℕ => (x.2.1 : ℝ) / x.2.2 < ω.val x.1.game

/-- **The value is r.e. from above**: the triples `(d, p, q)` with `val(G_d) < p / q` form an
r.e. set. The commuting-operator model has it (`ValueModel.commuting_upperRE`, blueprint
`lem:valco-upper-re`); the tensor-product model does not, by `MIP* = RE` itself. -/
def UpperRE (ω : ValueModel) : Prop :=
  REPred fun x : GameData × ℕ × ℕ => ω.val x.1.game < (x.2.1 : ℝ) / x.2.2

/-- **A halting reduction to the value, `RE` shape**: a computable map from codes to game
descriptions whose value is `1` on codes that halt on the empty input and at most `1/2` on the
others. At `tensor` this is `cor:main-quantum`. -/
def HaltingReductionRE (ω : ValueModel) : Prop :=
  ∃ g : Nat.Partrec.Code → GameData, Computable g ∧
    ∀ pc : Nat.Partrec.Code,
      (HaltsOnEmptyInput pc → ω.val (g pc).game = 1) ∧
      (¬ HaltsOnEmptyInput pc → ω.val (g pc).game ≤ 1 / 2)

/-- **A halting reduction to the value, `coRE` shape**: a computable map from codes to game
descriptions whose value is at most `1/2` on codes that halt on the empty input and `1` on the
others. At `commuting` this is `thm:halting-co`. -/
def HaltingReductionCoRE (ω : ValueModel) : Prop :=
  ∃ g : Nat.Partrec.Code → GameData, Computable g ∧
    ∀ pc : Nat.Partrec.Code,
      (HaltsOnEmptyInput pc → ω.val (g pc).game ≤ 1 / 2) ∧
      (¬ HaltsOnEmptyInput pc → ω.val (g pc).game = 1)

end ValueModel

end MIPRE
