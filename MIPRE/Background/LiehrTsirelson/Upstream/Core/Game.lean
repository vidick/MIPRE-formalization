/-
Vendored from `lukasliehr/MIPRE` (https://github.com/lukasliehr/MIPRE), a Lean 4 formalization of
Tsirelson's problem, by scripts/vendor-liehr.py; do not edit by hand. Upstream path:
Tsirelson/Core/Game.lean, from a snapshot of the `main` branch supplied on 2026-09-25 (archive, no
commit recorded). The import prefix `Tsirelson.` is rewritten to
`MIPRE.Background.LiehrTsirelson.Upstream.`; the Lean namespace `Tsirelson` is unchanged, and
nothing outside `MIPRE/Background/LiehrTsirelson/` may name it. Upstream carries no license file;
see README.md.
-/
import MIPRE.Background.LiehrTsirelson.Upstream.Core.Correlation

/-!
# Generic nonlocal games, finite / square aliases, and bundled signatures

Source: `Blueprint/Nodes/B23-Games/Parts/01-GamesAndStrategies.tex`, `def:game`
(which defers to `def:n7b`), `rem:symmetric-games`; and
`Blueprint/Nodes/B05-NPA-Core/Math.tex`, `def:n7b` (finite nonlocal games and
standard square games).

There is exactly one generic game notion.  The asymmetric finite games and the
square games used by the terminal statements are `abbrev` specializations of it,
never separate structures.

**GAME-1.**  The four nonemptiness proofs are game *data*, not typeclass
parameters.  Consequently `Game n k` is a well-formed type for arbitrary
`n k : ℕ` — merely uninhabited in the degenerate cases — which is what lets the
terminal statements quantify `G : Game n k` *before* stating `1 ≤ n` and
`1 ≤ k`.
-/

namespace Tsirelson

universe u v w z

/-- A two-player one-round nonlocal game on generic finite alphabets.

This is `def:game` / `def:n7b`: nonempty finite question alphabets `X`, `Y`,
nonempty finite answer alphabets `A`, `B`, an actual question distribution on
`X × Y`, and an actual Boolean decision predicate. -/
structure NonlocalGame (X : Type u) (Y : Type v) (A : Type w) (B : Type z)
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] where
  /-- Alice's question alphabet is nonempty. -/
  nonemptyX : Nonempty X
  /-- Bob's question alphabet is nonempty. -/
  nonemptyY : Nonempty Y
  /-- Alice's answer alphabet is nonempty. -/
  nonemptyA : Nonempty A
  /-- Bob's answer alphabet is nonempty. -/
  nonemptyB : Nonempty B
  /-- The question distribution `μ` on `X × Y`. -/
  questions : FiniteProbability (X × Y)
  /-- The decision predicate `D : X × Y × A × B → {0,1}`. -/
  accept : X → Y → A → B → Bool

/-- Finite games presented by the cardinalities of their four alphabets. -/
abbrev AsymGame (nX nY nA nB : ℕ) : Type :=
  NonlocalGame (Fin nX) (Fin nY) (Fin nA) (Fin nB)

/-- The *standard square game* of `def:n7b`: `X = Y = [n]`, `A = B = [k]`. -/
abbrev Game (n k : ℕ) : Type := AsymGame n n k k

namespace NonlocalGame

variable {X : Type u} {Y : Type v} {A : Type w} {B : Type z}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The real-valued `0/1` decision coefficient, *derived* from `accept`. -/
def D (G : NonlocalGame X Y A B) (x : X) (y : Y) (a : A) (b : B) : ℝ :=
  if G.accept x y a b then 1 else 0

theorem D_nonneg (G : NonlocalGame X Y A B) (x y a b) : 0 ≤ G.D x y a b := by
  unfold D; split <;> norm_num

theorem D_le_one (G : NonlocalGame X Y A B) (x y a b) : G.D x y a b ≤ 1 := by
  unfold D; split <;> norm_num

theorem D_mem_Icc (G : NonlocalGame X Y A B) (x y a b) : G.D x y a b ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨G.D_nonneg x y a b, G.D_le_one x y a b⟩

/-- The support of the question distribution — the set `S` of `def:comm-strategy`. -/
def questionSupport (G : NonlocalGame X Y A B) : Set (X × Y) := G.questions.support

/-- A game is *symmetric* when both invariance conditions of `rem:symmetric-games`
hold: the distribution is swap-invariant **and** the decision predicate treats the
players symmetrically.  Equal alphabets alone are not enough. -/
def IsSymmetric (G : NonlocalGame X X A A) : Prop :=
  (∀ x y, G.questions.prob (x, y) = G.questions.prob (y, x)) ∧
  (∀ x y a b, G.accept x y a b = G.accept y x b a)

/-- Symmetric games as a subtype of the one generic game notion. -/
abbrev SymmetricGame (X : Type u) (A : Type w) [Fintype X] [Fintype A] : Type _ :=
  {G : NonlocalGame X X A A // G.IsSymmetric}

end NonlocalGame

/-- A dependently bundled game signature: four finite nonempty alphabets together
with an actual generic game on them.

`GameSig` stores no cached value and no cardinality field; the question and
answer counts are recovered by `Fintype.card`.  This is the quantification
domain of the B28 quantitative separation proposition, which therefore needs no
separate cardinality-positivity hypotheses: the nonemptiness proofs are carried
by `game`. -/
structure GameSig where
  /-- Alice's question alphabet. -/
  X : Type
  /-- Bob's question alphabet. -/
  Y : Type
  /-- Alice's answer alphabet. -/
  A : Type
  /-- Bob's answer alphabet. -/
  B : Type
  [fintypeX : Fintype X]
  [fintypeY : Fintype Y]
  [fintypeA : Fintype A]
  [fintypeB : Fintype B]
  /-- The actual generic game carried by this signature. -/
  game : NonlocalGame X Y A B

attribute [instance] GameSig.fintypeX GameSig.fintypeY GameSig.fintypeA GameSig.fintypeB

namespace GameSig

/-- The square signature attached to a square game. -/
def ofGame {n k : ℕ} (G : Game n k) : GameSig where
  X := Fin n
  Y := Fin n
  A := Fin k
  B := Fin k
  game := G

@[simp] theorem ofGame_game {n k : ℕ} (G : Game n k) : (GameSig.ofGame G).game = G := rfl

end GameSig

end Tsirelson
