/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.SubgroupTestValue
public import MIPRE.TailoredGameValue

@[expose] public section

/-!
# The subgroup test associated with a tailored game

Paper I, Definition I:2086, for the tailored games of `MIPRE/TailoredGameValue.lean`. The test
`assocTest g` has the generators `J` (index `0`) and one generator `X(x, i)` for each vertex `x`
and each `i < Λ` (index `1 + x Λ + i`, `Λ = g.ansLen`); those with `i ≥ ℓ(x)` appear in no word.
It has one challenge per question pair `(x, y)`, weighted by the pair's weight in `g` (with the
game's convention when every weight vanishes: a single challenge at `(0, 0)`). The words `K` of
the challenge at `(x, y)` are, in order:

* the *fixed* words (`fixedLits`): `J` (required out of `H`), then `J²`, `[J, X]` for every
  variable `X` at `x` and at `y`, `X²` for the same, and `[X, X']` for the pairs of variables at
  `x` and at `y` (all required in `H`) — Checks 1 and 2;
* the *readable* words (`readWords`): for each readable variable at `x`, then at `y`, the pair
  `X`, `J X` — Check 3;
* the *constraint* words (`consWords`): one for each entry of `g.cons` at `(x, y)`, the word
  `J^{c_J} ∏ X(x, i)^{c_i} ∏ X(y, i)^{c_{ℓ(x) + i}}`, or `J` when the constraint has the wrong
  length (the game rejects it, and `J ∈ H` contradicts Check 1) — Check 4.

The decision is one clause per value `r` of the readable variables: the fixed literals, the
readable word of `r` at each readable variable (`X` when its bit is `0`, `J X` when `1`), and
the constraint words of the entries whose readable part is `r`. Exactly the subgroups the paper's
decision `D̃_{xy}` accepts satisfy some clause.
-/

namespace MIPRE.Tailored.Sofic

open SubgroupTestValue TailoredGameValue

/-! ## Words -/

/-- The inverse of a word. -/
def invW (w : Word) : Word := (w.map fun l => (l.1, !l.2)).reverse

/-- The commutator `[u, v] = u v u⁻¹ v⁻¹`. -/
def commW (u v : Word) : Word := u ++ v ++ invW u ++ invW v

/-- The one-letter word of a generator. -/
def genW (k : ℕ) : Word := [(k, false)]

/-- All bit lists of length `n`. -/
def allBits : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allBits n).flatMap fun r => [false :: r, true :: r]

variable (g : TailoredGameData)

/-- The generator of `J`. -/
def genJ : ℕ := 0

/-- The question weights of `g`, as a `GameData` (`g.weights`, computably). -/
def wts : HaltingGameValue.GameData := ⟨g.nV, 0, g.w, []⟩

theorem wts_eq : wts g = g.weights := rfl

/-- The generator `X(x, i)`. -/
def genX (x i : ℕ) : ℕ := 1 + x * g.ansLen + i

/-- The number of generators. -/
def nGen : ℕ := 1 + (g.nV + 1) * g.ansLen

/-- The word `J`. -/
def wJ : Word := genW genJ

/-- The word `X(x, i)`. -/
def wX (x i : ℕ) : Word := genW ((genX g) x i)

/-- The variables at `x`: `X(x, i)` for `i < ℓ(x)`. -/
def varsAt (x : ℕ) : List Word := (List.range (g.lenAt x)).map ((wX g) x)

/-! ## The words of a challenge -/

/-- The fixed words, Checks 1 and 2, with the membership each must have. -/
def fixedLits (x y : ℕ) : List (Word × Bool) :=
  let V := (varsAt g) x ++ (varsAt g) y
  [(wJ, false), (wJ ++ wJ, true)] ++ V.map (fun X => (commW wJ X, true)) ++
    V.map (fun X => (X ++ X, true)) ++
    ((varsAt g) x).flatMap (fun X => ((varsAt g) x).map fun X' => (commW X X', true)) ++
    ((varsAt g) y).flatMap (fun Y => ((varsAt g) y).map fun Y' => (commW Y Y', true))

/-- The readable variables at `x`, then at `y`. -/
def readVars (x y : ℕ) : List Word :=
  (List.range (g.lenRAt x)).map ((wX g) x) ++ (List.range (g.lenRAt y)).map ((wX g) y)

/-- The readable words: `X` then `J X` for each readable variable. -/
def readWords (x y : ℕ) : List Word := ((readVars g) x y).flatMap fun X => [X, wJ ++ X]

/-- The entries of `g.cons` at `(x, y)`. -/
def consAt (x y : ℕ) : List (ℕ × ℕ × List Bool × List Bool) :=
  g.cons.filter fun e => decide (e.1 = x ∧ e.2.1 = y)

/-- The word of a constraint `c` at `(x, y)`: `J^{c_J} ∏ X(x, i)^{c_i} ∏ X(y, i)^{c_{ℓ(x)+i}}`,
or `J` when `c` has the wrong length. -/
def consWord (x y : ℕ) (c : List Bool) : Word :=
  if c.length = g.lenAt x + g.lenAt y + 1 then
    (if c.getD (g.lenAt x + g.lenAt y) false then wJ else []) ++
      ((List.range (g.lenAt x)).filter (fun i => c.getD i false)).flatMap ((wX g) x) ++
      ((List.range (g.lenAt y)).filter (fun i => c.getD (g.lenAt x + i) false)).flatMap ((wX g) y)
  else wJ

/-- The constraint words at `(x, y)`, one per entry. -/
def consWords (x y : ℕ) : List Word := ((consAt g) x y).map fun e => (consWord g) x y e.2.2.2

/-- The words `K` of the challenge at `(x, y)`. -/
def words (x y : ℕ) : List Word :=
  ((fixedLits g) x y).map Prod.fst ++ (readWords g) x y ++ (consWords g) x y

/-! ## The clauses -/

/-- The clause of the readable value `r`: the fixed literals, the readable words of `r`, and the
constraint words of the entries whose readable part is `r`. -/
def clause (x y : ℕ) (r : List Bool) : List (ℕ × Bool) :=
  let F := ((fixedLits g) x y).length
  let R := ((readWords g) x y).length
  (((fixedLits g) x y).zipIdx.map fun p => (p.2, p.1.2)) ++
    ((List.range ((readVars g) x y).length).map fun t =>
      (F + 2 * t + (if r.getD t false then 1 else 0), true)) ++
    ((((consAt g) x y).zipIdx.filter fun p => decide (p.1.2.2.1 = r)).map fun p =>
      (F + R + p.2, true))

/-- The clauses at `(x, y)`, one per readable value. -/
def clauses (x y : ℕ) : List (List (ℕ × Bool)) :=
  (allBits (g.lenRAt x + g.lenRAt y)).map ((clause g) x y)

/-! ## The test -/

/-- The challenge at `(x, y)`, with weight `w`. -/
def challenge (w x y : ℕ) : ℕ × List Word × List (List (ℕ × Bool)) :=
  (w, (words g) x y, (clauses g) x y)

/-- **The synchronous subgroup test associated with a tailored game** (Definition I:2086). -/
def assocTest : SubgroupTestData where
  nGen := (nGen g)
  challenges :=
    if (wts g).totalWeight = 0 then [(challenge g) 1 0 0]
    else (List.range (g.nV + 1)).flatMap fun x => (List.range (g.nV + 1)).map fun y =>
      (challenge g) ((wts g).questionWeight x y) x y

/-! ## Actions passing Checks 1–3 -/

/-- The permutation of the generator `k` under a finite action. -/
def genPerm {n : ℕ} (σ : FiniteAction n) (k : ℕ) : Equiv.Perm (Fin σ.N) := σ.letterPerm (k, false)

/-- **An action passing Checks 1–3 of the associated test at every point and every question
pair** (Proposition I:2279, the strategies it applies to): `J` is a fixed-point-free involution
commuting with every variable `X(x, i)`, `i < ℓ(x)`; these are involutions, commuting at each
vertex; and each readable variable acts at every point as the identity or as `J` (Z-alignment,
Definition I:2026). -/
structure Checks (σ : FiniteAction (nGen g)) : Prop where
  J_invol : ∀ p, genPerm σ genJ (genPerm σ genJ p) = p
  J_free : ∀ p, genPerm σ genJ p ≠ p
  J_comm : ∀ x i, x < g.nV + 1 → i < g.lenAt x →
    genPerm σ genJ * genPerm σ (genX g x i) = genPerm σ (genX g x i) * genPerm σ genJ
  X_invol : ∀ x i, x < g.nV + 1 → i < g.lenAt x → ∀ p,
    genPerm σ (genX g x i) (genPerm σ (genX g x i) p) = p
  X_comm : ∀ x i i', x < g.nV + 1 → i < g.lenAt x → i' < g.lenAt x →
    genPerm σ (genX g x i) * genPerm σ (genX g x i') =
      genPerm σ (genX g x i') * genPerm σ (genX g x i)
  readable : ∀ x i, x < g.nV + 1 → i < g.lenRAt x → ∀ p,
    genPerm σ (genX g x i) p = p ∨ genPerm σ (genX g x i) p = genPerm σ genJ p

end MIPRE.Tailored.Sofic

end
