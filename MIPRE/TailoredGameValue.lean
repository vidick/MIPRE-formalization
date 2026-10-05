/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.HaltingGameValue
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import MIPRE.Tactics

@[expose] public section

/-!
# A self-contained statement of `TMIP* = RE` (Bowen–Chapman–Vidick, paper II)

This file states the main theorem of L. Bowen, M. Chapman and T. Vidick, *The Aldous–Lyons
Conjecture II: Undecidability* (arXiv:2501.00173), Theorem `thm:tailored_MIP*=RE`: there is a
computable map from Turing machines to *tailored* non-local games that sends halting machines
to games with a perfect *Z-aligned permutation strategy commuting along edges* (ZPC) and
non-halting machines to games of value at most `1/2`. Together with paper I (*Subgroup Tests*,
arXiv:2408.00110) this refutes the Aldous–Lyons conjecture. The plan for proving it is
`planning/aldous-lyons-track.md`.

Like `MIPRE.HaltingGameValue`, whose games, strategies and value it reuses, the file depends on
Mathlib only. Its definitions, with the paper's (line numbers of the arXiv LaTeX source):

* `TailoredGameData` (paper: tailored games, II:1243): a first-order description of a game with
  vertices `Fin (nV + 1)`, at each vertex `x` a set `S_x` of `ℓ^R(x)` *readable* and `ℓ^L(x)`
  *linear* formal variables, edge weights, and *controlled linear constraints*: for an edge
  `xy` and a value `γ^R` of the readable variables, a list `L_xy(γ^R)` of vectors `c` over
  `S_x ⊔ S_y ⊔ {J}`.
* `TailoredGameData.toGame`: its interpretation as a `HaltingGameValue.SynchronousGame`. The
  answers are bit vectors of the maximal length `Λ`; an answer at `x` must vanish beyond
  `ℓ(x) = ℓ^R(x) + ℓ^L(x)`, and the answer pair `(a, b)` at `xy` is accepted by the paper's
  *canonical decider* (II:1757–1787): every `c ∈ L_xy(a^R b^R)` satisfies `⟨c, a b 1⟩ = 0`,
  where `J` is the affine coordinate, set to `1`. The empty list accepts and the list `[J]`
  rejects.
* `PermStrategy`, `HasPerfectZPC` (paper: II:1043–1057, II:1279–1283): a strategy whose
  observables are signed permutation matrices — one per formal variable, involutions,
  commuting at each vertex — with diagonal observables for the readable variables
  (*Z-aligned*), commuting across every edge of positive weight (*commuting along edges*); its
  measurements are the Fourier transforms `P^x_a = ∏_i (1 + (-1)^{a_i} U(x, i)) / 2`, and it
  is *perfect* when its value is `1`.
* `TailoredHaltingReduction`: the statement.

Two conventions differ from the paper's text and are equivalent to it:

* **Loops.** At a loop `xx` the paper's decision reads one answer, over `S_x`. Here, as in the
  paper's tailored normal form verifiers, whose canonical decider is always given two answers,
  it reads the pair `(a, a)` — unequal answers at a loop lose, which is what makes the game
  synchronous — so a constraint over `S_x ⊔ S_x ⊔ {J}` evaluated at `(a, a)`; a one-copy
  constraint `(c, c_J)` is the two-copy constraint `(c, 0, c_J)`, and a two-copy constraint
  `(c₁, c₂, c_J)` acts as the one-copy constraint `(c₁ + c₂, c_J)`.
* **One answer alphabet.** The paper's answers at `x` are `F₂^{S_x}`; here they are the bit
  vectors of length `Λ = max_x ℓ(x)` that vanish beyond `ℓ(x)`, and the generators beyond
  `ℓ(x)` of a permutation strategy act as the identity. A strategy for the paper's game and
  one for this game determine each other by padding with zeros and truncating, with the same
  value; a ZPC strategy and its padding by identities likewise.

Clause (3) of the paper's theorem reads `val*(G_M) < 1/2`; its proof (II:2046–2065) shows that
every finite-dimensional strategy has value `< 1/2`, which bounds the supremum by `1/2` only,
and paper I uses the theorem with `≤ 1/2` (I:2140). The statement below has `≤ 1/2`.
-/

namespace TailoredGameValue

open HaltingGameValue

/-! ## Descriptions of tailored games -/

/-- A first-order description of a tailored game (II:1243). The vertices are `Fin (nV + 1)`;
vertex `x` has `lenR.getD x 0` readable and `lenL.getD x 0` linear formal variables; the
question distribution is given, as in `HaltingGameValue.GameData`, by a list `w` of
unnormalized weights `(x, y, weight)`; and the controlled linear constraints by the list
`cons` of entries `(x, y, γ^R, c)`, read as "`c ∈ L_xy(γ^R)`". Here `γ^R` is the readable part
of the answer pair (the readable bits of the answer at `x`, then those at `y`) and `c` is a
vector over `S_x ⊔ S_y ⊔ {J}` (the coefficients on the variables at `x`, readable then linear,
then those at `y`, then the coefficient of `J`). -/
structure TailoredGameData where
  nV : ℕ
  lenR : List ℕ
  lenL : List ℕ
  w : List (ℕ × ℕ × ℕ)
  cons : List (ℕ × ℕ × List Bool × List Bool)

namespace TailoredGameData

/-- `TailoredGameData` is a tuple of naturals and lists. -/
def equivTuple : TailoredGameData ≃
    ℕ × List ℕ × List ℕ × List (ℕ × ℕ × ℕ) × List (ℕ × ℕ × List Bool × List Bool) where
  toFun g := (g.nV, g.lenR, g.lenL, g.w, g.cons)
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2⟩

instance : Primcodable TailoredGameData := Primcodable.ofEquiv _ equivTuple

variable (g : TailoredGameData)

/-- The number `ℓ^R(x)` of readable variables at `x`. -/
def lenRAt (x : ℕ) : ℕ := g.lenR.getD x 0

/-- The number `ℓ^L(x)` of linear variables at `x`. -/
def lenLAt (x : ℕ) : ℕ := g.lenL.getD x 0

/-- The number `ℓ(x) = ℓ^R(x) + ℓ^L(x)` of variables at `x`. -/
def lenAt (x : ℕ) : ℕ := g.lenRAt x + g.lenLAt x

/-- The answer length `Λ = max_x ℓ(x)`. -/
def ansLen : ℕ := Finset.univ.sup fun x : Fin (g.nV + 1) => g.lenAt x.val

/-- Bit `i` of a bit vector, `false` beyond its length. -/
def bit {n : ℕ} (a : Fin n → Bool) (i : ℕ) : Bool := if h : i < n then a ⟨i, h⟩ else false

/-- An answer at `x` is well formatted when it vanishes beyond `ℓ(x)`. -/
def WellFormatted (x : Fin (g.nV + 1)) (a : Fin g.ansLen → Bool) : Prop :=
  ∀ i : Fin g.ansLen, g.lenAt x.val ≤ i.val → a i = false

/-- The readable part `a^R` of an answer at `x`: its first `ℓ^R(x)` bits. -/
def readable (x : Fin (g.nV + 1)) (a : Fin g.ansLen → Bool) : List Bool :=
  (List.range (g.lenRAt x.val)).map (bit a)

/-- The full answer at `x`: its first `ℓ(x)` bits, readable then linear. -/
def full (x : Fin (g.nV + 1)) (a : Fin g.ansLen → Bool) : List Bool :=
  (List.range (g.lenAt x.val)).map (bit a)

/-- A vector `v` satisfies the linear constraint `c` when they have the same length and
`⟨c, v⟩ = 0` over `F₂`. A constraint of the wrong length is never satisfied, as the paper's
canonical decider rejects malformed constraints. -/
def Satisfies (c v : List Bool) : Prop :=
  c.length = v.length ∧ Even ((List.zipWith (· && ·) c v).count true)

instance (c v : List Bool) : Decidable (Satisfies c v) := by
  unfold Satisfies; infer_instance

/-- The canonical decider (II:1757–1787) at the question pair `(x, y)`: unequal answers at a
loop lose; both answers are well formatted; and every constraint `c ∈ L_xy(a^R b^R)` is
satisfied by `a b 1`, the two full answers followed by the coordinate `J = 1`. -/
def Accepts (x y : Fin (g.nV + 1)) (a b : Fin g.ansLen → Bool) : Prop :=
  (x = y → a = b) ∧ g.WellFormatted x a ∧ g.WellFormatted y b ∧
    ∀ e ∈ g.cons, e.1 = x.val → e.2.1 = y.val → e.2.2.1 = g.readable x a ++ g.readable y b →
      Satisfies e.2.2.2 (g.full x a ++ g.full y b ++ [true])

instance (x y : Fin (g.nV + 1)) (a b : Fin g.ansLen → Bool) : Decidable (g.Accepts x y a b) := by
  unfold Accepts WellFormatted; infer_instance

/-- The question distribution: the weights `w` normalized as in `HaltingGameValue.GameData`. -/
noncomputable def weights : GameData := ⟨g.nV, 0, g.w, []⟩

/-- Interpret a `TailoredGameData` as a `SynchronousGame`: questions are vertices, answers are
bit vectors of length `Λ`, the distribution is that of the weights, and acceptance is the
canonical decider's. -/
noncomputable def toGame : SynchronousGame (Fin (g.nV + 1)) (Fin g.ansLen → Bool) where
  μ := g.weights.toGame.μ
  μ_nonneg := g.weights.toGame.μ_nonneg
  μ_sum_one := g.weights.toGame.μ_sum_one
  D x y a b := decide (g.Accepts x y a b)
  synchronous x a b hne := by
    simp [Accepts, hne]

end TailoredGameData

/-! ## Z-aligned permutation strategies commuting along edges -/

/-- The signed permutation matrix `e_j ↦ (-1)^{s j} e_{σ j}` (II:1043–1053): the action of the
signed permutation `(σ, s)` of `Ω_± = {±} × Fin m` on the anti-symmetric functions, in their
standard basis. -/
def signedPermMatrix {m : ℕ} (σ : Equiv.Perm (Fin m)) (s : Fin m → Bool) :
    Matrix (Fin m) (Fin m) ℂ :=
  fun i j => if σ j = i then (if s j then -1 else 1) else 0

variable (g : TailoredGameData)

/-- A permutation strategy for a tailored game (II:1056, II:1115): on `ℂ^m`, one observable
`U x i` for each variable `i` at each vertex `x`, a signed permutation matrix and an
involution, the observables at a vertex commuting; the variables beyond `ℓ(x)` act as the
identity (§ "One answer alphabet" of the module docstring). It is *Z-aligned* when the
observables of the readable variables are diagonal and *commutes along edges* when the
observables at the two ends of every edge of positive weight commute (II:1279–1283). -/
structure PermStrategy where
  /-- The dimension. -/
  m : ℕ
  m_pos : 0 < m
  /-- The observables. -/
  U : Fin (g.nV + 1) → Fin g.ansLen → Matrix (Fin m) (Fin m) ℂ
  signedPerm : ∀ x i, ∃ σ s, U x i = signedPermMatrix σ s
  invol : ∀ x i, U x i * U x i = 1
  comm : ∀ x i j, U x i * U x j = U x j * U x i
  pad : ∀ x (i : Fin g.ansLen), g.lenAt x.val ≤ i.val → U x i = 1
  zAligned : ∀ x (i : Fin g.ansLen), i.val < g.lenRAt x.val → (U x i).IsDiag
  commEdges : ∀ x y, 0 < g.toGame.μ x y → ∀ i j, U x i * U y j = U y j * U x i

namespace PermStrategy

variable {g} (S : PermStrategy g)

/-- The measurement at `x`, the Fourier transform of the observables (II:974):
`P^x_a = ∏_i (1 + (-1)^{a_i} U(x, i)) / 2`. -/
noncomputable def proj (x : Fin (g.nV + 1)) (a : Fin g.ansLen → Bool) :
    Matrix (Fin S.m) (Fin S.m) ℂ :=
  ((List.finRange g.ansLen).map fun i =>
    (1 / 2 : ℂ) • (1 + (if a i then (-1 : ℂ) else 1) • S.U x i)).prod

/-- The value of a permutation strategy, defined as `HaltingGameValue.strategyValue` defines
the value of a synchronous strategy: the players answer `(x, y)` with `(a, b)` with probability
`Tr(P^x_a P^y_b) / m`. -/
noncomputable def value : ℝ :=
  ∑ x, ∑ y, ∑ a, ∑ b,
    g.toGame.μ x y * (if g.toGame.D x y a b then 1 else 0) *
      ((S.proj x a * S.proj y b).trace.re / (S.m : ℝ))

end PermStrategy

/-- The game has a perfect Z-aligned permutation strategy commuting along edges (II:1279). -/
def TailoredGameData.HasPerfectZPC : Prop := ∃ S : PermStrategy g, S.value = 1

/-! ## The halting problem and `TMIP* = RE` -/

/-- **`TMIP* = RE`**, Theorem `thm:tailored_MIP*=RE` of Bowen–Chapman–Vidick, paper II
(arXiv:2501.00173, II:1505), with "polynomial-time" relaxed to "computable" and `< 1/2` read as
`≤ 1/2` (module docstring): there is a computable map from Turing machines to tailored games
such that

1. (completeness) if the machine halts on the empty input then the game has a perfect
   Z-aligned permutation strategy commuting along edges, and
2. (soundness) if it does not then the synchronous value of the game is at most `1/2`.

This is the statement; nothing in this file proves it. -/
def TailoredHaltingReduction : Prop :=
  ∃ g : Nat.Partrec.Code → TailoredGameData, Computable g ∧
    ∀ c : Nat.Partrec.Code,
      (HaltsOnEmptyInput c → (g c).HasPerfectZPC) ∧
      (¬HaltsOnEmptyInput c → gameValue (g c).toGame ≤ 1 / 2)

end TailoredGameValue

end
