/-
# MIP* = RE — the statements (Palomar Challenge, draft)

This file states, on top of Mathlib alone, what the MIPRE formalization of "MIP* = RE"
(Ji, Natarajan, Vidick, Wright, Yuen, arXiv:2001.04383) proves. Every definition the
statements need is spelled out here; every theorem is left as `sorry`, to be proved in the
companion Solution. Its five parts:

1. two-player one-round games on finite alphabets (`Game`);
2. finite-dimensional tensor-product strategies and the quantum value `quantumValue`, and
   synchronous strategies and the synchronous value `syncValue`;
3. the halting reduction (Theorem 12.2 of the paper): a computable map from Gödel numbers of
   partial recursive functions (`Nat.Partrec.Code`) to explicit games (`GameData`) that sends
   halting machines to value `1` and non-halting ones to value at most `1/2`, and the
   uncomputability of both values;
4. recursively enumerable languages over `{0,1}*` (`IsRE`);
5. the class `MIP*_{1,1/2}(2,1)` (`MIPStar`): a polynomial-time verifier — a sampler and a
   decider — and its game, and the theorem `MIPStar = IsRE`.

Polynomial time is measured in a small first-order model of computation, spelled out in part
5: programs over binary trees with a timed big-step semantics in which every operation costs
one unit except reading a value, which costs its size. A run of cost `t` therefore builds a
result of size at most `t`, and a pointer machine simulates a run of cost `t` in time `O(t)`;
the class of polynomial-time functions is the usual one. No other notion of machine appears.
-/

module
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Computability.PartrecCode
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Set.Finite.List
public import Mathlib.Data.Fintype.Vector

@[expose] public section

namespace MIPRE.Palomar

open Kronecker Matrix

/-! ## 1. Games -/

/-- A two-player one-round game: finite question alphabets `X`, `Y`, finite answer alphabets
`A`, `B`, a probability distribution `μ` on `X × Y`, and a decision predicate `D`
(`true` = accept). The players receive `(x, y)` drawn from `μ`, answer `(a, b)` without
communicating, and win when `D x y a b`. -/
structure Game (X Y A B : Type*) [Fintype X] [Fintype Y] [Fintype A] [Fintype B] where
  /-- The probability that the players are asked the question pair `(x, y)`. -/
  μ : X → Y → ℝ
  μ_nonneg : ∀ x y, 0 ≤ μ x y
  μ_sum_one : ∑ x, ∑ y, μ x y = 1
  /-- `D x y a b = true` when the answers `(a, b)` to the questions `(x, y)` are accepted. -/
  D : X → Y → A → B → Bool

section

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-! ## 2. Strategies and values -/

/-- A question-indexed family of projective measurements on `ℂ^d`: for each question `x`,
self-adjoint idempotent matrices (orthogonal projections) `M x a`, one per answer `a`,
summing to the identity. -/
structure PVM (X A : Type*) (d : ℕ) [Fintype A] where
  M : X → A → Matrix (Fin d) (Fin d) ℂ
  selfAdjoint : ∀ x a, star (M x a) = M x a
  projective : ∀ x a, M x a * M x a = M x a
  normalized : ∀ x, ∑ a, M x a = 1

/-- A finite-dimensional tensor-product strategy for `G`: Hilbert spaces `ℂ^dA` and `ℂ^dB`, a
unit vector `ψ` in their tensor product `ℂ^dA ⊗ ℂ^dB = ℂ^(dA × dB)`, and projective
measurements `{A^x_a}` on `ℂ^dA` for Alice and `{B^y_b}` on `ℂ^dB` for Bob. (Restricting to
projective measurements loses no generality, by Naimark dilation.) -/
structure TensorStrategy (G : Game X Y A B) where
  dA : ℕ
  dB : ℕ
  ψ : Fin dA × Fin dB → ℂ
  ψ_unit : star ψ ⬝ᵥ ψ = 1
  PA : PVM X A dA
  PB : PVM Y B dB

/-- The winning probability of a tensor-product strategy: by the Born rule the players answer
`(a, b)` to `(x, y)` with probability `⟨ψ| A^x_a ⊗ B^y_b |ψ⟩`, the tensor product of
matrices
being the Kronecker product. (The probability is a nonnegative real; `.re` makes the
definition typecheck without a proof.) -/
noncomputable def TensorStrategy.value {G : Game X Y A B} (S : TensorStrategy G) : ℝ :=
  ∑ x, ∑ y, ∑ a, ∑ b,
    G.μ x y * (if G.D x y a b then 1 else 0) *
      (star S.ψ ⬝ᵥ ((S.PA.M x a ⊗ₖ S.PB.M y b) *ᵥ S.ψ)).re

/-- The quantum (entangled) value `val*(G)`: the supremum of the winning probability over all
finite-dimensional tensor-product strategies, of every dimension. -/
noncomputable def quantumValue (G : Game X Y A B) : ℝ :=
  ⨆ S : TensorStrategy G, S.value

/-- A synchronous strategy for a game with equal alphabets for the two players: one family of
projective measurements `{M^x_a}` on `ℂ^d` (`d > 0`), used by both players, with outcome
probabilities computed against the normalized trace `τ(M) = Tr(M)/d`. Measurements for
different questions need not commute. -/
structure SyncStrategy (G : Game X X A A) where
  d : ℕ
  d_pos : 0 < d
  P : PVM X A d

/-- The winning probability of a synchronous strategy: the players answer `(a, b)` to `(x, y)`
with probability `Tr(M^x_a M^y_b)/d`. -/
noncomputable def SyncStrategy.value {G : Game X X A A} (S : SyncStrategy G) : ℝ :=
  ∑ x, ∑ y, ∑ a, ∑ b,
    G.μ x y * (if G.D x y a b then 1 else 0) *
      ((S.P.M x a * S.P.M y b).trace.re / (S.d : ℝ))

/-- The synchronous value of a game: the supremum of the winning probability over all
synchronous strategies. It is at most the quantum value. -/
noncomputable def syncValue (G : Game X X A A) : ℝ :=
  ⨆ S : SyncStrategy G, S.value

/-! ## 3. Explicit games, the halting problem, and the halting reduction -/

/-- A first-order description of a game, so that computability of maps into games can be
stated. The question alphabet is `Fin (nX + 1)`, the answer alphabet `Fin (nA + 1)`; `w`
lists unnormalized natural-number weights `(x, y, weight)` of question pairs, and `acc` lists
the accepted tuples `(x, y, a, b)`. -/
structure GameData where
  nX : ℕ
  nA : ℕ
  w : List (ℕ × ℕ × ℕ)
  acc : List (ℕ × ℕ × ℕ × ℕ)

namespace GameData

/-- A description is a tuple of naturals and lists; this is its Gödel numbering. -/
def equivTuple :
    GameData ≃ ℕ × ℕ × List (ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ × ℕ) where
  toFun g := (g.nX, g.nA, g.w, g.acc)
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩

instance : Primcodable GameData := Primcodable.ofEquiv _ equivTuple

/-- The total weight of the question pair `(x, y)` in `w`. -/
def questionWeight (g : GameData) (x y : ℕ) : ℕ :=
  ((g.w.filter fun t => decide (t.1 = x ∧ t.2.1 = y)).map fun t => t.2.2).sum

/-- The total weight of the question pairs in the alphabet. -/
def totalWeight (g : GameData) : ℕ :=
  ∑ x : Fin (g.nX + 1), ∑ y : Fin (g.nX + 1), g.questionWeight x.val y.val

/-- The game described by `g`: the question distribution is `w` normalized (a point mass at
`(0, 0)` if the total weight is zero, so that every description is a game), and the accepted
tuples are those listed in `acc`, except that unequal answers to equal questions always lose.
So the game is synchronous, and is played by both players on the same alphabets. -/
noncomputable def toGame (g : GameData) :
    Game (Fin (g.nX + 1)) (Fin (g.nX + 1)) (Fin (g.nA + 1)) (Fin (g.nA + 1)) where
  μ x y :=
    if g.totalWeight = 0 then (if x = 0 ∧ y = 0 then 1 else 0)
    else (g.questionWeight x.val y.val : ℝ) / (g.totalWeight : ℝ)
  μ_nonneg x y := by
    split_ifs
    · norm_num
    · norm_num
    · positivity
  μ_sum_one := by
    by_cases h : g.totalWeight = 0
    · simp only [if_pos h]
      rw [Finset.sum_eq_single (0 : Fin (g.nX + 1))]
      · simp
      · intro b _ hb
        simp [hb]
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    · simp only [if_neg h]
      have hT : (g.totalWeight : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h
      have hsum : ∑ x : Fin (g.nX + 1), ∑ y : Fin (g.nX + 1),
          (g.questionWeight x.val y.val : ℝ) = (g.totalWeight : ℝ) := by
        unfold totalWeight
        push_cast
        rfl
      simp_rw [← Finset.sum_div]
      rw [hsum, div_self hT]
  D x y a b := if x = y ∧ a ≠ b then false else decide ((x.val, y.val, a.val, b.val) ∈ g.acc)

end GameData

/-- The partial recursive function with Gödel number `c` (Mathlib's `Nat.Partrec.Code`, a
model of computation equivalent to Turing machines) halts on the empty input, encoded as
`0`. -/
def HaltsOnEmptyInput (c : Nat.Partrec.Code) : Prop := (c.eval 0).Dom

/-- **The halting reduction** (Theorem 12.2 of "MIP* = RE"): a computable map from machines
to games such that a halting machine is sent to a game of value `1` and a non-halting one to
a game of value at most `1/2` — in the synchronous value and the quantum value alike, for one
and the same map. -/
theorem halting_reduces_to_value :
    ∃ g : Nat.Partrec.Code → GameData, Computable g ∧
      ∀ c : Nat.Partrec.Code,
        (HaltsOnEmptyInput c →
          syncValue (g c).toGame = 1 ∧ quantumValue (g c).toGame = 1) ∧
        (¬ HaltsOnEmptyInput c →
          syncValue (g c).toGame ≤ 1 / 2 ∧ quantumValue (g c).toGame ≤ 1 / 2) := by
  sorry

/-- **The synchronous value is uncomputable**: no computable function, given a game promised
to have synchronous value `1` or at most `1/2`, tells which. -/
theorem syncValue_uncomputable :
    ¬ ∃ f : GameData → Bool, Computable f ∧
      (∀ g, syncValue g.toGame = 1 → f g = true) ∧
      (∀ g, syncValue g.toGame ≤ 1 / 2 → f g = false) := by
  sorry

/-- **The quantum value is uncomputable**, in the same sense. -/
theorem quantumValue_uncomputable :
    ¬ ∃ f : GameData → Bool, Computable f ∧
      (∀ g, quantumValue g.toGame = 1 → f g = true) ∧
      (∀ g, quantumValue g.toGame ≤ 1 / 2 → f g = false) := by
  sorry

end

/-! ## 4. Recursively enumerable languages -/

/-- Binary strings, the `{0,1}*` of the paper. -/
abbrev BitStr := List Bool

/-- A language `L ⊆ {0,1}*` is recursively enumerable if it is the halting set of a partial
recursive function: some `c : Nat.Partrec.Code` halts on (the Gödel number of) `z` exactly
when `z ∈ L`. -/
def IsRE (L : Set BitStr) : Prop :=
  ∃ c : Nat.Partrec.Code, ∀ z : BitStr, z ∈ L ↔ (c.eval (Encodable.encode z)).Dom

/-! ## 5. Polynomial-time verifiers and the class `MIP*_{1,1/2}(2,1)`

### The model of computation

Programs act on binary trees. A program is a term of a first-order language with de Bruijn
variables: it reads a variable, builds a tree, takes a tree apart, binds a value, or iterates.
The semantics `Eval env p r t` says that `p`, run in the environment `env` (the values of the
variables), halts with result `r` at cost `t`. Every rule costs one unit, and reading a
variable or a literal additionally costs the size of the value read; so a run of cost `t`
produces a result of size at most `t`. -/

/-- Binary trees, the data of the model. Bits, strings, pairs are all encoded as trees. -/
inductive Data where
  | nil : Data
  | cons : Data → Data → Data
  deriving DecidableEq

namespace Data

/-- The size of a tree: its number of nodes. -/
def size : Data → ℕ
  | nil => 1
  | cons a b => a.size + b.size + 1

/-- Bits: `false ↦ nil`, `true ↦ cons nil nil`. -/
def ofBool : Bool → Data
  | false => nil
  | true => cons nil nil

/-- Bit strings: `cons`-chains of bits, ending in `nil`. -/
def ofBits : List Bool → Data
  | [] => nil
  | b :: l => cons (ofBool b) (ofBits l)

end Data

/-- Programs. Variables are de Bruijn indices: `var 0` is the innermost bound variable, and
the input of a program is `var 0`. -/
inductive Prog where
  /-- Read variable `i` (copying it: cost `1 + size`). -/
  | var (i : ℕ)
  /-- The atom. -/
  | nil
  /-- The literal tree `d` (cost `size d`). -/
  | const (d : Data)
  /-- Build a node from the values of `h` and `t`. -/
  | cons (h t : Prog)
  /-- Inspect variable `i` in place: if it is `nil`, run `n`; if it is `cons a b`, run `c`
  with `a` and `b` bound as variables `0` and `1`. -/
  | elim (i : ℕ) (n c : Prog)
  /-- Bind the value of `e` as variable `0` and run `b`. -/
  | let_ (e b : Prog)
  /-- Iterate `b` on the state held in variable `0`: `b` returns `cons flag s'`; if `flag`
  is `nil` the loop stops with result `s'`, otherwise it continues with state `s'`. (A body
  result `nil` stops with result `nil`.) -/
  | loop (b : Prog)
  deriving DecidableEq

namespace Prog

/-- `WellScoped n p`: every variable of `p` is bound in an environment of length `n`. A
program with `WellScoped 1` is closed: it reads nothing but its input. -/
def WellScoped : ℕ → Prog → Prop
  | n, var i => i < n
  | _, nil => True
  | _, const _ => True
  | n, cons h t => WellScoped n h ∧ WellScoped n t
  | n, elim i a c => i < n ∧ WellScoped n a ∧ WellScoped (n + 2) c
  | n, let_ e b => WellScoped n e ∧ WellScoped (n + 1) b
  | n, loop b => 0 < n ∧ WellScoped n b

end Prog

/-- Environments: the values of the variables, innermost (index `0`) first. -/
abbrev Env := List Data

/-- Variable lookup; a variable beyond the environment reads as `nil`. -/
def Env.get (env : Env) (i : ℕ) : Data := env.getD i .nil

/-- Timed big-step semantics: `Eval env p r t` means that `p`, in environment `env`, halts
with result `r` at cost `t`. One unit per rule; reading a variable or a literal additionally
costs the size of the value. -/
inductive Eval : Env → Prog → Data → ℕ → Prop
  | var (env : Env) (i : ℕ) : Eval env (.var i) (env.get i) ((env.get i).size + 1)
  | nil (env : Env) : Eval env .nil .nil 1
  | const (env : Env) (d : Data) : Eval env (.const d) d d.size
  | cons {env : Env} {h t : Prog} {a b : Data} {s u : ℕ} :
      Eval env h a s → Eval env t b u → Eval env (.cons h t) (.cons a b) (s + u + 1)
  | elim_nil {env : Env} {i : ℕ} {n c : Prog} {r : Data} {t : ℕ} :
      env.get i = .nil → Eval env n r t → Eval env (.elim i n c) r (t + 1)
  | elim_cons {env : Env} {i : ℕ} {n c : Prog} {a b r : Data} {t : ℕ} :
      env.get i = .cons a b → Eval (a :: b :: env) c r t → Eval env (.elim i n c) r (t + 1)
  | let_ {env : Env} {e b : Prog} {v r : Data} {s t : ℕ} :
      Eval env e v s → Eval (v :: env) b r t → Eval env (.let_ e b) r (s + t + 1)
  | loop_nil {env : Env} {b : Prog} {t : ℕ} :
      Eval env b .nil t → Eval env (.loop b) .nil (t + 1)
  | loop_stop {env : Env} {b : Prog} {r : Data} {t : ℕ} :
      Eval env b (.cons .nil r) t → Eval env (.loop b) r (t + 1)
  | loop_step {env : Env} {b : Prog} {x y v r : Data} {s t : ℕ} :
      Eval env b (.cons (.cons x y) v) s → Eval (v :: env.tail) (.loop b) r t →
      Eval env (.loop b) r (s + t + 1)

/-- `p` computes `r` from the input `x` at cost `t`. -/
def Prog.Runs (p : Prog) (x r : Data) (t : ℕ) : Prop := Eval [x] p r t

/-- `p` halts on the input `x` within cost `t`. -/
def Prog.HaltsWithin (p : Prog) (x : Data) (t : ℕ) : Prop :=
  ∃ r t', t' ≤ t ∧ Eval [x] p r t'

/-! ### Verifiers -/

/-- A polynomial-time verifier: a sampler program, a decider program, both closed, and one
polynomial `P` bounding their running times. Writing `B = P(|z|)` on the input `z`: the
sampler reads `(z, r)` for a uniformly random seed `r ∈ {0,1}^B` and outputs a question pair
`(x, y)`; the decider reads `(z, x, y, a, b)` and accepts by outputting the bit `1`. -/
structure PolyVerifier where
  sampler : Prog
  sampler_closed : sampler.WellScoped 1
  decider : Prog
  decider_closed : decider.WellScoped 1
  bound : Polynomial ℕ

namespace PolyVerifier

variable (V : PolyVerifier)

/-- The bound `B = P(|z|)`: the seed length, and the length of the questions and answers of
the game on `z`. -/
def B (z : BitStr) : ℕ := V.bound.eval z.length

/-- The sampler, on the input `z` and the seed `r`, halts with the question pair `(x, y)`. -/
def SamplerOutputs (z r x y : BitStr) : Prop :=
  ∃ t, V.sampler.Runs (.cons (.ofBits z) (.ofBits r)) (.cons (.ofBits x) (.ofBits y)) t

/-- The decider accepts `(z, x, y, a, b)`: it halts with output `1`. -/
def Accepts (z x y a b : BitStr) : Prop :=
  ∃ t, V.decider.Runs
    (.cons (.ofBits z) (.cons (.ofBits x) (.cons (.ofBits y) (.cons (.ofBits a) (.ofBits b)))))
    (.ofBool true) t

/-- **Efficiency** on the input `z`: the sampler, on every seed of length `B`, halts within
cost `P(|z| + |r|)` with a pair of strings of length at most `B`; the decider halts within cost
`P(|z| + |x| + |y| + |a| + |b|)` on every input, and rejects whenever one of `x, y, a, b` is
longer than `B`. (Time is polynomial in the total input length because a program reads a
string only by walking it; with `|r| = B` and the messages cut at `B`, this is `poly(|z|)`.) -/
structure Efficient (z : BitStr) : Prop where
  sampler_runs : ∀ r : BitStr, r.length = V.B z →
    ∃ (x y : BitStr) (t : ℕ), t ≤ V.bound.eval (z.length + r.length) ∧
      x.length ≤ V.B z ∧ y.length ≤ V.B z ∧
      V.sampler.Runs (.cons (.ofBits z) (.ofBits r)) (.cons (.ofBits x) (.ofBits y)) t
  decider_time : ∀ x y a b : BitStr,
    V.decider.HaltsWithin
      (.cons (.ofBits z) (.cons (.ofBits x) (.cons (.ofBits y) (.cons (.ofBits a) (.ofBits b)))))
      (V.bound.eval (z.length + x.length + y.length + a.length + b.length))
  rejects_long : ∀ x y a b : BitStr,
    V.B z < x.length ∨ V.B z < y.length ∨ V.B z < a.length ∨ V.B z < b.length →
      ¬ V.Accepts z x y a b

end PolyVerifier

/-- The strings of length at most `n`: the question and answer alphabet of a verifier's game. -/
def Str (n : ℕ) : Type := {s : BitStr // s.length ≤ n}

instance (n : ℕ) : Finite (Str n) := (List.finite_length_le Bool n).to_subtype

noncomputable instance (n : ℕ) : Fintype (Str n) := Fintype.ofFinite _

/-- The seeds of length `n`, each of probability `2⁻ⁿ`. -/
abbrev Seed (n : ℕ) : Type := List.Vector Bool n

open Classical in
/-- **The class `MIP*_{1,1/2}(2,1)`.** A language `L ⊆ {0,1}*` is in it if some polynomial-time
verifier is efficient on every input `z`, and its game on `z` — the game on the strings of
length at most `B = P(|z|)` whose question distribution is the law of the sampler's output on
a uniform seed of length `B` and whose decision predicate is the decider's — has quantum value
`1` when `z ∈ L` and at most `1/2` when `z ∉ L`. -/
def MIPStar (L : Set BitStr) : Prop :=
  ∃ V : PolyVerifier, ∀ z : BitStr, V.Efficient z ∧
    ∃ G : Game (Str (V.B z)) (Str (V.B z)) (Str (V.B z)) (Str (V.B z)),
      (∀ x y, G.μ x y =
        ((Finset.univ.filter fun r : Seed (V.B z) => V.SamplerOutputs z r.1 x.1 y.1).card : ℝ)
          / 2 ^ V.B z) ∧
      (∀ x y a b, G.D x y a b = decide (V.Accepts z x.1 y.1 a.1 b.1)) ∧
      (z ∈ L → quantumValue G = 1) ∧
      (z ∉ L → quantumValue G ≤ 1 / 2)

/-- **`MIP* = RE`.** -/
theorem mipstar_eq_re : MIPStar = IsRE := by
  sorry

end MIPRE.Palomar

end
