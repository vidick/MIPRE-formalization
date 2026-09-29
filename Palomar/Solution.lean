/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import Palomar.Bridge

@[expose] public section

/-!
# MIP* = RE — the Palomar Solution

The same declarations as `Palomar/Challenge.lean`, proved. Every definition of the Challenge is
repeated here verbatim (Palomar's comparator matches the Challenge's declarations with this
file's by name, so this file declares them itself and imports nothing that does), and the four
theorems are proved by transport from the library: `halting_reduces_to_value` from
`MIPRE.Halting.halting_reduction_both_of`, `syncValue_uncomputable` and
`quantumValue_uncomputable` from `MIPRE.Halting.gameValue_uncomputable` and
`MIPRE.Halting.quantumValue_uncomputable`, and `mipstar_eq_re` from
`MIPRE.Halting.mipstar_eq_re`, all of `MIPRE/MainTheorem.lean`.

The transport is in the two sections marked "Transport to the library": structural maps
between the Challenge's types and the library's — games, measurements, strategies and game
descriptions in the first; trees, programs, the timed semantics, verifiers and the class in the
second — with the values, the running-time predicates and the class carried across. Nothing in
them is mathematical: the Challenge's structures are, field for field, the library's
(`planning/palomar-challenge.md`, section 2). What the library proves in its own vocabulary is
restated in the Challenge's shape in `Palomar/Bridge.lean`.

A diff against the Challenge shows the header, these insertions and the four proofs, and
nothing else.
-/

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

/-! ### Transport to the library: games, strategies, values

The Challenge's `Game`, `PVM`, `TensorStrategy` and `SyncStrategy` are, field for field,
`MIPRE.Game`, `MIPRE.ProjectiveMeasurement`, `MIPRE.TensorProductStrategy` and
`MIPRE.SyncStrategy`, and `GameData` is `HaltingGameValue.GameData`. The maps below identify
them and carry the two values across. -/

/-- The Challenge's game, as a game of the library. -/
def Game.toLib (G : Game X Y A B) : MIPRE.Game X Y A B where
  μ := G.μ
  μ_nonneg := G.μ_nonneg
  μ_sum_one := G.μ_sum_one
  D := G.D

/-- A game of the library, as a game of the Challenge. -/
def Game.ofLib (G : MIPRE.Game X Y A B) : Game X Y A B where
  μ := G.μ
  μ_nonneg := G.μ_nonneg
  μ_sum_one := G.μ_sum_one
  D := G.D

/-- A projective measurement family of the Challenge, as one of the library. -/
def PVM.toLib {d : ℕ} (P : PVM X A d) :
    MIPRE.ProjectiveMeasurement X A (Matrix (Fin d) (Fin d) ℂ) where
  M := P.M
  selfAdjoint := P.selfAdjoint
  projective := P.projective
  normalized := P.normalized

/-- A projective measurement family of the library on `ℂ^d`, as one of the Challenge. -/
def PVM.ofLib {d : ℕ} (P : MIPRE.ProjectiveMeasurement X A (Matrix (Fin d) (Fin d) ℂ)) :
    PVM X A d where
  M := P.M
  selfAdjoint := P.selfAdjoint
  projective := P.projective
  normalized := P.normalized

/-- Tensor-product strategies of the Challenge and of the library correspond. -/
def TensorStrategy.equivLib (G : Game X Y A B) :
    TensorStrategy G ≃ MIPRE.TensorProductStrategy G.toLib where
  toFun S := ⟨S.dA, S.dB, S.ψ, S.ψ_unit, S.PA.toLib, S.PB.toLib⟩
  invFun S := ⟨S.dA, S.dB, S.ψ, S.ψ_unit, PVM.ofLib S.PA, PVM.ofLib S.PB⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The correspondence preserves the winning probability (the same Born-rule formula). -/
theorem TensorStrategy.value_equivLib (G : Game X Y A B) (S : TensorStrategy G) :
    (TensorStrategy.equivLib G S).value = S.value := rfl

/-- The quantum value of the Challenge is the library's. -/
theorem quantumValue_toLib (G : Game X Y A B) :
    MIPRE.quantumValue G.toLib = quantumValue G :=
  ((iSup_congr fun S => (TensorStrategy.value_equivLib G S).symm).trans
    (TensorStrategy.equivLib G).iSup_comp).symm

/-- The quantum value of a game of the library, read in the Challenge, is unchanged. -/
theorem quantumValue_ofLib (G : MIPRE.Game X Y A B) :
    quantumValue (Game.ofLib G) = MIPRE.quantumValue G :=
  (quantumValue_toLib (Game.ofLib G)).symm

/-- A game description of the library, read as one of the Challenge: the same tuple. -/
def GameData.ofLib (d : HaltingGameValue.GameData) : GameData := ⟨d.nX, d.nA, d.w, d.acc⟩

/-- Reading a description across is computable: both `Primcodable` instances are the
Gödel numbering of the tuple. -/
theorem GameData.computable_ofLib : Computable GameData.ofLib :=
  (((Primrec.of_equiv_symm (e := GameData.equivTuple)).comp
    (Primrec.of_equiv (e := HaltingGameValue.GameData.equivTuple))).to_comp).of_eq
    fun _ => rfl

/-- Synchronous strategies of the Challenge's game of a description and of the library's
synchronous reading of it correspond. -/
def GameData.syncEquiv (d : HaltingGameValue.GameData) :
    SyncStrategy (GameData.ofLib d).toGame ≃ MIPRE.SyncStrategy d.syncGame where
  toFun S := ⟨S.d, S.d_pos, S.P.toLib⟩
  invFun S := ⟨S.d, S.d_pos, PVM.ofLib S.P⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The correspondence preserves the winning probability (`MIPRE.SyncStrategy.value_eq` is the
Challenge's formula). -/
theorem GameData.value_syncEquiv (d : HaltingGameValue.GameData)
    (S : SyncStrategy (GameData.ofLib d).toGame) :
    (GameData.syncEquiv d S).value = S.value := by
  rw [MIPRE.SyncStrategy.value_eq]
  rfl

/-- The synchronous value of the Challenge is the value `HaltingGameValue.gameValue` of the
library's headline, through `MIPRE.syncValue`. -/
theorem GameData.syncValue_ofLib (d : HaltingGameValue.GameData) :
    syncValue (GameData.ofLib d).toGame = HaltingGameValue.gameValue d.toGame := by
  rw [HaltingGameValue.GameData.gameValue_eq_syncValue]
  exact (iSup_congr fun S => (GameData.value_syncEquiv d S).symm).trans
    (GameData.syncEquiv d).iSup_comp

/-- The quantum value of the Challenge's game of a description is the library's. -/
theorem GameData.quantumValue_ofLib (d : HaltingGameValue.GameData) :
    quantumValue (GameData.ofLib d).toGame = MIPRE.quantumValue d.game :=
  (quantumValue_toLib (GameData.ofLib d).toGame).symm

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
  obtain ⟨g, hg, h⟩ := Bridge.halting_reduction_both
  refine ⟨fun c => GameData.ofLib (g c), GameData.computable_ofLib.comp hg,
    fun c => ⟨fun hc => ?_, fun hc => ?_⟩⟩
  · rw [GameData.syncValue_ofLib, GameData.quantumValue_ofLib]
    exact (h c).1 hc
  · rw [GameData.syncValue_ofLib, GameData.quantumValue_ofLib]
    exact (h c).2 hc

/-- **The synchronous value is uncomputable**: no computable function, given a game promised
to have synchronous value `1` or at most `1/2`, tells which. -/
theorem syncValue_uncomputable :
    ¬ ∃ f : GameData → Bool, Computable f ∧
      (∀ g, syncValue g.toGame = 1 → f g = true) ∧
      (∀ g, syncValue g.toGame ≤ 1 / 2 → f g = false) := by
  rintro ⟨f, hf, h1, h2⟩
  refine MIPRE.Halting.gameValue_uncomputable
    ⟨fun d => f (GameData.ofLib d), hf.comp GameData.computable_ofLib, fun d hd => ?_,
      fun d hd => ?_⟩
  · exact h1 _ (by rw [GameData.syncValue_ofLib]; exact hd)
  · exact h2 _ (by rw [GameData.syncValue_ofLib]; exact hd)

/-- **The quantum value is uncomputable**, in the same sense. -/
theorem quantumValue_uncomputable :
    ¬ ∃ f : GameData → Bool, Computable f ∧
      (∀ g, quantumValue g.toGame = 1 → f g = true) ∧
      (∀ g, quantumValue g.toGame ≤ 1 / 2 → f g = false) := by
  rintro ⟨f, hf, h1, h2⟩
  refine MIPRE.Halting.quantumValue_uncomputable
    ⟨fun d => f (GameData.ofLib d), hf.comp GameData.computable_ofLib, fun d hd => ?_,
      fun d hd => ?_⟩
  · exact h1 _ (by rw [GameData.quantumValue_ofLib]; exact hd)
  · exact h2 _ (by rw [GameData.quantumValue_ofLib]; exact hd)

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

/-! ### Transport to the library: the model of computation, verifiers, the class

The Challenge's `Data`, `Prog`, `Eval`, `Prog.Runs` and `Prog.HaltsWithin` are the text of
`MIPRE.Cost.Data`, `MIPRE.Cost.Prog`, `MIPRE.Cost.Eval`, `MIPRE.Cost.Prog.Runs` and
`MIPRE.Cost.HaltsWithin`, its `PolyVerifier` and `Efficient` those of `MIPRE.PolyVerifier` with
the encodings written out, and `IsRE` the halting-set form of `MIPRE.IsRE`. The maps below
identify the inductive types (structurally, in both directions), carry the semantics across by
induction on derivations, and then the verifier predicates and the class. -/

namespace Data

/-- The Challenge's trees, as the library's. -/
def toLib : Data → Cost.Data
  | nil => .nil
  | cons a b => .cons a.toLib b.toLib

/-- The library's trees, as the Challenge's. -/
def ofLib : Cost.Data → Data
  | .nil => nil
  | .cons a b => cons (ofLib a) (ofLib b)

@[simp] theorem toLib_nil : toLib nil = .nil := rfl
@[simp] theorem toLib_cons (a b : Data) : toLib (cons a b) = .cons a.toLib b.toLib := rfl
@[simp] theorem ofLib_nil : ofLib .nil = nil := rfl
@[simp] theorem ofLib_cons (a b : Cost.Data) : ofLib (.cons a b) = cons (ofLib a) (ofLib b) :=
  rfl

@[simp] theorem ofLib_toLib : ∀ d : Data, ofLib d.toLib = d
  | nil => rfl
  | cons a b => by rw [toLib_cons, ofLib_cons, ofLib_toLib a, ofLib_toLib b]

@[simp] theorem toLib_ofLib : ∀ d : Cost.Data, (ofLib d).toLib = d
  | .nil => rfl
  | .cons a b => by rw [ofLib_cons, toLib_cons, toLib_ofLib a, toLib_ofLib b]

@[simp] theorem size_toLib : ∀ d : Data, d.toLib.size = d.size
  | nil => rfl
  | cons a b => by rw [toLib_cons, Cost.Data.size_cons, size, size_toLib a, size_toLib b]

@[simp] theorem size_ofLib : ∀ d : Cost.Data, (ofLib d).size = d.size
  | .nil => rfl
  | .cons a b => by rw [ofLib_cons, size, Cost.Data.size_cons, size_ofLib a, size_ofLib b]

/-- The Challenge's bits are the library's. -/
@[simp] theorem toLib_ofBool (b : Bool) : (ofBool b).toLib = Cost.encode b := by
  cases b <;> rfl

/-- The Challenge's bit strings are the library's encoding of bit strings. -/
@[simp] theorem toLib_ofBits : ∀ l : List Bool, (ofBits l).toLib = Cost.encode l
  | [] => rfl
  | b :: l => by rw [ofBits, toLib_cons, toLib_ofBool, toLib_ofBits l]; rfl

end Data

theorem Env.get_map_toLib (env : Env) (i : ℕ) :
    Cost.Env.get (env.map Data.toLib) i = (Env.get env i).toLib := by
  show (env.map Data.toLib).getD i (Data.toLib .nil) = Data.toLib (env.getD i .nil)
  exact List.getD_map _ _ _

theorem Env.get_map_ofLib (env : Cost.Env) (i : ℕ) :
    Env.get (env.map Data.ofLib) i = Data.ofLib (Cost.Env.get env i) := by
  show (env.map Data.ofLib).getD i (Data.ofLib .nil) = Data.ofLib (env.getD i .nil)
  exact List.getD_map _ _ _

namespace Prog

/-- The Challenge's programs, as the library's. -/
def toLib : Prog → Cost.Prog
  | var i => .var i
  | nil => .nil
  | const d => .const d.toLib
  | cons h t => .cons h.toLib t.toLib
  | elim i n c => .elim i n.toLib c.toLib
  | let_ e b => .let_ e.toLib b.toLib
  | loop b => .loop b.toLib

/-- The library's programs, as the Challenge's. -/
def ofLib : Cost.Prog → Prog
  | .var i => var i
  | .nil => nil
  | .const d => const (Data.ofLib d)
  | .cons h t => cons (ofLib h) (ofLib t)
  | .elim i n c => elim i (ofLib n) (ofLib c)
  | .let_ e b => let_ (ofLib e) (ofLib b)
  | .loop b => loop (ofLib b)

@[simp] theorem toLib_ofLib : ∀ p : Cost.Prog, (ofLib p).toLib = p
  | .var _ => rfl
  | .nil => rfl
  | .const d => by simp [ofLib, toLib]
  | .cons h t => by simp [ofLib, toLib, toLib_ofLib h, toLib_ofLib t]
  | .elim i n c => by simp [ofLib, toLib, toLib_ofLib n, toLib_ofLib c]
  | .let_ e b => by simp [ofLib, toLib, toLib_ofLib e, toLib_ofLib b]
  | .loop b => by simp [ofLib, toLib, toLib_ofLib b]

@[simp] theorem ofLib_toLib : ∀ p : Prog, ofLib p.toLib = p
  | var _ => rfl
  | nil => rfl
  | const d => by simp [ofLib, toLib]
  | cons h t => by simp [ofLib, toLib, ofLib_toLib h, ofLib_toLib t]
  | elim i n c => by simp [ofLib, toLib, ofLib_toLib n, ofLib_toLib c]
  | let_ e b => by simp [ofLib, toLib, ofLib_toLib e, ofLib_toLib b]
  | loop b => by simp [ofLib, toLib, ofLib_toLib b]

/-- Well-scopedness is the same predicate on both sides. -/
theorem wellScoped_toLib : ∀ (n : ℕ) (p : Prog), p.toLib.WellScoped n ↔ p.WellScoped n
  | _, var _ => Iff.rfl
  | _, nil => Iff.rfl
  | _, const _ => Iff.rfl
  | n, cons h t => and_congr (wellScoped_toLib n h) (wellScoped_toLib n t)
  | n, elim _ a c =>
    and_congr Iff.rfl (and_congr (wellScoped_toLib n a) (wellScoped_toLib (n + 2) c))
  | n, let_ e b => and_congr (wellScoped_toLib n e) (wellScoped_toLib (n + 1) b)
  | n, loop b => and_congr Iff.rfl (wellScoped_toLib n b)

theorem wellScoped_ofLib (n : ℕ) (p : Cost.Prog) : (ofLib p).WellScoped n ↔ p.WellScoped n := by
  rw [← wellScoped_toLib, toLib_ofLib]

end Prog

/-- A run of the Challenge's semantics is a run of the library's, with the same cost. -/
theorem Eval.toLib {env : Env} {p : Prog} {r : Data} {t : ℕ} (h : Eval env p r t) :
    Cost.Eval (env.map Data.toLib) p.toLib r.toLib t := by
  induction h with
  | var env i =>
    have := Cost.Eval.var (env.map Data.toLib) i
    rwa [Env.get_map_toLib, Data.size_toLib] at this
  | nil env => exact .nil _
  | const env d =>
    have := Cost.Eval.const (env.map Data.toLib) d.toLib
    rwa [Data.size_toLib] at this
  | cons _ _ ih₁ ih₂ => exact .cons ih₁ ih₂
  | elim_nil hn _ ih => exact .elim_nil (by rw [Env.get_map_toLib, hn, Data.toLib_nil]) ih
  | elim_cons hc _ ih => exact .elim_cons (by rw [Env.get_map_toLib, hc, Data.toLib_cons]) ih
  | let_ _ _ ih₁ ih₂ => exact .let_ ih₁ ih₂
  | loop_nil _ ih => exact .loop_nil ih
  | loop_stop _ ih => exact .loop_stop ih
  | loop_step _ _ ih₁ ih₂ =>
    refine .loop_step ih₁ ?_
    rw [← List.map_tail]
    exact ih₂

/-- A run of the library's semantics is a run of the Challenge's, with the same cost. -/
theorem eval_ofLib {env : Cost.Env} {p : Cost.Prog} {r : Cost.Data} {t : ℕ}
    (h : Cost.Eval env p r t) :
    Eval (env.map Data.ofLib) (Prog.ofLib p) (Data.ofLib r) t := by
  induction h with
  | var env i =>
    have := Eval.var (env.map Data.ofLib) i
    rwa [Env.get_map_ofLib, Data.size_ofLib] at this
  | nil env => exact .nil _
  | const env d =>
    have := Eval.const (env.map Data.ofLib) (Data.ofLib d)
    rwa [Data.size_ofLib] at this
  | cons _ _ ih₁ ih₂ => exact .cons ih₁ ih₂
  | elim_nil hn _ ih => exact .elim_nil (by rw [Env.get_map_ofLib, hn, Data.ofLib_nil]) ih
  | elim_cons hc _ ih => exact .elim_cons (by rw [Env.get_map_ofLib, hc, Data.ofLib_cons]) ih
  | let_ _ _ ih₁ ih₂ => exact .let_ ih₁ ih₂
  | loop_nil _ ih => exact .loop_nil ih
  | loop_stop _ ih => exact .loop_stop ih
  | loop_step _ _ ih₁ ih₂ =>
    refine .loop_step ih₁ ?_
    rw [← List.map_tail]
    exact ih₂

/-- The two semantics agree. -/
theorem eval_iff {env : Env} {p : Prog} {r : Data} {t : ℕ} :
    Eval env p r t ↔ Cost.Eval (env.map Data.toLib) p.toLib r.toLib t := by
  refine ⟨Eval.toLib, fun h => ?_⟩
  have h' := eval_ofLib h
  rwa [List.map_map, Prog.ofLib_toLib, Data.ofLib_toLib,
    List.map_id'' (f := Data.ofLib ∘ Data.toLib) (fun d => Data.ofLib_toLib d)] at h'

theorem Prog.runs_iff (p : Prog) (x r : Data) (t : ℕ) :
    p.Runs x r t ↔ p.toLib.Runs x.toLib r.toLib t :=
  eval_iff

theorem Prog.haltsWithin_iff (p : Prog) (x : Data) (t : ℕ) :
    p.HaltsWithin x t ↔ Cost.HaltsWithin p.toLib x.toLib t := by
  constructor
  · rintro ⟨r, t', ht, h⟩
    exact ⟨r.toLib, t', ht, eval_iff.1 h⟩
  · rintro ⟨r, t', ht, h⟩
    refine ⟨Data.ofLib r, t', ht, eval_iff.2 ?_⟩
    rwa [Data.toLib_ofLib]

namespace PolyVerifier

/-- The Challenge's verifier, as the library's. -/
def toLib (V : PolyVerifier) : MIPRE.PolyVerifier where
  sampler := V.sampler.toLib
  sampler_closed := (Prog.wellScoped_toLib 1 V.sampler).2 V.sampler_closed
  decider := V.decider.toLib
  decider_closed := (Prog.wellScoped_toLib 1 V.decider).2 V.decider_closed
  bound := V.bound

/-- The library's verifier, as the Challenge's. -/
def ofLib (V : MIPRE.PolyVerifier) : PolyVerifier where
  sampler := Prog.ofLib V.sampler
  sampler_closed := (Prog.wellScoped_ofLib 1 V.sampler).2 V.sampler_closed
  decider := Prog.ofLib V.decider
  decider_closed := (Prog.wellScoped_ofLib 1 V.decider).2 V.decider_closed
  bound := V.bound

@[simp] theorem toLib_ofLib (V : MIPRE.PolyVerifier) : (ofLib V).toLib = V := by
  cases V
  simp [toLib, ofLib]

@[simp] theorem toLib_sampler (V : PolyVerifier) : V.toLib.sampler = V.sampler.toLib := rfl
@[simp] theorem toLib_decider (V : PolyVerifier) : V.toLib.decider = V.decider.toLib := rfl
@[simp] theorem toLib_bound (V : PolyVerifier) : V.toLib.bound = V.bound := rfl
@[simp] theorem B_toLib (V : PolyVerifier) (z : BitStr) : V.toLib.B z = V.B z := rfl
@[simp] theorem B_ofLib (V : MIPRE.PolyVerifier) (z : BitStr) : (ofLib V).B z = V.B z := rfl

/-- A run of the sampler, read in the library. -/
theorem sampler_runs_iff (V : PolyVerifier) (z r x y : BitStr) (t : ℕ) :
    V.sampler.Runs (.cons (.ofBits z) (.ofBits r)) (.cons (.ofBits x) (.ofBits y)) t ↔
      V.toLib.sampler.Runs (Cost.encode (z, r)) (Cost.encode (x, y)) t := by
  simp only [Prog.runs_iff, Data.toLib_cons, Data.toLib_ofBits, toLib_sampler, Cost.encode_prod]

/-- The sampler's output, read in the library. -/
theorem samplerOutputs_iff (V : PolyVerifier) (z r x y : BitStr) :
    V.SamplerOutputs z r x y ↔
      ∃ t, V.toLib.sampler.Runs (Cost.encode (z, r)) (Cost.encode (x, y)) t := by
  simp only [SamplerOutputs, sampler_runs_iff]

/-- The decider's time bound, read in the library. -/
theorem decider_haltsWithin_iff (V : PolyVerifier) (z x y a b : BitStr) (T : ℕ) :
    V.decider.HaltsWithin
        (.cons (.ofBits z) (.cons (.ofBits x) (.cons (.ofBits y) (.cons (.ofBits a) (.ofBits b)))))
        T ↔
      Cost.HaltsWithin V.toLib.decider (Cost.encode (z, x, y, a, b)) T := by
  simp only [Prog.haltsWithin_iff, Data.toLib_cons, Data.toLib_ofBits, toLib_decider,
    Cost.encode_prod]

/-- Acceptance, read in the library. -/
theorem accepts_iff (V : PolyVerifier) (z x y a b : BitStr) :
    V.Accepts z x y a b ↔ V.toLib.Accepts z x y a b := by
  simp only [Accepts, MIPRE.PolyVerifier.Accepts, Prog.runs_iff, Data.toLib_cons,
    Data.toLib_ofBits, Data.toLib_ofBool, toLib_decider, Cost.encode_prod]

/-- Efficiency, read in the library. -/
theorem efficient_iff (V : PolyVerifier) (z : BitStr) : V.Efficient z ↔ V.toLib.Efficient z := by
  constructor
  · intro h
    refine ⟨fun r hr => ?_, fun x y a b => ?_, fun x y a b hl => ?_⟩
    · obtain ⟨x, y, t, ht, hx, hy, hrun⟩ := h.sampler_runs r hr
      exact ⟨x, y, t, ht, hx, hy, (sampler_runs_iff V z r x y t).1 hrun⟩
    · exact (decider_haltsWithin_iff V z x y a b _).1 (h.decider_time x y a b)
    · exact (accepts_iff V z x y a b).not.1 (h.rejects_long x y a b hl)
  · intro h
    refine ⟨fun r hr => ?_, fun x y a b => ?_, fun x y a b hl => ?_⟩
    · obtain ⟨x, y, t, ht, hx, hy, hrun⟩ := h.sampler_runs r hr
      exact ⟨x, y, t, ht, hx, hy, (sampler_runs_iff V z r x y t).2 hrun⟩
    · exact (decider_haltsWithin_iff V z x y a b _).2 (h.decider_time x y a b)
    · exact (accepts_iff V z x y a b).not.2 (h.rejects_long x y a b hl)

theorem accepts_ofLib (V : MIPRE.PolyVerifier) (z x y a b : BitStr) :
    (ofLib V).Accepts z x y a b ↔ V.Accepts z x y a b := by
  rw [accepts_iff, toLib_ofLib]

theorem efficient_ofLib (V : MIPRE.PolyVerifier) (z : BitStr) :
    (ofLib V).Efficient z ↔ V.Efficient z := by
  rw [efficient_iff, toLib_ofLib]

open Classical in
/-- The seeds producing a question pair, read in the library. -/
theorem filter_samplerOutputs (V : PolyVerifier) (z x y : BitStr) :
    (Finset.univ.filter fun r : Seed (V.B z) => V.SamplerOutputs z r.1 x y) =
      Finset.univ.filter fun r : List.Vector Bool (V.B z) =>
        ∃ t, V.toLib.sampler.Runs (Cost.encode (z, r.1)) (Cost.encode (x, y)) t :=
  Finset.filter_congr fun r _ => samplerOutputs_iff V z r.1 x y

end PolyVerifier

/-- Recursive enumerability, read in the library (`MIPRE.IsRE`, Mathlib's `REPred`). -/
theorem isRE_iff (L : Set BitStr) : IsRE L ↔ MIPRE.IsRE L :=
  (Bridge.isRE_iff_exists_code L).symm

/-- The class, read in the library: the Challenge characterizes the verifier's game and the
library constructs it (`MIPRE.PolyVerifier.game`); `Bridge.mipstar_iff` identifies the two. -/
theorem mipStar_iff (L : Set BitStr) : MIPStar L ↔ MIPRE.MIPStar L := by
  rw [Bridge.mipstar_iff]
  constructor
  · rintro ⟨V, h⟩
    refine ⟨V.toLib, fun z => ?_⟩
    obtain ⟨hE, G, hμ, hD, h1, h2⟩ := h z
    refine ⟨(PolyVerifier.efficient_iff V z).1 hE, G.toLib, fun x y => ?_, fun x y a b => ?_,
      ?_, ?_⟩
    · show G.μ x y = _
      rw [hμ x y, PolyVerifier.filter_samplerOutputs]
      rfl
    · show G.D x y a b = _
      rw [hD x y a b]
      exact decide_eq_decide.2 (PolyVerifier.accepts_iff V z x.1 y.1 a.1 b.1)
    · exact fun hz => (quantumValue_toLib G).trans (h1 hz)
    · exact fun hz => (quantumValue_toLib G).trans_le (h2 hz)
  · rintro ⟨V, h⟩
    refine ⟨PolyVerifier.ofLib V, fun z => ?_⟩
    obtain ⟨hE, G, hμ, hD, h1, h2⟩ := h z
    refine ⟨(PolyVerifier.efficient_ofLib V z).2 hE, Game.ofLib G, fun x y => ?_,
      fun x y a b => ?_, ?_, ?_⟩
    · show G.μ x y = _
      rw [hμ x y, PolyVerifier.filter_samplerOutputs, PolyVerifier.toLib_ofLib]
      rfl
    · show G.D x y a b = _
      rw [hD x y a b]
      exact decide_eq_decide.2 (PolyVerifier.accepts_ofLib V z x.1 y.1 a.1 b.1).symm
    · exact fun hz => (quantumValue_ofLib G).trans (h1 hz)
    · exact fun hz => (quantumValue_ofLib G).trans_le (h2 hz)

/-- **`MIP* = RE`.** -/
theorem mipstar_eq_re : MIPStar = IsRE := by
  funext L
  exact propext ((mipStar_iff L).trans
    ((congrFun MIPRE.Halting.mipstar_eq_re L).to_iff.trans (isRE_iff L).symm))

end MIPRE.Palomar

end
