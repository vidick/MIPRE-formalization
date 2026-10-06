/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.SAT.Succinct
public import MIPRE.Foundations.Cost.Fold

@[expose] public section

/-!
# Succinct decoupled 6SAT descriptions of deciders with three input windows: the statement

Paper II's `prop:explicit-padded-succinct-deciders` (II:8675, a proof sketch), in the form the
Aldous–Lyons track's answer reduction needs (`planning/aldous-lyons-track.md`, slice P4g). Its
output indicator `L*` reads three strings — the two readable answers and the encoding `O` of the
decoupled linear system — and the PCP must hold each of them in its own block of variables: the
isolated player `B`, compared with the second, cannot hold a block containing `O`, which depends
on both readable answers. `lem:decoupled-5sat` (`MIPRE.SAT.DecoupledDescriber`) has two answer
blocks; this statement has three *windows*.

A decider reads `(n, x, y, a, b)`; the tableau of `thm:succinct-sat` has the tape encoding of `a`
on its variables `[0, 2T)` and that of `b` on `[2T, 4T)`. The describer outputs a circuit with
three index inputs of lengths `ℓa, ℓb, ℓc`, three of length `r` and six signs, describing a
decoupled 6SAT formula (`Circuit.formula6`) on blocks of `2^ℓa`, `2^ℓb`, `2^ℓc` and three times
`2^r` variables, such that three tables `A, B, C` extend to a satisfying 6-tuple exactly when
there are strings `a, b` of length at most `T` that the decider accepts within cost `T`, with `A`
and `C` the consecutive windows of lengths `2^ℓa` and `2^ℓc` at the start of the tape encoding
of `a`, and `B` the first `2^ℓb` bits of that of `b` (`Circuit.DescribesWindows`). The third
window starts at `2^ℓa`, a power of two, so that the describer computes its offset without
binary addition. `L*` reads `a = a^R ++ O` and `b = b^R`. A decider that
accepts only strings filling their windows exactly is then described completely by the windows:
that is how `L*`, which checks the lengths of its inputs, is used.

The window lengths are inputs, in unary, since a polynomial-time program must be polynomial in
its input on every input; the answer reduction computes them from its parameters.
-/

namespace MIPRE.SAT

open Cost Cost.PolyTimeFun

/-! ## Decoupled 6SAT -/

/-- A decoupled 6SAT clause: one literal from each of six blocks. -/
structure Clause6 (V₁ V₂ V₃ V₄ V₅ V₆ : Type*) where
  l₁ : Lit V₁
  l₂ : Lit V₂
  l₃ : Lit V₃
  l₄ : Lit V₄
  l₅ : Lit V₅
  l₆ : Lit V₆

/-- The value of a decoupled clause on six assignments. -/
def Clause6.eval {V₁ V₂ V₃ V₄ V₅ V₆ : Type*} (w₁ : V₁ → Bool) (w₂ : V₂ → Bool)
    (w₃ : V₃ → Bool) (w₄ : V₄ → Bool) (w₅ : V₅ → Bool) (w₆ : V₆ → Bool)
    (c : Clause6 V₁ V₂ V₃ V₄ V₅ V₆) : Bool :=
  c.l₁.eval w₁ || c.l₂.eval w₂ || c.l₃.eval w₃ || c.l₄.eval w₄ || c.l₅.eval w₅ || c.l₆.eval w₆

/-- A decoupled 6SAT formula. -/
abbrev Cnf6 (V₁ V₂ V₃ V₄ V₅ V₆ : Type*) := Set (Clause6 V₁ V₂ V₃ V₄ V₅ V₆)

/-- The six assignments satisfy every clause of `φ`. -/
def Cnf6.Sat {V₁ V₂ V₃ V₄ V₅ V₆ : Type*} (φ : Cnf6 V₁ V₂ V₃ V₄ V₅ V₆) (w₁ : V₁ → Bool)
    (w₂ : V₂ → Bool) (w₃ : V₃ → Bool) (w₄ : V₄ → Bool) (w₅ : V₅ → Bool) (w₆ : V₆ → Bool) :
    Prop :=
  ∀ c ∈ φ, c.eval w₁ w₂ w₃ w₄ w₅ w₆ = true

/-- The blocks of a decoupled clause of the describer: three windows, three witness blocks. -/
abbrev Clause6W (ℓa ℓb ℓc r : ℕ) : Type :=
  Clause6 (Fin (2 ^ ℓa)) (Fin (2 ^ ℓb)) (Fin (2 ^ ℓc)) (Fin (2 ^ r)) (Fin (2 ^ r)) (Fin (2 ^ r))

/-- The input bits presenting a decoupled clause: the three window indices, the three witness
indices, then the six signs. -/
def clauseInput6 (ℓa ℓb ℓc r : ℕ) (c : Clause6W ℓa ℓb ℓc r) : List Bool :=
  bitsOfNat ℓa c.l₁.var ++ bitsOfNat ℓb c.l₂.var ++ bitsOfNat ℓc c.l₃.var ++
    bitsOfNat r c.l₄.var ++ bitsOfNat r c.l₅.var ++ bitsOfNat r c.l₆.var ++
    [c.l₁.pos, c.l₂.pos, c.l₃.pos, c.l₄.pos, c.l₅.pos, c.l₆.pos]

@[simp] theorem length_clauseInput6 (ℓa ℓb ℓc r : ℕ) (c : Clause6W ℓa ℓb ℓc r) :
    (clauseInput6 ℓa ℓb ℓc r c).length = ℓa + ℓb + ℓc + 3 * r + 6 := by
  simp [clauseInput6]; omega

/-- The decoupled 6SAT formula that `C` succinctly describes. -/
def Circuit.formula6 (C : Circuit) (ℓa ℓb ℓc r : ℕ) :
    Cnf6 (Fin (2 ^ ℓa)) (Fin (2 ^ ℓb)) (Fin (2 ^ ℓc)) (Fin (2 ^ r)) (Fin (2 ^ r)) (Fin (2 ^ r)) :=
  {c | C.evalBits (clauseInput6 ℓa ℓb ℓc r c) = true}

/-! ## The description -/

/-- `C` **succinctly describes the decider `𝒟` through three windows**, on `n, x, y` and time
`T`: three tables `A, B, C` complete to a satisfying 6-tuple of the described formula exactly
when the decider accepts, within cost `T`, strings `a, b` of length at most `T` whose tape
encodings start with `A` then `C` (for `a`) and with `B` (for `b`). -/
def Circuit.DescribesWindows (Cc : Circuit) (ℓa ℓb ℓc r : ℕ) (D : Decider) (n : ℕ)
    (x y : Cost.BitStr) (T : ℕ) : Prop :=
  ∀ (A : Fin (2 ^ ℓa) → Bool) (B : Fin (2 ^ ℓb) → Bool) (C : Fin (2 ^ ℓc) → Bool),
    (∃ w₁ w₂ w₃ : Fin (2 ^ r) → Bool, (Cc.formula6 ℓa ℓb ℓc r).Sat A B C w₁ w₂ w₃) ↔
      ∃ ap bp : Cost.BitStr, ap.length ≤ T ∧ bp.length ≤ T ∧
        (∀ j : Fin (2 ^ ℓa), A j = tapeBits ap j) ∧ (∀ j : Fin (2 ^ ℓb), B j = tapeBits bp j) ∧
        (∀ j : Fin (2 ^ ℓc), C j = tapeBits ap (2 ^ ℓa + j)) ∧ D.AcceptsWithin n x y ap bp T

/-- The input of the windowed describer: the three window lengths in unary, then the input of
the 3SAT describer. -/
abbrev Desc6Input : Type := (Unary × Unary × Unary) × DescInput

/-- **Succinct decoupled descriptions of deciders through three windows**
(`prop:explicit-padded-succinct-deciders`, in the form of slice P4g). An instance of this
structure is the proposition. -/
structure WindowDescriber where
  /-- `r₀(T, σ)`, the index length of the three witness blocks. -/
  r₀ : ℕ → ℕ → ℕ
  /-- `s₀(n, T, Q, σ)`, the gate bound. -/
  s₀ : ℕ → ℕ → ℕ → ℕ → ℕ
  /-- The algorithm, in polynomial time. -/
  describe : PolyTimeFun Desc6Input Circuit
  /-- The parameters, in polynomial time from `(n, T, Q, σ)`. -/
  params : PolyTimeFun (ℕ × ℕ × ℕ × ℕ) (ℕ × ℕ)
  params_eq : ∀ n T Q σ, params (n, T, Q, σ) = (r₀ T σ, s₀ n T Q σ)
  /-- `r₀ = O(log T + log σ)`. -/
  r₀_le : ∃ c, ∀ T σ, r₀ T σ ≤ c * (Nat.size T + Nat.size σ + 1)
  /-- `4T ≤ 2^{r₀}`: the witness blocks hold the tableau's two input regions. -/
  four_mul_le : ∀ T σ, 4 * T ≤ 2 ^ r₀ T σ
  /-- `s₀ = poly(log n, log T, Q, σ)`. -/
  s₀_le : ∃ P : Polynomial ℕ, ∀ n T Q σ, s₀ n T Q σ ≤ P.eval (Nat.size n + Nat.size T + Q + σ)
  /-- The describer has `ℓa + ℓb + ℓc + 3 r₀ + 6` inputs. -/
  inputs_eq : ∀ (ua ub uc : Unary) D n T Q σ x y,
    (describe ((ua, ub, uc), (D, n, T, Q, σ), x, y)).inputs =
      ua.length + ub.length + uc.length + 3 * r₀ T σ + 6
  /-- The describer is a well-formed circuit. -/
  wellFormed : ∀ inp, (describe inp).WellFormed
  /-- At most `s₀` gates on valid inputs whose windows fit the witness indices. -/
  size_le : ∀ (ua ub uc : Unary) D n T Q σ x y, Valid D n T Q σ x y →
    ua.length ≤ r₀ T σ → ub.length ≤ r₀ T σ → uc.length ≤ r₀ T σ →
    (describe ((ua, ub, uc), (D, n, T, Q, σ), x, y)).size ≤ s₀ n T Q σ
  /-- The describer describes the decider through the windows, when the windows fit the two
  input regions of the tableau and the witness indices. -/
  describes : ∀ (ua ub uc : Unary) (D : Decider) n T Q σ x y, Valid D.prog n T Q σ x y →
    2 ^ ua.length + 2 ^ uc.length ≤ 2 * T → 2 ^ ub.length ≤ 2 * T →
    ua.length ≤ r₀ T σ → ub.length ≤ r₀ T σ → uc.length ≤ r₀ T σ →
    (describe ((ua, ub, uc), (D.prog, n, T, Q, σ), x, y)).DescribesWindows ua.length ub.length
      uc.length (r₀ T σ) D n x y T

end MIPRE.SAT

end
