/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.SAT.Circuit
import MIPRE.Foundations.SAT.Cnf
import MIPRE.Foundations.Cost.PolyTime
import MIPRE.Foundations.Verifier

/-!
# The succinct Cook–Levin theorem: the statement

`MIPRE.SAT.SuccinctCookLevin` is blueprint `thm:succinct-sat` — the paper's
`prop:standard-succinct-sat` (`answer_reduction.tex`, `sec:cook-levin`) — in the vocabulary
of the ambient model: a polynomial-time algorithm that, on a decider `𝒟`, an index `n`, a
time bound `T`, a question length `Q`, a description-length bound `σ` and questions `x, y`,
outputs a circuit `C` on `3m + 3` inputs which succinctly describes a 3SAT formula
`C.formula3 m` on `2^m` variables (`def:succinct-formulas`: `C(i₁, i₂, i₃, o₁, o₂, o₃) = 1`
iff `x_{i₁}^{o₁} ∨ x_{i₂}^{o₂} ∨ x_{i₃}^{o₃}` is a clause), such that

1. for all `a, b ∈ {0,1}^{2T}`, the formula has a satisfying assignment extending `a` and `b`
   on its first `4T` variables iff `a` and `b` are the two-bit tape encodings
   (`tapeBits`: `0 ↦ 00`, `1 ↦ 01`, blank `↦ 10`) of strings of length at most `T` on which
   `𝒟` accepts `(n, x, y, ·, ·)` within cost `T` (`Decider.AcceptsWithin`);
2. `m = O(log T + log σ)` and `2^m ≥ 4T`;
3. `C` has at most `s(n, T, Q, σ) = poly(log n, log T, Q, σ)` gates;
4. the algorithm runs in polynomial time (`PolyTimeFun`, whose bound is a polynomial in the
   size of the input, itself at most `poly(log n, log T, Q, σ)` under the validity
   hypotheses);
5. `m` and `s` are polynomial-time computable from the parameters.

"Within `T` steps" is cost at most `T` in the ambient model, the reading of every time bound
of the pipeline (`Decider.TimeBoundAt`). An instance of this structure is the theorem; its
inhabitation is `planning/succinct-cook-levin.md`. The validity hypotheses `Valid` are the
paper's: `max{Q, 2⌈log n⌉} ≤ T`, `|𝒟| ≤ σ`, `|x|, |y| ≤ Q`.
-/

namespace MIPRE.SAT

open Cost

/-! ## Succinctly described 3SAT formulas -/

/-- The input bits presenting a clause to a describer on `3m + 3` inputs: the three `m`-bit
indices, then the three signs. -/
def clauseInput (m : ℕ) (c : Clause3 (Fin (2 ^ m))) : List Bool :=
  bitsOfNat m c.l₁.var ++ bitsOfNat m c.l₂.var ++ bitsOfNat m c.l₃.var ++
    [c.l₁.pos, c.l₂.pos, c.l₃.pos]

@[simp] theorem length_clauseInput (m : ℕ) (c : Clause3 (Fin (2 ^ m))) :
    (clauseInput m c).length = 3 * m + 3 := by
  simp [clauseInput]; omega

/-- The 3SAT formula on `2^m` variables that `C` succinctly describes: the clauses `C`
accepts (`def:succinct-formulas`). -/
def Circuit.formula3 (C : Circuit) (m : ℕ) : Cnf3 (Fin (2 ^ m)) :=
  {c | C.evalBits (clauseInput m c) = true}

/-! ## Tape encodings of answers -/

/-- The two-bit encoding of a tape cell: `0 ↦ 00`, `1 ↦ 01`, blank `↦ 10` (the boundary
symbol of the tableau is `11`). -/
def cellBits : Option Bool → Bool × Bool
  | some false => (false, false)
  | some true => (false, true)
  | none => (true, false)

/-- The bits of a tape holding `s` followed by blanks: position `p` is bit `p % 2` of cell
`p / 2`. -/
def tapeBits (s : Cost.BitStr) (p : ℕ) : Bool :=
  if p % 2 = 0 then (cellBits s[p / 2]?).1 else (cellBits s[p / 2]?).2

/-! ## Deciders accepting within a cost -/

/-- `𝒟` accepts `(n, x, y, a, b)` within cost `T`. -/
def _root_.MIPRE.Decider.AcceptsWithin (D : Decider) (n : ℕ) (x y a b : Cost.BitStr) (T : ℕ) :
    Prop :=
  ∃ t ≤ T, D.prog.Runs (encode (n, x, y, a, b)) (encode true) t

theorem _root_.MIPRE.Decider.AcceptsWithin.accepts {D : Decider} {n : ℕ} {x y a b : Cost.BitStr}
    {T : ℕ} (h : D.AcceptsWithin n x y a b T) : D.Accepts n x y a b :=
  let ⟨t, _, h⟩ := h
  ⟨t, h⟩

/-! ## The theorem -/

/-- The input of the describer: `((𝒟, n, T, Q, σ), x, y)`. -/
abbrev DescInput : Type := (Prog × ℕ × ℕ × ℕ × ℕ) × Cost.BitStr × Cost.BitStr

/-- The validity hypotheses of the paper's proposition: `max{Q, 2⌈log n⌉} ≤ T`, `|𝒟| ≤ σ`
and `|x|, |y| ≤ Q`. -/
structure Valid (D : Prog) (n T Q σ : ℕ) (x y : Cost.BitStr) : Prop where
  q_le : Q ≤ T
  logn_le : 2 * Nat.size n ≤ T
  size_le : esize D ≤ σ
  x_le : x.length ≤ Q
  y_le : y.length ≤ Q

/-- A satisfying assignment of a formula on `2^m ≥ 4T` variables extending the answer blocks
`a, b ∈ {0,1}^{2T}` on the first `4T` variables. -/
def ExtendsAnswers {m T : ℕ} (h : 4 * T ≤ 2 ^ m) (φ : Cnf3 (Fin (2 ^ m)))
    (a b : Fin (2 * T) → Bool) : Prop :=
  ∃ w : Fin (2 ^ m) → Bool, (∀ j : Fin (2 * T), w ⟨j, by omega⟩ = a j) ∧
    (∀ j : Fin (2 * T), w ⟨2 * T + j, by omega⟩ = b j) ∧ φ.Sat w

/-- `a` is the tape encoding of a string of length at most `T` on which, together with the
string encoded by `b`, the decider accepts within cost `T`: the right-hand side of item 1. -/
def EncodesAccepted (D : Decider) (n : ℕ) (x y : Cost.BitStr) (T : ℕ)
    (a b : Fin (2 * T) → Bool) : Prop :=
  ∃ ap bp : Cost.BitStr, ap.length ≤ T ∧ bp.length ≤ T ∧ (∀ j : Fin (2 * T), a j = tapeBits ap j) ∧
    (∀ j : Fin (2 * T), b j = tapeBits bp j) ∧ D.AcceptsWithin n x y ap bp T

/-- **Explicit succinct Cook–Levin** (blueprint `thm:succinct-sat`; `prop:standard-succinct-sat`).
An instance of this structure is the theorem. -/
structure SuccinctCookLevin where
  /-- The variable-count exponent `m(T, σ)`. -/
  m : ℕ → ℕ → ℕ
  /-- The gate bound `s(n, T, Q, σ)`. -/
  s : ℕ → ℕ → ℕ → ℕ → ℕ
  /-- The algorithm: the describer circuit from `((𝒟, n, T, Q, σ), x, y)`, in polynomial
  time (item 4). -/
  describe : PolyTimeFun DescInput Circuit
  /-- Item 5: `m` in polynomial time from `(T, σ)`. -/
  mProg : PolyTimeFun (ℕ × ℕ) ℕ
  mProg_eq : ∀ T σ, mProg (T, σ) = m T σ
  /-- Item 5: `s` in polynomial time from `(n, T, Q, σ)`. -/
  sProg : PolyTimeFun (ℕ × ℕ × ℕ × ℕ) ℕ
  sProg_eq : ∀ n T Q σ, sProg (n, T, Q, σ) = s n T Q σ
  /-- Item 2: `m = O(log T + log σ)`. -/
  m_le : ∃ c, ∀ T σ, m T σ ≤ c * (Nat.size T + Nat.size σ + 1)
  /-- Item 2: `2^m ≥ 4T`. -/
  four_mul_le : ∀ T σ, 4 * T ≤ 2 ^ m T σ
  /-- Item 3: `s = poly(log n, log T, Q, σ)`. -/
  s_le : ∃ P : Polynomial ℕ, ∀ n T Q σ, s n T Q σ ≤ P.eval (Nat.size n + Nat.size T + Q + σ)
  /-- The describer has `3m + 3` inputs. -/
  inputs_eq : ∀ D n T Q σ x y, (describe ((D, n, T, Q, σ), x, y)).inputs = 3 * m T σ + 3
  /-- The describer is a well-formed circuit (fan-out at most two, terminal output). -/
  wellFormed : ∀ inp, (describe inp).WellFormed
  /-- Item 3: at most `s` gates on valid inputs. -/
  size_le : ∀ D n T Q σ x y, Valid D n T Q σ x y →
    (describe ((D, n, T, Q, σ), x, y)).size ≤ s n T Q σ
  /-- Item 1: the described formula has a satisfying assignment extending `a, b` on its first
  `4T` variables iff `a, b` encode strings of length at most `T` that `𝒟` accepts within
  cost `T`. -/
  accepts_iff : ∀ (D : Decider) n T Q σ x y, Valid D.prog n T Q σ x y →
    ∀ a b : Fin (2 * T) → Bool,
      ExtendsAnswers (four_mul_le T σ) ((describe ((D.prog, n, T, Q, σ), x, y)).formula3 (m T σ))
        a b ↔ EncodesAccepted D n x y T a b

end MIPRE.SAT
