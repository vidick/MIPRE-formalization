/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.SAT.Succinct

/-!
# Succinct decoupled 5SAT descriptions of deciders: the statement

`MIPRE.SAT.DecoupledDescriber` is blueprint `lem:decoupled-5sat` — the paper's
`prop:explicit-succinct-deciders` (`answer_reduction.tex`, `sec:succinct-deciders`) — the
first consumer of `SuccinctCookLevin` and the form in which answer reduction's PCP reads the
decider: a circuit with two inputs of length `ℓ₀` (indexing the answer blocks `a`, `b`), three
of length `r₀` (indexing three separate assignments) and five signs, describing a decoupled
5SAT formula (`Circuit.formula5`) such that `a, b` extend to a satisfying five-tuple iff they
encode strings of length at most `T` the decider accepts within cost `T`
(`Circuit.DescribesDecider`), with `ℓ₀ = ⌈log 2T⌉`, `r₀ = O(log T + log σ)`, at most
`s₀ = poly(log T, log n, Q, σ)` gates, in polynomial time, the parameters computable in
polynomial time from the parameters' bit lengths. Stated here, before anything is proved, so
that the statement of `thm:succinct-sat` is validated by its consumer
(`planning/succinct-cook-levin.md`, S0).
-/

namespace MIPRE.SAT

open Cost

/-- The input bits presenting a decoupled clause to a describer with two `ℓ`-bit and three
`r`-bit index inputs, then the five signs. -/
def clauseInput5 (ℓ r : ℕ)
    (c : Clause5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ)) (Fin (2 ^ r)) (Fin (2 ^ r)) (Fin (2 ^ r))) :
    List Bool :=
  bitsOfNat ℓ c.l₁.var ++ bitsOfNat ℓ c.l₂.var ++ bitsOfNat r c.l₃.var ++ bitsOfNat r c.l₄.var ++
    bitsOfNat r c.l₅.var ++ [c.l₁.pos, c.l₂.pos, c.l₃.pos, c.l₄.pos, c.l₅.pos]

@[simp] theorem length_clauseInput5 (ℓ r : ℕ)
    (c : Clause5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ)) (Fin (2 ^ r)) (Fin (2 ^ r)) (Fin (2 ^ r))) :
    (clauseInput5 ℓ r c).length = 2 * ℓ + 3 * r + 5 := by
  simp [clauseInput5]; omega

/-- The decoupled 5SAT formula, on two blocks of `2^ℓ` and three of `2^r` variables, that
`C` succinctly describes. -/
def Circuit.formula5 (C : Circuit) (ℓ r : ℕ) :
    Cnf5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ)) (Fin (2 ^ r)) (Fin (2 ^ r)) (Fin (2 ^ r)) :=
  {c | C.evalBits (clauseInput5 ℓ r c) = true}

/-- `C` **succinctly describes the decider `𝒟`** on `n, x, y` and time `T`: for all answer
blocks `a, b ∈ {0,1}^{2^ℓ}`, some three assignments complete them to a satisfying tuple of
the described formula iff `a, b` are the tape encodings of strings of length at most `T` on
which `𝒟` accepts within cost `T`. -/
def Circuit.DescribesDecider (C : Circuit) (ℓ r : ℕ) (D : Decider) (n : ℕ)
    (x y : Cost.BitStr) (T : ℕ) : Prop :=
  ∀ a b : Fin (2 ^ ℓ) → Bool,
    (∃ w₁ w₂ w₃ : Fin (2 ^ r) → Bool, (C.formula5 ℓ r).Sat a b w₁ w₂ w₃) ↔
      ∃ ap bp : Cost.BitStr, ap.length ≤ T ∧ bp.length ≤ T ∧
        (∀ j : Fin (2 ^ ℓ), a j = tapeBits ap j) ∧ (∀ j : Fin (2 ^ ℓ), b j = tapeBits bp j) ∧
        D.AcceptsWithin n x y ap bp T

/-- **Explicit succinct decoupled descriptions of deciders** (blueprint `lem:decoupled-5sat`;
`prop:explicit-succinct-deciders`). An instance of this structure is the lemma. -/
structure DecoupledDescriber where
  /-- `ℓ₀(T)`, the index length of the answer blocks. -/
  ℓ₀ : ℕ → ℕ
  /-- `r₀(T, σ)`, the index length of the three auxiliary blocks. -/
  r₀ : ℕ → ℕ → ℕ
  /-- `s₀(n, T, Q, σ)`, the gate bound. -/
  s₀ : ℕ → ℕ → ℕ → ℕ → ℕ
  /-- The algorithm, in polynomial time. -/
  describe : PolyTimeFun DescInput Circuit
  /-- The parameters, in polynomial time from `(n, T, Q, σ)`. -/
  params : PolyTimeFun (ℕ × ℕ × ℕ × ℕ) (ℕ × ℕ × ℕ)
  params_eq : ∀ n T Q σ, params (n, T, Q, σ) = (ℓ₀ T, r₀ T σ, s₀ n T Q σ)
  /-- `ℓ₀ = ⌈log 2T⌉`: `2T ≤ 2^{ℓ₀} < 4T` for `T ≥ 1`. -/
  ℓ₀_spec : ∀ T, 1 ≤ T → 2 * T ≤ 2 ^ ℓ₀ T ∧ 2 ^ ℓ₀ T < 4 * T
  /-- `r₀ = O(log T + log σ)`. -/
  r₀_le : ∃ c, ∀ T σ, r₀ T σ ≤ c * (Nat.size T + Nat.size σ + 1)
  /-- `s₀ = poly(log n, log T, Q, σ)`. -/
  s₀_le : ∃ P : Polynomial ℕ, ∀ n T Q σ, s₀ n T Q σ ≤ P.eval (Nat.size n + Nat.size T + Q + σ)
  /-- The describer has `2ℓ₀ + 3r₀ + 5` inputs. -/
  inputs_eq : ∀ D n T Q σ x y,
    (describe ((D, n, T, Q, σ), x, y)).inputs = 2 * ℓ₀ T + 3 * r₀ T σ + 5
  /-- The describer is a well-formed circuit. -/
  wellFormed : ∀ inp, (describe inp).WellFormed
  /-- At most `s₀` gates on valid inputs. -/
  size_le : ∀ D n T Q σ x y, Valid D n T Q σ x y →
    (describe ((D, n, T, Q, σ), x, y)).size ≤ s₀ n T Q σ
  /-- The describer describes the decider. -/
  describes : ∀ (D : Decider) n T Q σ x y, Valid D.prog n T Q σ x y →
    (describe ((D.prog, n, T, Q, σ), x, y)).DescribesDecider (ℓ₀ T) (r₀ T σ) D n x y T

end MIPRE.SAT
