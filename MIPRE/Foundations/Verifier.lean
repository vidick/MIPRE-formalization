/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.CL.Sampler
import MIPRE.Foundations.Games

/-!
# Deciders and normal form verifiers

Blueprint `def:decider`, `def:normal-verifier` and `def:lambda-bounded` (paper `games.tex`,
Definitions `def:decider`, `def:normal-ver`, `def:normal-game`, `def:lambda`; ledger node
`1.1.3`). A normal form verifier is the uniform way the pipeline presents an infinite family
of games: a sampler (`MIPRE.CL.Sampler`), which produces the questions, and a decider, which
checks the answers, both programs of the ambient cost model (`MIPRE.Cost`).

* `MIPRE.Decider`: a program whose one input is `encode (n, x, y, a, b)`; it *accepts* when it
  halts with output `1` (`Decider.Accepts`), and rejects otherwise. `Decider.TimeBoundAt n T`
  is `TIME_𝒟(n) ≤ T`, halting within cost `T` on every input of the form `(n, …)`.
* `MIPRE.Verifier ℓ`: a sampler and a decider, with the paper's requirement that the decider
  accept only questions of the sampler's dimension `s(n)` (it "first checks
  `|x| = |y| = s(n)`", `Verifier.accepts_length`).
* `Verifier.game n T`: the game `𝒱_n` — questions `𝔽₂^{s(n)}`, answers the bit strings of
  length at most `T` (`Verifier.Answers T`), the sampler's distribution, and acceptance by the
  decider. The paper's `𝒱_n` is the case `T = TIME_𝒟(n)`; the bound is a parameter here
  because every statement about `𝒱_n` carries an explicit time bound anyway, and taking the
  exact supremum would only add a degenerate case (`TIME_𝒟(n) = ∞`, where the paper's game is
  undefined) to every definition. `Verifier.syncGame` is the same game as a
  `SynchronousGame`, under the condition on the decider that makes it one
  (`Verifier.IsSynchronousAt`).
* `Verifier.IsBounded λ`: `def:lambda-bounded`, `TIME_𝒮(n), TIME_𝒟(n) ≤ n^λ` for `n ≥ 2` and
  `|𝒱| ≤ λ`.

Timeouts are not modelled: in the ambient cost model a decider with `TIME_𝒟(n) < ∞` halts on
every input of index `n`, and the paper's convention that a timeout is a rejection is the
convention that anything but halting with output `1` is.
-/

namespace MIPRE

open Cost

/-! ## Deciders -/

/-- `def:decider`: a decider is a program whose one input is `encode (n, x, y, a, b)` — an
index `n` and the questions and answers `x, y, a, b` of the two players. -/
structure Decider where
  /-- The program. -/
  prog : Prog
  /-- The program is closed. -/
  closed : prog.WellScoped 1

namespace Decider

variable (D : Decider)

/-- The decider **accepts** `(n, x, y, a, b)`: it halts with output `1`. Any other outcome —
output `0`, or not halting — is rejection. -/
def Accepts (n : ℕ) (x y a b : BitStr) : Prop :=
  ∃ t, D.prog.Runs (encode (n, x, y, a, b)) (encode true) t

/-- `TIME_𝒟(n) ≤ T`: the decider halts within cost `T` on every input of the form `(n, …)`,
well formed or not. -/
def TimeBoundAt (n T : ℕ) : Prop := ∀ d : Data, HaltsWithin D.prog (.cons (encode n) d) T

/-- `TIME_𝒟(n) ≤ T n` for every `n`. -/
def TimeBound (T : ℕ → ℕ) : Prop := ∀ n, D.TimeBoundAt n (T n)

/-- The description length `|𝒟|`. -/
def size : ℕ := esize D.prog

end Decider

/-! ## Normal form verifiers -/

/-- `def:normal-verifier`: a normal form verifier is a sampler and a decider, the decider
accepting only questions of the sampler's dimension (the paper's requirement that it first
check `|x| = |y| = s(n)` and reject otherwise). The number of levels of the verifier is that
of its sampler. -/
structure Verifier (ℓ : ℕ) where
  /-- The sampler, producing the questions. -/
  sampler : CL.Sampler ℓ
  /-- The decider, checking the answers. -/
  decider : Decider
  /-- The decider accepts only questions of the sampler's dimension. -/
  accepts_length : ∀ n x y a b, decider.Accepts n x y a b →
    x.length = sampler.dim n ∧ y.length = sampler.dim n

namespace Verifier

variable {ℓ : ℕ} (V : Verifier ℓ)

/-- The description length `|𝒱| = max(|𝒮|, |𝒟|)`. -/
def size : ℕ := max V.sampler.size V.decider.size

/-- The answer alphabet of `𝒱_n`: the bit strings of length at most `T`, the paper's
`{0,1}^{≤ TIME_𝒟(n)}`. -/
def Answers (T : ℕ) : Type := {a : BitStr // a.length ≤ T}

namespace Answers

instance (T : ℕ) : DecidableEq (Answers T) :=
  inferInstanceAs (DecidableEq {a : BitStr // a.length ≤ T})

/-- An answer is determined by its bits at the positions below `T + 1`. -/
theorem getElem?_injective (T : ℕ) :
    Function.Injective fun (a : Answers T) (i : Fin (T + 1)) => a.1[(i : ℕ)]? := by
  intro a b h
  apply Subtype.ext
  apply List.ext_getElem?
  intro i
  by_cases hi : i < T + 1
  · exact congrFun h ⟨i, hi⟩
  · have ha := a.2
    have hb := b.2
    rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

instance (T : ℕ) : Finite (Answers T) := Finite.of_injective _ (getElem?_injective T)

noncomputable instance (T : ℕ) : Fintype (Answers T) := Fintype.ofFinite _

end Answers

/-- The question alphabet of `𝒱_n`: `𝔽₂^{s(n)}`. -/
abbrev Questions (n : ℕ) : Type := Fin (V.sampler.dim n) → CL.𝔽₂

open Classical in
/-- The game `𝒱_n` with answers of length at most `T` (the paper's `def:normal-game`, at
`T = TIME_𝒟(n)`): questions `𝔽₂^{s(n)}` distributed as the sampler prescribes, answers
accepted when the decider accepts them. -/
noncomputable def game (n T : ℕ) :
    Game (V.Questions n) (V.Questions n) (Answers T) (Answers T) where
  μ := V.sampler.dist n
  μ_nonneg := V.sampler.dist_nonneg n
  μ_sum_one := V.sampler.sum_dist n
  D x y a b := decide (V.decider.Accepts n (CL.toBits x) (CL.toBits y) a.1 b.1)

/-- `val*(𝒱_n)`, the quantum value of the `n`-th game with answers of length at most `T`. -/
noncomputable def valStar (n T : ℕ) : ℝ := quantumValue (V.game n T)

/-- The decider rejects unequal answers to equal questions at index `n`, so that `𝒱_n` is a
synchronous game (blueprint `def:sync-game`). -/
def IsSynchronousAt (n : ℕ) : Prop := ∀ x a b, a ≠ b → ¬ V.decider.Accepts n x x a b

open Classical in
/-- `𝒱_n` as a synchronous game, when the decider makes it one. -/
noncomputable def syncGame (n T : ℕ) (h : V.IsSynchronousAt n) :
    SynchronousGame (V.Questions n) (Answers T) where
  μ := V.sampler.dist n
  μ_nonneg := V.sampler.dist_nonneg n
  μ_sum_one := V.sampler.sum_dist n
  D x y a b := decide (V.decider.Accepts n (CL.toBits x) (CL.toBits y) a.1 b.1)
  synchronous x a b hab := by
    rw [decide_eq_false_iff_not]
    exact h _ _ _ fun h' => hab (Subtype.ext h')

theorem syncGame_toGame (n T : ℕ) (h : V.IsSynchronousAt n) :
    (V.syncGame n T h).toGame = V.game n T := rfl

/-- `def:lambda-bounded`: `TIME_𝒮(n), TIME_𝒟(n) ≤ n^λ` for all `n ≥ 2`, and `|𝒱| ≤ λ`. -/
def IsBounded (lam : ℕ) : Prop :=
  (∀ n, 2 ≤ n → V.sampler.TimeBoundAt n (n ^ lam) ∧ V.decider.TimeBoundAt n (n ^ lam)) ∧
    V.size ≤ lam

end Verifier

end MIPRE
