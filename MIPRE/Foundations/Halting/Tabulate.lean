/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Cost.BoundedEval
import MIPRE.Foundations.Verifier

/-!
# Deciding acceptance under a time bound

The first half of obligation **O2** (blueprint `rem:compression-abstract`, item 3): the
acceptance table of the tabulated game. Filling it in needs `Decider.Accepts` — a `Σ₁`
statement, `∃ t, prog.Runs …` — to be *decided*, and that is exactly what `n`-boundedness
buys: the bound supplies a budget within which the decider must halt, so one budgeted run
settles the question (`Machine.runForD`).

* `Decider.acceptBudget`: the budget `T · (|d| + 1) ^ k` the bound gives at index `n` on the
  tuple `(x, y, a, b)`, read off the shape of `Decider.TimeBoundAt`.
* `Decider.accepts_iff_runForD`: for a decider obeying that bound, acceptance is one budgeted
  run returning `encode true`.
* `Decider.decidableAccepts` and `Verifier.decidableAccepts`: the resulting decision
  procedures, and `Verifier.accepts_iff_runForD` for the verifier a string denotes, where the
  bound comes from `Verifier.IsBounded`.

Nothing here is efficient and nothing needs to be: the tabulation is a computable map, not a
polynomial-time one, and the budget it runs under is the verifier's own time bound.
-/

namespace MIPRE

open Cost

namespace Decider

variable (D : Decider)

/-- The budget the time bound `TimeBoundAt n T k` gives on the tuple `(x, y, a, b)`: the
decider's input is `cons (encode n) (encode (x, y, a, b))`, and the bound is `T` times the
`k`-th power of one more than the size of the second component. -/
def acceptBudget (T k : ℕ) (x y a b : BitStr) : ℕ :=
  T * ((encode (x, y, a, b) : Data).size + 1) ^ k

/-- **Acceptance under a time bound is one budgeted run.** -/
theorem accepts_iff_runForD {n T k : ℕ} (hb : D.TimeBoundAt n T k) (x y a b : BitStr) :
    D.Accepts n x y a b ↔
      Machine.runForD (encode D.prog) (encode (n, x, y, a, b))
        (acceptBudget T k x y a b) = some (encode true) :=
  (Machine.runForD_eq_some_iff (hb (encode (x, y, a, b)))).symm

/-- Hence acceptance is decidable, for a decider that obeys a time bound at the index. -/
def decidableAccepts {n T k : ℕ} (hb : D.TimeBoundAt n T k) (x y a b : BitStr) :
    Decidable (D.Accepts n x y a b) :=
  decidable_of_iff _ (D.accepts_iff_runForD hb x y a b).symm

end Decider

namespace Verifier

variable {ℓ : ℕ} (V : Verifier ℓ)

/-- **Acceptance by an `n`-bounded verifier is one budgeted run**, at the budget its own
`λ`-boundedness supplies. This is what fills in the acceptance table of the tabulation. -/
theorem accepts_iff_runForD {n : ℕ} (hb : V.IsBounded n) (hn : 2 ≤ n) (x y a b : BitStr) :
    V.decider.Accepts n x y a b ↔
      Machine.runForD (encode V.decider.prog) (encode (n, x, y, a, b))
        (Decider.acceptBudget (n ^ n) n x y a b) = some (encode true) :=
  V.decider.accepts_iff_runForD (hb.1 n hn).2.2 x y a b

/-- Hence acceptance by an `n`-bounded verifier is decidable. -/
def decidableAccepts {n : ℕ} (hb : V.IsBounded n) (hn : 2 ≤ n) (x y a b : BitStr) :
    Decidable (V.decider.Accepts n x y a b) :=
  V.decider.decidableAccepts (hb.1 n hn).2.2 x y a b

end Verifier

end MIPRE
