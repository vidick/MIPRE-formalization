/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Cost.BoundedEval
import MIPRE.Foundations.Halting.Enumerate

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

/-! ## Sampler queries under the budget -/

namespace CL.Sampler

variable {ℓ : ℕ} (S : CL.Sampler ℓ)

/-- One query to the sampler, run under the budget its time bound supplies. The sampler is
required to halt on *every* input of the form `(n, …)`, so this is total wherever the bound
holds. -/
def queryUnder (T k n : ℕ) (q : Query) : Option Data :=
  Machine.runForD (encode S.prog) (encode (n, q)) (T * ((encode q : Data).size + 1) ^ k)

/-- Under the bound, a budgeted query returns exactly what the sampler's correctness clauses
say it returns. -/
theorem queryUnder_eq {n T k : ℕ} (hb : S.TimeBoundAt n T k) {q : Query} {r : Data} {t : ℕ}
    (h : S.prog.Runs (encode (n, q)) r t) : S.queryUnder T k n q = some r := by
  obtain ⟨r₀, t₀, ht₀, h₀⟩ := hb (encode q)
  obtain ⟨rfl, -⟩ := h₀.deterministic h
  exact Machine.runForD_eq_some h₀ ht₀

/-- The dimension query. -/
theorem queryUnder_dimension {n T k : ℕ} (hb : S.TimeBoundAt n T k) :
    S.queryUnder T k n Query.dimension = some (encode (S.dim n)) :=
  let ⟨_, h⟩ := S.runs_dimension n; S.queryUnder_eq hb h

/-- **The marginal at the top level is the CL function itself** (`CLFun.truncate_self`), so one
budgeted `marginal` query at level `ℓ` computes `L^w(z)` — which is what the question weights
of the tabulated game are counted from. -/
theorem queryUnder_marginal {n T k : ℕ} (hb : S.TimeBoundAt n T k) (hl : 1 ≤ ℓ) (w : Player)
    (z : BitStr) (hz : z.length = S.dim n) :
    S.queryUnder T k n (Query.marginal w ℓ z)
      = some (encode (toBits ((S.cl n w).eval (ofBits (S.dim n) z)))) := by
  obtain ⟨t, h⟩ := S.runs_marginal n w ℓ z hl le_rfl hz
  rw [CLFun.truncate_self] at h
  exact S.queryUnder_eq hb h

end CL.Sampler

/-! ## Questions as numbers -/

namespace Verifier

/-- The index of a bit string: the number whose binary digits it is, least significant first.
This is the `ℕ`-level form of `Verifier.questionEquiv`, and it is what the tabulation can
actually compute with — the question alphabet of a `GameData` is `Fin (nX + 1)`, so every
question reached by a sampler query has to be turned into a number. -/
def bitsToIdx : BitStr → ℕ
  | [] => 0
  | b :: l => (if b then 1 else 0) + 2 * bitsToIdx l

@[simp] theorem bitsToIdx_nil : bitsToIdx [] = 0 := rfl

@[simp] theorem bitsToIdx_cons (b : Bool) (l : BitStr) :
    bitsToIdx (b :: l) = (if b then 1 else 0) + 2 * bitsToIdx l := rfl

theorem bitsToIdx_ofFn {s : ℕ} (f : Fin s → Bool) :
    bitsToIdx (List.ofFn f) = ∑ i : Fin s, (if f i then 1 else 0) * 2 ^ (i : ℕ) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [List.ofFn_succ, bitsToIdx_cons, ih, Fin.sum_univ_succ, Finset.mul_sum]
    refine congrArg₂ (· + ·) (by simp) (Finset.sum_congr rfl fun i _ => ?_)
    rw [Fin.val_succ, pow_succ]
    ring

/-- The `Fin 2` form, where `finFunctionFinEquiv` is literally applicable: `CL.𝔽₂` is `ZMod 2`,
which reduces to `Fin 2` but does not unify with it at the transparency `rw` uses. -/
private theorem bitsToIdx_ofFn_fin2 {s : ℕ} (w : Fin s → Fin 2) :
    bitsToIdx (List.ofFn fun i => decide (w i = 1)) = (finFunctionFinEquiv w : ℕ) := by
  rw [bitsToIdx_ofFn, finFunctionFinEquiv_apply]
  refine Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) ?_ rfl
  revert i
  suffices h : ∀ a : Fin 2, (if decide (a = 1) then 1 else 0) = (a : ℕ) from fun i _ => h (w i)
  decide

/-- **The index of a question is the number its bit string denotes.** This is what lets the
tabulation name questions by numbers while the value agreement is read along
`questionEquiv`. -/
@[simp] theorem questionEquiv_symm_val {s : ℕ} (v : Fin s → CL.𝔽₂) :
    (((questionEquiv s).symm v : Fin (2 ^ s)) : ℕ) = bitsToIdx (CL.toBits v) :=
  (bitsToIdx_ofFn_fin2 v).symm

@[simp] theorem bitsToIdx_toBits_questionEquiv {s : ℕ} (i : Fin (2 ^ s)) :
    bitsToIdx (CL.toBits (questionEquiv s i)) = (i : ℕ) := by
  rw [← questionEquiv_symm_val, Equiv.symm_apply_apply]

end Verifier

end MIPRE
