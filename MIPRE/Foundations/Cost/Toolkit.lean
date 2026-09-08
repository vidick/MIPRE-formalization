/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Cost.PolyTime

/-!
# The efficient computability toolkit

The efficient versions of the universal machine, the s-m-n theorem, and Kleene's
recursion theorem, in the ambient cost model — blueprint Section
`sec:rr-computability` (`lem:universal-tm`, `lem:smn`, `lem:kleene`), following
[MNY, Lemmas 2.1–2.3]. Mathlib has the computability halves for `Nat.Partrec.Code`
(`Nat.Partrec.Code.smn`, `eval_part`, `fixed_point`); everything with a time bound
is new.

Contents:

* `constProg`/`hardcode`: the **efficient s-m-n**. `hardcode p d` binds the pair
  `(d, input)` as the input of `p`. The witness makes [MNY, Lemma 2.2] quantitative and
  stronger than stated there: program-size and time overheads are *linear* in the sizes of
  `d` and of the input (paper: polynomial), with universal constants. `smn_polyTime` is the
  runtime version — the map is itself polynomial-time computable in the model — generic in
  the type of the hardcoded value.
* `UniversalMachine` / `exists_efficient_universal` (`lem:universal-tm`): a fixed closed
  program `univ` that, on the pair `(encode c, v)`, halts exactly when `c` halts on `v`,
  with the same result and polynomial time overhead — packaged as data (the program and its
  overhead polynomial) whose existence is the sorried node.
* `ClockedUniversalMachine` / `exists_clocked_universal`: the time-bounded variant ("run
  `c` on `v` for `k` steps"), used by the recursive compression argument and by the
  pipeline's deciders (introspection and repetition simulate other deciders under a budget).
* `efficient_fixed_point` (`lem:kleene`): Kleene's recursion theorem for a polynomial-time
  map on programs, with the runs of the fixed point bounded by those of its image at
  polynomial overhead.

The statement shapes were audited against the proof of the recursive compression lemma
(`planning/compression-track.md`, K0): the universal machines are structures so that
downstream definitions can name the program and its polynomial without any sorried `def`;
the runtime s-m-n is generic in the hardcoded type; Kleene is stated in the one direction
the argument uses (see its docstring).

Effort notes (matching the blueprint's `\effortHard` on this section): the s-m-n lemmas
are elementary. The two universal-machine theorems are the hard core — a self-interpreter
of `Prog` written in `Prog` with polynomial overhead; this is the same kind of artifact as
the interpreter underlying the succinct Cook–Levin gateway (`thm:succinct-sat`), and the
two developments should share design.
-/

namespace MIPRE.Cost

open Polynomial

/-- Transport a run along an equation between costs. -/
theorem Eval.cast_cost {env : Env} {p : Prog} {r : Data} {t t' : ℕ} (h : Eval env p r t)
    (e : t = t') : Eval env p r t' :=
  e ▸ h

/-! ## Constants and the efficient s-m-n (blueprint `lem:smn`; [MNY, Lemma 2.2]) -/

/-- The program building the constant `d`: nested `cons`/`nil` nodes. -/
def constProg : Data → Prog
  | .nil => .nil
  | .cons a b => .cons (constProg a) (constProg b)

theorem constProg_wellScoped (d : Data) (n : ℕ) : (constProg d).WellScoped n := by
  induction d with
  | nil => trivial
  | cons a b iha ihb => exact ⟨iha, ihb⟩

/-- `constProg d` builds `d` in exactly `d.size` steps, in any environment. -/
theorem constProg_eval (d : Data) (env : Env) : Eval env (constProg d) d d.size := by
  induction d with
  | nil => exact .nil env
  | cons a b iha ihb => exact .cons iha ihb

theorem esize_constProg_le (d : Data) : esize (constProg d) ≤ 7 * d.size := by
  induction d with
  | nil => decide
  | cons a b iha ihb =>
    simp only [Prog.esize_eq_size_toData, constProg, Prog.toData, Data.size_cons,
      Data.size_ofNat] at iha ihb ⊢
    omega

/-- The s-m-n transformation: `hardcode p d` runs `p` on the pair `(d, input)`. -/
def hardcode (p : Prog) (d : Data) : Prog := .let_ (.cons (constProg d) (.var 0)) p

theorem hardcode_wellScoped {p : Prog} (hp : p.WellScoped 1) (d : Data) :
    (hardcode p d).WellScoped 1 :=
  ⟨⟨constProg_wellScoped d 1, Nat.zero_lt_one⟩, hp.mono (by omega) _⟩

/-- The run of the pairing prefix of `hardcode`. -/
theorem hardcode_prefix_eval (d x : Data) :
    Eval [x] (.cons (constProg d) (.var 0)) (.cons d x) (d.size + (x.size + 1) + 1) :=
  .cons (constProg_eval d _) (by simpa using Eval.var [x] 0)

/-- Efficient s-m-n, functional equation and forward time transfer: a run of `p` on
`cons d x` yields a run of `hardcode p d` on `x` with *additive, linear* overhead. -/
theorem hardcode_time {p : Prog} (hp : p.WellScoped 1) {d x r : Data} {t : ℕ}
    (h : p.Runs (.cons d x) r t) : (hardcode p d).Runs x r (t + d.size + x.size + 3) :=
  (Eval.let_ (hardcode_prefix_eval d x) (Eval.append_of_wellScoped h hp [x])).cast_cost
    (by omega)

/-- Efficient s-m-n, backward time transfer: runs of `hardcode p d` restrict to runs of
`p`. -/
theorem hardcode_time_rev {p : Prog} (hp : p.WellScoped 1) {d x r : Data} {t : ℕ}
    (h : (hardcode p d).Runs x r t) : ∃ t' ≤ t, p.Runs (.cons d x) r t' := by
  change Eval [x] (.let_ (.cons (constProg d) (.var 0)) p) r t at h
  cases h with
  | let_ h₁ h₂ =>
    obtain ⟨rfl, -⟩ := h₁.deterministic (hardcode_prefix_eval d x)
    exact ⟨_, by omega,
      Eval.of_append_of_wellScoped (env := [.cons d x]) (extra := [x]) h₂ hp⟩

/-- Efficient s-m-n, size bound: hardcoding costs *linear* program size. -/
theorem hardcode_size (p : Prog) (d : Data) :
    esize (hardcode p d) ≤ esize p + 7 * d.size + 21 := by
  have := esize_constProg_le d
  simp only [Prog.esize_eq_size_toData, hardcode, Prog.toData, Data.size_cons,
    Data.size_ofNat] at this ⊢
  omega

/-- The s-m-n map itself is polynomial-time computable *in the model* — the clause of
[MNY, Lemma 2.2] that the recursive compression argument uses at runtime (the
self-referential decider builds hardcoded programs while executing). The argument hardcodes
encoded programs and tuples, not only bit strings, hence the statement is generic in the
hardcoded type `α`. Requires the closure library. -/
theorem smn_polyTime (α : Type*) [SizedEncoding α] :
    ∃ S : PolyTimeFun (Prog × α) Prog,
      ∀ (p : Prog) (a : α), S (p, a) = hardcode p (encode a) := by
  sorry

/-! ## The efficient universal machine (blueprint `lem:universal-tm`; [MNY, Lemma 2.1])

The two universal machines are *structures*: the program and its overhead polynomial are
fields, so that downstream definitions (deciders simulating other deciders under a budget;
the λ-bookkeeping of [JNVWY, §12.2], which chooses λ above the concrete overhead
polynomials) can refer to them as data. Their existence is the sorried node; no `def` is
sorried. -/

/-- **Efficient universal machine.** A fixed closed program `univ` simulating any `c` on
any `v` — with the same halting behavior and result — at polynomial time overhead in
`esize c + v.size + runtime`. Its input is the pair `(encode c, v)`. -/
structure UniversalMachine where
  /-- The universal program. -/
  univ : Prog
  /-- It is closed. -/
  closed : univ.WellScoped 1
  /-- The overhead polynomial. -/
  bound : Polynomial ℕ
  /-- A run of `c` yields a run of the simulation, with the same result, at polynomial
  overhead. -/
  time_le : ∀ (c : Prog) (v r : Data) (t : ℕ), c.Runs v r t →
    ∃ t' ≤ bound.eval (esize c + v.size + t), univ.Runs (.cons (encode c) v) r t'
  /-- The simulation halts only if the simulated program does, with the same result. -/
  halts_of : ∀ (c : Prog) (v r : Data) (t' : ℕ), univ.Runs (.cons (encode c) v) r t' →
    ∃ t, c.Runs v r t

/-- Existence of an efficient universal machine (blueprint `lem:universal-tm`). -/
theorem exists_efficient_universal : Nonempty UniversalMachine := by
  sorry

open Classical in
/-- The result of running `c` on `v` for at most `k` cost, if it halts within the budget
(well-defined by `Eval.deterministic`). -/
noncomputable def evalWithin (c : Prog) (v : Data) (k : ℕ) : Option Data :=
  if h : ∃ r t, t ≤ k ∧ c.Runs v r t then some h.choose else none

/-- The value a clocked simulation returns: `cons (cons nil nil) r` ("halted, with result
`r`") on in-budget halting, and `nil` ("timeout") on budget exhaustion. -/
noncomputable def clockedResult (c : Prog) (v : Data) (k : ℕ) : Data :=
  match evalWithin c v k with
  | some r => .cons (.cons .nil .nil) r
  | none => .nil

/-- **Clocked universal machine**: total simulation under a step budget `k` (supplied in
unary), returning `clockedResult c v k` in time polynomial in the budget, the program size
and the input size. Its input is `(ofNat k, (encode c, v))`. This is the primitive with which
deciders of the pipeline run other deciders, and with which the recursive compression
argument runs "`e` for `log n` steps". -/
structure ClockedUniversalMachine where
  /-- The clocked universal program. -/
  univT : Prog
  /-- It is closed. -/
  closed : univT.WellScoped 1
  /-- The overhead polynomial. -/
  bound : Polynomial ℕ
  /-- Total, budget-bounded simulation. -/
  run : ∀ (c : Prog) (v : Data) (k : ℕ),
    ∃ t ≤ bound.eval (k + esize c + v.size),
      univT.Runs (.cons (.ofNat k) (.cons (encode c) v)) (clockedResult c v k) t

/-- Existence of a clocked universal machine (blueprint `lem:universal-tm`). -/
theorem exists_clocked_universal : Nonempty ClockedUniversalMachine := by
  sorry

/-! ## Efficient Kleene recursion (blueprint `lem:kleene`; [MNY, Lemma 2.3]) -/

/-- **Efficient Kleene fixed point**: for a polynomial-time map on programs, a closed
program `e` with the same input/output behavior as `F e`, whose runs are bounded by the
runs of `F e` at polynomial overhead. The proof is the classical construction through
`hardcode` and a `UniversalMachine`, tracking the overheads; the polynomial `p` depends on
`F.timeBound` and on the machine's `bound`.

Departure from [MNY, Lemma 2.3], which states the runtimes of `e` and `F e` as
*polynomially equivalent*: only the direction "runs of `F e` bound runs of `e`" is used by
the recursive compression argument (it is what makes the fixed point polynomial-time), and
only that direction follows from `UniversalMachine.time_le`. The converse would need a
lower-bound clause on the universal machine ("a simulation is never faster than the
simulated run"); it is omitted to keep the universal-machine obligation minimal and can be
restored with such a clause if a consumer needs it. -/
theorem efficient_fixed_point (F : PolyTimeFun Prog Prog) :
    ∃ (e : Prog) (p : Polynomial ℕ),
      e.WellScoped 1 ∧
      (∀ v r, (∃ t, e.Runs v r t) ↔ ∃ t, (F e).Runs v r t) ∧
      ∀ v r t, (F e).Runs v r t → ∃ t' ≤ p.eval (v.size + t), e.Runs v r t' := by
  sorry

end MIPRE.Cost
