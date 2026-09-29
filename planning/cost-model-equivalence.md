# The tree-program cost model against Turing machines: assessment and plan

Written 2026-09-29, at the maintainer's question: how much work is it to show that the
repository's polynomial time (programs over binary trees, `MIPRE/Foundations/Cost`) is
polynomially equivalent to the Turing-machine polynomial time already in Mathlib, and is
there a plan? Short answer: there was no plan; the pieces that exist were built for other
ends, and the largest of them, an interpreter Turing machine for the tree model, is already
here. What is missing is three bridges of a few thousand lines each; the estimate is 8 to
12 thousand lines, two to four months of pull requests at the project's pace, and the
result would retire the one divergence declared in the Palomar metadata.

## 1. The three models and what "equivalent" should say

* **T, the tree-program model** (`Cost/Basic.lean`): `Data` (binary trees), `Prog`, the
  cost-counting evaluation relation `Eval env p r t`, and `PolyTimeFun α β`: a function
  with a closed program computing it on `SizedEncoding` encodings within an explicit
  `Polynomial ℕ` bound in `esize a`, the size of the input's tree encoding.
* **M, the repository's Turing machines** (`MIPRE/TM`, 24k lines): `MultiInputTM i w
  Symbol State`, `i` read-only input tapes, `w` work tapes, one output tape, generalizing
  CSLib's `Turing.MultiTapeTM` (vendored, exactly the case `i = 1`,
  `MultiInput/OneInputEquiv.lean`); the finite syntax `Code i` with `Code.toTM`; the
  resource predicates `ComputesInTimeAndSpace` and `ComputesFunWithBounds`
  (`MultiInput/Complexity.lean`).
* **L, Mathlib's Turing machines**: `Turing.TM0`, `TM1`, `TM2` with translations proved as
  evaluation equivalences (`TM2to1.tr_eval`, `TM1to0.tr_eval`), and, as the only time
  notion Mathlib has, `Turing.FinTM2` (a TM2 with finitely many stacks, states and symbols)
  with `TM2OutputsInTime tm l l' m` and `TM2ComputableInPolyTime ea eb f`: a machine, a
  `Polynomial ℕ`, and for every `a` an output of `eb (f a)` on input `ea a` within
  `time.eval (ea a).length` steps (`Mathlib/Computability/TuringMachine/Computable.lean`,
  278 lines, of which only `id` is shown computable). `ToPartrec` compiles partial
  recursive functions to TM2 with no time bound.

The theorem to aim for is the equality of the two function classes on bit strings, and its
corollary for the class of the main theorem:

```
theorem polyTime_iff_tm2 (f : BitStr → BitStr) :
    (∃ F : PolyTimeFun BitStr BitStr, F.toFun = f) ↔
      Nonempty (TM2ComputableInPolyTime (fun s => s) (fun s => s) f)

theorem mipstar_eq_mipstarTM2 : MIPRE.MIPStar = MIPStarTM2
```

where `MIPStarTM2` is candidate (b) of `planning/palomar-challenge.md` section 3: a verifier
is two `FinTM2` with polynomial bounds, and everything else is as in `MIPRE.MIPStar`. The
encodings differ harmlessly: `PolyTimeFun` bounds time in `esize a`, the size of the tree
`encode a`, and Mathlib in `(ea a).length`; for bit strings the two are within a linear
factor of each other (`Cost/Encoding.lean`, `Cost/TreeBits.lean`), which composes with the
polynomials.

## 2. What exists

**On the T side.** The small-step evaluation machine (`Cost/Machine.lean`: `step`,
`eval_steps`, `eval_of_steps`, cost exact); its step function on `Data`
(`Cost/MachineData.lean`: `stepData`, first-order, `stepData_toData`); polynomial size
bounds on every configuration along a run (`Cost/MachineBound.lean`: `eval_steps_bound`,
`size_toData_le`); the self-interpreter of the model in the model (`Cost/Universal.lean`,
`interpLoop_runs`), which is how the project's universal machines are built (route β of the
universal-machine gate); the closure library of `PolyTimeFun`; and the serialization of a
tree to bits as a polynomial-time program (`Cost/TreeBits.lean`, `PolyTimeFun.toBits`).
2,650 lines for the machine and its bounds.

**On the M side, the decisive asset.** `MIPRE/TM/Interp` (13 files, 7,600 lines) is the
interpreter machine `U : MultiInputTM 7 6 Sym Ctl`, built for the succinct Cook-Levin
theorem (`planning/succinct-cook-levin.md`, S2): a Turing machine defined directly in Lean
that runs `stepData` on the serialized configuration of the evaluation machine, one
evaluation step per routine, with a tape-description calculus (`Desc.lean`) and per-step
cost bounds (`Run.lean`: `stepB`, `szBound`). Its theorems `init_run`, `sim_run` and
`acceptsWithin_of_accepts` say: on inputs `(𝒟, n, T, x, y, a, b)` with `|a|, |b| ≤ T`, `U`
halts having output `1` within an explicit polynomial number of steps iff the decider
program `𝒟` accepts within cost `T`. So the simulation of the tree model by a Turing
machine, with polynomial overhead, is done, in the repository's own model M and for the
decider interface. The plan of `planning/tm-infrastructure.md` had a Milestone H1 (compile
`Prog` to `Code i` with time bounds) that was never done because `U` made it unnecessary,
and its Milestones E to G (a universal machine at the machine level, `TM/Universal/Spec.lean`,
issues #17 and #18) were closed as not planned.

**On the L side.** Nothing of ours; Mathlib has no relation between `FinTM2` and any
multi-tape model, and no polynomial-time closure results.

**Previous assessments.** `planning/palomar-challenge.md` section 3(b) sized a Solution
bridge to Mathlib's TM2 as "months, nothing started", counting a `Prog`-to-`FinTM2`
compiler that `U` now replaces; section 3(d) sized the Cobham route (machine-independent
FP) at "months, fewer than (b)". Neither is a plan; this note is the first.

## 3. The three bridges

**B1. Generalize `U` from the decider interface to functions** (M side, 2 to 4k lines).
`U` takes the program, the unary budget and the five decider arguments on seven input tapes
and outputs one bit. The theorem needed is: for every `PolyTimeFun BitStr BitStr` (or every
`Prog` with a polynomial bound) there is a `MultiInputTM 1 w Sym State` computing it within
a polynomial number of steps (`ComputesFunWithBounds`). Two changes to `U`: the program and
the budget become constants written to work tapes by a prologue (the budget is
`P(|x|)` in unary, computable in polynomial time by a small routine, or taken from a
precomputed table hardwired per input length; the prologue is where the polynomial enters),
and the epilogue emits the bits of the result value (`toBits` of the returned tree, by the
existing tree-copy routines) rather than the acceptance bit. The routine calculus and the
description lemmas of `Interp/` carry over; the risk is the coupling of the 7,600 lines to
the seven-input layout (`IT`, `WT`, `ProgId`), which a variant with the program on a work
tape must re-derive for the routines that read it.

**B2. From M to L with step bounds** (3 to 5k lines). A compiler
`MultiInputTM i w Symbol State → FinTM2` (or to `TM1`, then Mathlib's `TM1to0`) with a
simulation proof and an explicit constant per step: each tape becomes two stacks (the cells
left of the head, reversed, and the cells under and right of it), a head move is a pop and
a push, and one M step is a bounded number of L steps since a `TM2.Stmt` is a finite tree
of `push`/`pop`/`peek`/`load`/`branch` ending in `goto` or `halt`. Only this direction is
needed: the other direction of the equivalence goes from L straight to T (B3). Mathlib's own
`TM2to1` (400 lines plus its infrastructure) shows the shape of such a proof; the new part is
counting steps, which Mathlib's translations do not state. Check first whether CSLib has
since added a `MultiTapeTM`-to-TM2 bridge (upstream moves; the vendored copy is at
`3aa9d44`, 2026-08-03).

**B3. From L to T: a program simulating a `FinTM2`** (1.5 to 3k lines, all in
`Foundations/Cost`). For a fixed `tm : FinTM2`, encode its configurations as `Data`: the
finite state `Option Λ`, the internal `σ` and the symbols `Γ k` as numerals through
`Fintype.equivFin`, the stacks as lists. The step function is a finite function of the state,
the internal value and the tops of the stacks, so it is a decision tree of `elim`s over a
hardcoded table, of cost bounded by a constant of the machine; iterate it `P(|input|)` times
with the clocked loop of the toolkit (`Cost/Loops.lean`, `Cost/Clocked.lean`), then decode
stack `k₁`. Correctness is an induction on steps (`iterate_stepData_toData` is the model);
the time bound is the constant times the polynomial plus the encoding cost. The program
depends on `Fintype.equivFin`, so it is `noncomputable`: fine for the existence statements
`polyTime_iff_tm2` needs, and `PolyTimeFun` already lives in `noncomputable` sections.

**B4. Assembly** (500 lines). The encodings (`esize` against `List.length` for bit strings),
the class `MIPStarTM2`, the two inclusions of verifiers (sampler and decider through B1+B2
one way and B3 the other, with the game characterized as in `Palomar/Bridge.lean`), the
class equality, and the blueprint node: this closes the divergence recorded in
`formalization.yaml`, so the Palomar submission's Challenge can then state polynomial time
through `FinTM2` (candidate (b)) without changing its other parts.

Total: 8 to 12 thousand lines, all mechanical, the B1 generalization being the delicate
piece because it edits proofs written for one layout. Alternatives considered: the Cobham
route gives machine independence but not Mathlib's machines (Cobham's theorem is not in
Mathlib either, so it would need B2 and B3 anyway); Mathlib's `ToPartrec` plus the
repository's `Cost/Partrec.lean` give the computability equivalence without time, which is
not the question.

## 4. Plan

Each step is one pull request; the order puts the self-contained piece first and the
delicate one second, so that the first two are independent and can run in parallel.

* **E0. Statements.** A spec module in the style of `TM/Universal/Spec.lean`: `MIPStarTM2`,
  `polyTime_iff_tm2`, `mipstar_eq_mipstarTM2`, the encoding lemmas' statements, as
  `sorry`ed theorems under a guard that they are not cited by any proof-level `\leanok`;
  a blueprint remark citing them. Half a day, and it fixes the target.
* **E1 = B3** (`Cost/TM2Sim/`): the configuration encoding, the step program, the clocked
  iteration, `TM2ComputableInPolyTime → ∃ PolyTimeFun`. Three to five weeks.
* **E2 = B1** (`TM/Interp/Function.lean` and what it needs in `Routines.lean`): the
  function-computing variant of `U`, `PolyTimeFun → ComputesFunWithBounds`. Three to six
  weeks; start by reading `Run.lean` and `Routines.lean` for what the seven-input layout
  is used for, and decide between a work-tape program (re-deriving the read routines) and a
  copy of `U` with the program tape kept as an input tape plus a wrapper machine that feeds
  it (Mathlib-style machine composition, which M does not have yet).
* **E3 = B2** (`TM/ToTM2/`): the compiler and its step-counted simulation. Four to six
  weeks.
* **E4 = B4**: assembly, blueprint, `formalization.yaml` divergence removed, Challenge
  variant (b) prepared for a Palomar resubmission. One to two weeks.

Gate before E2 and E3: if CSLib upstream has a `MultiTapeTM`-to-TM2 bridge with step
counts, vendor it and drop E3. Gate after E1: if the noncomputable program is unacceptable
to the maintainer, E1 gains a `Code`-like finite syntax for `FinTM2` (Mathlib's `FinTM2` is
already finite, so this is an enumeration, not new mathematics).

## 5. Decisions for the maintainer

1. Target: Mathlib's `FinTM2` (this plan), the repository's own M only (E2 alone, weeks, and
   a divergence still declared, since M is not Mathlib's model), or Cobham (machine
   independence rather than Mathlib).
2. Whether E1's `noncomputable` simulating program is acceptable for the existence theorem.
3. Whether the class equality should replace the Challenge's model in a resubmission, which
   is what removes the divergence from the registry's record.
