# The machine-level universal machines (#17, #18)

The two remaining `sorry`s of the TM track are the paper-literal universal machines in
`MIPRE/TM/Universal/Spec.lean`:

* `Turing.exists_boundedUniversalCode` (#18, blueprint `lem:bounded-universal-machine`): a code
  `U : Code (i + 2)` which, given `α`, `encodeNat T` and `x`, always halts within `P(|α| + T)`
  steps and outputs `encodeBoundedResult ((decodeCode i α).evalWithin x T)`;
* `Turing.exists_universalCode` (#17, blueprint `lem:universal-machine`): a code
  `U : Code (i + 1)` that produces exactly what `[α]` produces, and, when `[α]` halts in time
  `t`, halts in time and space `P(|α| + t)`.

The main theorem uses neither (route β, `planning/tm-infrastructure.md`): the ambient universal
machines are the `Prog` self-interpreter. These are the paper's own statements, kept as the
TM track's targets. This file is the plan for proving them, written on 2026-09-24 after a
design study of the existing interpreter machine (`MIPRE/TM/Interp/`).

## Two things the statements force

* **No `|x|` in the time bounds.** Both bounds are polynomials in `|α| + T` (resp. `|α| + t`)
  alone. A machine that reads the inputs `x_j` in full violates them. It must read each `x_j`
  only up to a pad of length at least `T + 1`, which is harmless: a machine running for `T`
  steps never sees past position `T` of an input tape (`Code.evalWithin_take`, M2).
* **`T` is given in binary.** A cost bound for the ambient program is polynomial in the size
  of its input, so `T` in binary cannot pay for `T` simulated steps. The program's input
  carries the unary pad as well; the machine writes it, of length `2^k` where `k` is the
  length of the unary prefix of `encodeNat T`, so that `T + 1 ≤ 2^k ≤ 2T + 1`.

Nothing in the statements is false. Malformed `α` decodes to `defaultRejectCode`, `T = 0` and
`i = 0` are ordinary cases, and the space clause of #17 is about the universal machine's own
space, which is at most linear in its time (`spaceUsed_linear`).

## The route

The algorithm — decoding `α`, simulating `[α]` — is written in the ambient `Prog` language, with
the `PolyTimeFun` combinators of `MIPRE/Foundations/Cost/`, where its cost is proved once. The
interpreter machine `MIPRE.TM.Interp.U`, which runs the ambient CEK machine on a `Prog` and is
proved correct in `Interp/Run.lean`, is reused **without being edited**: CookLevin consumes its
state and symbol types. A new machine `M` wraps the interpreter's core with input and output
plumbing, and its correctness is transferred from the interpreter's by a simulation lemma.

Two departures from the interpreter as it stands:

* **The program is not on an input tape.** `M` writes the fixed program onto the control tape
  itself.
* **The budget is a ghost.** The interpreter meters its cost on a unary budget tape and halts
  silently when it runs out. `M` runs the same core *unmetered*; the budget exists only in the
  transfer proof, where it is taken to be the actual cost. So `M` never computes a polynomial
  budget on a tape.

#17 is a restart loop inside `M`: run a round with pad `p`, and if the round's flag says the
simulated machine halted, emit its output; otherwise clean up, double `p`, and run again. By
`produces_iff_exists_evalWithin` and monotonicity of `evalWithin` this halts exactly when `[α]`
does, with the right output, after `O(log t)` rounds.

The alternative — a Turing machine that simulates `Code` directly, parsing descriptions and
multiplexing unboundedly many simulated tapes onto fixed ones — would be larger than the whole
interpreter and much harder to verify.

## Milestones

Each is one pull request, sorry-free, in dependency order. Line counts are estimates.

| | Content | Files | Lines |
|---|---|---|---|
| **M1** | A finite `MultiInputTM` compiled to a `Code`, with `toTM` agreement; the relabelled version and `ComputesInTimeAndSpace` iff | `Code/Compile.lean`, `MultiInput/Congr.lean` | 700–900 |
| **M2** | Generic reachability for `MultiInputTM`; inputs truncated past the time bound (`Code.evalWithin_take`) | `MultiInput/Reach.lean`, `Code/Truncate.lean` | 500–700 |
| **M3** | A pure-Lean reference decoder and simulator over lists and zippers, equal to `decodeCode` / `evalWithin` | `Universal/Reference.lean` | 1300–1500 |
| **M4** | Closure-library additions: capped unary multiplication and powers, capped binary to unary, equality, indexed lookup and update | `Foundations/Cost/UnaryArith.lean` | 800–1200 |
| **M5** | The bounded evaluation as a `PolyTimeFun`, and the round function of #17 | `Universal/BoundedProg.lean` | 1200–1500 |
| **M6** | The interpreter's core factored out: a run from dispatch to the final state for any program, and the static facts the transfer needs | `Interp/Core.lean` | 400–600 |
| **M7** | The machine `M` and the transfer lemma from the interpreter's runs | `Universal/Machine.lean` | 700–900 |
| **M8** | Pre- and post-phase routines: program writer, input encoders bounded by the pad, pad writer and doubler, output emitter, cleanup | `Universal/Phases*.lean` | 1200–1500 |
| **M9** | #18 assembled and packaged | `Universal/Bounded.lean` | 500–700 |
| **M10** | #17: the restart loop, produces-iff, time and space | `Universal/Unbounded.lean` | 800–1000 |

Total about 8.5k–10.5k lines. M1–M4 are independent of each other; M5 needs M3 and M4; M7
needs M6; M9 needs everything but M10.

**M1, M2 and M3 are done.**

* `Code/Compile.lean` compiles a machine over `Fin σ` and `Fin Q` (`MultiInputTM.compile`,
  `toTM_compile`) and, along a `FinCoding`, a machine over structured types
  (`MultiInputTM.toCode`, `toCode_computes_iff`).
* `MultiInput/Truncate.lean` and `Code/Truncate.lean` prove that a run of `L` steps does not see
  past length `L` on its input tapes (`configs_agree_of_take_eq`, `Code.evalWithin_take`).
* `Universal/Reference.lean` is the reference: `refEval_ofCode` (the list simulator is
  `evalWithin`) and `refDecode_eq` (greedy decoding is `decodeCode`), hence
  `refEval_refDecode`. The greedy decoder parses entries until the description is exhausted and
  compares the count with `Q (σ + 1)^(i + w)` only at the end, so no program ever counts to that
  number.

The generic reachability layer listed under M2 is deferred to M6, where the interpreter's core is
its first consumer.

## Risks worth knowing in advance

* **`FoldBounded` for the simulation loop** (M5). A simulated configuration grows by up to
  `w + 1` cells per step and `w` is data, so the step loop needs the general Cobham condition,
  not the additive one.
* **The transfer lemma** (M7) is a case analysis over the interpreter's instructions and phases,
  showing that nothing the core does depends on the budget tape unless the interpreter halts.
* **Executable codes.** `PolyTimeFun` bundles a polynomial and is `noncomputable`, and the
  packaged table of an interpreter-based machine has on the order of `10^10 · 6^i` entries. So
  decision D5's "`#eval`-able universal code" does not survive; the theorems are unaffected.
* **Spec imports.** `encodeBoundedResult` moves to its own file so that the proof files and
  `Spec.lean` do not import each other; the theorem names, which the blueprint tags, stay.
