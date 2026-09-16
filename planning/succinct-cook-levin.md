# The succinct Cook–Levin theorem (`thm:succinct-sat`): the plan

Status 2026-09-16, written after `Repetition ℓ` was inhabited (#86) and before anything of
this item existed. `thm:succinct-sat` (ledger node 1.3.1, `answer_reduction.tex`
`prop:standard-succinct-sat`) is the classical core of answer reduction: the statement "the
decider `𝒟` accepts `(n, x, y, a, b)` within time `T`" as a 3SAT formula on `2^m` variables,
described *succinctly* by a circuit of size polylogarithmic in `T`, with the answers `a`, `b`
as the first variables of the formula. It is the one input to answer reduction that is both
unwritten and independent of the low-degree test, which is why it is next. This file is the
decomposition, the analogue of `planning/repetition-verifier.md` for this item.

## What the theorem asks for

The paper's proposition (`prop:standard-succinct-sat`; the blueprint's statement is a
paraphrase, see "Blueprint repairs" below) has five items, all of which the consumers use:

1. For all `a, b ∈ {0,1}^{2T}`: there is a `c ∈ {0,1}^{M − 4T}` with `w = (a, b, c)`
   satisfying `φ`, if and only if `a`, `b` encode (two bits per tape cell, blanks after a
   prefix) strings `a_pre, b_pre` of length at most `T` such that `𝒟` accepts
   `(n, x, y, a_pre, b_pre)` in time `T`. The answer blocks are the *first* `4T` variables.
2. `m = O(log T + log σ)` and `M = 2^m ≥ 4T`.
3. The describer circuit `C` has `s(n, T, Q, σ) = poly(log n, log T, Q, σ)` gates.
4. The algorithm producing `C` runs in time `poly(log n, log T, Q, σ)`.
5. `m` and `s` are computable from the parameters in time polynomial in their bit lengths.

The hypotheses are `max{Q, 2⌈log n⌉} ≤ T`, `|𝒟| ≤ σ`, `|x|, |y| ≤ Q`. Downstream,
`lem:decoupled-5sat` (`prop:explicit-succinct-deciders`) turns `C` into a describer of a
*decoupled* 5SAT formula whose first two blocks are `a` and `b` and whose index lengths
`ℓ₀ = ⌈log 2T⌉`, `r₀ = O(log T + log σ)` and gate count `s₀` are explicit; the PCP
(`thm:pcp-decider`) arithmetizes the Tseitin formula of `C` and needs its exact variable
count (`m' = 5m + 5 + s`, a power of two) and individual degree 6, which is where the
output-wire conjunct and the out-degree-zero hypothesis of `lem:tseitin` enter
(`rem:pcp-power-of-two`; `paper/external/nw19/AUDIT-ERRATA.md` F7.2). Everything here is in
`Prog` cost: "within `T` steps" is `Runs (encode (n, x, y, a, b)) (encode true) t` with
`t ≤ T`, the vocabulary of `Decider.TimeBoundAt`.

## Why not a tableau over `Prog` itself

The classical tableau works because a Turing-machine step is *local*: cell `j` at time
`t + 1` depends on cells `j − 1, j, j + 1` at time `t`, so every clause is an instance of one
fixed check circuit and the describer is polylogarithmic. The step of the ambient model is
not local. The repository's small-step semantics is the CEK machine of `Cost/Machine.lean`
(`Machine.step`, `stepData` on `Data`): one step copies an environment entry of arbitrary
size, walks the environment, or destructures a subtree. On a serialized configuration,
"row `t + 1` is the step of row `t`" is a circuit of size polynomial in the configuration
size, and a succinct description of *that* circuit family is a uniformity theorem for
`stepData` — Cook–Levin in disguise. The alternative, a RAM-style tableau with memory
consistency by sorting, is far heavier than the theorem it would replace. So the tableau is
built for a Turing machine; what is chosen is *which* machine.

## The route: one fixed interpreter machine, and the tableau for it

The paper already applies the tableau to two machines — the fixed packing machine `PACK` and
the decider — and links them. Here both are replaced by one fixed machine `U`, in the
repository's multi-input model (`MIPRE/TM/MultiInput`, `Code k`), that runs `stepData` on a
serialized CEK configuration:

* `U` is fixed, so its local check circuit is a *constant*, as `PACK`'s is in the paper; the
  decider is data on an input tape and never becomes a machine.
* The five inputs `n, x, y, a, b` sit on five input tapes, so the answer blocks are the
  contents of two tapes at time `1` — item 1's block structure is free and no `PACK` is
  needed. (The paper's `PACK` exists only because its decider is a 3-tape machine reading a
  tuple-encoded input.)
* The time bound `T` of the decider, in `Prog` cost, becomes a polynomial tableau length
  through what is already proved: `eval_steps_count` (at most `3T` CEK steps) and
  `size_toData_le` (every configuration along the run has size polynomial in `T`, the
  program and the input), so `U` takes `S(T, |𝒟|, |input|) = poly` steps.
* No compiler from `Prog` to `Code k` per decider (the "requirement R3" of
  `planning/tm-infrastructure.md`); the Turing-machine work is one machine, written once.

Everything the pipeline consumes stays in `Prog` vocabulary; `MIPRE/TM/` is used as the
substrate of one theorem, as `tm-infrastructure.md` (route β, 2026-09-09) foresaw.

## The pieces

**S0 — the statement, consumer first** (`MIPRE/Foundations/SAT/`). Circuits as data: a gate
list with fan-in and fan-out at most two and a terminal output gate (`Circuit`), evaluation
on a bit vector, gate count, a `Data` encoding with `SizedEncoding`; 3-CNF over a finite index
type (`Cnf3`) with satisfaction; `Succinct3SAT.describes C φ` — `C` on `3m + 3` inputs
accepts `(i₁, i₂, i₃, o₁, o₂, o₃)` iff the clause is in `φ` (`def:succinct-formulas`); and
the structure `SuccinctCookLevin` with the five items above as fields, the algorithm a
`PolyTimeFun` of `(𝒟, n, T, Q, σ, x, y)` and the parameter functions `m`, `s` as fields
with their bounds. Validation: write the *statement* of `lem:decoupled-5sat` against it (a
structure `DecoupledDescriber` with the decoupled-5SAT describer and `ℓ₀, r₀, s₀`) before
proving anything, since that lemma and the PCP are the consumers and a statement nobody has
consumed has been wrong every time so far. Blueprint repaired in the same pull request.

**S1 — Cook–Levin for a fixed coded machine** (`MIPRE/TM/CookLevin/`). For any `Code k`
machine with its inputs on the input tapes and a step bound `S`: the tableau variables
(cells encoded on two bits with the boundary symbol, heads, state bits) over a finite index
type; the boundary rows (heads at cell `1`, start state, no boundary symbol inside, blanks
after the input prefixes, blank work tapes, boundary cells fixed at every time — the row the
audit added); the local check circuit reading the three-cell windows of every tape and the
state, its 3-CNF by the circuit-to-3SAT reduction with fresh variables per `(t, j₁, …, jₖ)`;
the acceptance row (halt state with output `1` at time `S + 1`, halting configurations
frozen); `lem:correct-tableau` by induction on `t`; and the equivalence "the formula is
satisfiable with the input-tape rows fixed iff the machine accepts within `S` steps", with
the explicit variable count. Pure combinatorics over `MultiInputTM.step`, generic in the
machine; independent of S2 and S3, and the piece with the least risk.

**S2 — the interpreter machine `U`** (`MIPRE/TM/Interp/`). The hardest and least certain
piece. A prefix serialization of `Cfg.toData` on a work tape (balanced-parenthesis form,
`Data.toBitsPost` or its two-symbol variant); a small *verified macro layer* over `Code`
first — sequencing, a counter tape, copy and skip of a balanced substring, comparison —
without which transition tables cannot be verified by hand; then `stepData` as a machine
(every case of `Machine.stepEv`/`stepRet` is "copy or skip a subtree" plus a tag dispatch),
the simulation theorem against the CEK machine, and the step count `poly(T, |𝒟|, |input|)`
from `MachineBound`. If the macro layer turns out well it also pays for the two TM-track
universal-machine statements still `sorry` (`TM/Universal/Spec.lean`, #17, #18).

**S3 — the explicit describer** (`MIPRE/Foundations/SAT/Describer.lean` and ambient
programs). The `Prog` that, given `(𝒟, n, T, Q, σ, x, y)`, outputs the circuit `C` for the
S1 formula applied to `U`: the variable formats (a tag `α` and the index tuple `β_α`, zero
padding to length `m`), the relabeling of the formula's variables into `{0,1}^m` with the
answer blocks first and dummy variables unused, `m` rounded up to a power of two, the
range checks, the boundary rows and the check-circuit clauses as circuits on the indices; the
proof that `C` describes the relabeled formula; the gate count and the running time. This
is ambient-model programming of the R3 kind (circuits built as `Data`), plus bookkeeping.
Depends on the exact formula shape of S1 and on the statement of S0.

**S4 — assembly.** `SuccinctCookLevin` inhabited from S1 at `U` (S2) and S3, with the five
items; proof-level `\leanok` with the guard in `MIPRE/Axioms.lean`; this file's status.

## Blueprint repairs (S0)

* The theorem's text says the output is a succinct description "in the sense of
  `def:succinct`". That is MNY's notion — a program answering bit queries — and it is not
  what the paper produces; the object is a circuit on `3m + 3` inputs deciding clause
  membership (`def:succinct-formulas`). The statement is restated with the circuit.
* The five quantitative items are absent. They are what `lem:decoupled-5sat` and the PCP
  parameters consume, and the existing comments on the Tseitin defect say a formalization
  must supply exactly them; they are added to the statement.
* `lem:decoupled-5sat` gets `\lean{}` for its statement once S0's consumer structure exists.

## Order, size, risk

S0, then S1 and S2 as separate pull requests (S1 first: it is the mathematics and it fixes
the formula shape S3 needs), then S3, then S4. Sizes, by comparison with item 2 (R3 was
about six thousand lines for two programs with their costs): S0 one to two thousand, S1
three to five, S2 five to eight, S3 three to five. The risk is concentrated in S2; the
mitigation is the macro layer, built and verified before any machine of size, and the
decision to serialize configurations in a form where every step is a bounded number of
subtree copies. Each piece validated against the next consumer before the next is started.

## Companion sources

`paper/answer_reduction.tex`: `sec:ar-tms` (circuits, `def:succinct-formulas`,
`lem:tseitin` with the F7.2 erratum, `prop:tseitin-arith-degree`), `sec:cook-levin`
(`prop:standard-succinct-sat` and its proof: tableau variables, boundary rows
`eq:pack-tape-heads-start`–`eq:pack-boundary-heads`, `def:local-check-circuit`,
`lem:correct-tableau`, `lem:circuit-to-sat-reduction`, `eq:variable-count`, the variable
formats `item:a=1`–`item:a=8`), `sec:succinct-deciders` (decoupled 5SAT,
`prop:explicit-succinct-deciders`, `prop:exciting-padding-prop`,
`prop:explicit-padded-succinct-deciders`). Ledger: node 1.3.1 validated, three challenges,
none open; 1.3.2 amended once (the scope of the existential over the equivalence, now
displayed as an equivalence of two existential statements — the form S0 states).
