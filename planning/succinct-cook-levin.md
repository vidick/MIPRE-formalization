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

**S2 — the interpreter machine `U`** (`MIPRE/TM/Interp/`). The hardest piece; the
design, revised after S1 (2026-09-16):

* *Not a `Code`, and not `stepData`.* `U` is a `MultiInputTM` defined directly in Lean,
  with a structured control type (an inductive of control points, each routine's phases
  parametrized by a return site) and a transition function written as a Lean `match`.
  The tableau needs only finiteness and decidable equality of states and symbols, and the
  check circuit of S3 is built from the truth table of `checkPred U acc` (a fixed Boolean
  function: any such function has a circuit, of constant size), so nothing requires a
  dense transition table. `U`'s spec is stated against `Machine.step` on `Cfg` directly,
  by the same case analysis as `stepData_toData`; the tape representation of a
  configuration is `U`'s own, chosen for the tape:
  - values `v : Data` as `v.toBits` (prefix code, bits `0`/`1`);
  - the control on tape `C`: `0 · (p.toData).toBits` for `ev p`, `1 · v.toBits` for `ret v`;
  - the environment on tape `E` as `S(vₙ) # … # S(v₁) #`, innermost value at the right end,
    so that push and pop are appends and truncations and `env.get i` is a walk over `i + 1`
    separators from the right end (past the start: `nil`);
  - the stack on tape `K` as frames bottom to top, each `tag · payload · $`, a closure frame
    carrying its environment in the same `#`-form after a `¶`;
  - alphabet `0 1 # $ ¶` and the blank; `s₀ s₁ = 0 1`, `acc = 1`.
  Each CEK step is a straight-line sequence of routine calls on the shape of the
  configuration (fifteen cases: seven controls to evaluate, the halted return, and the
  returns to the four frames, `loop1` in three sub-cases), rebuilding `C` through a scratch
  tape and updating `E` and `K` at their right ends. The routines: copy a subtree
  (prefix-code scan with a unary depth counter on a counter tape), copy to a marker, skip,
  rewind, move to the end, read a unary tag, locate the `i`-th environment entry, push and
  pop on `E` and `K`, write a constant, and `charge k` (pop `k` cells of a unary budget
  tape, rejecting when it is empty). Cost is exact: `stepCost` is charged per step, the
  sizes of copied values counted while copying, against a unary budget `T` built from the
  binary `T` on an input tape; so `U` accepts exactly when `𝒟` accepts within cost `T`.
* *Inputs.* Seven input tapes: `𝒟` as `(𝒟.toData).toBits`; `n`, `x`, `y` as the bits of their
  `encode`; `T` in binary; the answers `a'`, `b'` as raw bit strings, from which `U` builds
  `(encode a').toBits` (a list of `ofBool`), rejecting a string longer than `T` — so that the
  formula's answer blocks, cells `0 … T - 1` of the two free tapes, are exactly the two-bit
  encodings of strings of length at most `T` (`tapeBits`: bit `2k` "blank", bit `2k + 1`
  "symbol `1`"; the "symbol `0`" cell variable is forced by the one-hot clauses). `U` then
  runs `𝒟.toData` on `encode (n, x, y, a', b')` from `initData`.
* *Statement.* For every CEK configuration `c`, from the tape representation of `c`, `U`
  reaches the representation of `step c` in a number of steps linear in the size of the
  representation, having charged `stepCost c`; hence, with `eval_steps_count` (at most `3T`
  CEK steps) and `eval_steps_bound` (every configuration of the run bounded by
  `CfgBound`, hence of representation size polynomial in `T`, `|𝒟|` and the input), `U`
  halts with output `[1]` within an explicit polynomial `S(T, |𝒟|, |x| + |y| + 2T)` steps iff
  `𝒟` accepts within cost `T`; on other inputs it halts without output or runs past `S`.
* *Framework* (`Interp/Tape.lean`, `Interp/Reach.lean`): tape-content predicates (a list
  held from a position, blanks beyond), the composition of runs (`configs_add`,
  `outputString_add_eq_append`), and the routine specifications as reachability triples
  with step bounds. Routines are verified against the full machine, unfolding only their
  own control points; the correctness of a CEK step composes them.

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

## Status

**S0 — done** (`MIPRE/Foundations/SAT/{Circuit,Cnf,Succinct,Decoupled,Tseitin}.lean`). The
statement `MIPRE.SAT.SuccinctCookLevin`, validated by `MIPRE.SAT.DecoupledDescriber`; the
blueprint restated with the five items; Tseitin with its correctness, in the form the tableau
uses (`tseitin_sat_of_values`: a given assignment carrying the gate values satisfies the
formula; `eval_of_tseitin_sat`: a satisfying assignment witnesses acceptance).

**S1 — done** (`MIPRE/TM/CookLevin/{Local,Tableau,Semantics,Correct,Sound}.lean`;
blueprint `lem:correct-tableau`, guarded). The tableau `tableau M s₀ s₁ S fixed chk` of `S`
steps of a `Turing.MultiInputTM`, its correctness `tableau_sat_iff`, and the two halves
S4 will use directly: `tableau_sat_of_acceptsIn` (the assignment `runAssign` of an
accepting run satisfies the formula, and its time-`0` rows are `inputCellVal` of the inputs
by definition) and `acceptsIn_of_tableau_sat` (a satisfying assignment reads `inputOf` on
its time-`0` rows — `a (cell 0 (inl j) p v) = decide (v = inputCellVal (inputOf j) p)` —
and the machine accepts `inputOf` within `S` steps). Departures from the sketch above,
all deliberate:

* *Windows are five cells wide*, not three, indexed by a center on every tape
  (`Center S = Fin (2S + 3)`): a head at one of the middle three cells sees both the cell it
  leaves and the cell it reaches, and the clamped moves of an input head (`moveInputPos`
  at the ends of the input) are decided from the window alone (`newOffset`). The local
  check is a predicate on the window's one-hot bits (`checkPred`: the bits encode a
  `LocalCfg` that is `LocallyConsistent`), and *the check circuit is a parameter* of the
  formula with its specification `IsCheckCircuit M acc chk` (`chk.evalBits (winBits win) =
  true ↔ checkPred M acc win`) a hypothesis of the lemma. S3 supplies the circuit; the
  circuit-combinator library it needs (one-hot decoding, equality of encoded values,
  the transition table as a lookup) is S3's.
* *Cells*: `2S + 7` per tape, cells `0, 1` and the last two boundary markers; input position
  value `k` at cell `k + 2`, work position `z` at cell `z + S + 3`. Every head is on an
  interior cell at every time `t ≤ S` (`headsIn_cfgAt`: a head moves at most one cell per
  step), which is what makes the boundary rows sound without a bound on the input length —
  a longer input is truncated by the tableau but never reached within `S` steps.
* *Acceptance* is `AcceptsIn M acc input S`: halted at time `S` with output string exactly
  `[acc]`; the emission bookkeeping (`emitOne`, `emitBad`, `emitted`) encodes "one symbol
  output, and it is `acc`". S2's machine `U` must accept in this form (the `Code` convention
  `decodeBitOutput` of a single output symbol is the same thing).
* *Free tapes* hold strings over two symbols `s₀ s₁` (the bit symbols of a `Code` machine)
  followed by blanks; the string is read off the time-`0` row by `freeString`.
* *The explicit variable count* is deferred to S3, where the variables get their binary
  formats: `TabVar` is a finite inductive type and the count is a sum of products of `S`,
  `2S + 7`, the alphabet and state sizes and the window count `(2S + 3)^(i + w)`, which is
  what the padding to `2^m` needs, and the exact figure is only meaningful once the
  numbering is fixed.

**S2 — done** (`MIPRE/TM/Interp/`: `Instr`, `Machine`, `Tape`, `Reach`, `Routines`,
`CopyTree`, `CopyTreeCharge`, `InputRoutines`, `GetEnv`, `Repr`, `Desc`, `Step`, `Run`). The
machine `U : MultiInputTM 7 6 Sym Ctl` (`Machine.lean`; `Sym` has five symbols, `Ctl` is
`ProgId × Fin 32 × Phase`, both `Fintype` with `DecidableEq`, and `U.step` is a Lean
function on them), its inputs `uInput 𝒟 n T x y a b` (the bits of `𝒟.toData`, of
`encode n`, of `encode x` and `encode y`; `T` in unary; `a`, `b` as raw bit strings over
`0 1 = s₀ s₁`), and the acceptance theorem in two halves (`Run.lean`):
`accepts_of_acceptsWithin` — if `𝒟` accepts `(n, x, y, a, b)` within cost `T` and
`|a|, |b| ≤ T`, then `U` halts having output exactly `[1]` within
`runBound 𝒟 n x y a b T` steps, an explicit polynomial in `T`, `|𝒟|` and
`|encode (n, x, y, a, b)|` (`AcceptsFrom`, and `AcceptsFrom.acceptsIn` puts it in the form
`lem:correct-tableau` uses: halted at time `S` with output string `[1]`, for every
`S ≥ runBound`) — and `acceptsWithin_of_accepts` — if `U` halts with output `[1]` at any
time, `𝒟` accepts within cost `T`. Both depend on the standard axioms only. Departures from
the design above, all deliberate: routine instructions with phases (`Instr`, `execInstr`)
rather than a `Code`; `rewind` first moves left, because the case programs leave a head on
the blank after the content; `eraseRight` marks its start with `$` and returns to it; the
dispatcher on `ret` locates the top frame with `leftToMarker` from its `$`; the control tape
may carry garbage after the control word, the scratch tape holds an arbitrary word with its
head inside it. The proof is layered: routine specifications as reachability triples with
step counts (`Routines.lean` and the three routine files), a description layer
(`Desc.lean`: each work tape as an exact list with a head position, each routine a
transformation of descriptions), the fifteen case programs and the dispatcher
(`Step.lean`: `step_run` — from the dispatcher representing `m` with a budget `r ≥ stepCost m`,
`U` reaches the dispatcher representing `step m` with budget `r - stepCost m`, in at least one
and at most `stepBound m` steps; `step_fail` — with `r < stepCost m` it halts silently;
`final_run` — on `ret v` with an empty stack it accepts iff `v = encode true`), and the run
(`Run.lean`: `init_run`, `sim_run` by induction on the number of machine steps with
`CfgBound` giving the size bound `szBound`, and the two halves, the soundness half by taking
the first machine step that is final, over budget, or the `S`-th). What S3 needs from it: the
check circuit for `checkPred U .one`, from its truth table, and the counts
`Fintype.card Sym = 5`, `Fintype.card Ctl = 24 · 32 · 10`.

**S3, S4** — not started.

