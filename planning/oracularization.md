# Oracularization: the plan

Status 2026-09-23, written after reading the paper's `oracularization.tex` (`sec:orac-def`,
`thm:oracle-completeness`, `thm:oracle-soundness`, at the commit `bibliography.tex` pins), ledger
node `1.3.5` and its children `1.3.5.1`, `1.3.5.2`, the blueprint's `sec:ps-oracularization`, and
the precedent `planning/repetition-verifier.md` — and before any verifier-level Lean. It is the
analogue of that file for this item: what exists, what the target is, and the pieces in order.
Tracked by issue #189.

**Done:** O1 (#190, `Foundations/OracularTensor.lean`), O2 (#191, `Foundations/OracularTyped.lean`),
O3 (#192, `Foundations/OracularSampler.lean`) and the acceptance law of O4
(`Foundations/OracularDecider.lean`); O4's running time is next.
The rest of this file is the plan as written before the work; what changed on the way is recorded
in the entries below.

## What exists

* **The game level.** `SeededGame.oracular` (`def:oracular-game`), a synchronous game with no
  extra hypothesis; completeness `SeededGame.oracleStrategy` (`lem:oracular-completeness`): a
  PCC synchronous strategy of the doubled input game gives a PCC synchronous strategy of the
  oracularization with the same value; soundness `SeededGame.soundStrategy_value_ge`
  (`lem:oracular-soundness`): value `1 - ε` gives `1 - 24 √ε`, **for synchronous strategies**.
* **The contract.** `MIPRE.Oracularization ℓ` (`Foundations/Pipeline/Oracularization.lean`,
  `def:oracularization-contract`): untyped, level-preserving, with value transfers and a budget
  clause. `GapCompression.ofPipeline` does not consume it (`rem:oracularization-contract`).
* **The detyping compiler, complete.** `CL.Detyping.DeciderProgram.verifier E S D C :
  Verifier (ℓ + 2)` from a `TypedSampler ℓ T`, a total `TypedDecider T` and a cutoff program,
  with PCC completeness (`verifier_hasPerfectPCC`), same-state soundness at the factor `16^|T|`
  (`restrictAmbient_value_ge`), the sampler's cost transfer and a global answer cut
  (`verifier_rejectsLong`). This is `lem:detype-compiler`, and it is what answer reduction uses
  at its exterior boundary (`lem:ar-construction`).

## Three findings, before any Lean

**1. The contract is vacuous.** `Oracularization ℓ` is satisfied by a transformation that does
not oracularize at all: keep the input sampler, and let the output decider reject any answer
longer than the parse bound `p = (λn + 1)^β` and otherwise run the input decider. At the answer
cut `p` its game *is* `𝒱_n` at the cut `p` — same distribution, same predicate on `Answers p` —
so with `ansBound = X` completeness is the identity and soundness holds with `c = 1`
(`ε ≤ √ε` for `ε ≤ 1`, and `1 - √ε < 0 ≤ val*` beyond); the budget clause asks only for a length
check around the input decider. No field mentions the *oracle form* of the output — that one
player's answer alone decides the game check, and the other player's answer must equal one of
its components — which is the only property of oracularization that answer reduction uses: the
PCP replaces exactly that game check (`lem:ar-construction`), and the decoding step returns to
exactly that form (`lem:ar-decoding`). Any contract made of value transfers alone has the same
defect, since values do not see the form. So the target is the **construction** — the typed
oracularized verifier of `sec:orac-def` — with its value transfers as theorems about it, and the
contract is restated as that construction's specification (piece O5). This is the pipeline's
standing risk (`formalization-plan.md`) from the other side: a structure that no supplier had
tried to inhabit, read from the supply side, turns out to say too little rather than too much.

**2. Soundness in Lean is synchronous; every consumer is bipartite.** `valStar` is a supremum
over `TensorProductStrategy`, and so is the detyping transport. The paper's `thm:oracle-soundness`
is bipartite — Naimark, then the chain `eq:oracle-1` to `eq:oracle-3` — and the only bridge from
synchronous to bipartite, `thm:almost-sync`, is off the critical path. A bipartite proof is needed,
and there is a shorter one than the paper's chain. For a projective strategy (every
`TensorProductStrategy` is), fix a seed `z`, write `O` for the first player's oracle measurement at
`(oracle, z)`, `O^𝖠`, `O^𝖡` for its two component marginals, `C` for the first player's
isolated-Alice measurement at `L^𝖠 z`, and `P`, `Q` for the second player's isolated-Alice and
isolated-Bob measurements at `L^𝖠 z`, `L^𝖡 z`. Then

    C_u ⊗ Q_v - O^𝖠_u O^𝖡_v ⊗ Id = (Id ⊗ Q_v)(C_u ⊗ Id - Id ⊗ P_u)
                                  + (Id ⊗ Q_v)(Id ⊗ P_u - O^𝖠_u ⊗ Id)
                                  + (O^𝖠_u ⊗ Id)(Id ⊗ Q_v - O^𝖡_v ⊗ Id),


each front factor is a measurement and costs nothing summed over its outcome
(`sum_snorm_sq_mul_le`), and the three deviations are the cross-party consistencies of the role
pairs `(alice, alice)`, `(oracle, alice)`, `(oracle, bob)`, each at most twice that pair's
conditional failure (`xSqNorm_sum_le_condFail`). So the squared distance between the product
strategy and the oracle's joint marginal is at most `6` times three conditional failures, linearly;
the square root is spent once, in the measurement-level close-values estimate (the paper's
`fact:approx-implies-close-value`), against the oracle's own game check at `(oracle, oracle)`.
Averaging over the four role pairs, each of weight `1/9`: `val ≥ 1 - 9ε - 2√(54ε) ≥ 1 - 24√ε`,
the synchronous constant. Neither the paper's marginalization step nor its commutation step is
needed: the oracle's measurement enters only through its joint marginal `O^𝖠_u O^𝖡_v`, and the
product of the second player's two isolated measurements occurs in one order only.

**3. Levels.** The typed oracularized verifier has `ℓ` levels (the oracle's CL function is the
identity); detyped, `ℓ + 2`. In the paper oracularization is never detyped on its own
(the remark after `thm:oracle-completeness`): it is internal to answer reduction, whose output has
`max{ℓ + 2, 5}` levels precisely because of the one detyping at its exterior. So a
level-preserving *untyped* oracularization has no counterpart in the paper.

## The pieces

**O1 — bipartite soundness at the game level** (`Foundations/OracularTensor.lean`). The
extracted strategy is the adapter `TensorProductStrategy.adapt` (the first player's
isolated-Alice measurement and the second player's isolated-Bob measurement, relabelled along
`OAns.singlePart`); the per-seed estimate of finding 2; the budget over the four role pairs; the
corollary in `quantumValue`: `val*(S.oracular) > 1 - ε` gives `val*(S.toGame) ≥ 1 - 24√ε`.
Blueprint: a lemma beside `lem:oracular-soundness`, proof-level `\leanok` with its guard.

**O2 — the typed game.** `Detyping.typedGame` on the complete type graph with loops over `Role`,
with the role family `(id, L^𝖠, L^𝖡)` and bit-string answers under a bounded-parse predicate,
compared with `SeededGame.oracular` over `Answers B` through the parse (soundness: acceptance
factors through it) and the encoding (completeness). Delivered in the forms the detyping
transport consumes: a PCC value-`1` synchronous strategy of the doubled typed game from
`V.HasPerfectPCC n B` (`oracleStrategy`, doubled and relabelled), and
`quantumValue (typed game) > 1 - ε → V.valStar n B ≥ 1 - 24√ε` (O1, through the parse). Also
`lem:oracle-timeout-pcc` (`1.3.5.2`) at this level. Pure mathematics; no programs.

*As done:* `def:oracular-typed-game`, `lem:oracular-typed-transfers`. Both transfers are proved for
any typed predicate of the right form (`valStar_ge_of_typed`, `exists_typed_perfectPCC`) and then
for the concrete one (`Verifier.oracleTypedPred`: `pairEnc`/`pairDec` serialize a pair by the
postorder bits of its encoding, the format the repeated decider already parses; `parseAns` parses
by role against `B`; `oraclePred` rejects a failed parse). The encoding for completeness is a
pushforward, not an injective relabelling (`SyncStrategy.pushTo`): the honest encoding of a pair
and of a single answer may collide, and only accepted pairs need to survive. The output cut must
hold every honest encoding, `T ≥ 8B + 3`. Soundness holds at every output cut. What O4 has to
prove is exactly that the typed decider program accepts `(n, t, x, u, y, a, b)` iff
`oraclePred (V.seeded n B) (t, x) (u, y) a b`; the detyping transport then applies with
`C.inner n = C.outer n = T`.

**O3 — the typed sampler.** `TypedSampler ℓ Role` from `CL.Sampler ℓ`: the identity as an
`ℓ`-level CL function; a query adapter that forwards `alice`/`bob` queries to the input sampler
with the player replaced, and answers `oracle` queries directly; the `runs_*` clauses, halting on
every input, the time bound `poly(TIME_S)` and the program as a `PolyTimeFun` of `S.prog`
(`lem:oracle-effective-interface`, sampler half). Precedent: `CL/DetypingProgTyped.lean` (the
reverse adapter) and `Prog.routeOneCall`.

*As done:* `lem:oracle-typed-sampler`. The program is `hardcode core (encode S.prog)`, the core
being `Prog.routeOneCall` with the universal machine as the one callee, so `samplerProgFun` is the
s-m-n map, as in repetition. The oracle's queries need no call: the identity's zero vectors are
written over the supplied vector (`y` for a stage map, `u` for a factor space), whose length is the
dimension exactly when the query is well formed, the only case the correctness clauses concern.
The running time (`oracleSampler_timeBound`) is `c (W + 1)^m (|d| + 1)^{e (k + 1)}` with `W`
dominating only the input's coefficient, description length and the index; unlike repetition's
`Repetition.arg` it needs no `10^k`, because a forwarded query is at most twice the typed query
plus a constant, and `|d| + 1 ≥ 2` absorbs that constant factor into the degree.

**O4 — the typed decider.** A total `TypedDecider Role`: the dimension query, the type and length
checks, the bounded parse of each answer against `B` (pairs for the oracle, single strings
otherwise, failures rejected), `L^𝖠 z` and `L^𝖡 z` by marginal queries at level `ℓ`, the input
decider on sanitized copies (the repetition precedent: its cost then needs no factor in `B`), and
the checks of `fig:oracle-decider`. Its acceptance law is O2's predicate; its time bound
`poly(TIME_S, B)` times the input decider's (`lem:oracle-effective-interface`, decider half).

*As done, the acceptance law:* `lem:oracle-typed-decider`. What changed on the way:

* **Totality needs a clock.** The input decider need not halt on the inputs it rejects, and the
  detyping compiler needs a total typed decider. The paper gets both from the timeout-counter
  form, which bounds the input decider's running time by `B_𝒟(n)` read off its description; the
  ambient model has no such form. So the timeout is made explicit: an *index routine*
  (`OracleDecider.Index`) supplies at index `n` a parse cut `B n` and a simulation budget `K n`,
  and the decider (`oracleDecider`) runs an unclocked core under the clocked universal machine for
  `K n` steps. It halts on every input whatever the input programs do (`oracleDecider_total`).
* **The acceptance law is one-sided without a time bound.** The core accepts exactly what
  `oraclePred` accepts at the cut `B n`, with no hypothesis (`core_accepts_iff`, both directions
  through inversion lemmas of the programs, since the input decider may diverge). So the decider's
  acceptance implies `oraclePred` unconditionally (`accepts_sound`), and the converse holds once
  the core's accepting run fits in `K n` (`accepts_complete`). Soundness of the compiled typed game
  therefore holds at every budget (`valStar_ge_of_typedPredicate`), and completeness needs the
  budget to cover the core's runs on answers within the inner cut
  (`exists_typedPredicate_perfectPCC`, whose inner cut must hold every honest encoding,
  `8B + 3`). That hypothesis is the input verifier's running time at `n` in disguise — the role
  the timeout bound plays in the paper's completeness — and the restated contract (O5) must carry
  it. The present contract does not, which is one more sign that no construction inhabits it.
* **No dimension query and no sanitized copies.** The acceptance law concerns well-formed inputs
  only, and the clock makes every input halt, so the core never has to reject malformed data.
* The marginal queries are at the input sampler's top level, where the marginal is the CL function
  itself (`CLFun.truncate_self`). A run makes at most six calls: two marginals and one decision
  for each of at most two oracles.
* The program is `hardcode (shell j) (encode (S̄, D̄, Ī))`, so `deciderProgFun` is the s-m-n map.

*Still to do (O4b):* the core's running time in terms of the input's time bounds — which
discharges the budget hypothesis for an explicit `K` — and the decider's own running time: the
index routine's plus a polynomial in `K n` and the input (the clocked universal machine's
overhead).

**O5 — assembly.** Restate `Oracularization ℓ` as the specification of the construction — typed
output over `Role` on the complete graph, the oracle form of sampler and decider, the complexity
clauses — with completeness and soundness proved from it rather than asked of it; inhabit it with
O3 and O4; the detyped `ℓ + 2`-level verifier as a corollary through the compiler. Blueprint:
`\lean` and `\leanok` on `thm:oracularization`, `lem:oracle-effective-interface`,
`lem:oracle-timeout-pcc`; `def:oracularization-contract` and `rem:oracularization-contract`
rewritten.

## Order and size

O1 first: it is the mathematics the library lacks, and it does not depend on how the interface is
settled. O2 next, again mathematics. O3 and O4 are independent programs, each a pull request;
O4 is the bulk. O5 last — the repetition precedent's rule, consumer before witness, applied the
other way: the consumer is answer reduction's proof, which consumes the construction, so the
contract is written once the construction exists.
