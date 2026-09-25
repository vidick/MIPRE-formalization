# What to formalize next, and in what order

Written 2026-09-13 at the maintainer's request ("make a plan for progressing the
formalization … pick a few hard items that will enable real progress"). It supersedes the
forward-looking half of `planning/next-steps.md`, whose items 1–3 and 9 are done and whose
item 5 is now off the path; that file stays as the record of the direct-repetition track,
as `planning/ledger-informed-plan.md` stays as the record of the ledger accounting.

## Three artifacts, and what each is authoritative for

**Ambient introspection is supplied, 2026-09-23.**
`MIPRE.Introspection.exists_seven` in
[Compiler.lean](../MIPRE/Background/Introspection/Compiler.lean) proves
`Nonempty (MIPRE.Introspection 7)`; `MIPRE.Introspection.seven` selects the
compiler. The theorem has passed a standalone Lean check, and its axiom audit
contains only `propext`, `Classical.choice`, and `Quot.sound`. Its sampler,
executable decision compiler, all-index resource contract, honest perfect-PCC
completeness, and output-verifier soundness have passed targeted Lake builds.
The soundness proof uses the proved `QLD.qld_soundness`, with no extraction
callback, and composes the numbered quotient game, legal decoded Pauli support,
canonical error estimates, source-padding removal, and detyping loss.

This is the repository's **ambient seven-level contract**, with its
polynomial-exponent runtime budget and positive-index strict-value soundness
domain. A source-model theorem for arbitrary levels or different source
runtime budgets is a separate statement. Final umbrella, whole-repository,
blueprint coverage, ledger and diff validation all pass. The completed
implementation and validation record is
[introspection-local-progress-20260922.md](introspection-local-progress-20260922.md).

**Historical introspection checkpoint, 2026-09-22.**
[introspection-checkpoint-20260922.md](introspection-checkpoint-20260922.md)
records the boundary at PR #152. Its then-open full-game transport, sampler
packaging, executable branches, uniform budgets, and QLD extraction have since
been connected to the ambient contract above; its original checklist is not
the current task list.

**Construction update, 2026-09-21.** The classical PCP and effective self-dual
basis campaigns are complete, including the proved Shoup construction (#135).
PR #134's semantic detyping, PR #137's executable continuation and PR #140's
adaptive measurement/compiler components are merged.
The continuation constructs growing clocks and their actual binary
parameter compiler, a correctly reindexed clocked source decider with complete
runtime bounds, adaptive honest Read/Hide register PVMs, a coarse-test
product-form stage, common-ancilla quantitative dilation, and extraction from
the actual typed game. Dynamic binary-parameter answer parsers enforce the
inner original-answer cutoff. The actual uniform cross-introspection compiler
computes parameters, queries the source dimension, checks zero padding,
projects questions and makes the clocked source call; exact acceptance,
all-input halting and a composed runtime bound are proved. The full auxiliary
game has an explicit perfect PCC strategy, and the first Hide is identified
with its Pauli-X readout. The actual next-Hide rigidity step on an extracted
EPR seed with arbitrary auxiliary state now follows from the previous fine
estimate and the Introspect-prefix estimate, with no answer-cardinality loss.
The merged work constructs executable
detyping with polynomial sampler runtime, actual finite-game PCC completeness,
ambient Pauli mixing, parsed introspection tests and final strategy extraction.
The conditional compression theorem now accepts polynomial-exponent ambient
decider budgets and retains the input sampler's degree in answer reduction.
Full hiding rigidity is now proved from the extracted primitive X/Z bounds:
the actual Pauli tests supply its base and prefix estimates, and the finite
iteration covers every level on both parties. Read rigidity is also complete.
The actual Sample and Read joint measurements now give the coarse Z and dual
commutator estimates needed for product-form induction. The actual adaptive
prefix law, Z and dual-X register factorizations, exact weighted conditioning,
minimal continuation support, and next-prefix label/projector assembly are now
checked. A complete single-stage construction applies mixing, constructs actual
common-ancilla residual projectors, reassembles a global PVM, and returns a
concrete strategy with a quantitative value-loss bound. Deterministic answer
refinement and an updating decoder now connect the common full-answer alphabet
to the stage alphabet, retaining malformed answers. The next-prefix residual
PVM and its actual selected strategy measurement are constructed explicitly.
The parsed game supplies all three refined errors under one budget, including
the proved factor-two cost for malformed marginal mass. Identity extension
preserves the primitive Pauli, hiding, and Read errors exactly at unchanged
questions. The initial residual measurement, decoded valid-answer support,
and raw selected-measurement identity now give an actual successor constructor.
An explicit positive threshold discharges smallness throughout the finite
Alice iteration, with concrete auxiliary spaces and accumulated failure bounds.
At the terminal level, exact register coverage gives conditional question
readouts tensored with projective auxiliary measurements on the full option
alphabet. Both actual player iterations are now composed, and ordinary-answer
extraction completes malformed auxiliary outcomes without additional loss.
The complete finite parsed-game soundness theorem derives all hiding estimates
and Alice's Z estimate from just the primitive Alice-X/Bob-Z guarantees. It
includes the full recurrence, the large-error regime, and the paper's two-term
profile. Dimension-independent PVM state transfer also gives this conclusion
from an approximately extracted state, with one additional square root.
The honest arbitrary-pair Magic Square extension and its actual perfect PCC
strategy are constructed without the old sorried generic LCS value bridge.
The full 26-type Pauli strategy and its composition with all auxiliary
introspection types now give an actual perfect PCC strategy, including for
arbitrary binary CL source functions after self-dual register transport.
Local-isometry transport, image-complement completion, and valid-answer
error extension now connect the paper's unsquared-distance extraction
interface to finite-game soundness. No malformed-mass assumption is needed.
The concrete Pauli CL family has exact question-law and strategy transport,
explicit binary block numbering, and a checked uniform canonical-line program.
At this September 21 checkpoint, the actual QLD extraction theorem, remaining
executable branches and uniform budgets, and final verifier connection were
still open. The September 23 construction above now composes these into
`Introspection 7`. See
[classical-pcp-introspection.md](classical-pcp-introspection.md) for the earlier
component campaign; the active implementation record tracks the completed
ambient compiler and its remaining repository-wide validation. This supplies
the introspection input to the pipeline; it does not itself supply answer
reduction.

**Synchronization update, 2026-09-16.** The current paper-to-blueprint contracts
and remaining adapters are tracked in [paper-correspondence.md](paper-correspondence.md).
In particular, the formalized canonical-line LIDT theorem does not by itself
discharge the seeded CL game or the paper's tensor/Vid21 intermediates, and the
ambient runtime/PCC interfaces need their stated bridges. Earlier dated coverage
counts and route descriptions below are historical snapshots; the H5 and repetition
progress at the end remains valid with those supply-side obligations.

This is the thing to get right before any of the rest, because the three drift silently.

| artifact | authoritative for |
|---|---|
| `vidick/mipre-proof`, `paper/` | **The mathematics.** Every statement, every constant, every proof. 22k lines of LaTeX over 22 files, audited by a twelve-round adversarial campaign: 123 ledger nodes, 291 challenges all resolved, 120 validated and 3 admitted. |
| `blueprint/` | **The plan, and the record of progress.** What is to be formalized, in what order, and what is done. It is *derived*: every statement in it should be traceable to a paper statement, through `\ledgernode{}`. |
| `MIPRE/` | **What has actually been checked by machine.** Nothing else in the project carries that weight, and nothing in it is true because the blueprint says so. |

Four rules follow, and they are not symmetric:

1. **Read the paper's statement before formalizing the blueprint's.** The blueprint is a
   paraphrase written to be formalizable, and the paraphrase has been wrong — see
   `CLAUDE.md`, "The companion proof repository", for how to read the paper and the
   ledger, and for what may not be copied out of that repository.
2. **The formalization must keep the blueprint current as it goes.** Not only `\leanok`
   when a proof closes and `\lean{}` when a declaration appears: when formalizing shows a
   blueprint statement to be wrong, under-hypothesized or unusable as written, the repair
   belongs in the same pull request as the Lean. A blueprint that lags the Lean is worse
   than no blueprint, because the dependency graph then lies about what rests on what.
3. **When the Lean contradicts the *paper*, that is a finding, not a local fix.** Formalizing
   is the sharpest review a proof gets, and this project has already sent defects back
   (`thm:almost-sync` was false as printed; `thm:orthonormalization` was over-hypothesized).
   Report it to `vidick/mipre-proof` and record it here; do not quietly diverge, and do not
   weaken a Lean statement to make it go through.
4. **Keep the two checkers green.** `scripts/lean-coverage.py --check` holds the blueprint
   and the Lean together (every `\lean{}` name resolves, no accounted module loses its
   coverage, refs/cites/environments resolve); `scripts/ledger-sync.py` holds the blueprint
   and the ledger together (every `\ledgernode{}` names a live node, and stage coverage is
   reported). Both before merging, every time.

## Where things stand (measured 2026-09-13, at `a006c7e`)

- 80 non-vendored Lean modules, 1516 public declarations. The blueprint accounts for 34 of
  those modules, through 53 `\lean{}` tags naming 91 declarations.
- Four `sorry`s: `halting_reduces_to_gameValue` (the main theorem's own statement, the
  target of everything below), the two universal-machine specifications (#17, #18), and one
  LCS bridge lemma.
- Sorry-free and vendored: direct parallel repetition in both models, the classical low
  individual degree test, and — with PR #42 — POVM orthogonalization.
- The ledger is 118 of 123 nodes accounted for, the five missing being the anchoring nodes
  that left with the anchored material.
- **Chapter 6 — the compression pipeline, which is the theorem — has no Lean at all.**
  Not a line: no normal form verifier, no sampler, no conditionally linear function. That
  is the gap this plan is about.

## Read the Lean before adding to it

The blueprint names 91 declarations. The repository has **1516**. Forty-seven modules,
884 declarations between them, are not named by the blueprint at all — not because they
are unimportant but because the blueprint names headline statements and little else. An
agent who reads the blueprint and starts typing will rebuild things that already exist,
and will do it in slightly incompatible vocabulary, which is worse than not doing it.

So: before stating anything, look. `scripts/lean-coverage.py` (no arguments) prints every
module with its named/total counts and then the unaccounted list; `lean_local_search` and
`lean_loogle` from the `lean-lsp` MCP tools find declarations by name and by type. What is
already there, per item of the plan below:

- **H1** — `MIPRE/Background/LIDT/Bridge/Field.lean` already carries a coded finite field
  with a `FieldModel` instance and the encode/decode of scalars, points and lines, built
  for the low-degree test; CL functions live over the same `F_q^s`. `MIPRE/Foundations/Cost/`
  is the machine model a sampler's query interface has to be written in. Nothing exists yet
  for self-dual normal bases, so downsizing to `q = 2` genuinely starts from zero.
- **H2** — `MIPRE/TM/Code/` (raw syntax, semantics, well-formedness, the evaluator, the
  encodings) and `MIPRE/TM/MultiInput/` are a hundred-odd declarations built for exactly
  this proof, with `MIPRE/Cslib/…/MultiTape/` underneath. The two specifications are
  already stated; the infrastructure they are to be proved from is already there.
- **H3** — `MIPRE/Foundations/Cost/FromPartrec.lean` is the bridge from Mathlib's partial
  recursive functions into the ambient model, with `exists_compile` for the halting
  problem: that is the last step of H3, done. `Foundations/Distances.lean` has the POVM
  distance vocabulary (`hsNormSq`, `povmDistance`, `IsPOVMClose`, `inconsistency`) that the
  stability and density estimates want, and `Foundations/Games.lean` the value definitions.
- **H4** — `MIPRE/Foundations/Cost/Succinct.lean` is `IsSuccinctDesc` (blueprint
  `def:succinct`, MNY Definition 2.4) together with the bit-query program and
  `isSuccinctDesc_hardcode`, which is most of obligation (b); `Cost/Toolkit.lean` is the
  efficient universal machine, s-m-n and Kleene recursion *with time bounds*;
  `Foundations/Compression.lean` is the criterion itself.

The general habit: `Cost/` before writing any machine-level lemma, `Foundations/Games.lean`
before any statement about values or strategies, and the vendored bridges under
`Background/` before any statement about the low-degree test, repetition or
orthonormalization. When a reused declaration turns out to be the right name for a
blueprint statement, give that statement the `\lean{}` tag — that is how the accounted
fraction grows without anyone writing new Lean.

## Off the path: do not spend time here

- **`thm:almost-sync` (#22) and its commuting case (#23).** `rem:bipartite-route` now
  states every soundness clause of chapter 6 in `val*`, bipartitely, which is how the paper
  and the ledger state them — not one of the ledger's 123 nodes mentions the synchronous
  value. The transport is used nowhere on the path; `lem:sync-le-valstar`, which is proved,
  covers the one direction still wanted. This retires what was the hardest analysis in the
  project. Both issues should say so rather than sit open as apparent work.
- **Anchored parallel repetition.** Removed in #40; see `planning/ledger-informed-plan.md`,
  "Stage 1.4 is 3/8 on purpose".

## The hard items

Four, chosen because each unblocks work that cannot start without it.

### H1 — Conditionally linear functions and samplers

**Why it is the first thing.** Every object in chapter 6 is a normal form verifier, and a
normal form verifier is a *sampler* plus a decider. Introspection, oracularization and
answer reduction are all transformations of samplers. None of them can be *stated* in Lean
until this exists, so H1 is the difference between a pipeline that can be worked on and one
that can only be read.

**Why it is hard.** A CL function is recursive in its level: a direct sum decomposition
`V = V₁ ⊕ V_{>1}`, a linear map on `V₁`, and for *each value* of that map an
`(ℓ−1)`-level CL function on `V_{>1}`. The dependence of later levels on earlier outputs is
the whole point and is what makes the type awkward. A sampler then presents such a
distribution through a Turing machine answering a fixed query interface — dimensions,
marginals, evaluations of the linear maps and of their canonical complements — and the
blueprint is explicit that this interface should be fixed *once and for all*, because
every later transformation is written against it.

**Source.** `paper/linear.tex`: the definition of a CL function, direct sums of CL
functions, downsizing to `q = 2` through self-dual normal bases, the definition of a CL
sampler and of its distribution. Blueprint `def:cl-function` (ledger node `1.1.2`) and
`def:sampler`; `paper/types.tex` for the typed/detyped layer above it.

**First deliverable.** `MIPRE/Foundations/CL/` with the CL function as an inductive on
levels, its evaluation, the direct-sum lemma, and the sampler query interface; `\lean` tags
on `def:cl-function` and `def:sampler`.

**Done when.** The closure properties the later transformations consume — products,
concatenation, downsizing — are proved, and `def:normal-verifier` can be stated in Lean.

**Risk to manage.** The query interface is expensive to change later. Take it from
`paper/linear.tex`'s definition rather than inventing one, and record in the blueprint any
place where the paper's interface had to be made precise to be formalizable. The campaign
has offered CL closure lemmas (referee report, R9) — ask for them before proving them.

**Invariant 2026-09-15 (found from H4, obligation O2).** No repair this time: the definition
survived its second consumer, and the consumer documented a clause. The time clauses of
`Verifier.IsBounded λ` are guarded by `2 ≤ n`, so at `n = 0, 1` they say nothing and no budget
exists — acceptance at those indices is genuinely `Σ₁`, and `accOf_iff`, the tabulation's bridge
from its acceptance table to the verifier, would have nothing to run under. Nothing at the
use sites supplies `2 ≤ n`. What does is the clause `|𝒱| ≤ λ`, every program encoding to a
`Data.cons` (`Cost.Prog.two_le_esize`), now recorded as `Verifier.IsBounded.two_le` with the
consequence stated where it will be read: drop the size clause and that bridge becomes
unprovable, and with it obligation O2. `IsBounded` was written for `GapCompression`, which
*supplies* it; the tabulation is the first thing that *spends* it, which is why the clause could
look free for as long as it did. The reading of #61 has now been used from both sides and stands
unchanged.

**Amended later the same day, and the amendment is the more useful half.** This note named
*three* bridges — `accOf_iff`, `dimOf_eq`, `margOf_eq`. Only the first is hostage to the size
clause now. `dimOf` and `margOf` were budgeted from `IsBounded` because that was the budget in
the room; `GapCompression.sampler_time` is `∀ λ n` with no hypothesis, and always was, so the
two sampler runs now take the budget as parameters, fed `(ansBound G x n, G.deg)`, and
`dimOf_eq`, `margOf_eq` hold at every string and every level. The question that found it was
not "what does `dimOf` need?" but "what does `Verifier.ComputablyPresented (Vof G U)` ask
for?" — the true dimension at every string and level, `n = 0` and `n = 1` included, precisely
where an `IsBounded` budget says nothing, so the hypothesis had to go and the consumer had to
name the budget that replaced it. That is `planning/h4-assembly.md` §1's rule, *write the
consumer first*, paying on a definition that was already finished: it is usually heard as advice
about new definitions, and it is worth as much asked of an existing bridge by its second
consumer, which is where §1 now records it. `accOf_iff` cannot be freed the same way and must
not be — the decider of the verifier a string denotes is the string's own, wrapped, and nothing
bounds it unconditionally — so the size clause stays load-bearing, for one bridge instead of
three.

**Repair 2026-09-15 (found from H4, part 3b-iii).** The reading below was still too tight.
`Decider.TimeBoundAt n T` bounded the cost by `T · (|input| + 1)`, linear in the input size;
but every decider of the pipeline runs another program through the universal machine, whose
overhead polynomial has degree well above one, so a simulated run costing `T · (s + 1)`
becomes one costing about `Q(T · (s + 1))`, of degree `deg Q` in `s`. No fixed degree is
closed under that composition. `TimeBoundAt n T k` now bounds the cost by `T · (s + 1) ^ k`,
and `IsBounded λ` takes coefficient `n ^ λ` and degree `λ`, so that `λ` bounds both and the
condition stays a polynomial-time one. (Collapsing the two parameters into `T · (s + 1) ^ T`
would also compose, but would let `λ`-boundedness allow degree `n ^ λ` in the input size,
making `thm:compression` an assumption about verifiers its proof cannot compress.)
`GapCompression` gains a `deg` field. Found while writing the wrapper's own time bound, which
is the first place a concrete decider's cost had to be produced rather than assumed.

**Repair 2026-09-14 (found from H4).** `Decider.TimeBoundAt` and `Sampler.TimeBoundAt` were
stated as the paper's supremum over all inputs: halting within cost `T` on every input of
index `n`. In the ambient model that is unsatisfiable by any decider that checks
`|x| = s(n)` for unbounded `s(n)`: a value is inspected in place one node at a time, but a
loop carries the rest of a list to its next iteration only by copying it, so no program
walks an unbounded list within a cost independent of its length. So no normal form
verifier with `s(n) → ∞` was `λ`-bounded, and `MIPRE.GapCompression` had no instance. The
reading is now `T · (|input| + 1)`, the paper's bound up to the cost of reading the input,
with `s(n) ≤ n^λ` (in the paper a consequence) as a clause of `IsBounded`; `GapCompression`
gained `sampler_dim` and `output_rejects_long`, both properties the paper's construction
has and the pipeline will have to establish explicitly. Found while writing the frozen
verifier of H4 (part 3b), the first concrete program whose time bound had to be proved;
nothing else depended on the old reading, no `TimeBoundAt` having been proved anywhere. The
blueprint records the reading at `def:sampler`, `def:decider`, `def:lambda-bounded` and
`thm:compression`.

### H2 — The universal machine (#17, #18)

**Why.** `MIPRE/Foundations/Cost/` is 22 modules of computability toolkit, and the two
statements in `MIPRE/TM/Universal/Spec.lean` are what it assumes. Until they are proved,
every complexity claim in the pipeline rests on a `sorry`, and `thm:compression` and
`thm:halting` cannot be stated with real machines.

**Why it is hard.** A verified universal multi-tape machine over this repository's own
`Code` encoding, with a *polynomial* bound on both time and space, and a bounded variant
that always halts within its budget. The specifications are already written in Lean, with
exact signatures, so the statement work is done and the proof work is all that is left —
which is the hard part.

**Source.** `planning/tm-infrastructure.md` (milestones E–G); `paper/preliminaries.tex`
for the machine conventions and the cost model the paper assumes.

**Done when.** Both `sorry`s in `Spec.lean` are closed, and `Cost/`'s statements that
quote them are unconditional.

**Note 2026-09-14.** The premise above is out of date. Since route β
(`planning/tm-infrastructure.md`, decision of 2026-09-09) the ambient universal machines
are proved by the self-interpreter (`Cost/Universal.lean`, `exists_efficient_universal`),
and `Cost/` imports nothing from `TM/`: no complexity claim of the pipeline rests on these
two `sorry`s. They remain the paper-literal machine statements and the substrate of
`thm:succinct-sat` (requirement R3). H4 does not wait for them.

### H3 — MIP\* ⊆ RE, end to end

**Why.** It is one complete half of the main theorem, it is self-contained, and it is the
`hS` hypothesis that `MIPRE.Cost.compressibility_criterion` consumes. Already begun in
`MIPRE/Foundations/ValueApprox.lean` — continue it, do not restart it.

**Why it is hard.** A machine that on `(t, G)` halts iff `val*(G) > t`, with the boundary
case `val* = t` correctly non-halting. That needs an enumeration of candidate strategies
with entries in `(1/k)ℤ[i]`, a *stability* bound (every candidate is close in value to an
exact strategy of the same dimension) and a *density* bound (every exact strategy has a
candidate nearly as good), both with explicit constants, and then the passage from a
`RePred` to a well-scoped `Prog` through `Cost/FromPartrec.lean`.

**Source.** `paper/recursive.tex`, `cor:mip-re`, statement (S), with a full proof and
explicit constants (ledger nodes `1.1.7.2.1`–`1.1.7.2.6`); the campaign's own claim-test
`scripts/check_enum_stability.py`. The `synval` version is *not* a corollary — rounding
does not preserve synchronicity — which is one more reason the pipeline is in `val*`.

**Done when.** `lem:value-lower-approx` carries `\lean`/`\leanok`, and the easy inclusion
of `thm:mipstar-eq-re` follows from it in Lean.

**Status 2026-09-14** (issue #48). Part 1 of 3 done: the mathematics, in
`MIPRE/Foundations/ValueApprox/` — `lt_quantumValue_iff`, `val*(G) > t` iff some valid
exact strategy with `ℚ(i)` entries has value `> t`, by the Cayley route (exact candidates,
no stability claim, no psd test; the departure from the paper's proof of (S) is recorded
under `lem:value-lower-approx`). Part 2 done the same day: `lem:value-lower-approx` is `\lean`/`\leanok` with a `\leanok`
proof (`MIPRE.ValueApprox.rePred_lt_quantumValue`, an `REPred` on `GameData × ℕ × ℕ` for
thresholds `p / q`), by a primitive recursive certificate check on raw candidates. Part 3 done
the same day: `MIPRE.Cost.exists_semidecider` (`Cost/Semidecide.lean`) turns any `REPred` on
bit strings into a well-scoped `Prog` halting exactly on its members (a `ToPartrec` code for
the predicate, translated by `Prog.ofCode`, after an ambient loop shifts the bits up by one —
a `ToPartrec` code cannot see trailing zeros, and `false` encodes as `nil`), with the converse
`rePred_halts`; `Foundations/ClassMIPStar.lean` defines `IsRE` and `MIPStar` (the computable
version, on game descriptions — `def:mipstar` records the difference) and proves
`MIPStar.isRE`, the blueprint's new `lem:mipstar-sub-re`, and
`exists_semidecider_lt_quantumValue`, the criterion's `hS` for any computable family of game
descriptions. **H3 is done.** What it does not include is the tabulation of a normal form
verifier's game as a game description, which belongs to H4.

### H4 — Instantiating the compressibility criterion

**Why.** `MIPRE.Cost.compressibility_criterion` is proved and sorry-free — the abstract top
of the argument is *done*. What is missing is the join to the concrete pipeline, and
without it every transformation could be formalized and `thm:halting` still would not
follow. This is the item that turns a collection of theorems into the theorem.

**Why it is hard.** Four obligations, none of them bookkeeping (they are R1 of the referee
report, recorded in `rem:compression-abstract`): the criterion's strings are *descriptions*,
never games; `Compr` receives a succinct description and cannot read the described
verifier, whereas `thm:compression` reads it verbatim; the criterion demands preservation of
`A` and `B` for *every* string while λ-boundedness is undecidable, so either the lemma is
re-quantified over a `Compr`-closed class or preservation is proved for junk inputs; and λ
must be chosen along a recursion whose descriptions grow with the level.

**Source.** `paper/recursive.tex` for the recursion and the halting reduction;
`MIPRE/Foundations/Compression.lean` for what is already proved.

**Done when.** The instantiation is stated in Lean with each obligation either discharged
or an explicit hypothesis, and the blueprint says which is which.

**Status 2026-09-14** (started). Part 1: the criterion in the form the instantiation needs,
`MIPRE.Cost.compressibility_criterion_levels` (`Foundations/Compression.lean`; the previous
statement is now its corollary). Classes `A n`, `B n` per level, the semidecider run on
`(x, n)`, and the compression hypothesis restricted to what the proof uses: `n ≥ n₀`,
`2 · |c| ≤ n`, `c` a succinct description with parameter `n`, class at level `2n + 1` to
class at level `n`, with the start level `2 ^ (K + 1 + |e|)` explicit in the conclusion. Two
findings drove it, both recorded in `rem:compression-abstract`: the compressor's time is
polylogarithmic in `n` while one bit query to its input costs `n`, so it cannot read the
string it compresses at all (obligation b is not about reading a verifier verbatim: the
description is embedded in the output for the decider at index `n` to read); and the
recursion's levels go `n → 2n + 1` while compression relates `n` to `2^n`, reconciled by
freezing the described verifier at index `2n + 1` before compressing it. The dictionary now
stands as: strings are pairs `(λ, decider)` read with the compressed sampler `S^compr_λ`
(every string names a verifier); `λ` is the level, `n`-bounded at level `n`, which absorbs
obligation d; obligation c reduces to the semidecidability of `x ∉ B n`, a boundedness
violation or `val* > 1/2` on the tabulated game. Part 2 done the same day: `MIPRE.GapCompression`
(`Foundations/GapCompression.lean`), the statement of `thm:compression` as a hypothesis
structure — `C₀`, the compressed sampler with its polynomial-time description, `Compress` on
pairs of programs, every output packaged as a `Verifier 7`, the `poly(n, λ)` time bound,
completeness (`Verifier.HasPerfectPCC`) and value-form soundness at `n ≥ C₀` for `λ`-bounded
inputs, with the answer alphabets cut at the time bounds; `thm:compression` and
`lem:compress-sampler-indep` carry `\lean`. Part 3a done the same day: the value
bookkeeping, `Foundations/GameTransport.lean` (the quantum value under relabeling of the
alphabets, monotonicity in the decision predicate, and invariance under always-rejected
extra answers — zero extension one way, merging of outcomes the other, which needs the
orthogonality of the outcomes of a projective measurement; the synchronous counterparts
for PCC strategies and the constant strategy, joined in part 6 by the synchronous value
under relabeling) and `Foundations/VerifierValue.lean` (for the
games of a verifier: same sampler and same acceptance at an index give the same `val*` and
the same perfect PCC strategies; answer padding raises `val*`, preserves perfect PCC
strategies, and is neutral when the decider rejects long answers; a perfect PCC strategy
gives `val* = 1`). Part 3b done the same day, in two halves; the first is
the frozen verifier and the ambient toolkit its programs are built from
(`Foundations/Halting/`): `Verifier.freeze` at an index, with the transfer of acceptance,
of `val*`, of perfect PCC strategies and of `λ`-boundedness (`Freeze.lean`); descriptions
as bit strings through the postorder serialization `Data.toBitsPost`, read back by the
stack machine `Data.parse` — postorder because a stack machine is a loop of the ambient
model while a recursive-descent reader is not — with the normalization `Data.natOf` that
makes every string name a parameter (`Descriptions.lean`) and the two programs
`parseProg`, `serProg` (`Serial.lean`); the bounded walks `bitWalkProg`, `eqBitsProg`,
`normBinProg` for the format checks (`Lists.lean`); the arithmetic `incProg`,
`toUnaryProg`, `mulProg`, `polyProg` for the budgets (`Arith.lean`); and `PolyBounded`,
which composes the dozen cost bounds and supplies the threshold above which a polynomial
falls under `2 ^ n` (`PolyBounded.lean`). Every cost bound is of the shape
`T · (|input| + 1)` that `Decider.TimeBoundAt` asks for — which is what the H1 repair of
the same day was found from. Part 3b-ii done the same day: the classes at the level of verifiers
(`Verifier.InClassA`, `InClassB`, disjoint since a perfect PCC strategy gives `val* = 1`)
with the two distinguished verifiers — a decider that is synchronous at `n` and accepts one
fixed answer on every question pair has a value-`1` PCC strategy
(`hasPerfectPCC_of_accepts_diagonal`, the paper's trivial strategy; note that in the
synchronous framework the *everything-accepting* decider is not synchronous at all, so this
is the form the paper's halting case takes here), and a decider that accepts nothing gives
`val* = 0` (`Halting/Classes.lean`); and the reading of a string as a verifier,
`Decider.wrap` and `Verifier.ofSamplerDecider` (`Halting/Wrapper.lean`), with
`ofSamplerDecider_accepts`, the characterization of acceptance. A finding shaped the
wrapper: the *only* structural obligation of `def:normal-verifier` is `accepts_length`, so
the wrapper enforces the question-length check and nothing else — synchronicity and the
answer-length bound are conditions on class membership, not on well-formedness, and the
paper's timeout counter is unnecessary because a non-halting decider simply fails to be
`n`-bounded. Part 3c-i done the same day
(`Halting/Enumerate.lean`): the two alphabets of `V_n` enumerated — the bit strings of length
at most `T` without repetition, giving `Verifier.answerEquiv`, and the questions through
Mathlib's `finFunctionFinEquiv` (`𝔽₂ = ZMod 2` is `Fin 2`), giving `questionEquiv` — and the
bridge `quantumValue_toGame_eq_valStar`: a game description matching `V_n` along those
indexings has the same `val*`, which is what carries the verdict of `lem:value-lower-approx`,
a procedure that runs on game descriptions, back to a verifier. With it, `not_inClassB_iff`:
`x ∉ B n` is "not `n`-bounded" (a search for an input whose run exceeds the budget, Σ₁) or
"`val* > 1/2`", so the semidecider never has to decide `n`-boundedness, which is Π₁.

Part 5 done 2026-09-15, out of order and on purpose: the assembly
(`Halting/Instantiation.lean`), so that what is left is a structure to be inhabited rather
than an argument to be found. A string is read as a parameter and a decider (`descLam`,
`descDec`, with `descOf` the inverse), hence as a verifier (`Vof`), hence the two classes
`classA n`, `classB n` with answers cut at `bound (n + λ)`, the length beyond which a
compressed decider with that parameter rejects. `halting_reduction` then proves
`thm:halting` in `val*` form — a computable map from `Nat.Partrec.Code` to game descriptions
of quantum value `1` when the machine halts and at most `1/2` when it does not — from three
hypotheses: a `GapCompression`, a universal machine, and a `MIPRE.Halting.Obligations`,
whose fields are exactly the open obligations O1, O3 and O4, marked in the file and in
`planning/h4-assembly.md` (O2, the tabulation, is discharged and is no longer a field; the
assembly calls `tab_computable` and `tab_value` directly — and `tab_le`, until the doubling
below deleted it later the same day). It is sorry-free, so `#print axioms` cannot hide any of
them.
Two things are deliberately outside it: the conclusion is in `val*`, since carrying a
perfect PCC strategy to the tabulation needs a synchronous counterpart of
`quantumValue_eq_of_equiv`, and reaching `HaltingGameValue.halting_reduces_to_gameValue`
additionally needs `MIPRE.syncValue` related to `HaltingGameValue.gameValue`, those being
parallel developments. Soundness needs neither.
One tool was added on the way: `Data.primrec_size`, because the level at which the recursion
runs is `2 ^ (K + 1 + esize e)`.

O1 done 2026-09-15 (`Halting/Bounded.lean`, `WrapperCost.lean`, `Strings.lean`). The abstract
half: `IsBounded` is monotone in `λ`, so a verifier bounded at some `λ` lies in the classes at
every level above it, and a cost `C n · (|d|+1)^k` with `C` polynomially bounded fits under
`n^λ · (|d|+1)^λ` for a single `λ` — with the converse, which is the direction
`GapCompression` supplies. The concrete half: the cost of `Decider.wrap`, proved on arbitrary
data throughout, since `TimeBoundAt` quantifies over every input at the index. Then the two
strings, `yNo` with the decider `nil` and `yYes` with a six-node program accepting exactly the
empty answer from both players. The small-parameter corner the ledger flags did not bite: the
`|𝒱| ≤ λ` clause is free, a verifier's size being a constant, and the thresholds are what
`n₀` absorbs. Worth recording that before this nothing in the repository inhabited
`Verifier.IsBounded`, the definition repaired twice in #57 and #61; it went through unchanged.

O2 started 2026-09-15, and its first step was a repair. `Obligations.tab_value` had been
stated for every string; that field is unsatisfiable, acceptance being `Σ₁`, so a computable
`tab` correct at every string would decide the halting problem. It now carries
`(Vof G U x).IsBounded n`, which both uses in `halting_reduction` already have. Then the two
tools the tabulation is built on: `Cost/BoundedEval.lean`, running a program under a *cost*
budget as a total computable function (`Machine.evalData` is only partial recursive and
`Cost.evalWithin` is `noncomputable`, so neither could compute anything) — right because a
derivation of cost `t` is a machine run of at most `3 t` steps and final configurations are
fixed by the step function; and `Halting/Tabulate.lean`, acceptance by an `n`-bounded verifier
as one budgeted run, which is what fills in the acceptance table.

Part 6 done 2026-09-15: those two bridges, which are not part of the assembly and were the
only things standing between `halting_reduction` and `thm:halting` as stated.
`SyncStrategy.relabel` (`Foundations/GameTransport.lean`) plays a synchronous strategy through
a relabeling of the questions and of the answers, with `value_relabel` and `isPCC_relabel`
keeping the value and the commutation condition, hence `syncValue_eq_of_equiv`, the
counterpart of `quantumValue_eq_of_equiv` by the same two-sided `iSup` argument.
`GameData.gameValue_eq_syncValue` (`Foundations/GameDescription.lean`) identifies
`HaltingGameValue.gameValue g.toGame` with `MIPRE.syncValue g.syncGame`: the two structures
of synchronous strategy repackage into each other with the same dimension and the same
operators (`toSyncStrategy`, `ofSyncStrategy`), and `MIPRE.SyncStrategy.value_eq` is already
`HaltingGameValue.strategyValue` written out, so each strategy value is preserved by
definitional unfolding and the two suprema coincide. Both directions went through, so the
result is an equality and not just the two inequalities the reduction needs. The consumer is
`Foundations/SyncTransport.lean`, written against `V.HasPerfectPCC` as the synchronous
analogue of `quantumValue_toGame_eq_valStar`: a description matching `V_n` along the two
indexings inherits its value-`1` PCC strategy (`exists_perfectPCC_syncGame`), hence
`syncValue_syncGame_eq_one`, hence `gameValue_toGame_eq_one`; and in the other direction
`gameValue_toGame_le_of_valStar_le` carries `val*(V_n) ≤ c` to the description, so both
halves of `thm:halting` are now available in the vocabulary of
`halting_reduces_to_gameValue`. It also found a seam in O2, since closed: `Obligations.tab_value`
recorded the tabulation's agreement with `V_n` as an equality of `val*`, from which the
synchronous half cannot be recovered, `synval ≤ val*` pointing the wrong way. Both consumers
here want the matching data along `answerEquiv` and `questionEquiv` instead, so the field
became `tab_match` and delivers it (next paragraph). Both are theorems rather than fields now
that O2 is closed; the paragraph below records that.

O2 continued the same day, and the field changed shape a second time. The parallel branch that
proved the two synchronous bridges reported that an equality of `val*` is not enough for them:
`thm:halting` item 1 claims a value-`1` PCC strategy, so `synval = 1`, and `synval ≤ val*`
points the wrong way — from the value alone a perfect PCC strategy of `𝒱_n` cannot be pushed
onto the tabulation. So `tab_value` is now `tab_match`, delivering the two alphabet
relabelings with the agreement of `μ` and `D` along them, from which `tab_value` reads the
value equality off `quantumValue_toGame_eq_valStar` and the synchronous half is available
too. O2 has the relabelings in hand anyway, building `tab` from `answerEquiv` and
`questionEquiv`, so this costs nothing. Then the pieces the tabulation needs:
`CL.Sampler.queryUnder` (one sampler query under the budget its time bound supplies, with the
dimension and marginal queries read off it — the marginal at the top level is the CL function
itself, `CLFun.truncate_self`), and `Verifier.bitsToIdx` with `questionEquiv_symm_val`, which
says the index of a question is the number its bit string denotes: a `GameData`'s questions are
`Fin (nX + 1)`, so everything a sampler query returns has to become a number.

The question weights followed (`Halting/Tabulate.lean`): `Verifier.weightList` is one entry of
weight `1` per point of `𝔽₂^{s(n)}`, at the index pair its two marginals land on, and
`questionWeight_weightList` and `totalWeight_weightList` say that its `questionWeight` is the
number of points landing on a given pair and its `totalWeight` is `2^{s(n)}` — exactly the
quotient `clDist` is. The bridge is `length_filter_bitStrsOfLen`: the bit strings of length `s`
are the vectors of `𝔽₂^s`, so a count over one is a count over the other.

The answer side followed the question side: `answerEquiv_symm_val` says an answer's index is
its position among the bit strings of length at most `T`, the enumeration `answerList` being
`bitStrsLE` mapped by a truncation that is the identity on them.

Then `tab_match` had to be split, on a third finding of the same kind. A `GameData` denotes a
*synchronous* game by construction — `GameData.toGame` forces `D x x a b` to `false` for
`a ≠ b` — while `Verifier.game` does not, so no tabulation can match a verifier that is not
synchronous at `n`, and `classB n` does not ask for synchronicity. The match is now asked only
of a synchronous verifier, which `classA` supplies through its value-`1` PCC strategy; the
soundness branch needs only that the tabulation does not overshoot, and forcing those tuples to
reject can only lower the value, which is the new field `tab_le`. `halting_reduction` uses
`tab_value` in the halting branch and `tab_le` in the other, and is unchanged otherwise.

The acceptance table followed: `Verifier.accList` enumerates the index tuples of the answer
tuples a predicate accepts over the two alphabets, `mem_accList_iff` says exactly what is in
it, and `bitsToIdx_injOn` is what lets a tuple be read back — among the strings of a fixed
length, a question's index determines it.

O2 done 2026-09-15, and the four fields have left `Obligations`, which now carries O1
(inhabited, `Halting/Strings.lean`), O3 and O4. `MIPRE.Halting.tab`, `tab_computable`,
`tab_match`, `tab_le` and `tab_value` are theorems of `Halting/Instantiation.lean` that
`halting_reduction` calls directly; it is unchanged otherwise, and sorry-free as before. (Of
those five, `tab_le` did not survive the day: the doubling recorded below makes `tab_value`
hold in both branches, and `(tab_value …).le` inhabits `tab_le`'s exact type, so it is
deleted.)
`tab x n` is `Tabulate`'s `tabOf` — the `GameData` two encoded programs and three numbers
describe, and not a verifier, because a `Verifier` is a structure carrying proofs and no
`Primrec` statement can mention one — applied to what a string supplies: the encoded sampler
program `sampData`, the encoded *wrapped* decider `decProgData`, and the dimension, the answer
bound and the level. Both encoded programs needed new machinery. `sampData` is `G.samplerProg`
run by the ambient machine on an encoded input, which is the only way a `PolyTimeFun _ Prog`
reaches a computability proof at all, `Prog` deliberately having no `Primcodable` instance
(`PolyTimeFun.computable_encode_comp`, `Cost/Partrec.lean`). `decProgData` is the wrapper's own
syntax tree built directly in `Data` (`Cost.Prog.ProgD.dWrapCore`, `Halting/Wrapper.lean`,
`dWrapCore_eq` being `rfl`, since it is the same definition seen through the encoding) around
the string's decider read through `Cost.progNorm` — the new module `Cost/ProgData.lean`, which
decides program-hood by one `Data.recD` at a four-component state, four because `Prog.toData`'s
grammar reaches two levels down and a tree recursion sees its children but not its
grandchildren. That fallback is not a nicety: a string whose right component is not an encoding
denotes `Prog.nil`, which accepts nothing, so a tabulation that ran the junk instead would be
*wrong* rather than merely partial. Under all of it, the small arithmetic a budgeted run needs —
`encode_nat_rec`, `primrec_nat_pow` and a bridge between two `BEq` instances for `List.idxOf`
(`Cost/Codable.lean`), the two enumerations (`Halting/Enumerate.lean`), and Horner evaluation of
a fixed polynomial for the answer bound (`Halting/Arith.lean`).

The bridges back are what the rest rests on. `sampData_eq` and `decProgData_eq` hold of every
string; `accOf_iff`, `dimOf_eq` and `margOf_eq` say that on an `n`-bounded verifier the
tabulated numbers *are* the verifier's own. Those three need `2 ≤ n`, which nothing at the use
sites supplies and `Verifier.IsBounded.two_le` does — the subject of the invariant note in H1
above. Then the two clauses of the match: `mu_clause` is the counting argument (the tabulated
weight of a question pair is the number of points of `𝔽₂^{s(n)}` whose two marginals land on it,
over `2^{s(n)}`, which is exactly the quotient `clDist` is) and the `D` clause is the acceptance
table read back through `acc_mem_iff`, with `eXof` and `eAof` the two indexings transported
across `tab`'s sizes. Two findings are about elaboration rather than mathematics and will recur
in O4: the five arguments of `tabOf` are assembled one declaration at a time because the nested
tuple does not elaborate in one go within any heartbeat budget worth setting, and `tab` is made
`local irreducible` before `halting_reduction` for the same reason.

O3 done 2026-09-15, on `Halting/Semidecider.lean` over `Halting/CostBudget.lean` and
`Halting/Semidecide.lean`, and the five plumbing items it was expected to need went through as
listed: the `val*` disjunct of `Verifier.not_inClassB_iff` is two lines,
`rePred_lt_quantumValue_comp` at `tab_computable`; the boundedness disjunct is a search over
`Machine.runForD` with the `dim` clause and the sampler's time clause negated together
(`Verifier.rePred_not_isBounded`, for any computably presented family), over the
computable-test variant of `REPred.of_primrecRel_exists` that such a search needs — it is not
primitive recursive, `sampData` running a `PolyTimeFun` through the machine — which is
`REPred.of_computable_exists`; the two disjuncts merge by dovetailing (`REPred.or`, from
Mathlib's `Partrec.merge'`, which had no such corollary); and the passage to a program reading
`encode (x, n)` goes through `Halting/Semidecide.lean`, once for every type whose
`SizedEncoding` decodes primitive recursively. The sixth item, the one that was not plumbing,
is settled by O2's two payloads, delivered the same day, and they are what makes
`MIPRE.Halting.exists_sem` take **no** hypotheses.

The first payload is the re-budget of the sampler runs, and the amended invariant note in H1
above has it: `dimOf_eq` and `margOf_eq` lost their `IsBounded` hypothesis, which is exactly
what `Verifier.ComputablyPresented (Vof G U)` needed, and `Halting.computablyPresented_Vof` is
the consequence. The second is the doubled question set (`Foundations/GameDouble.lean`), the
cheapest of the three candidate repairs of `planning/h4-assembly.md` §4 item 3 and the only one
that changes nothing outside the tabulation: a `GameData` forces `D x x a b` to `false` for
`a ≠ b`, so a description can match `𝒱_n` only where `𝒱_n` is synchronous and `classB` does
not ask for that, whereas `Game.doubled` — Alice tagged `false`, Bob `true`, everything off that
block rejected — puts no weight on the diagonal at all, so the description's veto is implied by
the distribution rather than constraining the verifier. `hD` stays *total*, which is what made
it cheap: `quantumValue_eq_of_equiv` and `SyncStrategy.isPCC_relabel` apply unchanged and no
support-restricted version of either was needed. `quantumValue_doubled` is the two-sided `iSup`
on `TensorProductStrategy.double` and `undouble`, `SyncStrategy.double` with `isPCC_double`
carries completeness, and `Foundations/SyncTransport.lean` gains `Verifier.doubledGame` and six
lemmas on it beside the four bridges of part 6, which are unchanged. `tab_match` now matches
the doubled game, `tab_value` holds at every `n`-bounded string with no synchronicity
hypothesis, `halting_reduction` uses it in both branches, and `tab_le` is deleted. So neither
`Decider.wrap` nor `thm:compression` had to move, and the classes are fixed under the
compressor rather than waiting on it.

What H4 waits on now is O4, and O4 is the substance: the compressor's own decider, reading its
description by bit queries and freezing at `2n + 1`, and its time accounting (part 4,
unchanged). Before it, one piece of housekeeping that is not mathematics. `Obligations` still
carries O3's `sem`, `sem_closed` and `sem_spec`, and cannot drop them where it stands:
`Halting/Semidecider.lean`, where `exists_sem` is, imports `Halting/Instantiation.lean`, where
the structure is, so the structure sits above its own discharge. Moving `Obligations` and
`halting_reduction` into a module below `exists_sem` in the import order lets the three fields
go and leaves O1 and O4; `planning/h4-assembly.md` §4 item 5 says what moves where. `thm:main`
then waits on O4 alone among the obligations — O1's two strings are inhabited in
`Halting/Strings.lean`, the two synchronous bridges are in place (part 6), the tabulation's
`Computable` witness is proved, and the semidecider is a theorem.

## What to start with

H1 and H3 are done; H4 is in progress; H2 whenever someone wants a self-contained hard
problem.

- **H1 is the one to start now.** It is the only item that unblocks other people's work:
  every chapter-6 statement waits on it, and its interface decision gets more expensive
  the longer it is deferred.
- **H3 is done** (issue #48, three pull requests): `lem:value-lower-approx`, `def:re`,
  `def:mipstar` and `lem:mipstar-sub-re` are in Lean, and the criterion's `hS` is supplied
  for any computable family of game descriptions.
- **H2 is independent of both** and can proceed on its own schedule; it blocks H4 and the
  complexity clauses, not H1 or H3.
- **H4 now.** It does not wait for H2 (see the note there), and H1 has fixed what a
  description is: a sampler and a decider of the ambient model. Inside H4, O1, O2 and O3 are
  done, and the shape question that made O3 worth doing before O4 is settled the cheapest of
  the three ways: the synchronicity `classB` does not carry is supplied by the doubled question
  set, which changes the tabulation only, so neither `Decider.wrap` nor `thm:compression` moved
  and the classes are fixed under the compressor. **O4 is under way, and has a plan** —
  `planning/h4-assembly.md` §4 item 4, six pull requests: the module move (PR-0), the
  statements and an abstract transfer theorem written before any program (PR-1, which carries
  the two decisions that are the maintainer's, #77 and the rejection hypothesis `compr_spec`
  still lacks), the compressor's program (PR-2), its accounting with constants uniform in the
  level (PR-3), the assembly (PR-4), and `thm:main` conditionally on `GapCompression` (PR-5).
  What O4 landed first — `lem:lambda-bound`, the length bound `compr_spec` was unsatisfiable
  without, and the answer-budget comparison — is recorded there too, with two findings of the
  kind §1 of that file collects.

Then, and only then, the transformations themselves — introspection first, as the largest
(`paper/introspection.tex` is 3376 lines) and the one the other two build on — with one step
in between, argued in the next section.

## After H4: the milestone, and what to state before proving

**The milestone, reached 2026-09-16 (#82).** With O4 done (`MIPRE.Halting.exists_obligations`)
and `thm:main` proved conditionally on `GapCompression`
(`MIPRE.Halting.halting_reduces_to_gameValue_of`, `Halting/CompressorProgram.lean`), the
project's claim is *MIP\* = RE ⟸ `thm:compression`, machine-checked*: one structure is the
entire remaining assumption, and `#print axioms` shows nothing else. The blueprint's
`thm:main` and `thm:halting` say so, and so do the README and the blueprint's introduction,
since it is a different kind of claim from "H4 done". Chapter 7's corollaries (`cor:main-quantum`,
`cor:value-uncomputable`, `thm:mipstar-eq-re`) are in, conditionally on the same structure
(`Halting/Corollaries.lean`), together with `thm:halting-undecidable` from Mathlib's
`ComputablePred.halting_problem`; `lem:mipstar-sub-re` was already in.

**The mountain is chapter 6 and its chapter-3 inputs.** Coverage at `2f4cd53`: chapter 6 has 10
of 37 statements with `\lean{}` (the CL foundations and the two hypothesis structures) and 6
with a proof; chapter 3 has 10 of 44, and `thm:ms-rigidity` and the `lem:lidt-*` transfers are at
zero, as are
`thm:succinct-sat` and the two universal-machine specifications (#17, #18) that answer
reduction's Cook–Levin step rests on.

**`thm:qld` is no longer at zero, and this paragraph's count for it is stale.** The QLD campaign
has taken its appendix through stage 5; `planning/qld-campaign.md` is the current record, entry by
entry, and the blueprint's `lem:qld-*` commentary says per lemma what is formalized and what is
not. As of 2026-09-22 the position is: stages 1 to 4 are done; of stage 5,
`lem:qld-exact-paulis` is complete, `lem:qld-pauli-selfcons` has every step of its pulling chain
formalized and wants only the assembly, and `lem:qld-swap` has item 1 given its hypothesis and
four of item 2's displays. **What `thm:qld` still needs, in order of distance to done:**

1. ~~the two game consistencies `eq:qld-unitary-5` assumes~~ --- **done**: they are items 1 and 3
   of `lem:qld-win`, carried into the triangle's vocabulary by `sum_content_pt` and
   `inconsistency_eq_half_xPovmDist`, and `inconsistency_mTilde_pauli_le_of_win` is the display
   from the game's soundness alone;
2. ~~**Both entangled pairs in play.**~~ --- **done**: `MirrorSimul`
   (`MIPRE/Background/QLD/Mirror.lean`). The paper's expanded state is
   `|psi>_{AB} (x) |EPR>_{A'A''} (x) |EPR>_{B'B''}`; `Phi` carries only `A' A''`, read along the
   cut `A A' | B A''`. That economy was right while every consumer compared an exact Pauli object
   on one party with a *point* measurement on the other, which carries no ancilla. Both remaining
   assemblies compare two exact Pauli objects, each needing its party's whole triple, so neither
   could be *stated*. The resolution is neither a retyping of `Phi` nor hiding the second pair in
   `EA` and `EB`: each cut keeps the state it already sees, the other pair is **appended** with
   `expVec _ epr`, and the second cut is a second `SimulPair` at the swapped strategy --- so Bob's
   `mTildeAnc`, `swapA` and `eq:qld-unitary-6` are instantiations of Alice's, with no mirror lemma
   proved. `physVec` is the state on the physical cut and `bornProb_physVec` the bridge to it.
   `planning/qld-two-pairs-scope.md` keeps the two discarded designs and why each fails;
   `reports/qld-stage5-blueprint-repairs.md` records why the pair was needed at all;
3. then the two assemblies, in either order: `lem:qld-swap` item 2's threading
   (`eq:qld-unitary-7` through `-9` and `abs_qform_sub_qform_le` into the statement about
   `V M^(Pauli,W)_h V†`), and `lem:qld-pauli-selfcons`'s chain at a uniform probe, plus
   `lem:qld-povm-to-obs` at its end. The chain's **two ends** are in
   (`MIPRE/Background/QLD/Chain.lean`): `mTildeAnc_eq_sum_chainIdx` is `eq:qld-pulling-2b`,
   `endOpMirror_apply` is the symmetry of `eq:qld-pulling-12` that makes the lemma conclude, and
   `sum_xSqNorm_le_of_endOp` is the triangle that closes it. What is left is the eight `approx`
   steps between them --- every estimate in the tree, only the four-index bookkeeping missing;
4. `thm:qld` itself from the two lemmas.

Items 1 and 2 are done. **Neither of the remaining two needs a new estimate**: every estimate the
appendix uses is in the library, and what is left is assembly.

**Update 2026-09-23.** `lem:qld-pauli-selfcons` is done (#183) and item 1 of `lem:qld-swap` is
unconditional (#184), `MirrorSimul` having been discharged from the game's own hypotheses (#179,
`exists_mirrorSimul`). What is left is item 2's threading and `thm:qld`, and the second is *not*
pure assembly: it needs the error arithmetic that turns the chain `deltaCL -> ... ->
deltaSelfCons -> item 1` into the shape `a (md)^a (eps^b + q^{-b} + 2^{-bmd})`, the discharge of
the regime `48 m d <= q`, the derivation of `4m | q` from admissibility, and a Naimark descent for
general POVM strategies. The four pull requests that finish it, and why the descent was chosen over
narrowing the statement to projective strategies, are the last section of
`planning/qld-campaign.md`, "Finishing `thm:qld`".

**`thm:qld` is proved (2026-09-23).** `MIPRE.QLD.qld_soundness`
(`MIPRE/Background/QLD/Soundness.lean`) is the theorem at proof level, with universal constants
`a >= 1`, `0 < b < 1`, for an arbitrary POVM strategy, under characteristic two, `m | q`,
`m, d >= 1` only, and it depends on no axiom beyond Lean's three. Its shapes are the ones
`quantumValue_ge_of_valid_isometric_images` (introspection) takes.

**And it is connected to introspection (2026-09-23).** The glue recorded here --- item 2 is about
the cube-data reading, the consumer about the valid answers --- turned out to need no bound on the
malformed mass: for a projective strategy the only differing outcome is `h = 0`, and the honest
projector there has weight `q^{-M}` on the EPR state, so the valid sum is at most twice the coarse
one plus `8/q` (`cor:qld-valid`, `QLD/ValidAnswers.lean`). `cor:qld-binary` (`QLD/BinaryForm.lean`)
is the paper's `cor:pauli-binary`, the theorem on the qubit register through a self-dual basis.
`Background/Introspection/PauliExtraction.lean` then supplies the consumer's `hstate`, `hX`, `hZ`
for the actual binary (and field-register) introspection game from any projective strategy
(`lem:intro-pauli-extraction`), and composes them into
`1 - C root_{6l+2}(T) <= val*(G)` (`lem:intro-extracted-soundness`). This upstream theorem
requires original CL functions exact on the whole `M log q`-coordinate register.
The ambient compiler continuation separately composes source padding and its
removal in `CompiledSoundness.output_soundness`. Its decoded Pauli measurements
have proved legal support, so `QLDExtractionAdapter` identifies the coarse and
valid effects exactly and retains the original `errShape` bound. The broader
upstream theorem and the exact supported adapter serve different interfaces;
neither route requires an assumed bound on malformed-answer mass.

**H5, the assembly of `thm:compression` from the
hypothesis structures, is done** (`MIPRE/Foundations/Pipeline/`): `Introspection ℓ`,
`Oracularization ℓ`, `AnswerReduction ℓ`, `Repetition ℓ`, each a `structure` in the vocabulary
of `MIPRE.Verifier` with its time bounds stated as resource budgets (`Budget`,
`Verifier.Within`), and `GapCompression.ofPipeline : Introspection 7 → AnswerReduction 5 →
Repetition 7 → GapCompression` by the margin arithmetic (`Pipeline/Margin.lean`:
`lem:compress-margin`, `lem:compress-tau`, both proved). Oracularization is stated but not
consumed by the assembly, because the paper's `Compress` has three steps and oracularization
is the first step of the *proof* of answer reduction; a proof that `AnswerReduction` is
inhabited will consume it. Writing the consumer changed two blueprint statements:
`thm:parallel-repetition` needed the repetition count and the answer length as independent
parameters (it had coupled them through `TIME_𝒟(n) ≤ (λn)^τ` and a vestigial `κ`), and
`thm:answer-reduction` regained the paper's threshold `C_ar`. The mathematics is now three
independent structures to inhabit, each with a paper section and a ledger stage, each
validated by its consumer. **Repetition is supplied**: `MIPRE.repetition`
(`Background/Repetition/Verifier.lean`, `planning/repetition-verifier.md`) inhabits
`Repetition ℓ` with the repeated sampler and decider written as programs of the ambient model
and their running times accounted for explicitly. Order by distance to done for the rest:
oracularization (one theorem, an input to answer reduction's proof), answer reduction (needs
H2 and `thm:succinct-sat`), introspection last and deepest.

**Update 2026-09-23: answer reduction is the only missing stage.** `Introspection 7` is
inhabited (#193, `Introspection.seven`), and `MIPRE/Background/Pipeline.lean` instantiates
`ofPipeline` with it, `repetition 7` and `Cost.selfUniversal`:
`Halting.mipstar_eq_re_of_answerReduction : AnswerReduction 5 → MIPStar = IsRE`, sorry-free
(`cor:compression-from-answer-reduction`). An inhabitant of `AnswerReduction 5` now closes
`HaltingGameValue.halting_reduces_to_gameValue` in one line. Before starting its proof the
contract was audited against `thm:ar` (`ld_compiler.tex`) for the failure #189 found in
oracularization's: it is not vacuous (the complexity clause excludes the wrapper witness, and
constant deciders fail one of the value clauses), and every difference from the source is a
weakening a construction can absorb (no timeout-counter hypothesis, the time bound assumed
semantically at the index; a larger decider bound whose logarithm is still polynomial; `a >= 1`,
`b <= 1`; no Entanglement clause; `sigma = 0` excluded by `esize_pos`). The audit is recorded
under `def:answer-reduction-contract`. What is left is the source proof: oracularization is
inhabited (#196, `Oracularization.construction`, the typed construction with its value transfers
as theorems), so the thirteen `lem:ar-*` nodes and `thm:answer-reduction`.

The work is tracked in #198 as six packages (AR-1 to AR-6). **AR-1 is done:**
`lem:ar-sandwich-support`, the paper's `lem:ld-sandwich` (NW19's Fact 4.34 with an index), is
`one_sub_sum_bornProb_ldSandwich_le` in `MIPRE/Foundations/LowDegreeSandwich.lean`, for every `k`
and with the constant `2 sqrt 2 k` the source leaves implicit. Two things about it are worth
knowing before AR-5 consumes it. Its relations are the paper's consistency (a disagreement
probability), not the blueprint's squared distance; the blueprint entry had paraphrased both and
is repaired. And the error is linear in `k` only because the layers are added as square roots
(Minkowski in `l2` over index and outcomes); the obvious `(a+b+c)^2 <= 3(...)` triangle would
have made it exponential. The mirror with the parties exchanged, which `lem:ar-giant-sandwich`
also needs, is the same theorem applied to the swapped state.

**AR-2 is done: the simultaneous low-degree test** (`thm:lidt-cl-soundness` through
`lem:lidt-ldc`) is `MIPRE.LIDT.Simul.clSoundness` in `MIPRE/Background/LIDT/Simultaneous.lean`,
for `q` a power of two, `m | q` and `m, d, r >= 1`, with error
`deltaSim = a (dmr)^a (eps^b + q^{-b} + 2^{-bmd})`, `b` the single-codeword exponent and
`a = 40 a_1 4^{a_1}`. It is the paper's padding reduction (`ldt.tex`, Steps 0--5 of the
general-`ldc` proof) in three parts.

* *AR-2a, the extraction* (Step 4): `MIPRE/Background/LIDT/Extraction.lean`,
  `extracted_conclusions`, loss `(K + m) d / q`. The generic coefficient-vector algebra it needs
  (`LowIndDegPoly.coef`, `toMv`, Schwartz--Zippel for coefficient vectors) had been written inside
  the Pauli analysis; it now lives in `MIPRE/Background/LIDT/Coefficients.lean` under the same
  names, so that the LIDT side can use it without importing the QLD chain.
* *AR-2b, the adapter* (Steps 1--2 and Claims 1--3): `MIPRE/Background/LIDT/Padding.lean`,
  `exists_padded_value`, failure at most `9 (K + 1) eps`. It departs from the paper's seed choice.
  The paper draws each player's diagonal seed independently from the law `q^{j-1}`, and pays for
  the independence on the two same-type line subtests with a triangle chain and a `d/q` term,
  `27 M (eps + d/q)` in all. Here both players share one seed *offset* `sigma in Fin (q/m)`, and
  the original seed's block is the deterministic `j = max(i - K, 0)` of the combined seed's block
  `i`. Then every simulated question pair is the pair of questions of a *single* original sample
  (`sampleMap`, `qmap_question`), acceptance transfers subtest by subtest (`accepts_rmap`) ---
  the same-type line subtests to the original equality subtest --- and the push-forward bound of
  `exists_one_sub_value_adapt_le` is a fibre count (`card_sampleMap_fiber_le`): three preimages
  per type, `q^{2K}` combining coordinates, at most `(K + 1) q / M` combined seeds, the offset
  determined. That gives `9 (K + 1) (q/M) / (q/m)`, bounded crudely by `9 (K + 1)`; no `d/q`
  term. The decider is characterized once on the two questions of a sample
  (`accepts_sample_imp`, `accepts_sample_of`), so the transfer is checked on values
  (`valAt_rmap`).
* *AR-2c, assembly and error* (Steps 3 and 5): `clSoundness_padded` applies
  `clSoundness_ldc_one_deltaCL` to the padded strategy, whose point measurements are the combined
  ones (`pointPOVMA_padded`), then `extracted_conclusions`; `deltaCL_padded_le` absorbs
  `deltaCL q M d (9 (K+1) eps) + M d / q` using `M <= 2 (m + r) <= 4mr`, and `one_le_deltaSim`
  covers `m + r > q`, where no padding fits and constant measurements do. The paper's second
  trivial regime, `d >= q`, is not needed: the single-codeword theorem has no `d < q` hypothesis.

**AR-3 is done: the construction** (`lem:ar-construction`, `lem:ar-sampler-independence`):
`AnswerReduction.arVerifier` with its programs as polynomial-time functions and the contract's
`within` clause, `arVerifier_within`, in `MIPRE/Background/AnswerReduction/Construction.lean`;
the pieces and findings are in [answer-reduction.md](answer-reduction.md). Supplying `within`
changed the contract twice, both weakenings: the input sampler's size is bounded by `σ` as well
as the decider's (the output simulates the input sampler through the universal machine), and the
output bound's argument gains `λ + n` (inert in the paper's regime `λ, μ ≥ 1`, `n ≥ 2`). That is
the seventh time a time bound has been refuted from the other side. The construction also asks
of the PCP decider that its parameters be polynomial in `(log n, log T, Q, σ)`
(`ParamsBound`), which the classical PCP decider must be shown to satisfy.

**AR-4 is done: completeness** (`lem:ar-completeness`): `AnswerReduction.arVerifier_completeness`
in `MIPRE/Background/AnswerReduction/Complete.lean`, with the `within` clause and completeness at
one output bound. The contract's completeness now asks `λ, μ ≥ 1`: at `λ = 0` or `μ = 0` the PCP's
validity hypothesis `2 log n ≤ T` fails for large `n` and the clause was false. Compression
supplies both (`Compress.one_le_mu`). The PCP decider must also use the Shoup field
(`ShoupField`), a second hypothesis on it beside `ParamsBound`.

**AR-5 is done: soundness** (`lem:ar-soundness-setup` to `lem:ar-error-assembly`):
`AnswerReduction.arVerifier_soundness` in `MIPRE/Background/AnswerReduction/SoundFinal.lean`, the
contract's `soundness` clause at any answer bound above the answer cut, with `b = clB / 2` and `a`
depending only on the parameter polynomial `R`. It does not follow the paper's route through the
giant sandwich (`lem:ar-giant-sandwich`, `lem:ar-polynomial-strategy`): the oracle measures the
extracted simultaneous `J` itself, whose placement on its blocks, and agreement with the other
player's `G`, holds except with probability `O(E + theta + m'd/q)` by Schwartz--Zippel against the
lifted `G`. That leaves one square root, from oracularization, instead of four. No answer
truncation is needed either: an input within its budget rejects answers longer than its bound.
The route is in [answer-reduction.md](answer-reduction.md). It asks a third hypothesis of the PCP
decider, `FieldLarge`: for every `e`, eventually `q >= (8 (Q + 1) m')^e`, the paper's lower bound
on the field (`eq:pcp-q-choice`) that `thm:pcp-decider` does not carry. The classical decider's
field is `128 m'^2` or so, so AR-6 must enlarge its `fieldDegree` to about `size(8 (Q + 1) m')^2`
(and re-establish `ParamsBound`, which a polylogarithmic `k` keeps).

**AR-6 is done: answer reduction is supplied, and the main theorem is proved.**
`AnswerReduction.answerReduction : AnswerReduction 5`
(`MIPRE/Background/AnswerReduction/Instance.lean`) is `arVerifier` over the classical PCP
decider:

* **`ShoupField`** holds by definition.
* **`FieldLarge`** holds after one change to the classical field degree, now
  `k = 2 ((size Q + size m' + 3)^2 + size m') + 7` (`TM/CookLevin/PcpParameters.lean`,
  `pcpParams_field_eventually_large`). It is still odd and still at least `2 size m' + 7`.
* **`ParamsBound`** follows from `outerDim_polynomial` and `fieldDegree_le`.

With it, `GapCompression.ofAnswerReduction` gives `MIPRE.gapCompression`. `MIPRE/MainTheorem.lean`
proves `HaltingGameValue.halting_reduces_to_gameValue`, the quantum-value form, both
uncomputability statements and `MIPRE.Halting.mipstar_eq_re : MIPStar = IsRE`. All of them use
`propext`, `Classical.choice` and `Quot.sound` only.

The statement file `MIPRE/HaltingGameValue.lean` stays Mathlib-only. It now states the theorem as
the proposition `HaltingReducesToGameValue`, and `MainTheorem.lean` proves it. A proof there
would have to import the whole development, and `MIPRE/Foundations` imports the statement file,
so the proof cannot live in it.

**After AR-6 (2026-09-24): bookkeeping and the unused `sorry`s.** Chapter 6's paper-model
nodes for detyping, introspection and the timeout interface now either carry the Lean that
proves them (`def:typed-sampler-interface`, `def:typed-normal-interface`,
`lem:detype-completeness`, `lem:detype-soundness`, `def:intro-verifier`,
`lem:intro-completeness`) or say which ambient node the Lean uses instead. The chapter-3
nodes of the tensor-code route (`thm:tensor-codes` and its lemmas, `lem:lidt-*` transfers,
`thm:almost-sync`, `thm:ms-rigidity`) and `lem:tracial-le-co` say that the Lean proof does
not use them, and what replaces them. `thm:lcs-perfect` is proved. Six `sorry`s remain, and
the main theorem depends on none of them: the two universal-machine specifications, whose
issues #17 and #18 were closed as not planned (the pipeline uses the ambient universal
machines of `lem:universal-tm`), and the four vendored signed statements of
`Orthonormalization`, which are open upstream.

**The standing risk** is the one `planning/h4-assembly.md` §4 item 4 names: `GapCompression`
has been consumed five times and supplied never — `TimeBoundAt` was refuted three times and
`IsSynchronousAt` once (#77), each time by a consumer — and chapter 6 will read the structure
from the supply side. H5 multiplies that by four. The rule that has held — write the consumer
first, then a witness, even a trivial one — is the mitigation, and the reason H5's statement
work came before another three thousand lines of proof. `GapCompression` has now been
*supplied* once, by `ofPipeline`, which is the first check from the supply side that its
shape is right; of the four structures, consumed once (by `ofPipeline`), `Repetition` has
been supplied — and supplying it changed its statement once more (`Repetition.arg`), the
sixth refutation of a time bound by the other side. A cheap partial check is available
now: a witness for the non-theorem clauses of `GapCompression` alone (`output_*`,
`sampler_time`, `decider_time`, `sampler_dim`, `output_rejects_long`), to confirm the shape is
inhabitable; a full trivial instance is impossible, the structure asserting a genuine theorem.

**Chapter 8 — Tsirelson's problem (#214), proved 2026-09-24.** `MIPRE.tsirelson`
(`MIPRE/Tsirelson.lean`) proves `Cqa ⊊ Cqc` in a finite scenario, unconditionally, with only the
three standard axioms; [tsirelson-campaign.md](tsirelson-campaign.md) records the route. The
correlation sets and the conditional separation are in `MIPRE/Foundations/Correlations.lean`
and `MIPRE/Foundations/Tsirelson/Conditional.lean`. Closedness of `Cqc` comes from a compact
state space and GNS; upper semidecision of the commuting-operator value
(`MIPRE.commutingUpperRE`, `lem:valco-upper-re`) from an Archimedean Positivstellensatz with
exact sum-of-squares certificates and a primitive-recursive checker. No NPA levels, no
projective dilation and no real-closed-field decision: the Lean proof does not rest on the
admitted ledger node 1.8.3. **The explicit separation `thm:separation` (#222) is proved:**
`MIPRE.separation` gives a described game with `val* ≤ 1/2` and `ω_co = 1`, and a correlation in
`Cqc \ Cqa` of payoff 1. It comes from Kleene's recursion theorem applied to the halting
reduction and the upper semidecider, with no entanglement clauses
([explicit-separation.md](explicit-separation.md)). The game is not the paper's `G^sep`;
[reports/separation-upstream.md](../reports/separation-upstream.md) has the findings for the
paper. Still open in chapter 8: `thm:npa-convergence` as stated with its five lemmas, the
rational-data and dovetailed clauses of `lem:valco-upper-re`, and CEP/QWEP.

**Simplification survey (#225), 2026-09-25.** A `find-simplification` pass over every
project-written tree: [simplification-2026-09-25.md](simplification-2026-09-25.md) records 750
compiler-verified dead declarations (`scripts/lean-dead.py`, from Lean's `.ilean` reference
index), two name collisions, and the area surveys' cluster finds — whole files and superseded
routes, duplicates and Mathlib shadows, special cases kept beside their general form — plus the
tagged leaves the Lean proof never uses, which are blueprint decisions. The maintainer's
decision was record only; #225 tracks the implementing PRs.

**An independent statement of Tsirelson's problem, proved (#228), 2026-09-25.** The Lean 4
project `lukasliehr/MIPRE` states the quantitative separation, `Cqa ⊊ Cqc` and the strict
game-value separation in its own vocabulary (games on `EuclideanSpace`, POVMs on both sides,
`sSup` values) and proves none of them. Its statement core is vendored under
`MIPRE/Background/LiehrTsirelson/Upstream/` (`scripts/vendor-liehr.py`) and all three
propositions are proved from `MIPRE.separation` in `MIPRE/Background/LiehrTsirelson/Main.lean`,
sorry-free, through an identification of the two vocabularies: the commuting-operator
strategies are the same data, and a POVM tensor strategy is a projective one by Naimark
dilation. [reports/liehr-tsirelson-bridge.md](../reports/liehr-tsirelson-bridge.md) records
what the comparison showed; `rem:liehr-statements` cites it in the blueprint.

## Working rules for this track

- Every new Lean declaration that discharges a ledger node should say so, and the blueprint
  statement it serves should carry the matching `\ledgernode{}`.
- One transformation per pull request; the blueprint edit that goes with it in the same
  pull request.
- A `sorry` is acceptable only against a blueprint node tracked by an open issue, with one
  exception for vendored *signed statements* — `CONTRIBUTING.md`, "Style", states both and
  the three conditions the exception carries. The four in
  `Orthonormalization/Orthogonalization/Basic.lean` are the case it was written for: nothing
  depends on them, `rem:orthonormalization-scope` says what the tree does and does not
  prove, and `Orthonormalization/Axioms.lean` asserts that each still carries `sorryAx`.
- When the paper and the blueprint disagree, stop and resolve it before writing Lean. The
  answer is worth more than the hour it costs, and it belongs in the blueprint's comments.
