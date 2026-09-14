# What to formalize next, and in what order

Written 2026-09-13 at the maintainer's request ("make a plan for progressing the
formalization … pick a few hard items that will enable real progress"). It supersedes the
forward-looking half of `planning/next-steps.md`, whose items 1–3 and 9 are done and whose
item 5 is now off the path; that file stays as the record of the direct-repetition track,
as `planning/ledger-informed-plan.md` stays as the record of the ledger accounting.

## Three artifacts, and what each is authoritative for

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
thresholds `p / q`), by a primitive recursive certificate check on raw candidates. Part 3 —
the `Prog` semidecider with the `⊆` half of `thm:mipstar-eq-re` — remains.

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
violation or `val* > 1/2` on the tabulated game. Remaining, in order: (2) the Lean
statement of `thm:compression` as a hypothesis structure (Compress, ComputeSampler, `C₀`,
the clauses at `n ≥ C₀` for `λ`-bounded 7-level inputs); (3) descriptions, the classes, the
frozen verifier, and the tabulation of `V_n` as a `GameData` with the agreement of values;
(4) the ambient programs of the compressor's output and their time accounting; (5) the
assembly of `thm:halting` from `thm:compression`, then `thm:main` through the tabulation.

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
  description is: a sampler and a decider of the ambient model.

Then, and only then, the transformations themselves — introspection first, as the largest
(`paper/introspection.tex` is 3376 lines) and the one the other two build on.

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
