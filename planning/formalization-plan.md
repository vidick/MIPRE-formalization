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
for PCC strategies and the constant strategy) and `Foundations/VerifierValue.lean` (for the
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
whose fields are exactly the four open obligations, marked O1–O4 in the file and in
`planning/h4-assembly.md`. It is sorry-free, so `#print axioms` cannot hide any of them.
Two things are deliberately outside it: the conclusion is in `val*`, since carrying a
perfect PCC strategy to the tabulation needs a synchronous counterpart of
`quantumValue_eq_of_equiv` that does not exist yet, and reaching
`HaltingGameValue.halting_reduces_to_gameValue` additionally needs `MIPRE.syncValue` related
to `HaltingGameValue.gameValue`, those being parallel developments. Soundness needs neither.
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

O2 continued the same day, and the field changed shape a second time. The parallel branch that
proved the two synchronous bridges reported that an equality of `val*` is not enough for them:
`thm:halting` item 1 claims a value-`1` PCC strategy, so `synval = 1`, and `synval ≤ val*`
points the wrong way — from the value alone a perfect PCC strategy of `𝒱_n` cannot be pushed
onto the tabulation. So `tab_value` is now `tab_match`, delivering the two alphabet
relabelings with the agreement of `μ` and `D` along them, from which `Obligations.tab_value`
reads the value equality off `quantumValue_toGame_eq_valStar` and the synchronous half is
available too. O2 has the relabelings in hand anyway, building `tab` from `answerEquiv` and
`questionEquiv`, so this costs nothing. Then the pieces the tabulation needs:
`CL.Sampler.queryUnder` (one sampler query under the budget its time bound supplies, with the
dimension and marginal queries read off it — the marginal at the top level is the CL function
itself, `CLFun.truncate_self`), and `Verifier.bitsToIdx` with `questionEquiv_symm_val`, which
says the index of a question is the number its bit string denotes: a `GameData`'s questions are
`Fin (nX + 1)`, so everything a sampler query returns has to become a number.

Remaining for O2: the question weights (one entry per point of `𝔽₂^{s(n)}`, giving
`questionWeight` the count and `totalWeight` the value `2^{s(n)}`, which is exactly the shape
of `clDist`), the answer-index bridge for `answerEquiv`, the acceptance table, the assembly of
`tab`, and `tab_computable`. Then, in order, and identified with the fields of
`MIPRE.Halting.Obligations`:
the *computation* of the tabulation — running the sampler on every point of `𝔽₂^{s(n)}` to
count the question weights and the decider under its budget to fill in the acceptance table,
then `Computable` for the whole map; (O3) the semidecider, from the two Σ₁ disjuncts of
`not_inClassB_iff` once O2 exists; (O4, part 4) the compressor's own decider and its time
accounting. Then `thm:main`, which needs the two synchronous bridges above.

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
