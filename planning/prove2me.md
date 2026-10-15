# Submitting the recursive compression lemma to Prove2Me

Written 2026-10-01 at the maintainer's request ("look into the prove2me platform … possibly
starting with the MNY compression theorem"), against `e2f4de6`. Prove2Me (`prove2.me`) is the
collaborative Lean 4 formalization platform of Tianyi Peng's group at Columbia, grown out of
Kunal Marwaha and Henry Yuen's Spring 2026 class; its paper is arXiv:2608.28433. This note
records what the platform is, why the abstract recursive compression lemma is the right first
submission, what a submission needs, and the open points. It was written from the platform's
own documentation — the FAQ, About and Terms pages of `prove2.me` (read on 2026-10-01, platform
release 0.11.6), `prove2me/prove2me_workspace` (the agent harness: `SKILL.md`, `references/`,
`scripts/`, `examples/upload_full_project/`) and `prove2me/formalpedia` (the daily export) —
and against the repository as measured below. The arXiv paper itself could not be read from a
cloud session (the host is not in the allowed list); nothing here depends on it.

## What Prove2Me is

- **Missions** are formalization projects, one paper, textbook chapter or open problem each.
  A mission has a *captain* who assembles its core — the goal theorem, the definitions it
  rests on and the *milestones*, lemma-level targets stated "usually straight from the source
  paper" — and vouches for their faithfulness. Before a public mission goes live the captain
  audits that core and a platform moderator approves it; everything agents produce beneath it
  is checked by the kernel alone. A *private* mission skips review and is visible only to its
  creator; it can be released later, irrevocably.
- **A theorem is an immutable card**: a preamble plus a Lean 4 statement ending in `by sorry`,
  with a natural-language statement in Markdown and KaTeX and a source citation. Statements and
  proofs are separate: a proof is a file declaring a top-level `theorem solution` of exactly the
  target's type, with no `sorry`, verified server-side (verdicts `ACCEPTED`, `SKETCH_ACCEPTED`,
  `WA`, `CE`, `SORRY`, `FAILED`); its axioms are checked against a whitelist. Nothing is ever
  edited; a wrong item is *deprecated* and re-uploaded. Only the title, natural-language
  statement, source and tags stay editable.
- **A proof-sketch** is a solution that `import`s other platform theorems, proved or still
  open, each import becoming a new open problem; the parent resolves when the last child does.
  This is how large proofs are decomposed, and how results carry across missions.
- **Formalpedia** is the public library of everything proved, exported daily to
  `prove2me/formalpedia` (`Theorems/Thm_<slug>.lean`, `Definitions/Def_<slug>.lean`,
  `Solutions/Sol_<slug>.lean`, with `index.jsonl` and `graph.jsonl`). Author credit is
  permanent and import citations are recorded.
- **Licensing** (terms effective 2026-09-24): public contributions, including those submitted
  through an agent, are licensed Apache 2.0 "to the extent you own or are authorized to license
  them"; private content is excluded; the contributor keeps copyright. This repository is
  Apache 2.0 and the compression closure carries Thomas Vidick's copyright headers, so there is
  nothing to clear.
- **Environments.** Every theorem belongs to exactly one pinned environment and a proof may
  import only theorems and definitions of the same environment; nothing outside Mathlib and
  the platform's own content can be imported, so a project's dependencies have to be uploaded
  as content. The server elaborates with `autoImplicit false`. Three environments as of
  2026-10-01 (the FAQ says "newer versions will be added over time"; `GET /api/v1/environments`
  is authoritative and needs a login):

  | Lean toolchain | Mathlib | default |
  |---|---|---|
  | `v4.33.1` | `0df444a360eaa60ab8c11dca51a86af692955474` | yes |
  | `v4.30.0` | `c5ea00351c28e24afc9f0f84379aa41082b1188f` | |
  | `v4.29.0-rc3` | `777aaa61dcd2a1258d2b4962dbe983ede4d23b2e` | |

- **Uploading a finished Lean project** is an explicit, documented use case
  (`references/upload_full_project.md`, FAQ "I already have a Lean project"). Two Lean
  meta-programs in `scripts/` extract the declaration graph (`extract_decl_graph.lean`:
  names, kinds, `typeDeps` versus `valueDeps`, privacy, spans) and the statement/proof
  boundaries (`extract_sketch_info.lean`); a seven-phase playbook then plans the node set,
  generates the platform files by *deleting unselected declarations from the original
  sources* (never by hand), platformizes them (`namespace` → `open`, fully-dotted names, the
  solution hoisted to a top-level `theorem solution`), validates them by `lake build` and a
  diff of pretty-printed types, drafts metadata, and uploads definitions, then theorems
  leaves-first, then solutions leaves-first. A mission proposal is drafted on top and handed to
  the human for audit.
- **Cost and access.** The platform is free; work runs on one's own agent subscription. An
  account, an API key (`p2m_…`, 30 days) exchanged for hourly tokens, and the terms acceptance
  are all that is needed. Anyone can be a captain. The platform describes itself as the layer
  between foundational libraries and registries: "Registries such as Palomar record
  formalizations that are already finished. Prove2Me covers the stretch in between."

## Why `recursive_compression` first

The platform's unit is a self-contained statement whose proof can be rebuilt from Mathlib and
platform content alone. That rules out the main theorem for now — its proofs reach the vendored
trees (322 MIPStarRE modules, the repetition theorems) which would all have to be uploaded as
nodes first — and singles out the one headline result whose closure is small and entirely this
project's own. Measured at `e2f4de6`:

| | |
|---|---|
| theorem | `MIPRE.Cost.recursive_compression` (`Foundations/Compression.lean`); blueprint `lem:recursive-compression`; [MNY, Lemma 5.1] |
| axioms (`lean_verify`, 2026-10-01) | `propext`, `Classical.choice`, `Quot.sound`; no `sorry`; guarded in `MIPRE/Axioms.lean` |
| import closure | 24 modules, 8,872 lines: `Foundations/Compression.lean`, 22 modules of `Foundations/Cost/`, `MIPRE/Tactics.lean` |
| declarations | 626: 191 `def`, 420 `theorem`, 5 `structure`, 5 `inductive`, 2 `class`, 2 `abbrev`, 1 `instance` |
| external imports | Mathlib only: `Computability.{Halting,Partrec,PartrecCode,Primrec.List,TuringMachine.Config}`, `Algebra.Polynomial.Eval.*`, `Data.Nat.{Bits,Size}`, `Data.ENat.Lattice`, `Basic.Denumerable`, tactics |
| vendored code | none (nothing under `Background/`) |
| statement surface an auditor reads | `Data`, `Prog`, `Prog.WellScoped`, `Eval`, `Halts`, `SizedEncoding`/`encode`/`esize`, `BitStr`, `Prog.Runs`, `PolyTimeFun`, `IsSuccinctDesc`: about 300 lines of `Cost/{Basic,Encoding,PolyTime,Succinct}.lean` |
| proofs over 40 lines (platform nodes) | 26; largest `compressibility_criterion_nested` 339, `eval_steps_bound` 272, `stepCostProg_runs` 209, `recursive_compression` 168, `univTProg_runs` 157 |
| proofs of 11–40 lines (nodes if promoted) | 104 |
| proofs of at most 10 lines (inlined into consumers) | 290 |
| names the platform rejects | 12: `toBool?`, `toList?`, `toNat?` and their lemmas (`toBool?_ofBool`, `toList?_ofList`, `toNat?_ofNat`, `toBool?_eq`, `primrec_toBool?`, `toList?_eq_recD`, `primrec_toList?`), `isZeroProg_runs'`, `decProg_runs'` |
| custom syntax | one `macro "size_omega"` (`Cost/Interpreter.lean:40`), 40 uses in that file |
| `private`, `sorry`, `native_decide`, `set_option` | none |

The same closure carries the companions worth uploading with it: `recursive_compression_halting`
(the halting-problem corollary consumed by `MIPRE.HaltingGameValue`), Lin's
`compressibility_criterion` with its `_levels` and `_nested` forms (blueprint
`lem:compressible-criterion`), and the toolkit the blueprint lists as milestones —
`exists_efficient_universal` / `exists_clocked_universal` (`lem:universal-tm`),
`PolyTimeFun.smn` (`lem:smn`), `efficient_fixed_point` (`lem:kleene`), `IsSuccinctDesc`
(`def:succinct`).

**The Mathlib match.** The platform's default pin `0df444a` is Mathlib's commit "chore: bump
toolchain to v4.33.1", whose parent `db584cd` is the tag `v4.33.0` — exactly this repository's
pin until the bump of 2026-09-28 (PR #237). Its parent, **`70cbf1c`** ("Rename the classes …
Palomar plan", 2026-09-28), is therefore on Lean `v4.33.0` / Mathlib `db584cd`, one
toolchain-only commit behind the platform, and the compression closure at `70cbf1c` differs
from `e2f4de6` only by the module headers, the dropped `private` markers and the
`MIPRE.Tactics` bundle. So the upload source is `70cbf1c` and drift repair is nil: **checked 2026-10-01** (step 3
below), the closure builds unchanged against the platform's environment, with no errors and
no warnings, and every headline declaration depends on `propext`, `Classical.choice` and
`Quot.sound` only.

## Plan

1. **Account.** Register on `prove2.me`, mint an API key, accept the licensing terms. The
   agent bootstrap is `https://prove2.me/start.md`; the harness is cloned to
   `$HOME/prove2me_workspace`. Check `GET /api/v1/environments`.
2. **Source commit.** `70cbf1c` if `v4.33.1` is still the newest environment. If a `v4.35`
   environment has appeared, use `main` instead; then the module headers must be stripped
   (`module`, `public import` → `import`, `@[expose] public section` and its closing `end`),
   which the playbook's Phase 3 only half-covers ("strip the keyword `module` before the
   first `import`").
3. **Build the closure against the platform pin.** Done 2026-10-01, in a cloud session, in
   a scratch workspace outside the repository: the 23 modules of the closure at `70cbf1c`
   (`git show 70cbf1c:<path>`; `MIPRE/Tactics.lean` did not exist yet), a `lakefile.toml`
   with `autoImplicit = false` requiring Mathlib by git URL at `0df444a`, a `lake-manifest.json`
   written by hand from Mathlib's own manifest at that commit (its eight dependencies marked
   `inherited`, plus the Mathlib entry; `lake update` was not run), and Mathlib itself
   fetched shallow (`git fetch --depth 1 origin 0df444a…`, 121 MB) into
   `.lake/packages/mathlib` before Lake looked for it. The toolchain came from the GitHub
   release asset `lean-4.33.1-linux.tar.zst` (570 MB), unpacked next to the workspace and put
   first on `PATH`, since the cloud image has no `elan`. `lake exe cache get` restricted to
   the closure's 16 Mathlib imports restored 1,278 files in 17 s (the file arguments are
   resolved against the current directory, so they are written
   `.lake/packages/mathlib/Mathlib/….lean`); the full Mathlib cache was not needed. Then
   `lake build MIPRE`: **1,323 jobs, 27 modules of ours, 65 s, no errors, no warnings**, and
   `#print axioms` on `recursive_compression`, `recursive_compression_halting`, the four
   `compressibility_criterion*`, `exists_efficient_universal`, `exists_clocked_universal`,
   `efficient_fixed_point` and `PolyTimeFun.smn` gives the three standard axioms for each.
   Disk: about 2.5 GB in all. One Lake detail worth knowing: a `lean_lib` whose `roots` is
   the single module `MIPRE.Foundations.Compression` does not claim its sibling imports as
   local modules and fails with "object file … does not exist"; root the library at an
   aggregator `MIPRE.lean` instead.
4. **Extract and plan.** Run `extract_decl_graph.lean` and `extract_sketch_info.lean` over
   the closure; classify by the playbook's rules (node above 40 proof lines, or 11–40 with a
   promotion signal; inline helper otherwise; one `Definitions` bundle per source module with
   def-material; theorems cited by definition bodies proved inside the bundle). Expect on the
   order of 30 to 130 theorem nodes and about 20 definition bundles.
5. **Generate and platformize.** Skeleton subtraction from the originals; the 12 renames
   (`toNat?` → `toNatOpt` or similar, primes → `_alt`/`_rev`), rewriting the use sites from
   the extracted ranges; the `size_omega` macro kept in the `Interpreter` bundle, or expanded
   at its 40 uses; everything wrapped in the `MIPRE.Cost` namespace it already has.
6. **Validate locally**: `lake build` the staged `Definitions/`, `Theorems/`, `Solutions/`
   trees; pretty-print and diff every node's elaborated type against the original; accept only
   universe-name differences.
7. **Metadata.** Per node a title, a natural-language statement (KaTeX; the blueprint text of
   `lem:recursive-compression` is nearly ready) and a line-linked source. A shared project tag
   for the later `GET /theorems?tags=…` check.
8. **Upload**, idempotently and in order: definitions, theorems leaves-first, solutions
   leaves-first. Every solution resolves straight to `Proved`.
9. **Mission proposal**, type `ResearchPaper`: an 800–1,500-word description in the seven
   sections of `references/mission_description.md` (motivation, setting, target, significance,
   difficulty, formalization scope, references); goal `recursive_compression`; milestones the
   toolkit lemmas and `compressibility_criterion`, each with a read-back written by an
   independent agent from the Lean alone (`references/mission_auditor.md`); the maintainer
   audits the read-backs against the source and submits. Public (moderator review) or private
   (live at once, releasable later).

## Open points

- **Faithfulness.** The platform's single criterion for a mission core is that each Lean
  statement "say exactly what the source says, no less and no more". `recursive_compression`
  is a documented variant of [MNY, Lemma 5.1]: the ambient tree-program cost model in place of
  Turing machines, the succinctness budget `(n + 1) · (|m| + 1)²` in place of "≤ n for all m"
  (vacuous in a model that charges to read `m`), the next level `2n + 1`, and the
  one-directional Kleene recursion (`Compression.lean` module docstring; decisions K-D3, K-D5,
  K-D10 of `planning/compression-track.md`). State these in the natural-language statements
  and in the description's *formalization scope* section rather than let a moderator or a
  read-back find them.
- **Source.** The bibliography cites MNY as "Manuscript" with no URL; the platform wants a
  resolvable source per node and arXiv/DOI links in the description. A citable location for
  the manuscript is needed, or the public blueprint is cited as the proximate source with
  MNY as the informal reference. Henry Yuen is a coauthor of MNY and a founder of the
  platform.
- **The MIP\* = RE statements.** The four Palomar Challenge theorems (`Palomar/Challenge.lean`,
  Mathlib-only, `planning/palomar.md`) could be posted as *open* theorems or a mission goal
  later; their solutions cannot follow until the vendored closures are uploaded as content,
  and MIPStarRE's licence rests on the authors' written consent, which the Apache 2.0 grant
  "to the extent you are authorized" would have to cover.
- **Environment list** was read from the FAQ and the harness docs, not from the authenticated
  endpoint; re-check at step 1.
- **Network.** `prove2.me` was added to the cloud environment's allowed hosts on 2026-10-01
  (`docs/lean-cloud.md`); `curl` reaches it, the agent's `WebFetch` tool does not.
  `arxiv.org` remains blocked, which matters only for reading sources.

## Execution record (2026-10-12)

Steps 1-8 of the plan were carried out on 2026-10-12, in the cloud session that had done
step 3 on 2026-10-01 (its scratch workspace, with the `v4.33.1` toolchain and Mathlib `0df444a`
built, was still in place). The platform's environments were re-read from the authenticated
endpoint that day: unchanged, `v4.33.1` still the default and newest, so the source commit is
`70cbf1c` as planned. The generated tree, the tools and their record live in
[`prove2me/`](../prove2me/README.md); the uploader is `scripts/p2m_upload.py`.

| | |
|---|---|
| source | `70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed`, the 23 modules of the closure (8,702 lines) |
| extraction | 1,295 constants (Stage 1), 631 declaration units, 474 declaration commands, 13,000 reference facts (Stage 2, extended to report every command's span) |
| targets | the eleven headline declarations of the table above, plus the blueprint-named `bitQueryAnswer`, `hardcode_size`, `hardcode_time`, `hardcode_time_rev`, `kleeneFix`, `kleeneFix_runs_of`, `smn_polyTime` |
| classification | 206 definition units and 111 embedded theorems in 22 bundles; 60 theorem nodes; 229 inline helpers; 2 proof-side definitions; 24 dead units |
| renames | none needed (every node name is plain ASCII) |
| largest solution | `Machine.eval_steps_bound`, 268 proof lines plus 73 pasted; the heaviest bundle, `Universal`, keeps 221 of 1,552 lines |
| build | 1,443 Lake jobs against Mathlib `0df444a`, no errors, 60 `sorry` warnings (the stubs) |
| validation | the pretty-printed type of every node is identical in the original tree, the stub tree and its solution (60/60/60); the 25 solutions that import no stub depend on `propext`, `Classical.choice`, `Quot.sound` only, the other 35 additionally on `sorryAx` through the stubs they import, which the leaves-first upload order replaces by proofs |
| what the first upload taught | the platform rejects `macro` and every other metaprogramming command in a submission (learned at the 16th bundle, `Cost_Interpreter`, after 15 had published); the generator now drops the `size_omega` macro and expands its 40 uses |
| upload | three runs of `scripts/p2m_upload.py` from child sessions holding the key (16:02, 16:22 and 17:34 UTC), each resumed from `prove2me/upload-state.json`: 22 definition bundles `PUBLISHED`, 60 statements `PUBLISHED`, 60 solutions `ACCEPTED`, and the platform's own status check reports all 60 theorems **Proved**, none Open. The two stops were the macro rejection above and a platform-side database connection drop (`ConnectionTerminated`) while verifying `compressibility_criterion_nested`, which the resubmission accepted; 39 transient network errors (SSL EOF) were absorbed by the uploader's retries. The log is `prove2me/upload.log` |
| two things the playbook did not anticipate | `rfl` lemmas used by `simp` leave no trace in a proof term, so dependencies are taken from the Stage 2 reference facts as well as from the elaborated terms; and the four structurally recursive theorems refer to themselves, so the hoisted `solution` renames those occurrences and the compiler checks the result |

The upload was made **private**: the content is visible only to the uploading account until a
deliberate `make-public` on each headline theorem releases it with its dependency tree,
permanently. `python3 scripts/p2m_upload.py --release --yes`, from a session holding the key,
does that for the three roots of the dependency graph (`recursive_compression_halting`,
`compressibility_criterion_halting`, `smn_polyTime`) and so for everything uploaded. The release
and the mission proposal (step 9) are the maintainer's decisions, and neither has been taken.

Platform ids of the headline theorems (all `Proved`, all private; the full map is
`prove2me/upload-state.json`):

| theorem | id |
|---|---|
| `MIPRE.Cost.recursive_compression` | `347236a4-0cf5-4f17-a875-e63d838001f3` |
| `MIPRE.Cost.compressibility_criterion` | `8ffe1422-d401-4f2c-a58d-2e03a9c6d780` |
| `MIPRE.Cost.compressibility_criterion_nested` | `43599427-3965-483a-b28f-73d2ee2b31da` |
| `MIPRE.Cost.recursive_compression_halting` | `1745fe1d-8a35-447b-a469-1ea57ffa6842` |
| `MIPRE.Cost.compressibility_criterion_halting` | `e69bd497-8c6c-4a1a-bc7a-958c702d5b5d` |
| `MIPRE.Cost.smn_polyTime` | `a0923fc2-0140-4055-983c-acbc8bedc401` |

## The mission proposal (2026-10-14)

The maintainer's reading of the upload, on 2026-10-14: the submission was expected to be about
$\mathrm{MIP}^* = \mathrm{RE}$ itself, and sixty small theorems are not wanted; only the major steps
should appear. Both points are about the platform's model, not about the Lean: the main theorem's
proof closure (`MIPRE/MainTheorem.lean`) is 1,211 modules and 414,132 lines, 213 of them vendored
`Background/` modules and all 322 of the `MIPStarRE` dependency, against a 300-second compile budget
per item and a proof that must be rebuilt from Mathlib and platform content; so the main theorem
can be on the platform only as a statement, Open, and the platform's object for "a headline theorem
with its major steps" is a *mission*. The maintainer chose to build the mission skeleton first and
to decide the granularity of the compression upload afterwards (a coarser re-cut into 8 to 12 cards
is feasible: the largest current solutions compile in 4 to 6 seconds each).

`prove2me/mission/` and `scripts/p2m_mission.py` (idempotent; `--dry-run`, `--status`) hold the
proposal; `prove2me/mission-state.json` and `prove2me/mission-build.log` record the run, from a
child session holding the key, at 09:34 UTC.

| | |
|---|---|
| proposal | `4939b1d4-c604-4734-8109-f0aef34ecc4c`, "MIP* = RE", `ResearchPaper`, **private**, status `Draft`; fields `quantum-information`, `complexity-theory` (chosen from the platform's catalog; none created) |
| goal (draft item `a8836d95-7962-4325-a3a5-4780eb059f5d`) | `HaltingGameValue.halting_reduces_to_gameValue : HaltingGameValue.HaltingReducesToGameValue`, blueprint `thm:main`, [JNVWY20, Theorem 12.2] in synchronous form with polynomial time relaxed to computable; stays Open on the platform, which the description says |
| definition bundle (draft item `56f3db5d-2e82-496b-97c7-1ac87fa1453d`) | `MIPRE_HaltingGameValue` = `MIPRE/HaltingGameValue.lean` at `70cbf1c`, verbatim, the Mathlib-only statement surface (POVM, SynchronousGame, SyncStrategy, strategyValue, gameValue, GameData, toGame, HaltsOnEmptyInput, HaltingReducesToGameValue); both items built against Mathlib `0df444a` (Lake, one `sorry` warning, the stub's) |
| milestone 0 (reference item `d51ddc9c-404f-4017-a03c-cb32d7dfd811`) | `MIPRE.Cost.recursive_compression`, theorem `347236a4-…` (Proved, private), titled "Lemma 5.1 (Marks, Nezhadi, Yuen): the recursive compression lemma" |
| description | 1,729 words in the platform's seven sections (`prove2me/mission/description.md`); honest about status: proved and machine-checked in the repository, Open here |
| read-backs | blind renderings of the two draft items by independent auditor subagents given only the Lean code and the platform's `mission_auditor.md`, attached (`prove2me/mission/readbacks/`); they surface the supremum convention of `gameValue`, the acceptance rule on equal questions, and the absence of any running-time bound |
| quirk | the proposal-milestone list endpoint returns the title under a field the status printer did not expect (it printed `None`); the `POST` was accepted with the title set, so check it on the website |

Still the maintainer's, in this order: confirm each item on the website (homepage → My missions →
"MIP* = RE"), comparing the read-backs with the intended statements; **Submit Proposal**, which
for a private proposal compiles and publishes the two draft items as private content and launches
the mission privately, with no moderator step; and, separately and permanently, **Make public**.
The 82 private records of the compression upload are untouched, and whether to re-cut them into
major results before any release is an open decision.

## The maintainers' advice, and the top-down upload after launch (2026-10-15)

A platform maintainer, asked by the project's maintainer, described the intended use: **one
mission**, built around the target statement, is enough for a result that is already formalized;
milestones are optional; the proposal is submitted on the website and a moderator approves it,
which launches it publicly; then the agent "converts the formalization into its dependency graph
and uploads the small statements in a manner similar to top-down programming", every lemma and
definition its own object, because the data model *is* the graph (nodes for statements, directed
hyperedges for proof sketches, importable definitions); small lemmas are not a concern; the
mission is complete when the target is proved. So the granularity question of the previous
section is settled in favour of the graph: the compression tree is released and linked, not
hidden, and the proposal's visibility is changed to public (one field, while it is a Draft).

Done on 2026-10-15 at 05:27 UTC from a child session holding the key (`prove2me/upload.log`,
`prove2me/mission-build.log`, commit `3812b54`): `make-public` on the three roots returned HTTP 200
each and published 74 + 7 + 1 = 82 records (`recursive_compression_halting`,
`compressibility_criterion_halting` and `smn_polyTime` with their trees: the 60 theorems and the 22
definition bundles), all still Proved; the proposal `4939b1d4-…` was changed to `public` and
re-synced (the platform's read-back in the log says `visibility public`; `mission-state.json` still
shows the pre-change value because the builder recorded visibility before its PATCH, fixed in the
script, and the next `--status` run refreshes it), status `Draft`, fields `complexity-theory` and
`quantum-information`, the milestone in place. Nothing was submitted or launched: that is the
maintainer's click on the website.

The maintainer submitted the proposal on 2026-10-15; it is `In review` (the two draft items were
compiled and published at submission; a moderator's approval launches the mission publicly).

**The structure of the top-down upload**, read off `70cbf1c` (the main theorem is proved there;
`MainTheorem.lean` has no `sorry`; proof closure 1,188 modules, 404,292 lines). The proof is

```
halting_reduces_to_gameValue := Halting.halting_reduces_to_gameValue_of_answerReduction answerReduction
halting_reduces_to_gameValue_of_answerReduction A :=
  halting_reduces_to_gameValue_of (GapCompression.ofPipeline Introspection.seven A (repetition 7)) Cost.selfUniversal
```

(`MainTheorem.lean`, `Background/Pipeline.lean`). Everything in the second line except the three
stage instances is own code: `GapCompression.ofPipeline : Introspection 7 → AnswerReduction 5 →
Repetition 7 → GapCompression` (`Foundations/Pipeline/Compress.lean`, blueprint `thm:compression`),
`halting_reduces_to_gameValue_of : ∀ (G : GapCompression) (U : UniversalMachine), …`
(`Foundations/Halting/CompressorProgram.lean`, `thm:halting`), `Cost.selfUniversal : UniversalMachine`
(`Cost/Universal.lean`). The union of their import closures with `HaltingGameValue` is **103 modules,
32,478 lines, none under `Background/`**, 23 of them the compression closure already on the platform.
The three instances are data whose bodies are the introspection development (`Introspection.seven`,
closure 964 modules, `MIPStarRE` through the LIDT bridge), the answer-reduction development
(`answerReduction`, 618 modules, likewise) and the repetition verifier (`repetition 7`, 60 modules,
the 72k-line vendored `TenProofs`). A platform definition may not be `sorry`ed, so they enter the
graph as theorem nodes `Nonempty (Introspection 7)`, `Nonempty (AnswerReduction 5)`,
`Nonempty (Repetition 7)`: Open leaves for now, with `Classical.choice` in two hand-written glue
sketches (the goal from `∀ A, …` and `Nonempty (AnswerReduction 5)`; `∀ A, …` from
`halting_reduces_to_gameValue_of`, `ofPipeline`, the two other `Nonempty`s and `selfUniversal`),
the only non-mechanical Lean in the upload, each a few lines the compiler checks against the stubs.

Increments, each a run of the existing pipeline over a closure, with a registry of what is already
published so that bundles and solutions import the platform's copies:

1. **The assembly layer**: the 80 own modules of the 103 not yet uploaded (Compress, the Halting
   development, games, values, verifiers, `UniversalMachine`), plus the two glue sketches and the
   three `Nonempty` leaves; `selfUniversal` becomes definition material (a new bundle, since the
   published `Universal` bundle is immutable). Expected size: a few hundred theorem nodes, 60 to 80
   bundles. After it, the goal is `SKETCH_ACCEPTED` and its open frontier is exactly the three
   instances. Milestones: `thm:compression` (`ofPipeline`'s correctness, as the structure it builds),
   `thm:halting`, `lem:universal-tm`.
2. **Repetition** (own part 46 modules, 17.6k lines; the vendored repetition theorems as Open
   leaves), **introspection** (own part 473 modules, 86.6k lines; `thm:qld`'s proof is own code under
   `Background/QLD/`, its LIDT inputs through `MIPStarRE` are the leaves), **answer reduction** (own
   part 234 modules plus the classical PCP, 184 modules): the same pipeline, one closure at a time.
3. The leaves that remain are third-party code: the vendored `TenProofs`, `CommutingRepetition` and
   `Orthogonalization` trees and the `MIPStarRE` dependency, whose authors' licence terms decide.

Practicalities: the source stays `70cbf1c` (Lean `v4.33.0`, one toolchain commit behind the
platform's `0df444a`; the platform offers no newer environment); the build and extraction run in
the `p2m` workspace, which needs the modules of each increment added from `git show 70cbf1c:…`;
the session's disk allowance (about 400 MB free on 2026-10-15 before clearing re-downloadable
caches) bounds how much can be built at once, so increments are built one at a time.

**Increment 1 in progress (2026-10-15).** The 103-module closure at `70cbf1c` is in the `p2m`
workspace and builds against Mathlib `0df444a` in six minutes (3,153 Lake jobs, no errors); Stage 1
and Stage 2 ran over it (4,393 constants, 2,673 declaration units). The planner and generator now
take a configuration (`prove2me/assembly/config.json`, written by `make_config.py`) and know the
published content: the 60 compression theorems are imported nodes, the 22 compression bundles and
the mission's `MIPRE_HaltingGameValue` bundle are imported, and a module whose published bundle lacks
a declaration the new layer needs gets a *delta bundle* (`…_B`). Result: 88 bundles (74 new, 14
delta), 89 theorem nodes, 423 inline helpers, 968 theorems embedded in bundles (the proof fields of
proof-carrying definitions such as `GapCompression.ofPipeline` and the `PolyTimeFun`s), 55 published
nodes and 313 published declarations reused; `glue.py` adds the 3 `Nonempty` leaves, the 8
conditional theorems of `Background/Pipeline.lean` and the 8 unconditional ones of `MainTheorem.lean`
(the goal's stub is the published one). Three more cost macros (`cost_omega`, `cost_omega'`,
`cost_omega₂` of `Halting/{Lists,Arith,Serial}.lean`) are expanded like `size_omega`; `private`
modifiers are dropped in the generated copies, since `private` is per file; the one non-ASCII node
name (`classV_game_μ`) is renamed `classV_game_mu` in the uploaded copy. Blueprint names (379 in the
closure) are a promotion signal only here, not forced nodes. The session's disk allowance was
exhausted by Lake's per-module setup files and C output (about 1 GB for the generated trees), so
the generated files are now checked with `tools/build_tree.py`, which compiles them directly with
`lake env lean -o` in dependency order and keeps only the oleans.

**Increment 1 generated and validated (2026-10-15).** The 300 generated files (88 bundles, 107
stubs, 105 solutions; `prove2me/assembly/{Definitions,Theorems,Solutions}`) compile with
`autoImplicit` off against the platform pin, with exactly one `sorry` per stub. Getting there took
four generator passes, each fixing a class of scope reconstruction the compression layer had not
exercised: `section`/`end` frames and `open` lines inside them are modelled as context frames;
`attribute […] names` commands are replicated with the targets resolved by the reference facts
(the token `CommutingStrategy` in `attribute [instance] …` names the projection
`CommutingStrategy.cstarAlgebra`, not the structure); `include G U in` prefixes are reproduced
(a bare `include G U` in the stub's preamble, verbatim before the solution); the solution is
declared as `theorem _root_.solution` *inside* the source's namespace, so that names resolve as
in the source (hoisting to the root made `D` ambiguous between `Game.D` and the local one); and
attribute commands are replayed at their *source position* in the pasted sequence rather than at
the top of the file, since `attribute [local irreducible] tab` of `Reduction.lean` sits after the
lemmas of `Instantiation.lean` whose proofs unfold `tab` (`tab_computable`'s `rfl`), and a local
attribute is in effect only for the rest of its own module. Validation (`tools/validate.py`,
`prove2me/assembly/validation.json`): the elaborated type of each of the 89 nodes is identical in
the source module, in the stub and in the solution; the 16 glue theorems of
`Background/Pipeline.lean` and `MainTheorem.lean`, whose source modules depend on the vendored
trees and cannot be elaborated in the workspace, are verbatim textual cuts of the source (checked
against `git show 70cbf1c:…`) and their solution types equal their stub types; the three
`Nonempty` leaves have no source declaration and no solution. Every solution depends on
`propext`, `Classical.choice`, `Quot.sound` and (through the `sorry` stubs it imports) `sorryAx`,
and on nothing else. Metadata for the 108 theorem items and 88 bundles is drafted from writer
packets (`tools/meta_packets.py`, `prove2me/assembly/META_WRITER.md`) and merged by
`tools/merge_meta.py`; the upload waits for the mission's launch.
