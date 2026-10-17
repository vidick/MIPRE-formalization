# The Prove2Me submission: the recursive compression lemma and its closure

This directory is the platform tree uploaded to [Prove2Me](https://prove2.me) for the
recursive compression lemma `MIPRE.Cost.recursive_compression` (blueprint
`lem:recursive-compression`, [MNY, Lemma 5.1]) and the results it rests on: the
compressibility criterion, the efficient universal machine, the efficient s-m-n map, the
efficient Kleene recursion theorem and succinct descriptions. Why this closure went first, and
what the platform is, is recorded in [`planning/prove2me.md`](../planning/prove2me.md).

**Status (2026-10-17).** The mission's goal theorem `HaltingGameValue.halting_reduces_to_gameValue`
is Proved on the platform, with no open leaf: its closure went up in five trees, this directory's
and `assembly/`, `repetition/`, `answerreduction/`, `introspection/` (below), with the parallel
repetition proof the platform already hosted (openai/ten-proofs) in place of the vendored copy.

Everything here was **generated mechanically** from this repository at commit
`70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed` (Lean `v4.33.0`, Mathlib `db584cd`, the parent of
the platform's pin `0df444a` = "chore: bump toolchain to v4.33.1") and compiled against the
platform's own environment (Lean `v4.33.1`, Mathlib `0df444a`). Nothing in `Definitions/`,
`Theorems/` or `Solutions/` was written or edited by hand; a change goes through the tools and a
regeneration.

## Layout

| path | what |
|---|---|
| `Definitions/Def_<module>.lean` | 22 definition bundles, one per source module of the closure: the module's definitions, instances and the small lemmas their bodies need, obtained by deleting every other declaration from the original file (*skeleton subtraction*). Imports rewritten to the bundles of the module's import closure. |
| `Theorems/Thm_<name>.lean` | 60 statement stubs, one per uploaded theorem: the preamble (imports, `open`s and `variable`s reproducing the declaration's resolution scope) and `theorem <fully-dotted name> … := by sorry`. |
| `Solutions/Sol_<name>.lean` | the 60 proofs: the helper lemmas the proof uses (pasted verbatim inside their original namespace, with their `open`s), then the theorem hoisted to a top-level `theorem solution`, as the platform requires. Imports the stubs of the other uploaded theorems it uses, which makes each solution a *reduction* to them. |
| `tree.json` | the upload manifest: bundles in import order, nodes with their statement, preamble, imported nodes and pasted helpers. |
| `plan.json` | the classification of all 631 declaration units of the closure (see below). |
| `metadata.json` | titles, natural-language statements, sources, tags and proof explanations, per node and bundle. |
| `upload-state.json` | written by the uploader: job ids, theorem ids and statuses of every upload action. |
| `tools/` | the pipeline (below). |

## The pipeline

It follows the platform's own playbook (`references/upload_full_project.md` of
`prove2me/prove2me_workspace`, release 0.12.3), whose rule is: never hand-split a project and
never answer a question about Lean code by pattern matching.

1. **Extraction** (`tools/extract_decl_graph.lean`, `tools/extract_sketch_info_plus.lean`;
   the harness's scripts, the second with one addition that also reports every top-level
   command's kind and span). Over the 23 modules of the closure, built against the platform
   pin: 1,295 constants with their statement-level and proof-level dependencies; per file, the
   span, name, proof start, docstring and `private` token of every declaration, and the exact
   range of every resolved reference to a project constant.
2. **Planning** (`tools/plan.py`). Declarations are grouped into *units* (one per declaration
   command: a structure with its constructors and projections is one unit). Reachability from
   the eleven headline declarations and the blueprint-named ones, with every instance as an
   extra root, over the elaborator's dependencies and the reference facts (a `rfl` lemma used by
   `simp` leaves no trace in a proof term; the reference facts catch it). Then the playbook's
   classification: a theorem whose proof exceeds 40 lines is a **node** (a stub and a solution),
   as is one of 11–40 lines with a promotion signal (used by two nodes, used across files,
   documented, named in the blueprint); a theorem of at most 10 lines is an **inline helper**,
   pasted into every solution that needs it; definitions, instances and inductives that any
   statement or any definition body needs are **definition material**, bundled per module; a
   theorem cited by a definition body, or any attributed short lemma, is **embedded**, proved
   inside the bundle (a bundle may not import a `sorry` stub). Result at this commit: 206
   definition units, 111 embedded theorems, 60 nodes, 229 inline helpers, 2 proof-side
   definitions (`selfUniversal`, `selfClockedUniversal`, pasted into the two existence
   theorems), 24 dead units never uploaded. No name needed renaming: every node name is plain
   ASCII, and the `toNat?`-style names are all inline or bundled.
3. **Generation** (`tools/gen.py`). Bundles by skeleton subtraction; stubs and solutions by
   reconstructing each declaration's scope (namespace chain, `open`s, `variable`s) from the
   command facts. The four structurally recursive theorems (`ofCode_*`, `dispatch_runs`) have
   their self-references renamed to `solution` in the hoisted copy; the compiler checks the
   result. The platform rejects metaprogramming ("custom syntax/elaborator registration ... is
   not supported in submissions"), so the closure's one macro, `size_omega` of
   `Cost/Interpreter.lean`, is not uploaded: the generator drops its definition from the bundle
   and spells out its expansion, with the fully qualified names the macro pre-resolved, at each
   of its 40 uses. Every generated file keeps the copyright header of its source (since increment 3;
   see below).
4. **Build.** The three libraries compile against Mathlib `0df444a`: 1,443 Lake jobs, no
   errors, and exactly 60 `sorry` warnings, one per stub.
5. **Validation** (`tools/validate.py`). The elaborated type of every node is pretty-printed
   in the original tree, in the stub tree and in each solution; the three must agree exactly.
   The validation record is `validation.json` in the build workspace; its summary is in
   `planning/prove2me.md`.
6. **Metadata.** Drafted from the Lean sources, their docstrings and the blueprint statements,
   then reviewed; stored in `metadata.json`. Sources are `blob/<sha>/<file>#L<a>-L<b>` links at
   commit `70cbf1c`, with the blueprint label and the paper reference where one exists.
7. **Upload** (`scripts/p2m_upload.py`). Idempotent and strictly ordered: definitions in
   import order, then every statement (`POST /submit-problem`), then every solution
   (`POST /verify`) leaves-first, so that each theorem resolves straight to `Proved`. Everything
   is created **private** (visible to the uploading account only) unless `--public` is passed;
   release is a separate, deliberate `POST /theorems/:id/make-public` per headline theorem,
   which publishes it and everything it depends on, permanently (done on 2026-10-15).

## The mission proposal (`mission/`)

The platform's object for "a headline theorem with its major steps" is a *mission*: a goal theorem,
a description, and milestone theorems. `mission/` holds the private proposal "MIP\* = RE" that
`scripts/p2m_mission.py` builds idempotently (`--dry-run` shows the requests, `--status` reads the
proposal back; the state is `mission-state.json`):

| path | what |
|---|---|
| `mission/proposal.json` | name, type (`ResearchPaper`), visibility (`private`), the items and their metadata, the goal, the item order, the milestones. |
| `mission/description.md` | the mission description, in the seven sections of the platform's `mission_description.md` (motivation, setting, targets, significance, difficulty, formalization scope, references). |
| `mission/Definitions/Def_MIPRE_HaltingGameValue.lean` | draft definition item: `MIPRE/HaltingGameValue.lean` at `70cbf1c`, verbatim, the Mathlib-only statement surface of the main theorem (POVMs, synchronous games, strategies, value, game descriptions, halting, the proposition). Built against Mathlib `0df444a`. |
| `mission/Theorems/Thm_HaltingGameValue_halting_reduces_to_gameValue.lean` | draft goal item: `theorem HaltingGameValue.halting_reduces_to_gameValue : HaltingGameValue.HaltingReducesToGameValue := by sorry`, importing the bundle. Its proof is the whole development and is not uploadable (414k lines, vendored trees, the `MIPStarRE` dependency, a 300 s compile budget per item), so the goal stays Open on the platform; the description says so. |
| `mission/items/*.md` | the two items' natural-language statements. |
| `mission/readbacks/*.md` | blind read-backs of the two items, written by independent auditor subagents given only the Lean code and the platform's `mission_auditor.md`; attached to the items for the human audit. |
| `mission/milestones/recursive_compression.md` | the first milestone: `MIPRE.Cost.recursive_compression` (id `347236a4-…`, public since 2026-10-15 with its whole tree), referenced, not re-uploaded. |

The proposal is **public** since 2026-10-15, on the platform maintainers' advice (one mission around
the target statement; every lemma and definition of the formalization is its own object in the
dependency graph, which is the platform's data model), and the compression tree was released the
same day (`scripts/p2m_upload.py --release --yes`: `make-public` on its three roots, 82 records, all
Proved). The proposal stays a `Draft` until the maintainer confirms the items and clicks **Submit
Proposal** on the website (homepage → My missions); that compiles and publishes the two draft items
and sends the mission to a moderator, whose approval launches it publicly. After launch, the
dependency graph of the goal is uploaded top-down under it (`planning/prove2me.md`).

## The assembly layer (`assembly/`)

The first increment of the top-down upload after the mission's launch: everything between the
mission's goal `HaltingGameValue.halting_reduces_to_gameValue` and the published compression tree
that is this project's own Mathlib-only code (103 modules, 32,478 lines: the compressor, the
halting reduction, the class statements, the verifier and tabulation layers). The three stage
instances the pipeline consumes (`Introspection 7`, `AnswerReduction 5`, `Repetition 7`) are data in
vendored or `MIPStarRE`-dependent code the platform cannot host yet; they appear as three *Open*
leaves `Nonempty (MIPRE.Introspection 7)` etc., and the 16 glue theorems of
`MIPRE/Background/Pipeline.lean` and `MIPRE/MainTheorem.lean` are uploaded with their source
statement and a one-line sketch that applies the own-code theorem to the leaves' witnesses
(`Classical.choice`), so they stand as accepted sketches whose open frontier is the leaves. Later
increments fill the leaves.

| path | what |
|---|---|
| `assembly/config.json` | the planner/generator configuration (`make_config.py`): targets, definition-material targets, the published trees reused, renames. |
| `assembly/Definitions/`, `Theorems/`, `Solutions/` | 88 bundles (74 new, 14 *delta* bundles `…_B` adding declarations to a published compression bundle), 107 stubs (89 nodes, 3 leaves, 15 glue; the goal's stub is the mission's), 105 solutions. |
| `assembly/tree.json`, `glue.json`, `plan.json` | the manifest, the glue items, the classification of the 2,673 units of the closure. |
| `assembly/validation.json` | type diff (source, stub, solution) and axioms of every solution. |
| `assembly/metadata.json`, `META_WRITER.md`, `meta_packets/` | the platform metadata and how it was drafted. |
| `assembly/milestones.json`, `milestones/` | the twelve live-mission milestones (`scripts/p2m_mission.py --milestones`). |
| `assembly/upload-config.json` | `{"public": true}`: the mission is public, so is everything uploaded under it. |

The same pipeline runs with `P2M_CONFIG=prove2me/assembly/config.json`; the generated files are
compiled with `tools/build_tree.py` (direct `lake env lean -o`, dependency order) rather than
`lake build`, whose per-module setup files exhausted the session's disk allowance. The upload,
`python3 scripts/p2m_upload.py --tree prove2me/assembly`, ran on 2026-10-15 after the launch: 88
definitions and 108 statements published, 89 theorems Proved, 16 accepted sketches resting on the
3 Open leaves; the twelve milestones were then linked with `scripts/p2m_mission.py --milestones`.
The uploader resumes from `upload-state.json` and treats the platform's transient failures (a
dropped database connection, a security-checkpoint page in place of the API) as retries.

## The repetition stage (`repetition/`)

The second increment: the closure of the repetition stage instance `MIPRE.repetition 7`
(`MIPRE/Background/Repetition/Verifier.lean`) at `70cbf1c`, 60 modules of which 20 are new to the
platform, all own code: the repetition layer (`Foundations/Repeat/*`, `CL/Repeat`, `TensorFamily`,
`Dilation`, `Background/Repetition/{Direct,TensorPower,Entangled,Soundness,Verifier}`). The
vendored parallel repetition proof of openai/ten-proofs (`Background/Repetition/TenProofs/`, eight
parts of about 9,000 lines) is not uploaded: the platform has hosted that development since
2026-08-09 (tag `openai-ten-proofs`, public, Proved, the same upstream commit), so the tree imports
its game bundle (`quantum_parallel_repetition_game`, nine definitions) and five of its theorems
instead (`planning/prove2me.md`, "The platform already holds the vendored proof"). It closes the
leaf `Nonempty (MIPRE.Repetition 7)` with the solution `⟨MIPRE.repetition 7⟩`.

The stage's target is a definition, so the planner's increment-1 rule would have made every one of
the 2,099 theorems reachable through its body an embedded lemma of a definition bundle and the
stage would have had no statement on the platform at all. The planner now keeps in a bundle only
what the bundle needs (the same-module theorem closure of its definitions, statement-named,
short attribute and private theorems); the other theorems are nodes or inline helpers, a theorem
another bundle's content needs is a node that bundle imports, and since the platform accepts a
definition's import of a theorem only once that theorem is Proved, the uploader publishes in
waves (`planning/prove2me.md`, "Increment 2").

| path | what |
|---|---|
| `repetition/config.json` (`make_config.py`) | definition-material target `MIPRE.repetition`; the published registry: the compression and assembly trees, the platform's ten-proofs game bundle (nine definitions, as the published bundle of `Part01`) and its five theorems (`published_nodes_extra`); the leaf closure; one rename (`length_le_size_list'`) and one token rename (`effect` → `operator`, the field name of the platform's statement file). |
| `repetition/Definitions/`, `Theorems/`, `Solutions/` | 20 bundles (19 new, 1 delta; 114 definitions, 2 inductive types and 66 embedded theorems; the largest, Verifier, 905 lines), 94 stubs and 94 solutions (159 inline helpers pasted where used, 386 copies; median proof 14 lines), and the leaf-closure solution. |
| `repetition/tree.json`, `glue.json`, `plan.json` | the manifest (bundles record the same-tree nodes and the platform theorems they import: 5 bundles import 47 same-tree nodes, Entangled's imports the five ten-proofs theorems), the leaf closure, the classification of the 5,743 units of the closure. |
| `repetition/validation.json` | 94 statements with identical types in the source module, the stub and the solution; the leaf closure's solution type equals its published stub; no axiom beyond `propext`, `Classical.choice`, `Quot.sound` and the stubs' `sorryAx`. |
| `repetition/metadata.json`, `META_WRITER.md`, `meta_packets/` | templated records for every item (`tools/auto_meta.py`), writer records for the 12 blueprint-named theorems and the 7 blueprint-named bundles. |
| `repetition/platform-records.json`, `platform-imports.json` | the platform's records of the six ten-proofs items the tree imports, and the import lines they resolve to (`tools/ws_standins.py` writes local stand-ins of them for the build; they are never uploaded). |
| `repetition/orphans.json` | what a first upload attempt published before the platform's ten-proofs content was found: 39 statements of vendored lemmas (Open, no solution) and one definition bundle, none used by any tree. All 40 are retired (deprecated: hidden from discovery, reversible, still importable), one during the API probe and the rest on 2026-10-17 at the maintainer's request (`scripts/p2m_retire_orphans.py`); each statement's description ends with a note saying why and naming what replaces it (the hosted development, which publishes none of these lemmas on its own, and for the bundle the hosted `quantum_parallel_repetition_game` the tree imports). |
| `repetition/upload-state.json`, `upload-config.json` | the upload's record (every item's id, publish job and submission), and `{"public": true}`. |

The upload, `python3 scripts/p2m_upload.py --tree prove2me/repetition`, ran on 2026-10-16 in three
waves (13 bundles and 74 nodes; 6 and 20; the Verifier bundle and the leaf closure), each wave's
bundles published after the nodes they import were Proved, 33 minutes in all: 20 bundles and 95
statements published, 95 solutions accepted, and the platform shows all 95 theorems Proved,
`MIPRE.Repetition.nonempty_seven` among them. The goal theorem's frontier is now the two remaining
leaves, `MIPRE.Introspection.nonempty_seven` and `MIPRE.AnswerReduction.nonempty_five`.

## The answer-reduction and introspection stages (`answerreduction/`, `introspection/`)

The third increment: the closures of the two remaining stage instances at `70cbf1c`,
`MIPRE.AnswerReduction.answerReduction` (`AnswerReduction 5`, `MIPRE/Background/AnswerReduction/Instance.lean`)
and `MIPRE.Introspection.seven` (`Introspection 7`), 1,107 modules together: the rest of the
Foundations/TM/LCS own code, the low individual degree test (`Background/LIDT/`, much of it vendored
from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) with the authors' permission), the Pauli
basis test (`Background/QLD/`), the orthogonalization development vendored from
vidick/commuting-repetition, two CSLib files, Sean Perazzolo's LCS development and the two stage
layers. A platform search (`/search`, `GET /theorems?tags=`) found none of it hosted. Two trees, answer
reduction first; the introspection tree's registry includes it (125 of its bundles import
answer-reduction nodes, so they wait for those to be Proved):

| | answer reduction | introspection |
|---|---|---|
| modules with uploaded content | 600 | 425 |
| bundles (new + delta) | 476 (475 + 1) | 361 (342 + 19) |
| definitions in them, embedded theorems | 3,336, 2,012 | 1,634, 621 |
| theorem nodes, inline helpers | 1,673, 2,651 | 852, 2,765 |
| bundles importing same-tree nodes | 178 (975 imports) | 59 (192 imports) |
| leaf closed | `MIPRE.AnswerReduction.nonempty_five` | `MIPRE.Introspection.nonempty_seven` |

What this closure needed beyond the earlier increments, in the order it surfaced:

* **Metaprogramming.** The platform refuses custom syntax and elaborator registration in a
  submission. 23 modules use some: 30 `local notation` commands, the tactic macros `solve_line_comm`,
  `norm_ds` and `norm_ds_goal`, the recursive `macro_rules` tactic `quantum_nonneg`, the elaborator
  `avg_congr` and the simp set `ldt_simp`. `tools/ws_rewrite_meta.py` rewrites the workspace copies
  (never the sources) into what the elaborator would have produced; each rewritten module was
  recompiled before extraction. Check commands of the sources (`#guard_msgs in #print axioms`) are
  dropped from bundles, whose definitions rest on sorry stubs.
* **Copyright headers.** Each generated file carries the header of the source it copies, a solution
  the headers of every module its pasted helpers come from, and the metadata credits each third-party
  author (`tools/auto_meta.py`, `provenance`). Until this increment every file got the header of the
  closure's first module; of the published files, three assembly bundles carry this project's other
  header ("Thomas Vidick" for "MIPRE contributors"), and nothing third-party was published under it.
* **Names a generated file sees differently from its source.**
  - An `open` of a project namespace no declaration of the file's environment lives in is dropped
    (opening it would make nothing visible), resolved the way the source resolved it; a namespace
    Mathlib also has (`Matrix`, whose scoped `ᴴ` a stub parses) is kept (`tools/ext_namespaces.lean`).
  - A stub hoists its scope to the top level, where the opens reproducing the namespace chain compete
    with the source's own opens; a hoisted `variable` line writes in full each project constant its
    top level would not resolve as the source did (`Question`: MIPRE.QLD's, not MIPRE.LIDT's).
  - The copies drop `private`, so a private declaration can capture a reference elsewhere
    (`SourceCompiler.andCheck` against `AuxiliaryProgram.andCheck`); exactly the references Lean's
    resolution order (namespace chain, then opens) would give to the copy are written in full.
  - A `local instance` is in effect for the rest of its section, and each generated block lives in
    its own section: the blocks after one activate it again by name. An anonymous instance's name
    depends on its module (`instDecidableEq_mIPRE` in the source, `instDecidableEq_definitions` in a
    bundle), so the copies are named explicitly with the source's name.
  - A node the source declares as an `instance` (of a Prop-valued class) has a plain theorem stub, so
    the files that import it register it.
  - The tree records name an imported node by its platform name (the ASCII renames): naming it by its
    source name made the uploader take it for published content.
  - A node is uploaded as `solution`, and inside its own proof that name is the node itself (the
    local of a recursive reference comes before any constant): `AuxiliaryScan.stage_correct` refers
    to the definition `AuxiliaryScan.solution`, which its solution writes in full.
  - A solution sees what its node's module sees, so a constant a pasted helper's module could not
    see can take one of the helper's references: `MIPRE.Introspection.C`, a field of the structure
    `Introspection`, took `C` (`Polynomial.C`) from a helper of `namespace MIPRE.Introspection`. The
    extraction records references to the project's constants only, so such a capture of a Mathlib
    name is listed (`PASTE_FIX` in gen.py, from the local check's report) and written in full where
    the capturing constant is in the solution's environment.
  - Lean shares one matcher among the declarations of a file whose `match`es compile to the same
    function, so a solution's statement could take the matcher of a helper pasted before it
    (`router_context.match_1` in `untypedKernel_iff`'s type, whose stub has its own); that helper
    is pasted with `bootstrap.genMatcherCode false`, part of the matcher cache's key, and the type has
    `solution.match_1` as the other solutions' do (`FRESH_MATCHER`).
* **Published content is never regenerated differently.** A generator fix made after part of a tree
  is published must reproduce the published bundles byte for byte: gen.py reads the tree's upload
  state and refuses to change a published bundle's file, and code that refers into a published bundle
  uses the names Lean gave there (checked against the compiled bundles; the published text read back
  from the platform equals the local files).
* **Validation.** The source types come from a dump made while the source oleans existed
  (`tools/orig_types.lean`, 18,570 theorems), so the oleans could be archived. Each solution is
  checked by compiling a copy with the check appended (no olean written), and its type is compared
  with its stub's printed with `pp.all`: the default print depends on the notation the environment
  has (`∀ i < n, …` where Mathlib's binder predicates are imported, `∀ (i : ℕ), i < n → …` where not).
  A statement naming a private definition prints it `name✝` in the source and bare in the stub, whose
  copy is public; the check lists such pairs apart. It held back three introspection solutions while
  the upload ran (the last three name cases above: two compile failures, one type naming another
  declaration's matcher), none of which reached the platform.
* **Upload.** `scripts/p2m_upload.py --pipeline` replaces the waves' barriers by one scheduler: each
  bundle, statement and solution is submitted as soon as what it imports is ready (a bundle's imported
  nodes Proved), with one cap on the jobs of all kinds; `--gate` holds each solution until the local
  check has passed it; `--after` lets a tree wait for content of a sibling tree uploaded alongside;
  `--stop-after` ends a run between two submissions (a run killed from outside can lose a job it
  submitted and had not yet recorded), and the next run polls the jobs left in flight.

The upload of both trees ran from 2026-10-16 23:08 UTC to 2026-10-17 12:16 UTC, the introspection
tree alongside the answer-reduction tree (`--after`), in runs of at most two hours each resumed from
the upload state (`answerreduction/upload-state.json`, `introspection/upload-state.json`): 476 and
361 bundles published, 1,673 and 852 statements (the leaves' were published with the assembly
layer), 1,674 and 853 solutions accepted. Read back afterwards, the platform shows every theorem of
both trees Proved, `MIPRE.AnswerReduction.nonempty_five` from 11:48 and
`MIPRE.Introspection.nonempty_seven` from 12:15; the goal theorem
`HaltingGameValue.halting_reduces_to_gameValue` is Proved, with no open leaf left. No submission
failed for a reason of its own. The platform's transient failures (import-parser and token-scanner
timeouts, dropped database connections) cost 295 and 204 resubmissions, all accepted in the end, and
the three solutions the local check had held back were regenerated and accepted. From about 08:00 the
upload was a single dependency chain: the soundness of the low individual degree test
(`MIPRE.LIDT.Simul.clSoundness`), on which both leaves rest, then the soundness bundles of each stage
one after the other, at five to twenty minutes a step.

## Reproducing

The build workspace is a Lake project pinned to the platform environment (toolchain
`leanprover/lean4:v4.33.1`, Mathlib `0df444a…`, `autoImplicit = false`) holding the closure modules
of `70cbf1c` under `MIPRE/`, with `lean_lib`s `MIPRE`, `Definitions`, `Theorems`, `Solutions` (the
last three with `globs = ["<Name>.+"]`). `docs/lean-cloud.md` and `planning/prove2me.md` describe how
it was set up in a cloud session and what not to do in it (never `lake build` there). With `P2M_DIR`
pointing at a directory holding `ws/` (the workspace) and `toolchain/`, an increment is:

```
python3 tools/ws_extend.py <root module>               # the root's closure at 70cbf1c into ws/
lake env lean --run tools/min_imports.lean <vendored modules> > mi.out   # in the main repository
python3 tools/ws_rewrite_imports.py --from-lean mi.out && python3 tools/ws_rewrite_imports.py
tools/ws_fetch_closure.sh <list of Mathlib files>      # oleans the cache has, in batches
python3 tools/ws_rewrite_meta.py                       # metaprogramming the platform refuses, rewritten away
python3 tools/compile_modules.py --parts <roots>       # the rest, with lean --setup, in import order
lake env lean tools/extract_decl_graph.lean            # in ws/: decl_graph.jsonl (Stage 1)
lake env lean --run tools/extract_sketch_info_plus.lean <file> MIPRE,MIPStarRE,QuantumParallelRepetition  # Stage 2
lake env lean --run tools/orig_types.lean <roots> > orig_types.txt   # source types, before archiving the oleans
lake env lean --run tools/ext_namespaces.lean <external modules> > ext_namespaces.txt
python3 <tree>/make_config.py                          # config.json: targets, published trees, glue leaves
P2M_CONFIG=<tree>/config.json python3 tools/plan.py    # plan.json: bundles, nodes, inline helpers, waves' edges
P2M_CONFIG=… python3 tools/gen.py && python3 tools/glue_leaves.py     # the generated files, tree.json, glue.json
P2M_CONFIG=… python3 tools/build_tree.py --jobs 3 --no-solutions   # bundles and stubs, lean --setup
P2M_CONFIG=… python3 tools/validate.py --phase orig --orig-from orig_types.txt && … --phase stubs
P2M_CONFIG=… python3 tools/validate.py --phase solutions --compile --wave-order <tree> --jobs 3   # alongside:
P2M_CONFIG=… python3 tools/meta_packets.py && python3 tools/auto_meta.py --packets … --out <tree>
python3 tools/merge_meta.py --tree <tree>              # metadata.json (writer records override)
PROVE2ME_API_KEY=… python3 scripts/p2m_upload.py --tree <tree> --pipeline --gate <validation-solutions.jsonl> \
    [--after <sibling tree>] [--stop-after <seconds>] --dry-run   # then without --dry-run, until it says done
```

The uploader publishes in dependency order (a bundle that imports a theorem of the same tree only
once the platform shows that theorem Proved): wave by wave, or with `--pipeline` each item as soon as
what it imports is ready. It resumes from `upload-state.json`, needs only Python 3 and network access
to `prove2.me`, and reads the API key from the environment without printing or storing it. A
generator change made after part of a tree is published must leave the published bundles unchanged;
`gen.py` checks this against the tree's upload state, and `P2M_GEN_DRYRUN=1` lists the files a run
would change without writing them.
