# The Prove2Me submission: the recursive compression lemma and its closure

This directory is the platform tree uploaded to [Prove2Me](https://prove2.me) for the
recursive compression lemma `MIPRE.Cost.recursive_compression` (blueprint
`lem:recursive-compression`, [MNY, Lemma 5.1]) and the results it rests on: the
compressibility criterion, the efficient universal machine, the efficient s-m-n map, the
efficient Kleene recursion theorem and succinct descriptions. Why this closure went first, and
what the platform is, is recorded in [`planning/prove2me.md`](../planning/prove2me.md).

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
   result. Every generated file keeps the copyright header of its source.
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
   which publishes it and everything it depends on, permanently.

## Reproducing

The build workspace is a Lake project pinned to the platform environment (toolchain
`leanprover/lean4:v4.33.1`, Mathlib `0df444a…`, `autoImplicit = false`) containing the 23
closure modules of `70cbf1c` under `MIPRE/`, with `lean_lib`s `MIPRE`, `Definitions`,
`Theorems`, `Solutions` (the last three with `globs = ["<Name>.+"]`). `docs/lean-cloud.md` and
`planning/prove2me.md` describe how it was set up in a cloud session. With `P2M_DIR` pointing at
a directory holding `ws/` (the workspace), `toolchain/` and `extract/`:

```
lake env lean extract_decl_graph.lean                      # in ws/, writes decl_graph.jsonl
lake env lean --run extract_sketch_info_plus.lean <file> MIPRE > extract/sketch_info.<Base>.jsonl
python3 tools/plan.py && python3 tools/gen.py              # plan.json, tree.json, the three trees
lake build Definitions Theorems Solutions                  # in ws/
python3 tools/validate.py                                  # type diff and axioms
PROVE2ME_API_KEY=… python3 scripts/p2m_upload.py           # from the repository root
```

The uploader needs only Python 3 and network access to `prove2.me`; the API key is read from
the environment and never printed or stored.
