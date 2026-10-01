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
`MIPRE.Tactics` bundle. So the upload source is `70cbf1c` and drift repair should be nil.
Not yet checked: the closure has not been built against `0df444a` with `v4.33.1`. That is
step 3 below, and the first thing to do.

## Plan

1. **Account.** Register on `prove2.me`, mint an API key, accept the licensing terms. The
   agent bootstrap is `https://prove2.me/start.md`; the harness is cloned to
   `$HOME/prove2me_workspace`. Check `GET /api/v1/environments`.
2. **Source commit.** `70cbf1c` if `v4.33.1` is still the newest environment. If a `v4.35`
   environment has appeared, use `main` instead; then the module headers must be stripped
   (`module`, `public import` → `import`, `@[expose] public section` and its closing `end`),
   which the playbook's Phase 3 only half-covers ("strip the keyword `module` before the
   first `import`").
3. **Build the closure against the platform pin**: a workspace with `lean-toolchain`
   `v4.33.1` and `lakefile.lean` requiring Mathlib at `0df444a`, `lake exe cache get`, the 24
   modules copied in, `lake build`. Expected: no fixes. Cloud sessions can do this
   (`releases.lean-lang.org` and the Mathlib cache hosts are allowed; the Mathlib cache is a
   multi-GB download against the session's disk allowance).
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
