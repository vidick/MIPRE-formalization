# Submitting the formalization to Palomar

Palomar (`palomar-registry.org`) is the registry of Lean-verified mathematics that opened on
2026-08-18, maintained by Matthew Ballard, Nestor Guillen, Jaume de Dios Pont and Terence Tao and
incubated by the Lean FRO and ICARM. This note records what a submission needs, where this
repository stands against it (measured on 2026-09-28 at `2498541`), and the plan. The site was
read through its public repositories: `PalomarRegistry/PalomarTemplate` (the starter layout),
`PalomarRegistry/PalomarSubmission` (the verifying CI, with `toolchains.json`,
`allowed-challenge-repositories.json` and `verification-profile.json`) and
`PalomarRegistry/PalomarPolicy` (`CONTRIBUTING.md`, the submission guidelines).

## What a submission is

A public GitHub repository at one 40-character commit, holding

* `lean-toolchain`, `lakefile.toml` (or `.lean`) and a committed `lake-manifest.json`;
* `Challenge.lean`: the statement surface a mathematical reader audits. Every compared theorem is
  stated there with `sorry` for its proof, and every definition the statements need is there too,
  with a docstring. Hard limit 1,000 lines and 100 KiB, mechanical warning above 300 lines or
  32 KiB. Its transitive import closure may contain only Lean core, Mathlib, Tau Ceti and CSLib
  (the last two are recorded as "qualified" trust), and it is compiled by Palomar against its own
  frozen copy of those libraries, not against the submission's build;
* `Solution.lean`: the same declarations, proved. It may import anything, including arbitrary
  public-GitHub Git dependencies pinned at full commit SHAs;
* `comparator.json`: `challenge_module`, `solution_module`, `theorem_names`, `definition_names`,
  `permitted_axioms` (only `propext`, `Quot.sound`, `Classical.choice`), `enable_nanoda`;
* `formalization.yaml` (schema v0.4): name, abstract, human authors and responsible maintainers
  (no AI systems in either list), SPDX licence matching the root `LICENSE`, arXiv and MSC2020
  classes, a nonempty `sources` list with `relationship` per source, `automation.methods`
  (`manual`, `copilot`, `agent`, `autonomous`, `other`, with models), `status` (sorry counts,
  axioms, main results), `fidelity.divergences`, `review.status`, an `alignment` table from
  source statements to Lean declarations;
* exactly one licence file at the root, Apache-2.0 in the template.

The verifier rebuilds everything in a fresh `.lake` (Mathlib cache used), compiles the Challenge
separately under a per-run namespace so the Solution cannot capture it, runs `lake comparator`,
and replays the exported proofs in Lean's kernel, NanoDa and con-ron. Budget: 19,800 s on a
GitHub-hosted `ubuntu-24.04` runner with at least 14 GB of memory. Then a language model
reviews the metadata and the Challenge against the informal account through fixed prompts
(no human reads an ordinary submission); outcomes are `neutral`, `revision_required` or
`rejected`; on `neutral` the submitter may register, which publishes the review and mints a
`PALOMAR-YYYY-MM-DD-NNNNNN` identifier.

Mechanical rules that bind us:

| rule | value | this repository |
|---|---|---|
| minimum toolchain | `v4.35.0-rc2` (`toolchains.json`); Mathlib's `lean-toolchain` must equal ours | `v4.33.0` |
| Mathlib pin | an ancestor of `master` or a semver release tag | tag `v4.33.0`, too old |
| module system | every regular `.lean` file starts with a `module` header | none of ~1,400 files |
| per-file cap | 10,000 physical lines | one file: `Repetition/TenProofs/QuantumParallelRepetition.lean`, 70,994 lines; nothing else above 5,000 |
| Challenge | 1,000 lines, Mathlib-only imports | `MIPRE/HaltingGameValue.lean` (201 lines, Mathlib only) qualifies; `MIPStar = IsRE` does not (its definitions need 53 modules, 17.6k lines) |
| axioms | the three standard ones; no `sorryAx`, no `Lean.ofReduceBool` | guards in `MIPRE/Axioms.lean` enforce it; `native_decide` occurs only in `TM/Code/Examples.lean`, outside the closure |
| repository | 500 MiB, no submodules, no LFS, deps on public GitHub at SHAs | 30 MB, all satisfied |
| licence | one root file, SPDX detectable, equal to `project.license` | Apache-2.0 |

Licensing of the vendored trees, which the Solution's closure includes: ten-proofs and
commuting-repetition are Apache-2.0; `LIDT/MIPStarRE` (322 modules in the closure) rests on the
authors' written consent of September 2026, to be recorded in `sources` (since 2026-10-05 it is
a Lake dependency rather than a copy, recorded under `related_formalizations`; see
`planning/palomar-dependencies.md`); the Liehr Tsirelson
upstream carries no licence and is not in the main theorem's closure, so it stays out of the
submitted snapshot or its terms are settled first.

## Plan

Each phase is one pull request unless noted; the order is forced by the dependencies.

1. **Mathlib bump** to the newest tag at or above `v4.35.0-rc2` (`v4.35.0-rc3` on 2026-09-28;
   re-bump to `v4.35.0` when it is released). `lake update` cannot run in cloud sessions
   (Reservoir is unreachable), so `lake-manifest.json` is rewritten by hand from Mathlib's own
   manifest at the tag, the toolchain is installed from `releases.lean-lang.org`, and
   `lake exe cache get` fetches the oleans. The vendored trees are repaired only through
   `scripts/vendor-*.py`. The cloud setup script must be re-saved afterwards (it reads
   `lean-toolchain`).

   Done 2026-09-28 (v4.33.0 to v4.35.0-rc3, Mathlib `db584cd` to `c55e6e7`). What it took,
   for the next bump: Mathlib's cache moved to `cache.mathlib.org`, which the cloud
   environment does not allow (`docs/lean-cloud.md` has the workaround); six full build
   passes of about 25 minutes each, because a failed module hides its dependents until the
   next pass (compiling a suspect file alone with `lake env lean` once its imports are
   built, in parallel with the pass, saves a pass); some twenty distinct breakages in our own code, all mechanical (a `congr` or
   `gcongr` that now closes the goal and leaves dead tactics behind, the deleted
   `MvPolynomial.coeff`, renamed or re-argumented lemmas such as `nonneg_iff_isPositive`,
   `Finset.prod_le_one₀`, `norm_le_norm_of_le_of_nonneg`, `NNRat.cast_pow` moved to another
   module, and two `Primrec` lemmas that only needed a larger heartbeat budget); and about
   forty in the vendored trees, recorded as `Fix` and `PatternFix` entries of the vendor
   scripts, whose `--apply-fixes` re-applies them without a clone. One recurring and
   non-obvious failure: rewriting with `map_sum` at a `MvPolynomial` ring homomorphism now
   times out, because instance search tries `RingHomClass.toLinearMapClassNNRat` first and
   asks for a `Module ℚ≥0` on the polynomial ring that never resolves when the coefficient
   type is a class projection; supplying the `AddMonoidHomClass` instance with `haveI` is
   the fix. Another: on `H →L[ℂ] H` the `Star` instance is `⟨adjoint⟩`, and `rw` and
   `simp` no longer match the generic `star_sub`, `star_add`, `star_zero` (stated for the
   `StarAddMonoid`-derived instance) against it; applying the lemma to its explicit
   arguments, or rewriting `star 0` through `star_eq_adjoint`, resolves the instance first.
2. **Module headers**: `module` at the top of every `.lean` file, with `public import` for
   re-exported imports and `@[expose] public section` where importers unfold definitions.
   Mechanical, scripted (`scripts/modularize.py`), one PR; vendored trees through their
   vendor scripts. The recipe was checked on Lean 4.33 with small experiments
   (2026-09-28): a plain `import` inside a module is private to it, so every import becomes
   `public import` to keep the transitive re-exports the library relies on; without
   `@[expose]` a public definition is opaque to importers (`rfl` fails across files), so
   every file opens `@[expose] public section`; a `private` definition may not occur in a
   public theorem's statement or an exposed definition's body (private theorems in proofs
   are fine), so the 198 private non-theorem declarations lose `private`, after a check
   that their full names are distinct (one clash: `isEmptyProg` in three `LowDegree`
   files).

   Done 2026-09-28, on Lean v4.35.0-rc3, with the recipe corrected by experiments
   (`MIPRE/ModExp`, kept in `Scratch/`): macros and elaborators are visible to module
   importers whether inside or outside the public section, so they stay where they are; a
   `macro` needs no `meta` import at all (its quotation must be a single tactic, so a
   sequence `t₁; t₂` is parenthesised, which every macro of the library already is); an
   `elab`, or a definition carrying `[tactic]`, needs `public meta import Lean` (the script
   twins every `import Lean` line with a `meta` one), and a definition with such an attribute
   must be `meta`, together with every definition it calls (one site, the vendored
   `avg_congr`, recorded in `scripts/vendor-lidt.py`). The private-name clash became two after
   the first rename (`isEmptyBitsProg` already existed in `BinaryDivision.lean`), so the three
   are now `isEmptyDivProg`, `isEmptyRemProg` and `isEmptyListProg`. Two more things the
   first build taught: a private *theorem* is also forbidden in the body of an exposed
   definition, and a `PolyTimeFun` is a program with its cost proof, so the private cost
   lemmas of the `LowDegree` programs were "unknown identifiers"; the script now drops
   `private` from every declaration (791 theorems, one clash, `matrix_ite_entry`, renamed
   per file). And Mathlib is itself a library of modules that imports its tactic modules
   privately where it can, so a module sees `norm_num` only along a public import path
   (a non-module file saw everything in its closure): `MIPRE/Tactics.lean` re-exports the
   common tactics and the heavy ones, and the script inserts `public import MIPRE.Tactics`
   into every module that imports part of Mathlib rather than the `Mathlib` umbrella
   (154 files). The vendor scripts call the modularizer on the trees they produce and on
   `--apply-fixes`, and CI runs `scripts/modularize.py --check`.

   The second full build (the first was cut short once the bundle existed) found three more
   things, fixed in the follow-up PR: a formerly private name can become *ambiguous* rather
   than clash, when a file opens two namespaces that both define it (`andCheck` of the
   source-compiler guard against the auxiliary program's, `basisIndex` of the Pauli CL
   against the branch program's; renamed `guardAndCheck`, `basisFin`); and a file that runs
   compiled code at elaboration time (`#eval`, `native_decide`: the four `TM/Code` demo
   files) gets that code only through `meta import`, so the script twins every import of
   such a file. Each full pass costs about 50 minutes on the cloud VM; a failed module hides
   its dependents until the next pass, so compiling a suspect file alone with
   `lake env lean` as soon as its imports are built, in parallel with the pass, is what
   keeps the count of passes down.
   One more consequence for the tooling: a module's `.olean` holds only its exported
   interface, in which every theorem is an axiom, and the proofs sit in the `.olean.private`
   part; `scripts/blueprint-deps.lean` (behind `blueprint-edges.py`) read the `.olean` alone
   and reported 374 stale and 854 missing edges, and now reads both parts. Anything else that
   inspects oleans directly (rather than through `import`) needs the same.
3. **Split the 71k-line module** in `scripts/vendor-repetition.py` into files under 10,000
   lines, deterministically, recorded like every other vendor fix.
4. **The Challenge**: a self-contained, Mathlib-only statement file. `HaltingGameValue.lean`
   already states the halting reduction and the uncomputability corollaries. The class equality
   `MIPStar = RE` needs a compact definition of a polynomial-time verifier that a reader can
   audit; the candidates and their cost (the bridge from `MIPRE.Cost` to the Challenge's model)
   are worked out in a separate draft and decided with the maintainer.

   Done 2026-09-28. `Palomar/Challenge.lean` (419 lines, Mathlib-only, module form, four
   `sorry`ed theorems) with the decisions of `planning/palomar-challenge.md` section 4;
   `Palomar/Solution.lean` (846 lines) repeats every Challenge declaration verbatim (the
   comparator matches by name, and a file cannot import the Challenge and declare its names
   again) and proves the four theorems by transport, the structural identifications of the
   Challenge's types with the library's sitting in two marked sections of the Solution and
   the library's results restated in the Challenge's shape in `Palomar/Bridge.lean`
   (188 lines). All four depend on `propext`, `Classical.choice` and `Quot.sound` only. The
   `Palomar` library of `lakefile.toml` (roots `Challenge`, `Bridge`, `Solution`) is a
   default target, so `lake build` and CI build them; `Palomar.lean` exists only because
   `mk_all --check` wants an aggregator and is not a root, since it could not compile. The
   Challenge is exempt from the `MIPRE.Tactics` bundle and imports what it uses.

   **No extensible tactic inside a Challenge definition** (found 2026-10-05, by the first
   Palomar preflight). The comparator (`leanprover/comparator`, `Compare.lean`) walks every
   constant reachable from the compared statements — definitions' values, their auxiliary
   `_proof_n` lemmas, instances — and requires the Challenge's and the Solution's
   `ConstantInfo` to be *equal*, proof terms included; only the named targets are compared by
   statement. The Solution repeats the definitions verbatim, but elaborates them with the
   whole library imported, so a `simp`, `norm_num` or `positivity` inside a definition can
   produce a different term there (the MIPStarRE dependency's simp set changed
   `toGame.μ_sum_one`: "Const does not match between challenge and target
   `GameData.toGame._proof_3`"). Proof obligations inside Challenge definitions are therefore
   written with `rw`/`exact` and named Mathlib lemmas only, and the local
   `scripts/palomar/verify-comparator.sh` (with `--inadvisably-no-sandbox` here) is the test:
   it reproduces the verifier's verdict, with the exports built in the same two environments.
5. **Submission files**: `Solution.lean`, `comparator.json`, `formalization.yaml`, the
   `docbuild/` doc-gen4 project of the template, and the pre-submission scripts
   (`validate-formalization.rb`, `verify-comparator.sh`, `check-lean-sources.py`); then the
   form at `submit.palomar-registry.org`.

   Done 2026-09-28, except `docbuild/`: `comparator.json` (the four theorem names, no
   definition holes, the three axioms), `formalization.yaml` (schema v0.4, validated by the
   template's script; the fidelity section states the tree-program divergence, the sources
   record the three vendored formalizations and the consent for MIPStarRE, the automation
   section names the agent workflow), and the template's three pre-submission scripts under
   `scripts/palomar/` (the source check skips the git-ignored `Scratch/`; the comparator
   script needs `bwrap`, which the cloud container lacks, so `lake comparator` was run with
   `--inadvisably-no-sandbox` here). `docbuild/` (added 2026-09-29) is the template's
   nested doc-gen4 project: `docbuild/lakefile.toml` shares the parent's package directory
   and pins doc-gen4 to the toolchain's tag, its manifest was written by `lake update`
   there, and `cd docbuild && lake build @MIPRE/Palomar:docs` (the library is a target of
   the `MIPRE` package, hence the `@MIPRE/` prefix, unlike the template's own
   `PalomarTemplate:docs`) writes the API documentation of the submission under
   `docbuild/.lake/build/doc/`; `@MIPRE/MIPRE:docs` does the whole library, which the
   blueprint workflow already generates from the root project. Either target first
   generates the doc data of the whole Mathlib closure (22,341 jobs): a run on the cloud
   VM had done 14,006 of them after 65 minutes when the container restarted, so budget
   about two hours, or run it where the blueprint workflow's doc-gen cache is. Open before
   submitting: the
   `LiehrTsirelson/Upstream` tree carries no license and is not in the Solution's closure,
   so either its terms are settled or it leaves the submitted snapshot (removed 2026-10-05,
   with its bridge, by the maintainer's decision; `rem:liehr-statements` records what the
   check showed and the commit that holds it); the metadata's review status is
   "self-assessed"; and `formalization.yaml` names the models used, which the schema
   requires.
