# Palomar: the dependence on the registered LIDT and QPBT results

Written 2026-10-05, for the submission planned in `planning/palomar.md`. The maintainer wants
the MIP* = RE entry to be marked as dependent on the two results already in Palomar: the
soundness of the low individual degree test (LIDT) and the quantum Pauli basis test (QPBT).
This note records what those entries are, what Palomar means by "depends on", what was done
(A and B below) and what was deliberately not done (C).

## The two registered results

| | repository | commit | Lean | compared declaration(s) |
|---|---|---|---|---|
| LIDT | `LionSR/LDT-comparator`, a thin wrapper, **PALOMAR-2026-08-18-000001** | wraps `LionSR/MIPStarRE` at `892b939c541e90192a8c77917cbb106678fd43b3` | v4.32.0 | `MIPStarRE.LDT.Test.mainFormal` |
| LIDT, substantive | `LionSR/MIPStarRE` (Sirui Lu, Ruixuan Deng, Zhengfeng Ji) | `5fc363bc8b77b1a6bbdaaeea634f1b0f3ff0ad79` (2026-10-04): the Lean-module port of `507e8122`, the commit this repository used to vendor; its audit `audits/2026-10-03-lean-module-upgrade.md` says the statement text of `mainFormal` is unchanged | v4.35.0-rc2, Mathlib `065356127b1d` | — |
| QPBT | `Dengnifer/MIPStarRE-QPBT` (Ruixuan Deng) | `179a37893d2a037cce0587ea932f5da819c7d78c` (2026-10-04) | v4.35.0-rc2, Mathlib `065356127b1d` | `MIPStarRE.QPBT.Palomar.{exists_spcc_value_one, exists_ld_soundness, pauli_soundness, pauli_soundness_qubit}` (Lemma 7.13, Theorems 7.8 and 7.14, Corollary 7.15 of MIP* = RE) |

QPBT takes `LionSR/MIPStarRE` at `5fc363b` as a **pinned Lake Git dependency**, not a copy,
and records it under `related_formalizations` with `relationship: builds-on`, naming the
Palomar identifier in the note. Its own `formalization.yaml` lists this repository as an
*independent* formalization of the Pauli basis test (`MIPRE/Background/QLD`). Whether QPBT is
registered, and under which identifier, is read off the registry
(`https://data.palomar-registry.org/repositories/dengnifer/mipstarre-qpbt.json`; the `data.` host is refused by the cloud proxy even with `palomar-registry.org` allowed, so it is read from outside a session) and goes
into the note of our `related_formalizations` entry for it.

## What "depends on" means in Palomar

From `PalomarRegistry/PalomarPolicy` `CONTRIBUTING.md` (2026-09-28):

- **The Challenge cannot import a registered result.** Its transitive import closure may
  contain only Lean core, Mathlib, Tau Ceti and CSLib; "Previous registration by Palomar does
  not make a repository an approved Challenge dependency." So the statement of MIP* = RE stays
  self-contained (`Palomar/Challenge.lean`, Mathlib only), whatever the proof uses.
- **Solution-side dependencies may be any public GitHub repository pinned at a full commit
  SHA** in `lake-manifest.json`. The verifier materialises them and records the "full
  dependency graph" in the registered report. This is the mechanical sense of dependence.
- **`related_formalizations`** entries (`id`, `relationship` among `builds-on`, `adapts`,
  `independent`, `supersedes`, `other`, and a `note`) are the metadata sense. Earlier Lean
  work goes there, not under `sources`, which is for mathematical sources only (`type` among
  `paper`, `book`, `web discussion`, `folklore`, `original-proof`, `other`).

So "MIP* = RE depends on LIDT" is expressed by (i) a Lake dependency on `LionSR/MIPStarRE`
that the proof uses, and (ii) a `builds-on` entry naming PALOMAR-2026-08-18-000001.

## A. Metadata (done)

`formalization.yaml`: `sources` now holds mathematical sources only, with the policy's `type`
values (the paper, the companion manuscript as `other`, and the LIDT paper as `background`);
the three reused formalizations moved to `related_formalizations` (`builds-on`: LDT-comparator
with its identifier, MIPStarRE at the pinned commit, ten-proofs, commuting-repetition);
QPBT is listed as `independent`, with its identifier to be added once read off the registry.
The file passes the template's validator and the verifier's own loader
(`PalomarSubmission/scripts/submission_contract.py: load_formalization_metadata`, run from a
clone).

## B. LIDT as a Lake dependency (done)

Before: `MIPRE/Background/LIDT/MIPStarRE/`, a vendored copy of 322 modules of `507e8122`
with recorded compile fixes (`scripts/vendor-lidt.py`), imported by the six
`LIDT/Bridge/*.lean` and — contrary to what CLAUDE.md said — by 96 modules of the
commuting-operator port `LIDT/Co/`, which reuse its definitions. After: `lakefile.toml`
requires `MIPStarRE` at `5fc363b`; the copy is gone; the 102 importers import `MIPStarRE.*`
(the namespaces were never renamed, so only the module paths change); the bridge consumes
exactly the registered declaration, `MIPStarRE.LDT.Test.mainFormal`.

What it took, and what to know:

- **Mathlib pins differ**: upstream is on `v4.35.0-rc2` (`065356127b1d`), this repository on
  `v4.35.0-rc3` (`c55e6e786f49`, 142 commits later). Lake builds the dependency against the
  root's Mathlib; on 2026-10-05 all 337 modules of `5fc363b` compiled that way with no error
  or warning. A fix the dependency needs cannot be applied here (there is no vendored copy to
  patch): it goes upstream, or the pins are aligned (the maintainers chose rc2 "so that the
  two developments can eventually share a Lake build", and `v4.35.0` final is the natural
  common point).
- **`5fc363b` is not `507e8122`**: the Lean-module port made 45 helpers `private` and
  `Parameters.next` `@[reducible]`. A `private` name inside an `open NS (names…)` list makes
  Lean reject the whole list, so 33 helpers that `LIDT/Co/` named this way (and their private
  dependencies) are now copied into the port, public, with upstream's proofs and a docstring
  saying so (`scripts/port-pairing.py` lists them as `new`); the one exception is
  `hypercubeSpectralGap_operator_posSemidef`, derived from the public Loewner-order form instead
  of copying its dozen Fourier lemmas. The reducible `next` changed what `simp` sees in one
  `Co` proof (`three_le_k_sq_mul_next_m_of_nonneg`), repaired in place.
- `scripts/port-pairing.py` and `scripts/port-classify.py` pair the port against
  `.lake/packages/MIPStarRE/MIPStarRE/LDT` now, so they need the dependency checked out
  (`lake build` does it). `scripts/vendor-lidt.py` is retired, kept for the record of its fixes.
- **Licence**: `LionSR/MIPStarRE` has no licence file at `5fc363b`; the authors' consent of
  September 2026 is recorded in `related_formalizations`. As a dependency rather than a copy,
  nothing of it is redistributed from this repository.
- CI clones the dependency on each run (`lake build` does); its oleans live under
  `.lake/packages/MIPStarRE/.lake/build`, which the build cache of `build-project.yml` does
  not include. The cloud snapshot (`.claude/cloud-setup.sh`) builds from `lake-manifest.json`
  and picks it up the same way.

## C. Routing the main theorem through QPBT (not done, by decision)

The main theorem uses the Pauli basis test at one line (`Introspection/Compiler.lean`,
`QLD.approxSoundIn_tensor`), through `MIPRE/Background/QLD` (34k lines), which proves the test
in a bipartite model because the commuting-operator track needs it in dyadic pairs. Replacing
that route by QPBT's `pauli_soundness` would need a bridge comparable to the LIDT bridge and
adapter (about 5k lines): a game equivalence between `MIPRE.QLD.qldGame` and QPBT's
`pauliGame` (two encodings of the paper's figure), strategy and extraction transports, a
`SoundIn` generalised over its error function (QPBT's `deltaQld` has the same closed form as
our `errShape`), and a transport along QPBT's fixed-field contract (`fixedFieldModel`), since
its theorem is stated for one chosen field per size. The QLD development would stay for the
commuting-operator track regardless. The maintainer judged this too expensive for what it
buys (2026-10-05); QPBT is cited as related, independent work instead.
