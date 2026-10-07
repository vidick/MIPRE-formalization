# MIP* = RE — a Lean formalization project

[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-lightblue.svg)](https://opensource.org/licenses/Apache-2.0)

This repository hosts a collaborative Lean 4 formalization project for the theorem
**MIP\* = RE** (Ji, Natarajan, Vidick, Wright, Yuen,
[arXiv:2001.04383](https://arxiv.org/abs/2001.04383)).

A Mathlib-only statement of the main theorem is in
[`MIPRE/HaltingGameValue.lean`](MIPRE/HaltingGameValue.lean)
(`HaltingGameValue.HaltingReducesToGameValue`): there is a computable map from Turing machines
to nonlocal games sending halting machines to games of synchronous value 1 and non-halting
machines to games of value at most 1/2.

**Status.** That statement is proved:
[`HaltingGameValue.halting_reduces_to_gameValue`](MIPRE/MainTheorem.lean), with no `sorry` and
no axiom beyond `propext`, `Classical.choice` and `Quot.sound`. The proof lives in
[`MIPRE/MainTheorem.lean`](MIPRE/MainTheorem.lean), because it needs the whole development and
the statement file imports Mathlib only. The same file proves the reduction to the quantum
value, the uncomputability of both values, and `MIPRE.Halting.mipstar_eq_re : MIPStar = IsRE`
for the paper's polynomial-time class (`MIPRE.MIPStar`; the computable relaxation is
`MIPRE.MIPStarComputable`, with `mipstarComputable_eq_re`).

The proof is the compression pipeline (`MIPRE.GapCompression.ofPipeline`) with its three
stages supplied:
* introspection, [`MIPRE.Introspection.seven`](MIPRE/Background/Introspection/Compiler.lean);
* answer reduction, [`MIPRE.AnswerReduction.answerReduction`](MIPRE/Background/AnswerReduction/Instance.lean),
  over the classical PCP decider;
* parallel repetition, [`repetition 7`](MIPRE/Background/Repetition/Verifier.lean).

**The Aldous–Lyons conjecture.** The development also proves the main theorem of *The
Aldous–Lyons Conjecture II: Undecidability* (Bowen, Chapman, Vidick,
[arXiv:2501.00173](https://arxiv.org/abs/2501.00173)), `TMIP* = RE`, as the Mathlib-only
statement [`TailoredGameValue.TailoredHaltingReduction`](MIPRE/TailoredGameValue.lean), and
with it the corollary of *The Aldous–Lyons Conjecture I: Subgroup Tests* (Bowen, Chapman,
Lubotzky, Vidick, [arXiv:2408.00110](https://arxiv.org/abs/2408.00110)) that the Aldous–Lyons
conjecture is false, `SubgroupTestValue.aldous_lyons_false : ¬ AldousLyons`
([`MIPRE/SubgroupTestValue.lean`](MIPRE/SubgroupTestValue.lean)). Both are proved in
[`MIPRE/TailoredMIP.lean`](MIPRE/TailoredMIP.lean), with the same three axioms; the plan was
[`planning/aldous-lyons-track.md`](planning/aldous-lyons-track.md).

## Project links

- [Project website](https://vidick.github.io/MIPRE-formalization/)
- [Blueprint](https://vidick.github.io/MIPRE-formalization/blueprint/) — the proof plan,
  with a dependency graph linking informal mathematics to Lean declarations
- [API documentation](https://vidick.github.io/MIPRE-formalization/docs/)
- [Task dashboard](https://github.com/vidick/MIPRE-formalization/projects) — see
  [CONTRIBUTING.md](CONTRIBUTING.md) for how to claim a task
- Independent verification with the Lean comparator, each in a repository whose only file
  to audit is a Mathlib-only `Challenge.lean`:
  [mipre-comparator](https://github.com/vidick/mipre-comparator) for the halting reduction
  of `MIP* = RE`, and
  [aldous-lyons-comparator](https://github.com/vidick/aldous-lyons-comparator) for
  `TMIP* = RE` and the refutation of the Aldous–Lyons conjecture

## Building the project

1. Install Lean 4 following the
   [Lean installation guide](https://leanprover-community.github.io/get_started.html)
   (this installs `elan` and VS Code support).
2. Clone this repository and fetch the Mathlib build cache — do **not** build
   Mathlib from source:
   ```bash
   git clone https://github.com/vidick/MIPRE-formalization.git
   cd MIPRE-formalization
   lake exe cache get
   lake build
   ```

For native Windows development, see [the local Lean workflow](docs/lean-local-windows.md)
for caches outside OneDrive and timed single-file, module, and full-library checks.

### Cloud sessions

Claude Code cloud sessions on this repository get Lean 4, a compiled Mathlib and
this repository's own compiled modules — the latter published by CI on every push
to `main` and downloaded into the environment's snapshot by its setup script
(`.claude/cloud-setup.sh`), since nothing can be compiled inside the five minutes
a setup script gets. A SessionStart hook and the `lean-lsp` MCP server expose all
of it to the session's checkout; see
[docs/lean-cloud.md](docs/lean-cloud.md) for the one-time environment
configuration.

## Building the blueprint locally (optional)

The blueprint is compiled by CI on every push to `main`, so you do not need a
local setup to contribute. If you want a local preview (requires a TeX
distribution and [leanblueprint](https://github.com/PatrickMassot/leanblueprint)):

```bash
pip install leanblueprint
leanblueprint pdf    # -> blueprint/print/print.pdf
leanblueprint web    # -> blueprint/web/   (requires graphviz/pygraphviz)
leanblueprint serve  # preview the website locally
```

## Repository layout

- [`MIPRE/`](MIPRE) — the Lean source files (`MIPRE.lean` is the root module
  importing everything).
  - [`MIPRE/Mathlib/`](MIPRE/Mathlib) — general-purpose declarations destined
    to be upstreamed to Mathlib (tracked on the
    [upstreaming dashboard](https://vidick.github.io/MIPRE-formalization/)).
  - [`MIPRE/LCS/`](MIPRE/LCS) — binary linear constraint system (LCS) games,
    contributed by Sean Perazzolo (vendored with permission from
    [sean-prz/LCS_In_Lean](https://github.com/sean-prz/LCS_In_Lean) and adapted
    to this repository: Lean/Mathlib v4.32.0, `ZMod 2` outcome types, Mathlib
    naming conventions): observable and projector strategies, loss operators
    and their sum-of-squares decomposition, solution groups, the Mermin–Peres
    magic square, and a bridge interpreting an LCS instance as a `MIPRE.Game`
    ([`MIPRE/LCS/NonlocalGame.lean`](MIPRE/LCS/NonlocalGame.lean)).
  - [`MIPRE/Background/LIDT/`](MIPRE/Background/LIDT) — the classical low
    individual degree test. Its soundness theorem is the one formalized by
    Sirui Lu, Ruixuan Deng and Zhengfeng Ji in
    [MIPStarRE](https://github.com/LionSR/MIPStarRE), which `lakefile.toml`
    requires as a Lake dependency at a pinned commit (registered in Palomar as
    PALOMAR-2026-08-18-000001; see
    [`planning/palomar-dependencies.md`](planning/palomar-dependencies.md)). The
    directory states the theorem in this repository's vocabulary and bridges the
    two (`Bridge/`), and `Co/` ports the proof to commuting-operator strategies;
    the plan is in [`planning/lidt-port.md`](planning/lidt-port.md).
- [`blueprint/src/`](blueprint/src) — the LaTeX sources of the blueprint.
- [`website/`](website) — the Jekyll home page deployed to GitHub Pages.
- [`.github/workflows/`](.github/workflows) — CI: project build on every PR,
  blueprint/docs/website deployment on `main`, task-dashboard automation.
- [`planning/`](planning) — plans and decision records of the larger tracks;
  [`planning/formalization-plan.md`](planning/formalization-plan.md) is the current plan
  (what to work on next, and which of the three artifacts is authoritative for what).

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for the full workflow (task claiming,
pull requests, review cycle). The blueprint's introduction describes entry
points by background (quantum information, complexity/computability, operator
algebras, Lean/Mathlib), and required external results are tagged with effort
estimates (easy / medium / hard / in Mathlib) in the blueprint.

## Acknowledgements

This repository is based on the
[LeanProject template](https://github.com/leanprover-community/LeanProject) and
copies its collaboration mechanisms from the
[FLT project](https://github.com/ImperialCollegeLondon/FLT). 
