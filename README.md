# MIP* = RE — a Lean formalization project

[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-lightblue.svg)](https://opensource.org/licenses/Apache-2.0)

This repository hosts a collaborative Lean 4 formalization project for the theorem
**MIP\* = RE** (Ji, Natarajan, Vidick, Wright, Yuen,
[arXiv:2001.04383](https://arxiv.org/abs/2001.04383)).

A candidate Mathlib-only statement of the main theorem is in
[`MIPRE/HaltingGameValue.lean`](MIPRE/HaltingGameValue.lean): there is a computable map
from Turing machines to nonlocal games sending halting machines to games of synchronous
value 1 and non-halting machines to games of value at most 1/2.

## Project links

- [Project website](https://vidick.github.io/MIPRE-formalization/)
- [Blueprint](https://vidick.github.io/MIPRE-formalization/blueprint/) — the proof plan,
  with a dependency graph linking informal mathematics to Lean declarations
- [API documentation](https://vidick.github.io/MIPRE-formalization/docs/)
- [Task dashboard](https://github.com/vidick/MIPRE-formalization/projects) — see
  [CONTRIBUTING.md](CONTRIBUTING.md) for how to claim a task

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

### Cloud sessions

Claude Code cloud sessions on this repository get Lean 4, a compiled Mathlib
and a warm build of `MIPRE`, provisioned once by the cloud environment's setup
script (`.claude/cloud-setup.sh`) and exposed to the session's checkout by a
SessionStart hook and the `lean-lsp` MCP server; see
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
    individual degree test. The subdirectory
    [`MIPStarRE/`](MIPRE/Background/LIDT/MIPStarRE) is a generated, read-only copy
    of Sirui Lu's [MIPStarRE](https://github.com/LionSR/MIPStarRE) formalization of
    the soundness theorem of arXiv:2009.12982 (vendored with the authors'
    permission by [`scripts/vendor-lidt.py`](scripts/vendor-lidt.py); see its
    [README](MIPRE/Background/LIDT/MIPStarRE/README.md)). The rest of the
    directory states the theorem in this repository's vocabulary and bridges the
    two; the plan is in [`planning/lidt-port.md`](planning/lidt-port.md).
- [`blueprint/src/`](blueprint/src) — the LaTeX sources of the blueprint.
- [`website/`](website) — the Jekyll home page deployed to GitHub Pages.
- [`.github/workflows/`](.github/workflows) — CI: project build on every PR,
  blueprint/docs/website deployment on `main`, task-dashboard automation.

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
