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
