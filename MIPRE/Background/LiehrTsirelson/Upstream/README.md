# Vendored `lukasliehr/MIPRE` core

This directory is a **generated, read-only** copy of the statement vocabulary of
[lukasliehr/MIPRE](https://github.com/lukasliehr/MIPRE), an independent Lean 4 formalization
whose goal is the negative resolution of Tsirelson's problem along the route of MIP* = RE.
Its terminal file `Tsirelson/MainStatement.lean` states three propositions in its own terms
(games on `EuclideanSpace`, POVMs on both sides, `sSup` values) and proves none of them.
`MIPRE/Background/LiehrTsirelson/Main.lean` proves all three from `MIPRE.separation`, through
the identification of the two vocabularies in `MIPRE/Background/LiehrTsirelson/Bridge.lean`;
`MIPRE/Background/LiehrTsirelson/Axioms.lean` asserts that the three proofs use only the
standard axioms. `reports/liehr-tsirelson-bridge.md` records what the exercise showed about
the two sets of definitions.

## License

The upstream repository carries **no license file**, and the archive it was vendored from
carries none either. The files here are reproduced as the statements this repository
proves, with their provenance in every header; the maintainer is to settle the terms with
upstream before the tree is relied on for anything else.

## Conventions

- Do not edit files here by hand: re-run `scripts/vendor-liehr.py` instead. The only
  differences from upstream are the header, the rewritten `import` prefix (`Tsirelson.`
  becomes `MIPRE.Background.LiehrTsirelson.Upstream.`) and one redirected import:
  `MainStatement.lean` imports upstream's facade `Tsirelson.Operational`, which re-exports
  the core together with a bridge tree the statements do not use, and the import is
  redirected to `Tsirelson.Core`. The Lean *namespace* is unchanged (`Tsirelson`).
- Nothing outside `MIPRE/Background/LiehrTsirelson/` may refer to that namespace.
- Only the import closure of `Tsirelson.MainStatement` (after the redirection) is vendored:
  the eight `Core` modules and the facade `Core.lean`. Docstrings cite upstream's own
  blueprint (`Blueprint/Nodes/...`); those resolve in the upstream repository.

## Local deviations from upstream

None beyond the mechanical ones above.

## Provenance

<!-- BEGIN GENERATED (scripts/vendor-liehr.py) -->
- Upstream: https://github.com/lukasliehr/MIPRE
- Snapshot: a snapshot of the `main` branch supplied on 2026-09-25 (archive, no commit recorded)
- Vendored files: 9 Lean files, 1628 lines (the import closure of `Tsirelson.MainStatement` after the redirection); 14 import lines rewritten from `Tsirelson.` to `MIPRE.Background.LiehrTsirelson.Upstream.`, 1 redirected `Tsirelson.Operational` to `Tsirelson.Core`
- `set_option autoImplicit true` inserted: no (not needed)
<!-- END GENERATED -->
