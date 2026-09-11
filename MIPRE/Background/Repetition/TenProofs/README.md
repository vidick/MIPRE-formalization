# Vendored ten-proofs sources

This directory is a **generated, read-only** copy of one Lean module of
[ten-proofs](https://github.com/openai/ten-proofs), the formalizations accompanying
OpenAI's *Ten Advances in Mathematics and Theoretical Computer Science* (2026):
`QuantumParallelRepetition.lean`, the proof of Chapter 6, *Exponential parallel
repetition for all two-player entangled games*. The root is
`QuantumParallelRepetition.distributionUniformExponential`. It is used in this
repository only through the bridge in `MIPRE/Background/Repetition/`; see
`planning/repetition-port.md`.

## License

Upstream is released under the Apache 2.0 license, the same license as this
repository. Every file carries a header saying so.

## Conventions

- Do not edit files here by hand: re-run `scripts/vendor-repetition.py` instead. The
  only differences from upstream are the header, the `set_option autoImplicit true`
  line inserted after the imports, and the compile fixes listed below. The Lean
  *namespace* is unchanged (`QuantumParallelRepetition`).
- Nothing outside `MIPRE/Background/Repetition/` may refer to that namespace.
- `G_QuantumParallelRepetition.lean.expected` is upstream's Mathlib-only statement file
  (the definitions and the two root statements, with `sorry` proofs), kept as a reading
  aid; it is not built.

## Local deviations from upstream

Compile fixes for the toolchain crossing (upstream builds with Lean v4.32.0, this
repository with v4.33.0), applied by `scripts/vendor-repetition.py` from its recorded
`fixes` table:

1. `exists_proofSchmidtDecomposition`: `set_option backward.isDefEq.respectTransparency
   false in` before the theorem. Under Lean v4.33's transparency check its closing `simpa`
   no longer sees through the abbreviation `Matrix.toEuclideanLin` (the same fix Mathlib
   applies to affected declarations). The statement and proof are unchanged.

## Provenance

<!-- BEGIN GENERATED (scripts/vendor-repetition.py) -->
- Upstream: https://github.com/openai/ten-proofs
- Commit: `94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6` (2026-08-01)
- Vendored files: 1 Lean files, 70984 lines
- Copied verbatim: `G_QuantumParallelRepetition.lean.expected` = upstream `ComparatorChallenges/G_QuantumParallelRepetition.lean`
- `set_option autoImplicit true` inserted after the imports: yes
- Recorded compile fixes applied: 1 (listed under "Local deviations from upstream")
<!-- END GENERATED -->
