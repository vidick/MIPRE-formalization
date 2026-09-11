# Vendored commuting-repetition sources

This directory is a **generated, read-only** copy of Lean sources of
[commuting-repetition](https://github.com/vidick/commuting-repetition), Thomas Vidick's
formalization of the uniform direct parallel repetition theorem for commuting-operator
strategies (manuscript *Uniform direct parallel repetition for two-player
commuting-operator strategies*, 2026), which also proves Lin's tracial density theorem
(arXiv:2304.01940, Theorem 3.2). The roots are
`CommutingRepetition.uniform_parallel_repetition` (`MainTheorem/Main.lean`) and its
Mathlib-only restatement `MainStatement.uniform_parallel_repetition`
(`StatementBridge.lean`, proving the proposition of `Statement.lean`); Lin's theorem is
`CommutingRepetition.Density.tracialDensity` (`Tracial/Density/Main.lean`). They are
used in this repository only through the bridge in `MIPRE/Background/Repetition/`; see
`planning/repetition-port.md`.

## License

Upstream is released under the Apache 2.0 license, the same license as this
repository. `NOTICE`, copied from upstream, records the material it ports from
`openai/ten-proofs`. Every file carries a header saying so.

## Conventions

- Do not edit files here by hand: re-run `scripts/vendor-repetition.py` instead. The
  only differences from upstream are the header, the rewritten `import` prefix
  (`CommutingRepetition.` becomes `MIPRE.Background.Repetition.CommutingRepetition.`),
  the `set_option autoImplicit true` line inserted after the imports, and the compile
  fixes listed below. Lean *namespaces* are unchanged (`CommutingRepetition`,
  `MainStatement`).
- Nothing outside `MIPRE/Background/Repetition/` may refer to these namespaces.
- Only the import closure of the root modules is vendored (`CR_ROOTS` in the script);
  upstream's audit-node map (`Fidelity/Nodes.lean`) and the modules not needed for the
  roots are left out. Docstrings cite upstream documents (`FIDELITY.md`,
  `DIFFERENCES.md`, `PLAN-*.md`, manuscript section files); these resolve in the
  upstream repository at the commit below.

## Local deviations from upstream

None yet (beyond the mechanical ones above).

## Provenance

<!-- BEGIN GENERATED (scripts/vendor-repetition.py) -->
- Upstream: https://github.com/vidick/commuting-repetition
- Commit: `cfa2f1bf199139cea65827e708f7956c743f14e8` (2026-09-11)
- Vendored files: 130 Lean files, 54798 lines (the import closure of 2 root modules); 246 import lines rewritten from `CommutingRepetition.` to `MIPRE.Background.Repetition.CommutingRepetition.`
- Copied verbatim: `NOTICE` = upstream `lean/NOTICE`
- `set_option autoImplicit true` inserted after the imports: yes
- Recorded compile fixes applied: 0 (listed under "Local deviations from upstream")
<!-- END GENERATED -->
