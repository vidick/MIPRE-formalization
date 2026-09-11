# Vendored MIPStarRE sources

This directory is a **generated, read-only** copy of Lean sources of
[MIPStarRE](https://github.com/LionSR/MIPStarRE), Sirui Lu's formalization of the
soundness of the classical low individual degree test (Ji, Natarajan, Vidick, Wright,
Yuen, arXiv:2009.12982). The main theorem is `MIPStarRE.LDT.Test.mainFormal`
(`LDT/Test/MainTheorem/MainFormal.lean`). It is used in this repository only through
the bridge in `MIPRE/Background/LIDT/Bridge/`; see `planning/lidt-port.md`.

Only the import closure of the upstream modules that the bridge imports is vendored
(the `ROOTS` of `scripts/vendor-lidt.py`); upstream's aggregators, its own axiom-audit
file, and a few modules not needed for the main theorem are left out.

## Permission and license

The upstream repository carries no license file. Its authors agreed (September 2026,
by correspondence with Thomas Vidick) to the inclusion of their code in this
repository under its Apache 2.0 license. Copyright remains with Sirui Lu and the
MIPStarRE contributors; every file carries a header saying so.

## Conventions

- Do not edit files here by hand: re-run `scripts/vendor-lidt.py` instead. The only
  differences from upstream are the header, the rewritten `import` prefix
  (`MIPStarRE.` becomes `MIPRE.Background.LIDT.MIPStarRE.`), and the compile fixes
  listed below. Lean *namespaces* are unchanged (`MIPStarRE.LDT`, `MIPStarRE.Quantum`).
- Nothing outside `MIPRE/Background/LIDT/` may refer to the `MIPStarRE` namespace.
- Docstrings cite upstream paths (`blueprint/src/chapter/...`, `references/ldt-paper/...`,
  `docs/paper-gaps/...`); these resolve in the upstream repository at the commit below.

## Local deviations from upstream

Compile fixes for the toolchain crossing (upstream builds with Lean v4.32.0, this
repository with v4.33.0), applied by `scripts/vendor-lidt.py`:

1. Every file gets `set_option backward.isDefEq.respectTransparency false` after its
   imports: Lean v4.33's transparency check rejects a number of `rw`/`simp` steps of the
   upstream proofs (targets that are not type-correct at implicit transparency), and this
   is the option Mathlib sets on its own affected declarations. Setting it for the whole
   tree matches what a project-wide setting achieved for these files, while the rest of
   the repository keeps the check.
2. With the option, a tactic step may close the goal one line earlier than under Lean
   v4.32, and a trailing `rfl` then fails with "no goals". Every bare `rfl` tactic line of
   the tree is therefore `try rfl` (marked by a comment); a `rfl` that is still needed
   runs as before. Term-mode proofs consisting of `rfl` alone are left unchanged.
3. Two recorded fixes in the script's `FIXES` table, marked in the source by a comment:
   the same tolerance for one trailing `exact` in
   `LDT/ExpansionHypercubeGraph/Theorems/Foundations.lean`, and, in
   `LDT/Pasting/ComparisonLemmas/CommuteGHalfSandwich/MoveChain/FlatChain.lean`, the two
   index conditions of a summand supplied to `simp` explicitly (they follow from the
   hypothesis `hone_lt` already in the proof).

## Provenance

<!-- BEGIN GENERATED (scripts/vendor-lidt.py) -->
- Upstream: https://github.com/LionSR/MIPStarRE
- Commit: `507e81220d95266ff3d589d125b2f87c7300a9fb` (2026-08-25)
- Vendored files: 322 Lean files, 122381 lines (the import closure of 10 root modules); 658 import lines rewritten from `MIPStarRE.` to `MIPRE.Background.LIDT.MIPStarRE.`
- Audit aid: `Challenge.lean.expected` = upstream `scripts/comparator/expected/Challenge.lean.expected`
- `set_option backward.isDefEq.respectTransparency false` inserted after the imports of every file; every bare `rfl` tactic line made `try rfl`; recorded compile fixes applied: 2 (listed under "Local deviations from upstream")
<!-- END GENERATED -->
