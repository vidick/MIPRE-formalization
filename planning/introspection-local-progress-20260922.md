# Introspection continuation: local implementation status

This continuation starts at PR #152 (`82bf8fe2b94c1f7b90ea289d2a9cc6adb4928c11`)
on `codex/introspection-completion-20260922`. The maintainer authorized
completion against the QLD extraction interface; a separate agent owns the
proof of QLD extraction itself.

**The ambient introspection theorem is proved.**
`MIPRE.Introspection.exists_seven` constructs `Nonempty (MIPRE.Introspection 7)`;
`MIPRE.Introspection.seven` supplies a fixed compiler for the compression
pipeline. Both declarations check with only `propext`, `Classical.choice`, and
`Quot.sound`. Repository-wide validation also passes, as recorded below.
The earlier checkpoint remains a historical account of the published work.

## Resumption on 2026-09-23

Upstream `main` now proves `MIPRE.QLD.qld_soundness` (PR #187,
`25f3b15c10285eae94fc98fc9149070df5e79dc5`). It was merged into this branch as
`8b77d46`; the two conflicts were additive import lists. Local introspection
implementation files were preserved. The rolling prebuilt bundle at that exact
upstream commit was downloaded and checked against its release SHA-256
`0011d79d1acef3c80b16ffd644f7c2e4e9e6c3bbf23caa06373ead294fd7e6fb`.
Only the newly merged QLD modules' artifacts were installed, preserving the
local introspection build cache.

The final upstream refresh also found PR #188, `48d14e1`, adding general
valid-answer and binary QLD extraction. It was merged without conflicts.
Those results complement this continuation's exact adapter: the actual raw
decoder supplies legal Pauli support, so its coarse and genuine Pauli effects
agree exactly, with no additional malformed-answer error term.
The exact PR #188 bundle was also verified (SHA-256
`58112436bbaba2bf82089b5e1c9588c4be92b156b993fe76c9a37ed96cce1045`);
only its three new modules' 24 artifacts were installed in the working cache.

The all-index sampler, decision compiler, bounded five-level output verifier,
and the complete resource contract have passed targeted Lake builds. The raw
kernel now has checked acceptance transports in both directions, using the
explicit register numbering. The finite honest PCC construction supplies all
prefix, source-output, and Pauli-format support certificates needed by the
executable guards.

The actual QLD theorem controls `POVM.map rdPauliVec`, which sends malformed
answers to a default vector. `QLDExtractionAdapter` now proves the required
identification with genuine Pauli effects from legal support, and numbers
the ancillary spaces returned by QLD. `CanonicalDecodedStrategy` proves that
the raw type-directed decoder supplies that support. The numbered canonical
soundness theorem has checked against the actual `qld_soundness` theorem;
no extraction callback remains in that result.

## Local checking pipeline

The pinned native Lean 4.33.0 toolchain, the pinned Mathlib cache, and the
repository build cache are installed. The working `.lake` junction points
outside OneDrive to a short local cache path. `scripts/lean-local.ps1`
provides explicit cache, targeted build, check, and validation commands.
`scripts/lean-lsp-check.py` retains named Lean sessions and document snapshots
for incremental proof checks; it does not silently build missing imports.
Configuration and session state live in ignored `Scratch/` files. See
`docs/lean-local-windows.md` for reproduction and troubleshooting.

Focused builds are being run after LSP checks, with a single coordinated
Lake build at a time. Most warm proof edits check in less than a few seconds.
The generated umbrella and whole-repository validation now pass.

## Checked implementation components

- Explicit-selector game and strategy transport, preserving values, states,
  distinguished Pauli effects, PCC, and dimensions.
- The actual canonical Pauli sampler, its binary compiler, its extension to
  all introspection types, and its five-level detyping and positive-index
  polynomial sampler bound.
- Uniform Pauli answer parsing and all arithmetic branches, finite type
  dispatch, raw-answer round trips, actual raw-question decoding, and the
  full-register projection in an explicit cube-major coordinate order.
- A polynomial-time adaptive Gaussian scan that maintains a source seed
  witness. Source factor and matrix queries are proved correct only at
  attained prefixes, as required by the existing sampler contract.
- Executable initial, interior, and final hiding edges. Interior dual
  comparisons use row-space quotient membership; deterministic dual-answer
  decoding restores the legacy exact predicate. The complete typed quotient
  predicate and game have checked transport proofs.
- Question-local prefix guards and proofs that nonzero honest Hide and Read
  outcomes satisfy them. Guarded-game copying preserves honest value, PCC,
  and dimension.
- Shared-clock Sample and cross-Introspect checks, the auxiliary finite
  dispatcher, canonical auxiliary answer coding, and the program computing
  the common runtime resources before the decision kernel.
- Actual polynomial-time source-description clamps, exact preservation for
  bounded source verifiers, and the uniform compiler description-size bound,
  including the zero-parameter case.
- QLD restriction and field-to-binary extraction adapters, uniform finite
  source-game soundness, padding return, and absorption of the actual QLD
  three-term error profile using the canonical parameters.

The final completeness and soundness modules have passed targeted Lake builds.
The assembled contract has passed its standalone Lean check and transitive
axiom audit. QLD itself is supplied by upstream PR #187.

## Final scope and validation

The result supplies all fields of the existing ambient contract: actual
polynomial-time sampler and decider compilers; a five-level verifier on every
input; all-input, all-index runtime, description and answer-cutoff bounds;
perfect PCC completeness including index zero; and soundness at every positive
index with universal constants derived from the proved QLD theorem.

The separate source-model theorem for arbitrary depth and its original
absolute-time budget is not asserted by this ambient seven-level result.
Answer reduction remains an independent obligation for compression.

Final validation passed on 2026-09-23 after merging upstream `48d14e1`:

- `lake exe mk_all` regenerated the umbrella with 118 new imports; the
  subsequent `mk_all --check` passed without changes.
- The complete `lake build MIPRE` passed all 10,013 jobs. The first final
  umbrella build took 89.26 seconds; the cached validation build took 21.40.
- All final axiom guards passed. Blueprint coverage and ledger checks each
  report `PROBLEMS: 0`; `git diff --check` passes.
- The complete Windows `Validate` command passed in 32.13 seconds, including
  the corrected selection of a single executable when PATH contains more
  than one Git or explicitly named Python installation.

The local validation log is
`Scratch/lean-local-20260923-092400-294-34012-validate.log` (ignored).

The private paper repository could not be freshly accessed in this session.
The previously recorded paper reference is `MIPRE-proof@a459dee`; the checked
repository interfaces and blueprint are being used as the permitted fallback.
