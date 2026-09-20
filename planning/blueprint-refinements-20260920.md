# Blueprint refinements — 20 September 2026

Applied the corrections from the comparison of formalization
`43c115f968f8bf7dbb1cd31abeee9e8a4926a887` with companion proof
`a459dee4413a256107fc2d227bab298eba04051c`. These changes refine statements
and formalization obligations; they add no Lean proof claims.

## Changes

- Corrected submeasurement completion to `Dψ(A,C) ≤ 2δ + 4√δ` and separated
  the exact twirl, commutator transfer, unitary mixing and completion steps.
- Added axis-degree and conditional-distribution contracts for QLD, then
  separated its ten global-measurement obligations. The active route uses
  the proved single-codeword seeded theorem.
- Separated the multi-codeword adapter, extraction and error absorption
  required by answer reduction; added the low-degree test's full answer
  parsing and effective-construction costs.
- Added eleven typed-verifier interfaces, including supplied effective field
  access, bounded-prefix parsing, graph weights, detyping failure loss,
  same-state soundness and PCC completeness.
- Decomposed answer reduction into its twelve current source steps and the
  full-seed indexing obligation. Added sandwich, effective oracle and timeout
  support, and retained the complete-tuple projectivity, alphabet alignment,
  original answer cutoff, field-error floor and final exponent losses.
- Updated the source pin, event-derived ledger snapshot, correspondence and
  work plans. Historical audit provenance remains identified as historical.

## Verification and scope

- Exact-string edit preparation checks each anchor occurs once; application
  preserves unrelated current edits and checks every input file for concurrent
  changes before writing.
- `scripts/lean-coverage.py --check`: zero problems, with all existing Lean
  names and proof-status marks retained (454 proof-level declarations guarded).
- `scripts/ledger-sync.py`: zero problems against the refreshed snapshot:
  5,449 events, 347 active nodes, five archived. Explicit annotations cover
  200 active nodes, including all 28 answer-reduction nodes. Annotation
  coverage measures correspondence, not machine-checked proofs.
- Dependency check: no new cycles among statement/proof `uses` edges.
- PDF compilation could not start: local MiKTeX reports that installation
  setup is unfinished. References, environments and command definitions were
  checked by the repository's structural checker.

No Lean source or axiom guard was changed by this correction pass. Existing
PCP work in the checkout was preserved. A Lean build was not run for these
documentation-only changes. The new blueprint obligations remain unformalized.
