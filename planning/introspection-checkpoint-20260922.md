# Introspection checkpoint — 2026-09-22

This is the resumption point after PR #149 was merged as `e036a33`. Work is
on `codex/introspection-verifier-20260922`, tracking #115. The maintainer asked
to stop and publish the checked work because usage credits were running low.
The authoritative paper consulted is private `MIPRE-proof` at `a459dee`;
no private paper material has been copied into this repository.

## Status at this checkpoint

**Introspection is not yet complete.** Full hiding rigidity, both adaptive
iterations, terminal extraction, valid-outcome/isometric soundness adapters,
and the honest finite typed game's PCC completeness were already completed
in earlier work. This continuation closes executable and representation gaps;
it does not construct an inhabitant of `MIPRE.Introspection 7`.

The new checked components are:

- `BasisProg`, `BinaryBlockProg`, and `Background/QLD/BinaryBlocks`: actual
  uniform conversion between canonical Shoup bits and the effective self-dual
  basis, in both directions; row splitting/flattening; exact agreement with
  `binaryVectorEquiv` and its explicit coordinate numbering. No basis oracle
  or equality of the computational and self-dual bases is assumed.
- `PauliStageProg`, `PauliRowsProg`, and their Background bridges: actual
  uniform marginal and linear-query programs for all Pauli types. The
  `linear_correct` and `linearBits_correct` theorems hold on arbitrary
  prefixes, not just attained prefixes. Diagonal stages use the prefix
  direction without selecting it a second time. Zero directions are covered.
- `PauliFactorProg` and `PauliFactorPrograms`: fixed-register factor masks,
  with exact downsized/reindexed semantics for arbitrary prefixes and bases.
- `TypeEncoding` and `SamplerQueryProgram`: faithful labels for the fixed
  twenty-six types and an actual total query router. Parameters are still
  supplied explicitly as `(unary k, unary j, unary m)`. The router is **not
  yet packaged as the index-dependent `CL.TypedSampler 3 QLD.Ty`**.
- `AuxiliaryReadProgram`: full-register Read checks and their exact parsed
  semantics, including original-answer cutoffs. Dual labels may use padded
  coordinates.
- `AuxiliarySamplingProgram`, `AuxiliaryRegisterBits`, and
  `AuxiliarySamplingCorrect`: actual clocked source marginal invocation at
  index `2^n`, total raw parsing, timeout rejection and runtime; exact
  `samplingProg_depthFamily` correctness for same-depth source padding.
  Its explicit hypotheses include bounded source verifier, positive depth
  and index, source dimension at most Q, `Nat.size ell <= (2^n)^lambda`,
  `4 <= Q`, and `3*R <= Q`. Both ordinary answers remain bounded by R.
- `AuxiliaryCanonicalProgram.canonicalProg_correct`: actual polynomial-time
  binary elimination computes **the exact `CL.canonLin`** of the supplied
  row span, not merely an arbitrary quotient representative.
- `CLExplicitTransport`: actual field/binary output equivalences intertwine
  the explicit-selector and legacy Pauli presentations and their decoded
  questions. The higher-level full-game/strategy transport is not checked.

Two unvalidated transport drafts are preserved in
`planning/introspection-wip/ExplicitGame.lean.txt` and
`planning/introspection-wip/ExplicitStrategy.lean.txt`, outside the Lean
library and umbrella. They are not proved results. The final local run was
stopped at the maintainer's usage limit before a clean result. Earlier
diagnostics included expensive definitional reductions in `toLegacy_state`,
`toLegacy_pauli_A/B`, and `pccToExplicit_dimension`; the final bounded rerun
had raised local heartbeats but did not finish. Local logs remain at
`Scratch/explicit-game-check.log` and `Scratch/explicit-check.log`.

## Next work, in dependency order

First finish and check the two preserved full-game transport drafts. They
are intended to preserve value, state, dimensions, distinguished Pauli
effects and PCC completeness, and to compose the concrete selector with
QLD restriction. Only the underlying `CLExplicitTransport` equivalences
have passed Lean; do not mark the higher-level statements proved yet.

1. **Package the actual sampler.** Consume `SamplerProgram.query`,
   `linearBits_correct`, `marginalBits_correct`, and `factorBits_correct`.
   Adapt raw full-length vectors using `CL.toBits_ofBits` and
   `binaryVectorEquiv.symm`; attach canonical index-dependent parameters and
   construct `CL.TypedSampler 3 QLD.Ty`. Existing
   `Introspection.typedSampler` and `detypedSampler` then extend to all
   introspection types and five levels. Reuse `SourceCompilerParams` and
   `SourceCompilerParamsCost`; prove the selector-width inequality, odd
   field degree, and uniform parameter/runtime bounds. No new field or line
   algorithm is needed.
2. **Finish executable hiding.** Instantiate `canonicalProg_correct` with
   row span equal to `perp (ker L)` to compute `CL.lperp`; collect stage
   matrices by legal sampler queries. The source sampler promises factor
   and map correctness only at attained prefixes, whereas `TypedPredicate`
   evaluates arbitrary claimed prefixes. Do not silently strengthen that
   contract. A possible resolution is an adaptive solvability scan that
   maintains a genuine seed witness, rejects unattainable prefixes, and
   proves acceptance implies the existing predicate while preserving honest
   completeness. The full-register Read and Sample branches are already
   supplied; their hypotheses must be discharged by canonical parameters.
3. **Implement the Pauli decider.** `QLD.Game.accepts` is a finite semantic
   predicate, not an ambient program. A repository audit found no complete
   encoded Pauli-answer parser/decider. Needed work includes line-polynomial
   evaluation, multilinear `ldEnc` evaluation of a full Pauli answer, trace
   probes/gamma, finite Magic Square checks, and dispatch. Reuse existing
   `SAT.FieldTrace.shoupTraceProg` and `SAT.TraceGram.shoupTraceBitProg`;
   trace arithmetic itself is already executable. The unfinished trace
   subtest draft is only scratch work and is not a proved component.
4. **Assemble the bounded verifier.** Combine Pauli, Read, Sample, Hide and
   existing cross-Introspect source checks, enforce one consistent answer
   format/cutoff, detype, and prove compiler size/construction cost and the
   single `Verifier.Within` budget. Connect the actual executable game to
   the checked finite-game completeness and soundness results.
5. **Supply actual QLD extraction.** Upstream had not advanced beyond PR
   #147 at the start of this continuation. At publication, PR #150 is open
   for stage 4c (separation, completion, marginals, and simultaneous
   extraction); check its current state before continuing or duplicating
   that work. The local isometries, unsquared
   state-distance estimate and valid-answer Alice-X/Bob-Z estimates are
   still supplied inputs to `ValidPauliSoundness`; their existence is not
   proved by introspection. Once available, compose with the explicit-game
   restriction and padding value return, and only then inhabit
   `Introspection 7` and mark `thm:introspection` proved.

   **Update 2026-09-23: the extraction is supplied.** `thm:qld` is proved (#187), and
   `Background/Introspection/PauliExtraction.lean` proves the existence of exactly these inputs:
   `exists_binary_extraction` gives the isometries, the unit `ξ`, `hstate`, `hX` and `hZ` (and
   the other two Pauli estimates) for any projective strategy of `BinaryComplete.game` with a
   self-dual basis, at `T = ε + 2 errShape a b (N ε) m d q + 8/q`, and
   `exists_quantumValue_ge_of_binary` composes them with `ValidPauliSoundness`. The field-register
   game has the same pair. No malformed-mass premise is used (`QLD/ValidAnswers.lean`). What is left
   of this item is the composition with the explicit-game restriction and the source padding: the
   corollaries assume the original CL functions are exact on the whole register.

## Validation and local resumption

New modules are checked with Lean 4.33.0 in dependency order and headline
declarations are guarded against `sorryAx`. The PR also updates the blueprint,
axiom guards, generated umbrella, coverage and ledger checks. Full repository
CI is separate from the focused local checks; consult the PR check status.

Local cached checker (Windows/WSL):
`Scratch/check-campaign-linux.sh`, using
`/home/vidick/.cache/codex-mipre-check-20260920`.
`Scratch/run-mk-all-linux.sh` runs the real umbrella generator. These are
ignored local helpers, not prerequisites for other environments. Avoid
`lake clean`, `lake update`, or rebuilding Mathlib. The pre-existing stash
of unrelated Shoup planning edits has been preserved and must not be popped
automatically. Resume from the PR branch, or from updated main after merge.
