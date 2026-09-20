# Paper–blueprint correspondence

Current synchronization pass: 20 September 2026. Based on formalization
`43c115f968f8bf7dbb1cd31abeee9e8a4926a887` (completed QLD expansion and
state-dependent linearity) and companion paper/ledger
`a459dee4413a256107fc2d227bab298eba04051c`, also pinned by `AuditSync26`.
The source has 347 active nodes (344 validated, three admitted), five archived
nodes, 5,449 events, and no open challenges. Its 350 challenges comprise
346 resolved and four withdrawn. Natural-language validation is not a Lean
certificate. The historical `Audit26` citation still identifies the September 11 report.

This table distinguishes a matching statement from an adapter that remains to
be proved. It does not turn an informal source review into a Lean proof or an
uninhabited transformation structure into an implementation.

The source transformation displays have no Lean completion marks. The marked
`def:introspection-contract`, `def:oracularization-contract`, and
`def:answer-reduction-contract` describe the actual ambient structures. The open
`lem:introspection-supply` and `lem:answer-reduction-supply` nodes carry the
source-to-ambient obligations; `thm:compression-target` depends on them and the
checked conditional assembly. The chapter-2 normal-verifier, boundedness, and
computable-class marks likewise describe their ambient definitions, with source
comparisons separately labelled. This preserves declaration coverage without
marking an unproved equivalence as complete.

| Interface | Current correspondence | Remaining obligation |
|---|---|---|
| Compression assembly | The paper has three exterior stages; `GapCompression.ofPipeline` consumes `Introspection 7`, `AnswerReduction 5`, and `Repetition 7`. Oracularization is internal to the source proof of answer reduction. | Inhabit the remaining transformation structures. Repetition is supplied. |
| Oracularization | The source outputs a typed verifier with polynomial sampler overhead. The separate ambient Lean structure is an untyped contract. These are distinguished in `rem:oracularization-contract`. | Prove the chosen typed-to-ambient interface; generic detyping adds two levels, so the source does not directly supply the same-level structure. |
| Runtime and answer cuts | The paper's absolute index-dependent budget differs from `TimeBoundAt`'s input-size-dependent coefficient/degree budget. `rem:runtime-contract-bridge` and `rem:runtime-normalization` record the distinction. | Normalize or reprove the transformations, preserving the original answer cut, value and completeness witnesses, and propagate any polynomial reparameterization of lambda. |
| PCC completeness | Synchronous PCC and the paper's same-measurement consistency are separately defined. A value-preserving `M/Mᵀ` realization alone does not identify them. | Supply the representation bridge stated in chapter 2; any converse needed by an imported source proof is a separate obligation. |
| Low-degree soundness | The canonical-line theorem and the seeded single-codeword adapter are proved. QLD uses the latter at `(q,4m,d,1)`. | Prove `lem:lidt-ldc` for the simultaneous tuple contract required by answer reduction at `(q,m′,d,m′+6)`; the tensor route remains a separate alternative. |
| Tensor-code transfer | Synchronous and bipartite theorem contracts are separated. `cor:sync-transfer` retains the PME premise, marginal domination, clipped losses and POVM output; the application has R=9/4. | Formalize the selected route. The alternative LIDT proof does not certify the paper's Vid21/Takagi/tensor intermediates. |
| Magic Square | The direct original-observable anticommutation lemma is proved; full rigidity remains separate background. | Finish its remaining QLD consumers; do not add full rigidity as an active admitted premise. |
| Orthonormalization | Source and Lean error conventions must retain strict slack where required; finite-dimensional compactness supplies the non-strict endpoint on the source route. | Apply the precise selected theorem, including its strict parameter hypotheses, without silently identifying the two error functions. |
| Halting output | Efficient sampler/decider descriptions and computable explicit game tables are distinguished. | The existing conditional Lean results remain conditional on compression; a stronger polynomial-time statement must use its proper representation and complexity convention. |
| Explicit separation | The source route uses bipartite Schmidt-rank entanglement growth and effective bounded self-reference; it is separate from the value-only assembly. | Supply those extra premises, or a separately proved value-route fixed-point construction. No commuting-completeness extension is silently required. |
| CEP | The displayed route is general bipartite correlation separation followed by the forward CEP implication. | The admitted forward Kirchberg implication remains. A synchronous-correlation witness or finite-projection-generation strengthening needs an additional argument. |

The three recorded companion imports are unchanged: the fixed-characteristic
irreducible-polynomial constructor, exact real-closed-field decision, and the
forward CEP-to-Kirchberg implication. The refined field/NPA/CEP decompositions
and the corrected halting transfer remain available. Missing fine-grained
ledger annotations are not automatically missing mathematical premises: the
anchored-repetition branch is deliberately replaced here.

## September 20 refinements

Chapter 3 now separates the ten QLD global-measurement obligations and the
multi-codeword adapter, with explicit axis degrees, seed laws and trivial
parameter regimes. Chapter 6 separates typed construction, Pauli mixing and
the twelve answer-reduction steps plus full-seed indexing. Its completion
lemma uses `Dψ(A,C) ≤ 2δ + 4√δ`, not the false coefficient-one bound.

The new source interfaces include supplied effective field access, bounded
parsing, same-state detyping, complete-tuple polynomial measurements, timeout
truncation and the field-error-floor comparison. The compression sampler
lemma remains a checked conditional result; `lem:ar-sampler-independence`
records the newly decomposed supply premise. All added obligations are
unmarked, and existing Lean names and proof-status marks are preserved.

## Checks when either repository changes

1. Pin the companion revision being read. Consult current source statements and
   amended ledger text; an old creation event is not the current node statement.
2. Compare hypothesis, quantifier, game/strategy class, runtime/answer convention,
   parameter domain and conclusion. For a different proof route, record the actual
   adapter or keep it as a named open obligation in the dependency graph.
3. Update the statement, its comments and `uses` edges together. Keep Lean names
   attached to the result they actually establish; proof-level marks on conditional
   results do not remove their hypotheses. Check that required adapters lie on the
   appropriate supply path and that the dependency graph remains acyclic.
4. Run `python scripts/lean-coverage.py --check` and `python scripts/ledger-sync.py`.
   With a companion checkout, inspect `scripts/ledger-sync.py --ledger PATH`'s
   changed-node report before committing its refreshed snapshot. That mode writes
   the snapshot, so do not treat refreshing it as approval of the changed mathematics.
5. Review manuscript-only changes too: the ledger checker checks IDs and snapshot
   data, not theorem equivalence or every paper edit. Record the decision in this
   table and update the bibliography pin when the comparison is complete.

The public repository keeps correspondence notes and references, not copies of
the private manuscript, third-party source files, or private review packets.
