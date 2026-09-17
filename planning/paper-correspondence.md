# Paper–blueprint correspondence

Current synchronization pass: 16 September 2026. Based on formalization `2c75130`
(including the H5 assembly and proved repetition) and companion paper/ledger
`d6d9b7a66042c70fc08d85168d3494c90b270535`. The bibliography entry `AuditSync26`
pins the integrated paper source at `caa9ea45ffe969294c511f9176800e7a47a0e44b`.
That paper update changes provenance notes and review records, not ledger claims.
The historical `Audit26` entry continues to
identify the September 11 report.

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
| Low-degree soundness | `thm:lidt-soundness` is the proved canonical-line theorem; `thm:lidt-cl-soundness` is the paper's seeded CL theorem. The paper's padded/simultaneous consumers use the latter. | `rem:lidt-cl-adapter`: translate games, strategies, distributions, degrees and measurements, and choose the free sampling parameter with the required error bound, or formalize the paper's tensor route directly. |
| Tensor-code transfer | Synchronous and bipartite theorem contracts are separated. `cor:sync-transfer` retains the PME premise, marginal domination, clipped losses and POVM output; the application has R=9/4. | Formalize the selected route. The alternative LIDT proof does not certify the paper's Vid21/Takagi/tensor intermediates. |
| Magic Square | Active Pauli dependencies use the direct original-observable anticommutation lemma. Full rigidity remains a stronger separate theorem. | Formalize the direct lemma and the point-observable transfer as needed; do not treat full rigidity as an active admitted input. |
| Orthonormalization | The non-strict finite-dimensional endpoint follows by a compactness limit from the strict source theorem. | Follow the precise source contract and the scope of the existing Lean declarations. |
| Halting output | Efficient sampler/decider descriptions and computable explicit game tables are distinguished. | The existing conditional Lean results remain conditional on compression; a stronger polynomial-time statement must use its proper representation and complexity convention. |
| Explicit separation | The source route uses bipartite Schmidt-rank entanglement growth and effective bounded self-reference; it is separate from the value-only assembly. | Supply those extra premises, or a separately proved value-route fixed-point construction. No commuting-completeness extension is silently required. |
| CEP | The displayed route is general bipartite correlation separation followed by the forward CEP implication. | The admitted forward Kirchberg implication remains. A synchronous-correlation witness or finite-projection-generation strengthening needs an additional argument. |

The three recorded companion imports are unchanged: the fixed-characteristic
irreducible-polynomial constructor, exact real-closed-field decision, and the
forward CEP-to-Kirchberg implication. The refined field/NPA/CEP decompositions
and the corrected halting transfer remain available. Missing fine-grained
ledger annotations are not automatically missing mathematical premises: the
anchored-repetition branch is deliberately replaced here.

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
