# Classical PCP, then introspection

Started 20 September 2026 at the maintainer's request. Complete the effective classical
PCP campaign first, then construct `Introspection 7` using the Pauli-test theorem being
developed independently. The QLD campaign's files are outside this implementation track.

Baseline: formalization `43c115f`; manuscript `vidick/MIPRE-proof@a459dee`.
The paper's `answer_reduction.tex`, especially the padded succinct description,
zero-basis proposition and `thm:pcp-decider`, and `preliminaries.tex`'s effective-basis
construction are the mathematical sources. The manuscript
and its private audit material remain outside this repository.

**Current status:** the classical campaign is complete. The repository now has an
actual `MIPRE.TM.CookLevin.Pad.classicalPcpDecider` and the complete effective
self-dual normal-basis and multiplication-table constructor. Both have passed
native Lean builds. The separate [Shoup campaign](shoup-axiom-removal.md) now
proves their former irreducible-polynomial assumption. Introspection is in
progress, with checked Pauli mixing in question-dependent coordinate presentations,
conditioning identities, and the semantic two-level graph sampler used by detyping.
There is still no inhabitant of `Introspection 7`.

The dated implementation notes below record the assumptions present at each earlier
checkpoint. Their references to the Shoup axiom are historical; current public guards
track the proved construction.

## Completion criteria

1. An actual inhabitant of `PcpDecider`, with honest polynomial bounds on parameter
   computation and verification, completeness and soundness against the stated
   low-degree proofs. No new axiom or `sorry` discharges any of these obligations.
2. The effective field and self-dual-normal-basis construction, with the polynomial
   bound in the extension degree. The separate Shoup campaign strengthens the original
   criterion by proving its formerly declared irreducible-polynomial assumption.
   Abstract field/basis existence is not this algorithm.
3. After the classical campaign: an actual `Introspection 7`, including its sampler,
   decider, PCC completeness, bipartite soundness and ambient resource budgets.
   The completed Pauli-test theorem is a dependency, not an additional admitted axiom.

Constructing `AnswerReduction 5` is a separate campaign. Supplying introspection alone
does not remove the final compression hypothesis.

## Classical construction

Work through the entire construction, with infrastructure included in its deliverables:

* **Interfaces and polynomial arithmetic.** Restrict `PcpDecider.fld` to admissible odd
  degrees. Prove the Boolean-cube zero-basis theorem with individual-degree bounds and
  the formula/circuit arithmetization lemmas. The classical PCP has no dependency on
  `thm:qld`; its input proof is assumed to consist of low-degree polynomials.
* **Effective fields.** Represent `F_2[T]/(f)` by coefficient bits using Shoup's
  irreducible polynomial; give and verify the required ambient programs. Supply a
  constructive normal element, trace/Gram computation, self-dualization and coordinate
  transport with polynomial cost in the unary extension degree.
* **Padded describer.** Consume `decoupledDescriber`, align all five blocks, enforce the
  two power-of-two variable counts and exact gate count, and prove the resulting circuit
  still describes precisely the accepting answer prefixes.
* **PCP.** Construct the formula and zero-basis tests, prove completeness and quantitative
  soundness, implement their verifier and parameter computation, and assemble the
  inhabitant with blueprint proofs and axiom guards.

## Interface checks to resolve while constructing

The existing `Circuit.WellFormed` bounds the fan-out of gate nodes but does not bound
how often an external input bit is read by distinct `.input` gates. The source's
individual-degree-six argument counts occurrences of input wires too. The padded
describer/arithmetization construction must supply the missing input-use control; it
must not infer that control from the current well-formedness predicate.

The existing self-dualization mathematics identifies squaring on the group algebra
with squaring coefficients and doubling indices. In the binary cyclic case, the square
root is computed by reading coefficient `g + g` at output position `g`. This direct
construction is now implemented and checked. Inversion and the normal-element
construction are also complete; their algorithms and verification are recorded below.

## Introspection after the PCP

Before inhabiting the existing contract, repair its zero-index soundness clause.
`Introspection.delta a b lam 0 eps` is zero in Lean when `a, b > 0`, including its
negative-exponent term, because `Real.zero_rpow` is zero for every nonzero exponent.
The current soundness clause quantifies over all natural `n` and all positive `eps`.
At `n = 0`, choosing `eps` large enough to make the premise automatic would therefore
force every bounded input verifier to have value one at index one. This is not the
intended theorem. The input's `IsBounded` hypothesis itself only supplies time bounds
at indices at least two. Restricting the introspection soundness clause to `1 ≤ n`
matches that requirement (`2 ≤ 2^n`), and its compression consumer already uses
`2 ≤ n`. Check this repair against the paper's indexing convention and record it in
the blueprint when implementing this phase; do not use an inhabitant of the current
zero-index clause as an assumed theorem. This issue is independent of `thm:qld`.

Read the final `thm:qld` interface supplied by the parallel campaign. Construct the
typed introspective sampler and decider, normalize them into the ambient verifier
model, prove resource bounds and answer rejection, and then prove completeness and
soundness. Keep the source-to-ambient runtime and PCC bridges explicit. Finish by
assembling `Introspection 7` and checking it with the existing compression consumer.

## Verification and progress

Use targeted Lean builds while developing; run the full library and the two blueprint
checkers for a finished deliverable. New modules must appear in `MIPRE.lean`. Proof-level
completion marks and guards are added together. Conditional lemmas are labelled with
their hypotheses; they do not count as an inhabited final contract.

* Field-domain repair implemented and checked: `PcpDecider.fld` now takes an oddness
  proof, so it cannot demand a field of cardinality one at degree zero.
* Removed the erroneous Pauli-test dependency from the classical PCP blueprint nodes.
* `LowDegree/ZeroBasis.lean`: individual-degree-preserving division and Boolean-cube
  zero certificates, fully proved.
* `SAT/Arithmetization.lean`: Boolean evaluation correctness and the occurrence-count
  degree bound. This does not supply a bounded-occurrence circuit normalization.
* `SAT/PcpAlgebra.lean` and `SAT/PcpBlocks.lean`: the two polynomial tests, the majority
  argument, disjoint answer blocks, the honest degree-seven `PcpProof`, and satisfying
  decoded Boolean clauses. These theorems explicitly require a degree-six Boolean
  clause-description polynomial and its satisfying assignments. They do not assume
  that the current circuit interface already supplies those hypotheses.
* `LowDegree/BinarySquareRoot.lean`: the actual uniform coefficient-permutation program,
  correctness in the odd-order binary cyclic group algebra, and polynomial time in
  vector length. This discharges the square-root operation, not inverse Gram computation.
* `LowDegree/BinaryPolynomial.lean` and `SAT/QuotientField.lean`: canonical polynomial-basis
  fields, uniform XOR and modular multiplication, normalization of Shoup's output,
  `shoupAdmissibleField`, and correctness and polynomial-in-degree runtime of
  `shoupMulProg`, including construction of its modulus. The Shoup-based declarations
  use only the already-declared Shoup axiom beyond Lean's standard axioms.
* All these source modules passed direct Lean checks with the repository options and
  pinned Lean 4.33.0, and the normal targeted Lake build passed (3,092 jobs). All 42 new
  headline declarations passed their `#guard_sorry_free` checks. The PCP and square-root
  results use only the standard axioms; the Shoup multiplication correctness and runtime
  results add exactly `MIPRE.LowDegree.exists_shoup_irreducible`.
* `lake exe mk_all` regenerated the root imports. Both structural blueprint checks
  (`lean-coverage.py --check` and `ledger-sync.py`) report zero problems. The full
  library build is the final verification pass for this implementation checkpoint.
* The padded-describer construction is now implemented through exact gate count.
  `SAT/Padding.lean` proves complete blank-tail semantics; `SAT/ArrayProg.lean`,
  `SAT/Rename.lean`, and `SAT/PowerPadding.lean` supply safe binary indexing,
  formula renaming, and capped unary power rounding. `CookLevin/Padded.lean`
  consumes the existing decoupled describer and aligns all five blocks.
  `SAT/GatePadding.lean` appends copying OR gates while preserving fan-out two
  and the last-gate output convention. `CookLevin/ExactPadding.lean` gives exactly
  `s` gates and exactly `5*m+5+s` variables, a power of two, with all semantic
  equivalences and polynomial dimension bounds proved.
* `Cost/BinaryArithmetic.lean` verifies binary normalization, predecessor, and
  addition/subtraction of unary offsets. `CookLevin/PaddingParams.lean` computes
  `(m,s)` in polynomial time in the binary parameter lengths. These nine new
  modules passed direct Lean checks with the repository options.
  All 34 headline declarations for this padding checkpoint passed their axiom
  guards. The exact-size semantics, exact variable count, and parameter program
  depend only on Lean's standard axioms. Both blueprint checks still report zero
  problems. The normal targeted Lake build passed (3,611 jobs).
* **Output-budget distinction:** printing `s` gates is polynomial in the values
  of `Q` and `sigma`, not necessarily their binary lengths. `describeExact`
  therefore takes a unary output budget; on a budget of length `s` it has the
  precise required size. The PCP view must supply this budget after its format
  check. Parameter computation remains binary and needs no such budget. This
  follows the two different runtime claims of the paper's padded-describer
  proposition rather than assuming an impossible globally polynomial printer.
* `SAT/InputRouting.lean`, `SAT/CircuitArithmetization.lean`, and
  `SAT/FiniteCircuitArithmetization.lean` now supply the missing circuit polynomial.
  A repeated input read is linked to its preceding input gate, without introducing
  variables. The routing preserves every Boolean gate value and bounds each variable
  to one copy link. In characteristic two, the consistency indicator `1+w+rhs`
  yields individual degree at most five, sufficient for the PCP's degree-six bound.
  `LowDegree/FiniteVariables.lean` restricts to exactly `n+s` coordinates while
  preserving degree and evaluation. Boolean-valuedness and the exact acceptance
  equivalence are proved. All 11 headline guards passed; the main results use only
  standard axioms. The field evaluator and the link to the five clause blocks remain.
* The earlier full-library checkpoint passed (9,468 jobs). The circuit-polynomial
  and PCP-parameter modules also passed their normal targeted Lake build (3,618 jobs).
* `CookLevin/PcpParameters.lean` supplies the actual `pcpParamsProg`, with odd
  `k = 2*Nat.size m' + 7`, field size at least `82*m'`, and both dimensions
  dividing the field size. All six headline declarations passed direct Lean and
  axiom-guard checks, using only standard axioms. This is the classical majority
  requirement; the later low-degree-test consumer has a stronger field-size choice.
* `SAT/GateProg.lean`, `SAT/InputRoutingProg.lean`, `SAT/GateFieldEval.lean`,
  `SAT/CircuitFieldEval.lean`, and `SAT/CircuitFieldCorrect.lean` implement the complete
  uniform coefficient-vector circuit evaluator. It scans preceding input copies,
  dispatches all five gate constructors, and directly multiplies the consistency
  factors and output coordinate. Its global polynomial bound holds on malformed
  inputs too. Correctness is proved for arbitrary field points, both for the routed
  polynomial and its exact finite coordinate restriction. All five modules passed
  direct Lean checks. All twelve headline guards passed. The evaluator and its
  semantic correctness use only Lean's standard axioms; the Shoup representation
  additionally uses exactly the existing irreducible-polynomial axiom. The Shoup
  field now exposes its unchanged quotient carrier directly, with characteristic
  two and canonical coefficient decoding proved. Both blueprint checks report zero
  problems. The normal targeted native build passed (3,073 jobs).
* `CookLevin/PcpClauses.lean` identifies the five PCP blocks with the actual
  little-endian clause format, with both encoding round trips. `PcpCircuit.lean`
  now proves typed PCP completeness and majority soundness against the concrete
  circuit polynomial, and against `Circuit.DescribesDecider`, recovering actual
  accepted prefixes and both full decoded answer tapes. `PcpViewSize.lean` bounds
  the entire formatted input in `Nat.size n + Nat.size T + Q + sigma` and proves
  that every ambient polynomial-time PCP program has the required source runtime
  bound on these inputs. All three modules and all fifteen headline axiom guards
  passed direct Lean checks, using only Lean's standard axioms. Their normal
  targeted native Lake build also passed (3,649 jobs).
* `CookLevin/ClassicalPcp.lean` now assembles `classicalPcpDecider`, including
  executable specification/format rejection, the raw field tests, polynomial runtime,
  completeness, and strict-majority soundness recovering both full answer tapes.
  The assembled inhabitant passed the pinned Lean checker. The construction uses the
  canonical Shoup polynomial basis. Effective self-dual normal basis construction is
  still open, so the whole requested step 2 is not yet complete. Introspection has not
  begun; the independent QLD work remains untouched.
* The complete classical PCP passed its normal native Lake build (3,668 jobs).
  All 19 new assembly/bridge guards passed. The final inhabitant's axiom audit is
  exactly `propext`, `Classical.choice`, `Quot.sound`, and the existing Shoup axiom.
  Both structural blueprint checks reported zero problems.
* `LowDegree/BinaryPower.lean`, `BinaryInverse.lean`, `BinaryTrace.lean`, and
  `SAT/FieldTrace.lean` implement uniform field exponentiation, nonzero inversion,
  Frobenius iteration and algebraic trace. Each passed the pinned Lean checker;
  the source runtime bounds for inversion and trace are polynomial in unary degree.
  These are element operations, not yet the normal-element algorithm.
  All 13 new field-operation guards passed. The normal native build for these and
  the first matrix modules passed (3,102 jobs); both blueprint checks reported zero
  problems after their addition.
* Eight `LowDegree/Binary*.lean` modules now provide binary matrix arithmetic,
  triangular elimination with coefficient certificates, a basis-building program,
  consistent-system solving and square-matrix inversion. The basis is proved
  independent and to span exactly the input family. Matrix inversion returns
  canonical coordinates and satisfies both multiplication identities. All eight
  modules and all 25 headline axiom guards passed the pinned Lean checker, using only
  standard axioms. `BinaryKernel.lean` additionally supplies a polynomial-time kernel
  generator program: a proved linear projection onto the kernel is applied to the
  standard basis. The kernel module also passed the pinned checker. The field-matrix
  applications are recorded below; the initial normal element remains open.

* `SAT/FieldCoordinates.lean`, `FrobeniusMatrix.lean`, `TraceGram.lean`, and
  `BasisTransport.lean` passed the pinned Lean checker. Canonical bit vectors form a
  binary linear equivalence; a uniform program constructs Frobenius, whose minimal
  polynomial is proved to be `X^k-1` and squarefree for odd `k`. Uniform programs also
  compute trace Gram matrices and their inverses, exact coordinates in any supplied
  basis, and all multiplication-table bits with a source polynomial bound in `k`.
  All 22 headline guards passed, with no axioms beyond the standard three and Shoup.
  Both structural blueprint checks reported zero problems.
* The five kernel guards passed with only standard axioms. The native integration
  build through binary matrix inversion passed its new module jobs, but its final
  Axioms job saw an import added while it was running and failed on a missing
  `BinaryKernel.olean`. After regenerating the module list, the native integration
  build passed all 3,931 jobs, including every current axiom guard.

* `Cost/Iterates.lean`, `LowDegree/BinaryCirculant{,Prog}.lean`, `SAT/NormalGram.lean`,
  and `SAT/EffectiveSelfDual.lean` passed the pinned checker. The complete
  `shoupSelfDualizeProg` computes the inverse Gram square root and applies it to a
  supplied normal basis. Its exact output forms an actual basis proved self-dual and
  normal; its source runtime is polynomial in `k`.
* **Normal-element implementation route (now implemented):** use the paper's binary
  fixed-subspace separation directly in the cyclic group algebra. Splitting by its
  fixed idempotents can produce the CRT projections without printing polynomial
  factors or running polynomial gcd. The correctness proof establishes that the
  resulting nonzero components are primitive, and that selecting the first nonzero
  polynomial-basis image in each component yields a normal element. Faithfulness
  follows from independence of the Frobenius automorphisms. No abstract normal-basis
  choice or enumeration of fixed-space elements enters the executable program.

* The 18 self-dualization guards passed, and the native integration build passed
  all 3,937 jobs. The subsequent normal-element construction uses primitive fixed-space
  projections and independence of Frobenius automorphisms. `SAT/EffectiveNormalBasis.lean`
  now composes the full unary-degree basis and multiplication-table algorithm; its
  correctness and polynomial runtime are proved by `effective_selfDualNormalBasis`.
  No normal-element choice or enumeration of the field enters the executable program.

## Remaining implementation sequence

1. The final 26 normal-basis guards passed (248 campaign guards total), and both
   blueprint checks report zero problems. The exact axiom list of
   `effective_selfDualNormalBasis` is `propext`, `Classical.choice`, `Quot.sound`,
   and the pre-existing `MIPRE.LowDegree.exists_shoup_irreducible`. Native integration
   of the complete basis constructor passed all 3,429 jobs. The classical campaign now supplies both `classicalPcpDecider` and
   the complete effective self-dual normal-basis constructor.
2. Proceed to introspection as described above, consuming `thm:qld` as the dependency
   supplied by the separate campaign. The concrete verifier and its proofs remain open.

## Introspection implementation checkpoint

The soundness contract now requires `1 ≤ n`; `delta_zero_index` records why the
zero-index version is unsuitable, and `two_le_exp_index_iff` connects this condition
to the original verifier's bounded range. The compression consumer passes its
existing `2 ≤ n` hypothesis. The paper's overview explicitly sets `n ≥ 1`, although
the later theorem display says all naturals; the blueprint records the distinction.

The first substantive proof module is `Introspection/LinearMeasurement.lean`:
Fourier expansion and inversion for a coarse-grained linear-map measurement over
any finite characteristic-two field. It passed the pinned checker, as did
`Commutation.lean` (the sampling/hiding criterion), `Twirl.lean` (both exact Pauli
twirls), and `Measurements.lean` (projective single and joint readouts).
`BlockTwirl.lean` and `BlockPOVM.lean` now prove the full ancillary block
decomposition and construct the resulting POVMs, specializing the paper's
`lem:mixing-L` to characteristic two. `TwirlDistance.lean` proves `lem:mixing-U`
with constant one, arbitrary state vectors, and explicit outcome sums and question
averages. All 21 introspection headline guards passed, using only standard axioms
(269 guards for this campaign including the classical construction). The native
integration build through the first 13 introspection guards passed all 3,951 jobs;
the last eight guards also passed the direct pinned checker. The compression
consumer checked successfully with the new positive-index hypothesis.

The next substantial deliverables remain:

1. The commutator Parseval identity, two-sided commutation estimate and
   retained-fibre mixing theorem in tensor coordinate presentations are now proved.
   Transport the ambient CL register subspaces into those presentations.
2. Construct the typed introspective sampler and decider and their detyping, with
   actual ambient programs. Resolve the documented runtime normalization before
   claiming the existing budget: input-size degree `lambda` and answer length
   `N^lambda` can introduce a quadratic exponent in `lambda`. Any polynomial
   reparameterization must propagate through the compression interfaces.
3. Supply the PCC representation bridge and prove completeness. Apply the
   completed QLD theorem, prove the soundness induction, and assemble
   `Introspection 7` against the compression consumer.

The runtime and PCC bridges remain explicit obligations already recorded in the
blueprint. Completing QLD alone does not discharge them, and none is replaced by
a new axiom here.

## Final checkpoint validation, 20 September 2026

The full native `lake build` passed all **9,540 jobs**, including `MIPRE.Axioms`
and the root `MIPRE` module. Every new headline declaration passed its axiom
guard. `scripts/lean-coverage.py --check` and `scripts/ledger-sync.py` both
reported **zero problems**, and `git diff --check` passed. The generated root
module includes all new files. No new axiom or admitted proof was introduced.

The classical campaign is complete. The introspection checkpoint consists of
the positive-index contract repair and the seven proved modules under
`MIPRE/Foundations/Introspection/`; the final transformation remains open as
described above.

## Continuation after merging PR #127

The previous checkpoint was pushed, passed CI and merged as `82726d6` in PR #127.
This continuation starts from that main commit, including the QLD distributional
inputs merged in PR #128. The paper snapshot is still `a459dee`. The upstream
QLD campaign has advanced, but `thm:qld` is not yet an assembled theorem.

Thirteen further modules have passed the pinned Lean checker:

* `CommutatorParseval` proves the exact readout/observable identity, including
  outcome sums and question averages.
* `TwoSidedCommutation` and `ComposedTwirl` give explicit coefficients `4,4,8`
  for two commutators and a mirror error, and the resulting composed twirl bound.
* `SubmeasurementCompletion`, `RetainedFibre`, and `BlockRetention` retain a
  matching fibre and complete it to actual ancillary POVMs, with bound
  `2 delta + 4 sqrt(delta)`. No outcome-count factor is introduced.
* `EPR` and `PauliTwirlDistance` establish the exact mirrors and transfer the
  readout hypotheses into the twirl estimate.
* `PauliMixing` and `VaryingPauliMixing` assemble the result for fixed or
  question-dependent register dimensions and ancillary spaces. With each of the
  three averaged input errors at most `eps <= 1`, the output distance is at most
  `56 sqrt(eps)`. The source's ambient coordinate embeddings remain to be supplied;
  the blueprint therefore gives this proved core its own node.
* `Conditioning` gives exact conditional squared-norm and commutator identities
  with varying tensor decompositions. `ConditionalConsistency` proves the
  agreement-to-conditioned-measurement bound with coefficient two.
* `CL/Graph` constructs the semantic two-level graph sampler. Its factors partition
  all four binary blocks. Valid seeds are in bijection with ordered graph edges,
  including loops; their probability is exactly `|ordered edges| / 16^|types|`.
  Conditioning gives the uniform ordered-edge law. Each rejected seed gives at
  least one player an invalid local view and a zero opposite-neighbor block.
  This is not yet the ambient sampler program of `lem:detype-sampler`.

The blueprint has 51 matching new headline axiom guards. No new axiom or admitted
proof was used. Repository-wide integration and structural checks are the final
validation for this continuation.

The remaining construction still includes typed sampler/decider programs and their
detyping, runtime normalization through the compression interfaces, PCC completeness,
the QLD extraction, and the sampling/hiding induction. Assuming a completed QLD
theorem discharges only the QLD dependency. It does not supply those other proofs.

## Detyping continuation after PR #131

PR #131 passed the full 9,564-job build and was merged as `73e4e96` on
20 September 2026. This continuation also includes PR #132 (`ae2a13e`),
the QLD padded-line consistency bound. The source paper remains pinned to
`a459dee`; the detyping definitions and proof in `paper/types.tex` were read
before implementation.

The new construction comprises seven modules:

* `CL/Embedding.lean` extends CL presentations along coordinate injections,
  preserving exactness, evaluation, marginals, factors, and linear queries.
* `CL/Detyping.lean` constructs the actual `ell + 2` presentation on the
  graph-plus-content register. Rejected graph views select a zero presentation
  that consumes the entire content register at the first content level.
* `CL/DetypingLaw.lean` identifies valid local views and proves the full joint
  conditional law: a uniform ordered edge and one shared content seed. It does
  not replace the two correlated outputs by independent samples.
* `CL/DetypingQueries.lean` proves every branch of the sampler's query dispatch:
  two graph levels, then selected typed marginal/factor/linear queries. Factor
  and linear identities hold even for prefixes outside the sampler's image.
* `SampledGame.lean` supplies finite games with arbitrary uniform sample spaces
  and the corresponding expectation and failure identities.
* `CL/DetypingGame.lean` constructs the finite typed and detyped games, proves
  that the latter uses the constructed CL distribution, and defines the
  same-state restriction to fixed graph views.
* `CL/DetypingSoundness.lean` identifies restricted failure with conditional
  detyped failure and proves the explicit factor `16 ^ card T`.

This closes `lem:detype-cl` for positive levels, including the three-level
typed introspective sampler. Separate proved blueprint nodes record the query
identities and finite-game soundness. The 44 matching headline guards check
the construction as well as its proofs. The finite games use the same answer
alphabets; no machine-level answer cutoff, truncation, or runtime is assumed
by a newly introduced contract.

Next construction work is to compile these query branches into the ambient
sampler and decider wrappers and prove their malformed-input and time bounds.
The existing pipeline runtime normalization issue, PCC representation and
completeness, ambient-register mixing transport, and sampling/hiding induction
remain open. In particular this continuation does not inhabit `Introspection 7`.

Validation: all seven new modules and all 44 headline guards passed the pinned
Lean 4.33.0 checker. The presentation exactness, linear-query dispatch, and
same-state failure bound have exactly the standard axioms `propext`,
`Classical.choice`, and `Quot.sound`. Root imports were regenerated with
`lake exe mk_all`; blueprint coverage and ledger correspondence both report
zero problems. Repository-wide CI is the final integration check.
