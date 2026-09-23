# Tsirelson's problem: implementation plan

Written 2026-09-23. Status: proposed implementation campaign; no new Lean proofs
are claimed by this document. The target is the negative answer to Tsirelson's
problem, `Cqa ⊊ Cqc`, in a finite bipartite scenario.

## 1. Scope, provenance, and current position

The first delivery is **existence of a separating correlation**, through the
halting reduction. The paper's particular explicit separating game, its
`quantumValue ≤ 1/2` versus `commutingOperatorValue = 1` gap, Connes embedding,
and QWEP are separate campaigns. The classical CHSH Tsirelson bound is also a
different target.

This plan was checked against:

- MIPRE local checkout `f71d43e` (introspection, PR #193) and upstream main
  `867f4e2` (answer reduction AR-1, PR #199) for the interface audit. The
  intervening PR #197 supplies the compression pipeline from a single
  `AnswerReduction 5` hypothesis. At publication, upstream main is `c74b451`:
  PR #200, answer reduction AR-2a, has also merged.
- [Chapter 8](../blueprint/src/content/08_downstream.tex), especially
  `thm:npa-convergence`, `lem:valco-upper-re`, and `cor:tsirelson`.
- Companion `vidick/MIPRE-proof` at
  `a459dee4413a256107fc2d227bab298eba04051c`: `paper/recursive.tex`, and the
  September 13 `frontier-npa-proposal.md`, `frontier-npa-independent-review.md`,
  and `frontier-npa-specs.json` under `proofs/mipre-undecidability/reviews/`.
  Those are mathematical source/review records, not Lean certificates. Private
  source text is not copied here.
- The public NPA source, [arXiv:0803.4290v1](https://arxiv.org/abs/0803.4290v1),
  especially Theorem 8, Corollary 9, and Appendix B.
- Both upstream branches of `vidick/commuting-repetition`, including development
  head `24a88239e55a3448074c061fbdac1abc347df23d`, and the local vendored tree.
  No Lean NPA hierarchy/convergence development was found. Lin's tracial density
  theorem and substantial operator infrastructure are present.
- Lean 4.33.0 and the pinned Mathlib revision
  `db584cd6d46c92f209a44c0f1c829460d327499d`.

Refresh the upstream status before starting implementation. Work can proceed
while answer reduction is being completed: the final integration theorem will
carry that hypothesis explicitly until its actual inhabitant is available.

## 2. Exact targets and the shortest consumer

Use ordinary bipartite correlations on finite nonempty alphabets `X,Y,A,B`,
with no synchrony constraint on correlations. Define `Cq` using arbitrary
finite-dimensional tensor-product strategies, `Cqa := closure Cq` in the usual
finite product topology, and `Cqc` using the existing
`MIPRE.CommutingOperatorStrategy`. Keep the existing projective convention for
finite tensor strategies, with a correlation-preserving POVM dilation bridge
to justify the standard interpretation.

The final theorem should supply natural numbers `nx,ny,na,nb` with

```text
Cqa (Fin (nx+1)) (Fin (ny+1)) (Fin (na+1)) (Fin (nb+1))
  ⊊
Cqc (Fin (nx+1)) (Fin (ny+1)) (Fin (na+1)) (Fin (nb+1)).
```

The construction through `GameData` actually supplies common question and
answer alphabets (`nx = ny`, `na = nb`). That does not make its separating
correlation synchronous or tracial. State the stronger common-alphabet witness
if it comes for free, and derive the displayed general form.

The main new computational interface, with a proposed name, is:

```text
CommutingUpperRE :=
  REPred (fun x : HaltingGameValue.GameData × ℕ × ℕ =>
    commutingOperatorValue x.1.game < (x.2.1 : ℝ) / (x.2.2 : ℝ)).
```

This deliberately matches the existing lower-approximation threshold encoding.
The zero-denominator case denotes threshold zero and is false by value
nonnegativity. Nonnegative rational thresholds suffice; `3/4` alone suffices
for the final contradiction. A general signed-rational API is optional.

Write the consumer before its analytic supplier:

1. Obtain the computable reduction `g : Code → GameData` from
   `Halting.halting_reduction_quantum_of G U`.
2. Suppose quantum and commuting values agree on every game in its image.
   Then `¬ HaltsOnEmptyInput c` is equivalent to
   `commutingOperatorValue (g c).game < 3/4`: the two promised quantum values
   are `1` and at most `1/2`.
3. Pull `CommutingUpperRE` back along `g` to make non-halting recursively
   enumerable. Combine with `MIPRE.halting_re` using Mathlib's
   `ComputablePred.computable_iff_re_compl_re'`, contradicting
   `MIPRE.halting_undecidable`.
4. Conclude that some reduction game has unequal values. The tensor-to-commuting
   embedding makes the inequality strict in the correct direction.
5. A commuting strategy with payoff above the quantum supremum supplies a point
   outside `Cqa`: the payoff is continuous, and its upper bound extends from
   `Cq` to its closure. This step needs no maximizing finite-dimensional strategy.
6. Closedness of `Cqc` and `Cq ⊆ Cqc` give `Cqa ⊆ Cqc`; together with the point
   from step 5, obtain strict inclusion.

This consumer uses the existing halting semidecider directly. The already
proved quantum lower semidecider remains useful for a general two-sided
approximation theorem, but need not be imported by the minimal contradiction.
Do not construct a purported total decider on all games by a race that is only
known to terminate on promised instances.

Proposed milestones, all with honest explicit hypotheses:

- `exists_value_gap_of_upperRE (G : GapCompression) (U : UniversalMachine)`.
- `tsirelson_of_upperRE_of_closed (G) (U)`: additionally assumes closedness of
  each finite-scenario `Cqc` and the effective upper procedure.
- `tsirelson_of_compression (G) (U)`: the analytic/computability hypotheses
  have been supplied by the new NPA development.
- `tsirelson_of_answerReduction (A : AnswerReduction 5)`: use
  `GapCompression.ofAnswerReduction A` and `Cost.selfUniversal`.
- Unconditional `tsirelson`: only after a checked answer-reduction inhabitant
  is available. Do not use a headline theorem that still carries `sorryAx`.

Names and displayed signatures above are design targets, not compiled declarations.

## 3. Reuse audit and module boundaries

| Existing component | Reuse | Work still required |
|---|---|---|
| `Foundations/Games.lean` | `TensorProductStrategy`, projective measurements, Born-rule bounds, `quantumValue` | Game-independent correlation witnesses, value transport to a linear payoff, matrix-to-operator embedding |
| `Foundations/CommutingOperator.lean` | Arbitrary-Hilbert-space POVM strategies, correlations, `commutingOperatorValue` | Probability/value bounds in Foundations, projective subclass, correlation-set topology |
| `Foundations/Dilation.lean` | Finite-dimensional projective dilation and Born-rule transport | Common dilation on arbitrary Hilbert space preserving cross-player commutation |
| `Foundations/GameDescription.lean`, `HaltingGameValue.lean` | Codable `GameData` and its exact interpretation | Computable NPA input generation, preserving weight normalization and acceptance semantics |
| `Foundations/ValueApprox/{RawInt,Gaussian,RawPrimrec,RE}.lean` | Coded integer/Gaussian-integer arithmetic, rational-complex facts, bounded searches, `REPred.of_primrecRel_exists` | New upper-bound certificate checker and its semantic equivalence |
| `Foundations/Halting/{CompressorProgram,Corollaries}.lean` | Computable halting reduction and undecidability | Small upper-RE consumer described above |
| Upstream `Background/Pipeline.lean` (#197) | Actual introspection/repetition/universal-machine assembly | Supply `AnswerReduction 5` when its independent campaign finishes |
| Mathlib `Analysis/CStarAlgebra/GelfandNaimarkSegal.lean` | GNS for a positive functional on an existing C*-algebra | NPA initially produces a functional on an algebraic measurement algebra; bounded representation must still be justified |
| Mathlib `LinearAlgebra/Matrix/PosDef.lean` | `posSemidef_iff_dotProduct_mulVec` and Gram positivity | Dense rational/Gaussian-integer negative witnesses for failure of PSD |
| `Background/Repetition/TracialDensity.lean` and its vendored implementation | Lin's theorem, separable compression, operator examples and supporting analysis | These do not supply moment hierarchies or effective upper bounds; use a Background bridge for any direct reuse |

Keep the import direction in `CLAUDE.md`: Foundations and general Mathlib
extensions cannot import Background. Proposed layout:

```text
MIPRE/Foundations/Correlations/{Basic,Tensor,Commuting,Value}.lean
MIPRE/Foundations/NPA/{Words,Relations,Levels,Soundness,Bounds,Limit,
                      Representation,Convergence}.lean
MIPRE/Foundations/CommutingDilation/{Basic,Common,Correlation}.lean
MIPRE/Foundations/ValueUpper/{Raw,Certificates,Soundness,Complete,Primrec,RE}.lean
MIPRE/Foundations/Tsirelson/{Conditional,Main}.lean
MIPRE/Background/Tsirelson.lean
```

Split files according to actual proof size. Generic bounded-operator, dense PSD
witness, or compact-refutation lemmas belong under `MIPRE/Mathlib/` with
Mathlib-shaped paths. Avoid reorganizing existing ValueApprox or strategy
definitions solely to obtain attractive names. New correlation witnesses should
have explicit conversions to/from the existing game-indexed strategy, with the
Born probabilities and payoff proved equal.

The current commuting-strategy universe is `Type 0`. Keep it consistent with
the existing API, and document that the NPA reconstruction is separable. If
an arbitrary-universe equivalence is advertised, it needs the cyclic separable
restriction bridge; it must not be inferred from a comment alone.

## 4. NPA design decisions

### Full words and exact level conventions

Use tagged Alice/Bob generators and finite lists of generators. Star reverses
the word because generators are self-adjoint. Begin at level `k ≥ 1`; use an
offset index internally if it removes repeated positivity side conditions.
The matrix is indexed by words of length at most `k`, while moment coordinates
range over words of length at most `2k`.

Retain redundant words. Encode contextual instances of the finite projection,
orthogonality, completeness, and cross-player commutation relations, with every
monomial within the degree bound. Include normalization, conjugate symmetry,
and explicit real/nonnegative/normalized probability coordinates. Restriction
of a level `k+1` certificate must literally produce a level `k` certificate.

The analytic API may use finite types and `Matrix.PosSemidef`; its computational
API must use explicit finite lists, codes, and bounds. Prove the interpretations
equivalent. `Fintype` finiteness or `classical` decidability alone does not prove
that the constraint generator is computable uniformly in the scenario and level.

Full-word convergence suffices for the target. The existing `lem:npa-levels`
also promises equivalence with a standard reduced presentation. Track that as a
separate clause: either prove the degree-preserving substitutions, or split the
blueprint statement and leave that clause open. A proof of the full-word clause
must not mark the entire stronger statement complete.

### Common commuting dilation

Extend the finite-dimensional pattern to bounded operators on a general Hilbert
space, using finite Hilbert direct sums, not the default sup-norm product.
Prove square-root commutation with arbitrary operators in the relevant
commutant using continuous functional calculus. All Alice questions share one
isometric embedding; after dilating Bob, both families remain projective and
commute across players. Prove preservation of joint probabilities, not merely
the individual effects. Zero outcomes are allowed; answer alphabets are nonempty.

### Bounds, limit, and reconstruction

- Establish the prefix diagonal bound from completeness and positivity; induct
  on word length, then use PSD Cauchy-Schwarz to bound every moment by one.
  Compactness applies to the entire finite certificate set before projection.
- Extend each truncated certificate by zeros outside its domain into the
  countable product of closed unit disks. Prefer existing compactness and
  sequential-compactness APIs to a bespoke subsequence construction. Extract a
  subsequence whose levels tend to infinity; fixed constraints are eventually
  in range. Do not assume certificates chosen at different levels are compatible.
- Represent word polynomials with finite-support coefficients. Prove that the
  limiting sesquilinear form is positive and that the measurement relations
  vanish in the required contextual sense. A full quotient-algebra API is
  optional if direct forms on word polynomials prove exactly the same relations.
- Use the seminormed pre-inner-product/completion infrastructure behind Mathlib's
  GNS. Prove each generator acts contractively before extending it to the
  completion; establish null-space invariance rather than assuming it.
  Establish adjoints, projectivity, completeness, and commutation on a dense
  subspace and extend by continuity. The distinguished vector has norm one.
- Recover correlations, prove `Cqc = ⋂ k, K k`, compactness, and payoff
  attainment. `Cqa ⊆ Cqc` is then a closure argument. No effective convergence
  rate is needed or promised.

## 5. Effective upper semidecision: proposed certificate route

The reviewed source route uses exact real-closed-field decision, currently an
admitted companion-ledger input (`1.8.3`). Do not turn that admission into a new
Lean axiom. Full quantifier elimination would be a substantial independent
project. The first implementation choice is a narrower **exact refutation
procedure for bounded NPA feasibility**.

The following is a proposed replacement argument requiring its own proof and
review. It has not been established by the previous NPA review. It avoids both
general real-closed-field decision and an unproved SDP duality/Slater assumption.

### 5.1 Certificate and checker

At a fixed level, put the real and imaginary parts of all moments in the
explicit rational box `B = [-1,1]^d`. This bound loses no feasible point by the
moment-bound theorem. All NPA identities, behavior constraints, and the payoff
condition `payoff ≥ r` are rational affine constraints in these coordinates.
Split an equality into two weak inequalities.

For the PSD condition use the following separate density lemma: for a Hermitian
finite matrix `M`, if it is not PSD, some Gaussian-rational vector `v` has
`Re(v* M v) < 0`. Clear denominators to obtain a Gaussian-integer vector. For
each fixed coded `v`, this quadratic form is **affine in the moment coordinates**.
Hermitian constraints must also be checked; real quadratic forms alone do not
detect a non-Hermitian matrix.

A certificate consists of a dyadic grid depth `N` and, for every cell covering
`B`, either a violated affine constraint or a Gaussian-integer PSD test vector.
For its associated affine function `f(z) = a0 + Σ ai zi`, compute
`L = Σ |ai|`. At the rational cell center `c`, of sup-norm radius `h`, require

```text
f(c) + L*h < 0.
```

This exact rational inequality excludes the whole cell. The checker validates
every dimension, index, vector length, cell, and witness. The grid is generated
canonically, so coverage is not a trusted certificate assertion. Clear only
strictly positive denominators; implement the check with coded integers.

### 5.2 Soundness and completeness obligations

Soundness: a feasible moment assignment lies in a grid cell and satisfies every
affine inequality and every PSD test, contradicting that cell's strict bound.

Completeness: at every point of an infeasible box system, either a finite
affine constraint fails or a Hermitian PSD condition has a Gaussian-integer
negative witness. These strict failures form an open cover of the compact box.
Choose a finite subcover. The minimum of its finitely many affine test functions
is continuous and strictly negative throughout the box, hence has a uniform
negative margin. Their Lipschitz constants have a finite maximum. A sufficiently
fine dyadic grid therefore admits a refutation witness for every cell.

The finite subcover and margin are used only to prove that a finite certificate
exists. The algorithm enumerates all coded certificates and runs the checker;
it is not asked to compute a compactness witness or an analytic modulus. If the
system is feasible, including singular and boundary cases, it never accepts.

This approach also avoids a missing all-principal-minors characterization or a
general polynomial feasibility engine: PSD is tested through rational vectors,
and each chosen test is affine in the unknown moments. It is potentially very
inefficient, which is acceptable for `REPred`.

### 5.3 Uniformity and NPA integration

Prove uniformly, not separately for each fixed game or level:

```text
PrimrecRel CheckUpper
(∃ cert, CheckUpper (g,p,q) cert)
  ↔ commutingOperatorValue g.game < (p:ℝ)/(q:ℝ).
```

The certificate includes both the NPA level and the finite grid refutation.
Enumerating whole certificates automatically dovetails levels and grids. Do
not run a partial infeasibility search to completion at level one before trying
level two; a feasible first level would block that algorithm forever.

For the semantic equivalence, prove that the threshold-constrained level is
infeasible at some finite level exactly when `commutingOperatorValue < r`.
Use the nested compact correlation projections and attainment, taking care at
`commutingOperatorValue = r`. Then apply the existing
`REPred.of_primrecRel_exists` pattern.

The `GameData` compiler must preserve its exact semantics: duplicate weights
are summed, out-of-range weights do not enter the total, zero total weight
becomes a point mass, and unequal answers on equal questions are rejected.
Prove a single interpretation theorem relating the compiled payoff to
`GameData.game`; all later proofs should use it.

**Decision gate:** first prove the abstract finite-matrix/affine-box certificate
theorem and prototype the coded checker. Only then adopt this route in the
blueprint. If it fails, record the actual obstruction and compare the explicit
RCF and other certified-refutation alternatives. Do not silently leave
`CommutingUpperRE` as a final assumption. Under the certificate route,
`lem:rcf-decision` remains an unproved, unused optional result; it receives no
completion mark and leaves the Tsirelson dependency graph.

## 6. Implementation sequence and PR acceptance criteria

Each row is a proposed PR-sized milestone. Large rows may need more than one
PR; the count is an organization estimate, not a commitment to a fixed amount
of code. No row below is marked completed by writing this plan.

| ID | Deliverable | Depends on | Acceptance criterion |
|---|---|---|---|
| T0 | Contract audit and scratch probes | Current baseline | Elaborate the final targets, inspect the GNS/completion path, and settle the exact certificate theorem. Record source/blueprint deviations and the initial import graph. Compile a scalar certificate example and the PSD-witness lemma before committing to the algorithm. |
| T1 | Correlation sets and payoff bridges | T0 | Game-independent tensor witnesses, `Cq/Cqa/Cqc`, probability bounds, deterministic witnesses, tensor-to-commuting embedding, continuous payoff, equality with both existing value definitions, and payoff bounds on `Cqa`. Include equivalence/relabeling needed for finite alphabets. |
| T2 | Conditional Tsirelson consumer | T1 | Prove the halting contradiction, existence of a strict value gap, and a correlation outside `Cqa`, with upper RE explicit. Derive strict inclusion with closedness explicit. Axiom guards must pass despite the visible mathematical hypotheses. |
| T3 | Common commuting projective dilation | T1 | A complete arbitrary-Hilbert-space construction preserving both players' joint correlations and common embeddings. Reuse or prove the finite tensor POVM bridge as needed for the interpretation of `Cq`. |
| T4 | Full-word hierarchy and strategy feasibility | T0, T1, T3 | Uniform word/relation enumeration, exact analytic/raw correspondence, Gram positivity, level restriction, and inclusion of every commuting POVM strategy. Audit the reduced-presentation clause separately. |
| T5 | Moment bounds and finite-level compactness | T4 | All moment coordinates bounded, closedness and compactness of the full feasible set and its correlation projection. Normalization and the first nontrivial level covered explicitly. |
| T6 | Infinite limiting moments | T5 | Positive normalized word functional satisfying all measurement relations and the desired correlation coordinates, extracted from arbitrary feasible certificates. No compatibility assumption. |
| T7 | Hilbert-space reconstruction | T6 | Null quotient/completion, bounded self-adjoint projection generators, cross commutation, unit vector, correlation realization, and separability. No assumed representation theorem equivalent to the desired conclusion. |
| T8 | NPA convergence and topological consequences | T3–T7 | `⋂ Kk = Cqc`, closedness, compactness, maximum attainment, `Cqa ⊆ Cqc`, and the finite-level threshold infeasibility equivalence. All analytic ingredients available without any computability or RCF premise. |
| T9 | Exact compact-box refutation theory | T0 | Sound and complete affine/PSD grid certificates for arbitrary finite rational input. Density, finite open cover, uniform margin, exact cell bounds, and boundary behavior proved. This can be developed independently of T3–T8. |
| T10 | Uniform executable NPA upper semidecider | T4, T5, T8, T9 | Coded generator/checker, primitive recursiveness, `GameData` payoff interpretation, certificate semantic equivalence, and the actual `CommutingUpperRE` theorem. Reject malformed certificates. |
| T11 | Tsirelson assembly and audit | T2, T8, T10 | Supply every downstream hypothesis; prove `tsirelson_of_compression` and `tsirelson_of_answerReduction`; close the unconditional theorem if answer reduction is available. Synchronize the blueprint and axiom guards, run full validation, and audit the final statement against the standard correlation sets. |

Recommended execution order: T0, T1, T2, then settle the T9 mathematical proof
and coding prototype early. Complete T3–T8, finish T10, then T11. The analytic
and computability branches have independent interfaces, so work can be split
later if explicitly assigned; this plan does not create additional agents or tasks.

The critical analytic chain is T3 → T4 → T5 → T6 → T7 → T8. The second major
risk is T9 → T10. Answer reduction is an external dependency only for the
unconditional final corollary. Useful reviewed milestones are a conditional
separation theorem (T2), unconditional NPA convergence (T8), and unconditional
commuting upper semidecision (T10).

## 7. Blueprint accounting and proof acceptance

| Blueprint/ledger | Planned discharge |
|---|---|
| `lem:npa-dilation`, `1.8.2.1` | T3 |
| `lem:npa-levels`, `1.8.2.2` | T4; split off unproved reduced-presentation equivalence if necessary |
| `lem:npa-moment-bound`, `1.8.2.3` | T5 |
| `lem:npa-diagonal`, `1.8.2.4` | T6 |
| `lem:npa-gns`, `1.8.2.5` | T7 |
| `thm:npa-convergence`, `1.8.2` and `1.8.2.6` | T8 |
| `lem:valco-upper-re`, `1.8.4` and `1.8.4.1` | T10; explain the exact-certificate proof route and its changed dependency on `1.8.3` |
| `cor:tsirelson`, `1.8.5` | T11; use a separately labelled non-explicit separation lemma instead of claiming `thm:separation` |
| `lem:rcf-decision`, `1.8.3` | Remains open if bypassed; no completion claim |
| Explicit `thm:separation`, CEP and Kirchberg nodes | Remain outside this campaign |

Add genuinely new compact-refutation and conditional-consumer blueprint nodes
with their exact scope. Maintain source correspondence explicitly; a different
proof is not evidence that a stronger ledger statement has been formalized.
Do not assign new ledger IDs without the companion ledger process, and do not
refresh its snapshot merely to make a local coverage check pass.

Every proved result gets the appropriate `\lean{}` and statement/proof
`\leanok` marks together with its axiom guard. Exact final guards should show
only `propext`, `Classical.choice`, and `Quot.sound` (or a subset). Explicit
conditional theorems must remain labelled conditional. No final theorem may
depend on `sorryAx`, an assumed NPA theorem, an assumed certificate-completeness
theorem, or an unexplained effective decision oracle.

Semantic checks deserving concrete examples include a scalar deterministic
strategy, zero POVM effects, a one-question/one-answer level, a singular PSD
matrix with no strict feasibility, a feasible threshold attained exactly, an
inconsistent pair of affine constraints, malformed codes, and `GameData` with
zero total weight. These exercise boundary cases that a floating-point SDP
check or a generic happy-path example would miss. Do not require a quantitative
NPA convergence rate or numerical solver performance as a completion condition.

## 8. Fast local feedback and final validation

Use the established [Windows workflow](../docs/lean-local-windows.md). Preserve
the existing warm toolchain and dependency pins; keep the Lake tree outside
OneDrive. An isolated checkout needs its own writable Lake tree, seeded from a
compatible cache if available. Do not let independently changing checkouts
share the same writable build outputs.

Before implementation, bring its working branch up to date with upstream.
Publishing this plan does not establish that newly fetched Lean sources have
been built in the local cache. Inspect the cache with `Doctor`, then build the small initial
import closure. Use the persistent checker for edits and one Lake build at a
time per cache. Do not run `lake update`, `lake clean`, or rebuild Mathlib from
source. Scratch experiments import exact modules, never `MIPRE` or all Mathlib.

Example commands once the proposed modules exist:

```powershell
./scripts/lean-local.ps1 Doctor
./scripts/lean-local.ps1 Build -Targets MIPRE.Foundations.NPA.Bounds
python scripts/lean-lsp-check.py start --session tsirelson
python scripts/lean-lsp-check.py check Scratch/NPAProbe.lean --session tsirelson --timeout 300
./scripts/lean-local.ps1 Check -File Scratch/NPAAxioms.lean
./scripts/lean-local.ps1 Validate
```

Build new or changed imports explicitly before opening consumers in the
persistent checker; close stale workers after dependency builds. Keep unrelated
introspection and answer-reduction imports out of the NPA development. Only
the final Background assembly needs the supplied compression pipeline.

At each PR: targeted builds and semantic/axiom checks, regenerate the umbrella
with the pinned `lake exe mk_all` when files change, run `Validate`, and check
CI. `Validate` covers the full library, import coverage, blueprint references,
ledger correspondence, and whitespace. Documentation-only planning edits need
link/consistency and diff checks, not a new full Lean build.

## 9. Effort and completion boundary

Budget this as approximately twelve review milestones, with T3, T7, T9, and
T10 the most likely to split. This is a scope estimate, not a calendar estimate.
Existing GNS/dilation/arithmetic infrastructure and the reviewed NPA argument
reduce invention and duplication, but do not discharge the new proofs.

Re-estimate after T0/T2 and the T9 probe: by then the final theorem has an actual
consumer, the reconstruction API has been exercised, and the computational
route has a soundness/completeness argument with compiled examples. Until
then, a precise line count or delivery date would obscure the main uncertainty.

The downstream campaign is mathematically complete when T8 and T10 supply all
inputs to T11 and the finite-scenario strict inclusion has no downstream
hypotheses. If answer reduction is still in progress, report the exact final
`AnswerReduction 5` parameter. Full unconditional Tsirelson completion requires
that parameter to be replaced by its checked construction and the resulting
root theorem to pass the same axiom audit.
