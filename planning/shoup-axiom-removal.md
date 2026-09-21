# Removing the Shoup axiom

Recorded 2026-09-20 at the maintainer's request.

**Status: S0–S5 complete; final integration passed 2026-09-21.** Tracking issue:
[#130](https://github.com/vidick/MIPRE-formalization/issues/130).
This is a separate campaign
from introspection and QLD. It extends the completed classical PCP and effective
self-dual normal-basis work by removing their remaining named assumption.
It does not change the order of the active introspection campaign.

The [construction audit](shoup-construction-audit.md) records the fixed-binary
route, squarefree factorization calls, auxiliary-field bounds, and the checked
algebraic bridges. The prerequisite import graph has been separated and checked:
`BinaryRepresentation`, `BinaryPolynomial`, `BinaryConstants`, and `BinaryPower`
do not import the public Shoup interface; `ShoupCoefficients` is its consumer
adapter. Existing public declarations and field consumers retain their types.

Checked arithmetic includes normalization (`BinaryNormalize`), monic division
(`BinaryDivision`), degree and encoding lemmas (`BinaryCanonical`), gcd
(`BinaryGCD`), exact division (`BinaryExactDivision`), positive-power substitution
(`BinarySubstitution`), and arbitrary monic quotient coordinates (`BinaryQuotient`).

The squarefree factorization oracle is checked in `BinaryFactorization`: its fixed
ambient program prints monic irreducible factors whose product is the supplied
positive-degree squarefree monic polynomial. Frobenius kernel generators, capped
component separation, and the component-to-factor bridge are all proved below the
Shoup interface. The audit requires only this squarefree oracle.

The complete constructor is checked in `BinaryIrreducibleConstructor`. Unary trial
arithmetic decomposes the degree; the odd-prime branch uses bounded nonresidue
lifting and trace descent; the power-of-two branch uses an Artin–Schreier tower;
and a capped composed-sum fold combines the coprime degrees. The ambient program
has an explicit polynomial time-bound field, including output printing and its
fixed `[true]` output at degree zero.

`Shoup.lean` now defines `shoupIrreducible` directly as `irreducibleBitsProg` and
proves `exists_shoup_irreducible` with its original type. Its exact axiom guard
passes with `[propext, Classical.choice, Quot.sound]`. The exact guards also pass for
`MIPRE.TM.CookLevin.Pad.classicalPcpDecider` and
`MIPRE.SAT.effective_selfDualNormalBasis`, after rebuilding their dependency
closure. The native consumer build passed all 3,864 jobs; the full-library build
passed all 9,616 jobs on Linux with Lean 4.33.0, including `MIPRE.Axioms`. Root
imports were regenerated, and blueprint coverage, ledger synchronization, and
whitespace checks passed.

## Exact target

The original target was to replace `MIPRE.LowDegree.exists_shoup_irreducible`, formerly an `axiom` in
[`Shoup.lean`](../MIPRE/Foundations/LowDegree/Shoup.lean), with a theorem of the
same type:

```lean
∃ F : PolyTimeFun Unary (List Bool), ∀ k : ℕ, 1 ≤ k →
  (polyOfBits (F (unary k))).Monic ∧
    Irreducible (polyOfBits (F (unary k))) ∧
    (polyOfBits (F (unary k))).natDegree = k
```

The witness must have a specified deterministic program, correctness for every
positive degree, and an explicit polynomial runtime bound in the repository's
ambient cost model. Unary input makes this polynomial in `k`, not in `log k`.
Give degree zero a fixed inexpensive output so the bundled function is total;
the polynomial correctness clauses apply only to positive degrees.

All positive degrees are in scope, even though the self-dual-basis consumer uses
odd degrees. Preserve the existing public constructor and correctness interfaces.
Prefer defining `shoupIrreducible` directly from the proved implementation, then
proving the existential contract from that witness, rather than leaving the
program hidden behind a choice from an existence theorem.

Abstract finite-field existence, exhaustive search, a randomized expected-time
algorithm, or a family of advice tables does not satisfy this target. A loose
polynomial bound does: optimized arithmetic and Shoup's best exponent are not
completion requirements.

## Mathematical source and chosen route

The primary source is Victor Shoup, *New algorithms for finding irreducible
polynomials over finite fields*, Mathematics of Computation 54(189), 435–447
(1990), already cited as `Sho90` in the blueprint:
[author's copy](https://www.shoup.net/papers/detirred.pdf),
[DOI](https://doi.org/10.1090/S0025-5718-1990-0993933-0).

The implemented route is Shoup's construction specialized throughout to the fixed
prime field `F₂`. Theorem 2.1 constructs the requested polynomial from suitable
auxiliary splitting fields and nonresidues; Theorem 3.1 reduces that preparation
to polynomial factorization over the prime field. A deterministic binary
factorization algorithm then supplies the needed oracle. Theorem 3.2 is the
result cited by the present contract.

The dependency audit was completed before implementation, including the companion
manuscript's `preliminaries.tex` and live ledger node `1.1.6.1.1` at revision
`a459dee4413a256107fc2d227bab298eba04051c`. The source contract is unchanged.
Private source and audit material remain outside this public repository; the
companion ledger's admitted status is historical provenance, not a Lean assumption.

The old description of Shoup as deliberately outside the formalization is
historical context. The implementation now proves the construction, and all S5
integration checks below have passed.

## Existing work to reuse

Paths in this table are relative to `MIPRE/Foundations/`.

| Existing component | Intended reuse and limitation |
|---|---|
| `Cost/PolyTime.lean`, `Fold.lean`, `Iterates.lean` | Encoded programs, composition, bounded loops, and polynomial cost accounting. |
| `LowDegree/BinaryPolynomial.lean`, `BinaryPower.lean` | Coefficient bits, XOR, modular multiplication, and exponentiation. Extract generic code from the Shoup-dependent wrappers before using it in the constructor. |
| `LowDegree/BinaryElimination.lean`, `BinaryBasis*.lean`, `BinarySolve.lean`, `BinaryMatrixSolve.lean`, `BinaryKernel.lean` | Verified binary linear algebra for Frobenius fixed spaces and related systems. Audit the exact dependencies of reused declarations. |
| `LowDegree/FiniteReducedComponents.lean` | Algebraic facts about primitive components in finite rings with bijective squaring. |
| `LowDegree/BinaryComponents*.lean`, `BinaryGroupAlgebra.lean` | A possible starting point for splitting by fixed idempotents. The existing programs are specialized to cyclic group algebras, not general polynomial quotients. |
| `SAT/QuotientField.lean` and field-coordinate modules | Quotient representation and coordinate correctness. Reuse generic lemmas or generalize them to a supplied certified modulus; the concrete `shoup*` fields cannot bootstrap their own construction. |
| Mathlib finite fields, polynomials, and extension theory | Algebraic correctness lemmas. Abstract choices in proofs do not supply executable search or runtime bounds. |

Importing a file that declares the axiom does not itself make a theorem depend
on the axiom. Nevertheless the import graph must be reorganized before the
constructor can replace it without an import cycle. Use both import inspection
and `#print axioms` to distinguish these two issues.

## Milestones

### S0 — Audit the construction and separate its prerequisites

Read the full proofs behind Theorems 2.1 and 3.1 and write a declaration-level
dependency map for the `p = 2` specialization. Identify the auxiliary extension
representations, factorization calls, nonresidue constructions, degree bounds,
and termination arguments actually needed. Check which results Mathlib already
provides and which require effective versions.

Move `polyOfBits` and the generic coefficient representation into a small module
below `Shoup.lean`, preserving the declaration's namespace and name. Separate
generic binary arithmetic from `shoupLowerCoeffs` and other wrappers. Arrange
the graph as generic arithmetic → constructor → public Shoup interface → field
and normal-basis consumers. Keep any abstraction small enough for an actual
consumer.

**Done when:** the concrete algorithm and its dependencies are recorded; generic
prerequisites build without importing the public Shoup interface; existing
consumer statements remain intact. Every later constructor dependency must be
independent of `exists_shoup_irreducible`.

### S1 — Supply the missing polynomial and quotient algorithms

Implement the missing list-based polynomial operations required by the audited
route: normalization, division with remainder, gcd, exact division, and
modular operations. Reuse existing operations where their contracts suffice.
Prove agreement with Mathlib polynomials, representation-size bounds, and
polynomial runtime as each routine is introduced.

Handle repeated factors in characteristic two, including zero-derivative
polynomials and coefficientwise square roots, if the factorization interface
requires general inputs. Specify zero, constants, and malformed encodings so
every ambient program has a global bound. Represent quotients by arbitrary
monic moduli without assuming they are already fields.

**Done when:** the selected factorization/construction route has all required
arithmetic with checked semantics and cost. No call silently enumerates a
quotient ring or a field.

### S2 — Prove deterministic factorization over `F₂`

Implement a Berlekamp-style factorization algorithm. For a squarefree modulus,
compute the binary matrix of Frobenius, find its fixed subspace, and split using
the resulting fixed elements. Prove that the output factors are monic,
irreducible, and reconstruct the input. Adapt the existing primitive-component
arguments where useful; turning a component into an explicit factor still
requires a proved bridge.

Bound all intermediate representations and the number of splits by polynomial
functions of the input degree. If S0 permits only squarefree oracle calls,
prove that restriction at every call site; otherwise assemble full factorization
with multiplicities from S1. This scope decision must follow the source audit.

**Done when:** a fixed ambient program supplies exactly the factorization
contract the construction consumes, with deterministic polynomial cost and
standard-axiom-only correctness. This is independently useful progress, but
does not yet prove the Shoup contract.

### S3 — Construct an irreducible polynomial of the requested degree

Formalize the specialized construction using the S2 factorization routine.
Supply the necessary auxiliary extensions and nonresidue witnesses by specified
algorithms. Prove their properties, every intermediate degree bound, and that
the final coefficient list is monic, irreducible, and has degree exactly `k`.

Track representation changes explicitly: a correctness proof may use abstract
field isomorphisms, but any map used by the executing program needs a proved
effective implementation. Integer degree decomposition can use elementary
algorithms when their cost is polynomial in unary `k`.

**Done when:** one deterministic constructor is correct for all positive `k`,
and its loops, auxiliary dimensions, and output sizes have explicit polynomial
bounds suitable for ambient compilation. The correctness proof has no dependency
on the existing axiom or on concrete fields constructed from it.

### S4 — Finish the uniform ambient program and cost theorem

Compose the constructor from the verified primitives as a
`PolyTimeFun Unary (List Bool)`. Prove a global explicit polynomial bound,
including all representation conversions, auxiliary construction, and output
printing. Use a generous polynomial if that simplifies the proof; no asymptotic
optimization is required. Ensure the program code is specified independently
of classical choices, even if proof fields and polynomial-bound data are
noncomputable in Lean.

**Done when:** the concrete witness satisfies the exact current existential
contract, including total polynomial-time behavior at degree zero. Small-degree
computations can check encoding conventions, but do not replace the correctness
or complexity proofs.

### S5 — Replace the axiom and verify all consumers

Replace the axiom with its proved theorem, connect `shoupIrreducible` to the
concrete implementation, and preserve the existing monicity, irreducibility,
and degree lemmas. Update the exact axiom pin in `Shoup.lean`, the commentary
and guards in `MIPRE/Axioms.lean`, and the corresponding blueprint and planning
status. Remove descriptions saying this construction is permanently imported.

Audit the final constructor, `MIPRE.TM.CookLevin.Pad.classicalPcpDecider`, and
`MIPRE.SAT.effective_selfDualNormalBasis` using exact `#print axioms` guards:
none may contain the Shoup axiom, `sorryAx`, or a replacement unproved
assumption. A `#guard_sorry_free` check alone does not rule out a fresh axiom.

**Done when:** those consumers build with only Lean's standard axioms and the
full validation below passes. This removes this particular assumption; it does
not discharge other unfinished pipeline theorems.

## Validation and integration

- Check specific modules during development, using the pinned toolchain and
  repository options. Keep new code in the non-vendored Foundations layer.
- Add source-based blueprint statements, proof marks, and corresponding guards
  with each completed mathematical deliverable. Conditional intermediate results
  must display their hypotheses and must not be marked as the final construction.
- Regenerate `MIPRE.lean` with `lake exe mk_all` whenever Lean modules change.
- Run targeted consumer builds, then the full library for the final integration.
- Run `scripts/lean-coverage.py --check`, `scripts/ledger-sync.py`, and
  `git diff --check` before merging a deliverable.
- Preserve the existing ledger history: proving the imported result in Lean does
  not authorize rewriting the companion repository's audit events.

Use substantial deliverables: prerequisite separation and arithmetic; binary
factorization; the complete constructor and removal of the axiom. Split further
only where a coherent theorem or algorithm forms a useful review boundary.
Implementation is tracked by [#130](https://github.com/vidick/MIPRE-formalization/issues/130).
The pull request is submitted only after every milestone and integration check passes.

## Original implementation risks

The largest unknown is the effective auxiliary-extension and nonresidue part
of S3. Binary factorization is only one input to it. The other major risks are
circular use of a `shoup*` field, uncontrolled growth of intermediate extensions,
and a mismatch between an algebraic operation count and actual encoded cost.
Factoring `X^(2^k) - X` by explicitly printing it is exponential in `k` and is
not an acceptable construction route.

These risks are addressed by the checked import separation, explicit unary
arithmetic, caps on every growing loop state, and standard-axiom guards. The
milestone descriptions above retain the original acceptance criteria.
