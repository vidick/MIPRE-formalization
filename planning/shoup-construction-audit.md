# Shoup construction: checked dependency audit

Recorded 2026-09-20. This is the source and implementation dependency map for
[the axiom-removal plan](shoup-axiom-removal.md). The uniform constructor and its
public Shoup theorem now pass the pinned Lean checker. The plan records the
separate full-library, downstream-consumer, and repository validation status;
this mathematical audit does not substitute for those integration checks.

The public mathematical source is Victor Shoup, [*New algorithms for finding
irreducible polynomials over finite fields*](https://www.shoup.net/papers/detirred.pdf),
Sections 2 and 3, especially Theorems 2.1 and 3.1 and their proofs (printed
pages 4–8 of the author's copy). Both branches needed in characteristic two
are implemented. The companion manuscript contract was checked at revision
`a459dee4413a256107fc2d227bab298eba04051c`; no private source or ledger material
is reproduced here, and the companion ledger's historical admission is unchanged.

## Public contract and encoded computation

`MIPRE.LowDegree.BinaryPolynomial.irreducibleBitsProg` is one fixed
`PolyTimeFun Unary BitStr`. `irreducibleBits_correct` proves monicity,
irreducibility, and degree `n` for every `n ≥ 1`; `irreducibleBits_length`
proves that exactly `n+1` coefficient bits are printed. Degree zero returns
`[true]` directly. Degree one is covered by the same assembly proof, whose
neutral prime-power contributions use the polynomial `X`.

`irreducibleBitsProg_time_le` supplies an actual `code.Runs` witness for the
encoded input and output, with one polynomial bound in `n`. That polynomial
is the composed program's `timeBound` after substitution of the unary encoding
size `2*n+1`. Thus the theorem counts ambient execution, including list copies,
arithmetic, intermediate coefficients, and output printing.

`MIPRE.LowDegree.shoupIrreducible` is defined directly as this specified program.
`exists_shoup_irreducible` is now a theorem with exactly its former existential
type, and its monicity, irreducibility, and degree consumer lemmas retain their
interfaces. No existential choice selects the program. Exact guards for the
constructor, correctness theorem, runtime theorem, and public API contain only
`propext`, `Classical.choice`, and `Quot.sound`. The final downstream guards
live in `MIPRE/Axioms.lean`; their integration status is tracked in the plan.

## Checked declaration map

Namespaces below are relative to `MIPRE.LowDegree`. All implementation modules
are in `MIPRE/Foundations/LowDegree`, outside the vendored trees.

| Layer | Actual declarations and contract |
|---|---|
| Binary representation | `polyOfBits` in `BinaryRepresentation` preserves the existing little-endian convention. `BinaryPolynomial.evalBits`, `xorBits`, `mulReduce`, and their programs have generic ring semantics. A lower-coefficient list `p` represents `polyOfBits (p ++ [true])`. |
| Canonical arithmetic | `BinaryPolynomial.normalizeBitsProg`, `divModBitsProg`, `gcdBitsProg`, and `quotientBitsProg` implement normalization, monic division, gcd, and quotient. Their semantic and width theorems cover zero and constant cases. |
| Supplied monic quotient | `BinaryQuotient.coordinateEquiv`, `toBits`, `ofBits`, `ofBits_toBits`, `toBits_ofBits`, and `evalBits_eq_iff` give faithful fixed-width coordinates without assuming irreducibility. |
| Quotient Frobenius | `BinaryQuotient.frobeniusMatrixProg_correct` identifies modular squaring. `fixedGeneratorsProg_correct`, `fixedGenerator_idempotent`, and `fixedGenerator_spans` identify the full fixed space. `square_bijective` uses squarefreeness. |
| Factorization | `BinaryQuotient.quotientComponentsProg` implements capped idempotent splitting; `factorBitsProg_factors` and `factorBitsProg_prod` give monic irreducible factors and exact reconstruction for nonconstant monic squarefree inputs. |
| Orbit product and descent | `BinaryQuotient.orbitPolynomialBitsProg`, `map_orbitPolynomialBits`, and `orbitPolynomialBits_monic_natDegree` compute closed binary orbit products. `orbitPolynomialBits_eq_minpoly` and `orbitPolynomialBits_irreducible` use an explicit exact-degree hypothesis. |
| Odd-prime auxiliary field | `BinaryPolynomial.nonresidueLiftBitsProg_correct`, `nonresidueLiftBits_order`, and `nonresidueLiftBits_degree_coprime` certify the bounded auxiliary nonresidue constructor. |
| Powers of two | `BinaryArtinSchreier.powerTwoBitsProg`, `powerTwoBits_correct`, and `powerTwoBits_length` construct every degree `2^e`, including degree one. |
| Odd prime powers | `BinaryPrimePowerTrace.flat_trace_natDegree` proves the exact trace degree. `BinaryPolynomial.oddPrimePowerBitsProg`, `oddPrimePowerBits_correct`, `oddPrimePowerBits_length`, and `oddPrimePowerBits_width_le` supply the uniform program and output contract. |
| Coprime combination | `BinaryFiniteField.minpoly_natDegree_add_of_coprime` proves the generator degree. `BinaryQuotient.composedSumBitsProg` and `composedSumBits_correct` compute the binary composed sum. |
| Unary decomposition | `DegreeArithmetic.primeUnaryProg`, `primePowerUnaryProg`, and `primePowerPairsProg` compute the decomposition. `primePowerPairs_eq`, `primePowerPairs_prod`, and `primePowerPairs_pairwise` identify its factors and product. |
| Final assembly | `BinaryPolynomial.primePowerBitsProg`, `degreePolynomialsProg`, `assembleBitsProg`, and `irreducibleBitsProg` compose the complete program. `fold_assemblyStep_correct` shows all valid cap operations are inert. |

The generic arithmetic no longer imports the Shoup interface: zero and one
vectors are in `BinaryConstants`, and only the consumer adapter
`ShoupCoefficients` imports the constructed family. Abstract fields, their
bases, and isomorphisms occur in correctness proofs; executable representations
are coefficient lists and bounded lists of such lists.

## Squarefree binary factorization

The constructor requires factorization only for nonconstant monic **squarefree**
polynomials over `ZMod 2`. Every call site proves that condition. It does not
restrict the requested positive degree and does not require executable
factorization over an extension field or recovery of multiplicities.

For a degree-`d` modulus `f`, the Frobenius matrix sends the `X^j` basis vector
to `X^(2*j)` modulo `f`. The existing binary kernel program computes a spanning
family for Frobenius plus the identity. It need not print a linearly independent
basis or enumerate any binary linear combinations.

Start with the identity idempotent and split every retained component `e` by
each fixed generator `b`, retaining the nonzero elements among `e*b` and
`e*(1-b)`. Orthogonality bounds the number of nonzero components by `d`.
Spanning of all idempotents implies that final unsplit components are primitive.
The executable loop caps component lists at `d`; the dimension proof shows that
this is inert on valid inputs.

`BinaryQuotientFactors` proves the extraction bridge. For an idempotent
`e = mk f E`, `componentFactor f E = gcd(f,E-1)` divides a polynomial `H`
exactly when `e * mk f H = 0`. Bijective squaring in the finite reduced quotient
and primitivity imply that each extracted factor is irreducible. Orthogonal
components yield coprime factors; their sum is the identity, giving exact
reconstruction. The list wrapper `componentFactors_toBits_prod` connects this
argument to the actual coefficient encodings.

Squarefree quotient squaring is injective because a lift `H` of an element whose
square vanishes satisfies `f | H^2`, hence `f | H`; finiteness then gives
bijectivity. This route needs no executable Chinese-remainder reconstruction,
extension-field inversion, or enumeration of quotient elements.

## Odd primes: effective auxiliary nonresidues

For odd prime `q`, factor `Phi_q = 1+X+...+X^(q-1)` and select the first factor.
Its degree is `m = ord_q(2)`, with `1 ≤ m ≤ q-1` and `m` coprime to `q`.
From the current polynomial `f`, query the squarefree factorization of `f(X^q)`.
A singleton factor list means this composition is irreducible; retain the old
`f`, whose root is then a `q`th nonresidue. Otherwise select the first factor.

The running invariant says that `f` divides `Phi_(q^j)` and has degree `m`.
If the current root is a `q`th power in the field with `2^m` elements, and
`M=2^m-1`, then `f(X^q)` divides `X^M-1`. An irreducible factor therefore has
degree at most `m`; the minimal polynomial of its root's `q`th power gives the
reverse inequality. Thus every nonterminal selection has degree exactly `m`
and advances the primitive-root order to `q^(j+1)`.

At most `m` iterations are possible: otherwise the field of size `2^m` would
contain an element of order `q^(m+1)`. Stopping is absorbing. The executable
program obtains `m` from the canonical seed's length, uses that length as fuel,
and clips every nonterminal choice to the original `m+1` coefficient cap.
The exact-degree invariant proves that no valid choice is truncated.

The first query has degree `q-1`; subsequent queries have degree `m*q`.
Squarefreeness follows from the cyclotomic invariant and odd characteristic-to-
order coprimality. No high-order cyclotomic polynomial is printed, and neither
`2^m-1` nor its valuation is computed in executable code. Multiplicative orders
and large powers occur only in proofs.

## Odd prime powers: flat extension and trace

For requested degree `r=q^(e+1)`, let `f` be the auxiliary polynomial. The
program uses the flat binary quotient by `f(X^r)`, of degree `m*r`, with root
`beta`. The odd-prime-power Kummer criterion proves this modulus irreducible
from the certified nonresidue. Transport to arbitrary roots occurs only in the
proof of irreducible composition.

`BinaryQuotient.traceBitsProg` computes
`gamma = sum(i<m, beta^(2^(r*i)))` by repeated modular squaring and addition.
Its Frobenius period divides `r`. If its binary degree were a proper divisor
of `r`, it would lie in the subfield generated by `beta^q`. In that subfield,
the residues of `2^(r*i)` modulo `q` would give a nonzero polynomial of degree
less than `q` vanishing at `beta`. They are distinct because `ord_q(2)=m` and
`gcd(r,m)=1`; the relative degree of `beta` is `q`, a contradiction. The checked
`flat_trace_natDegree` therefore gives exact degree `r` without an additional
unproved primitive-generator premise.

The orbit program prints the minimal polynomial of `gamma`, and normalization
produces exactly `r+1` bits. The executable inputs are unary `q` and unary `r`.
The exponent notation `2^(r*i)` means `r*i` squarings, not an allocation or loop
of length `2^(r*i)`. The flat field width `m*r` is polynomial in the supplied
input lengths, and the raw final output width is at most `r+1` on every input.

## Powers of two: Artin–Schreier tower

Degree one uses `X`; degree two starts from `X^2+X+1`. At each later step the
current root `alpha` has the invariant that
`Y^2+Y+(alpha^3+alpha^2)` is irreducible. The initial cubic parameter equals
`alpha`. If `beta^2+beta=a`, the next parameter is
`a*beta = beta^3+beta^2`; the quadratic-basis no-root argument preserves
irreducibility.

The flat implementation forms `Q(Y)=product(i<d, Y+a^(2^i))` in the old
field. Its coefficients descend to binary coefficients even if the conjugates
repeat; the next polynomial is `Q(X^2+X)`. This reuses the orbit product and
`BinaryPolynomial.substituteArtinSchreierBitsProg`. A quadratic root outside a
field of degree `2^t` has full binary degree `2^(t+1)`, and a canonical embedding
transports the cubic invariant to the new flat quotient.

`powerTwoBitsProg` takes the requested degree in unary, caps the running modulus
by that degree, and stops when the target width is reached. Its fold bound holds
on malformed inputs as well. The exponentially growing mathematical stage
sequence is confined to correctness proofs; it is not the executing program.

## Coprime combination and all-degree assembly

For monic irreducibles `f,g` of coprime degrees `a,b`, the program remains in the
quotient by `f` and forms
`H(X)=product(i<a, g(X+alpha^(2^i)))`. Frobenius permutes its factors, so its
coefficients descend to binary bits. It is monic of degree `a*b` and vanishes
at `alpha+beta` in a common abstract algebraic closure. Coprimality of the
Frobenius periods forces this sum to have exactly degree `a*b`, identifying
`H` with its minimal polynomial. No executable two-level quotient is needed.

Bounded unary trial division computes the list of contributions
`q^(n.factorization q)` for `0 ≤ q ≤ n`, with neutral value one outside the
prime support. The mathematical factorization function appears only in proofs;
`primePowerUnaryProg` uses capped unary multiplication and divisibility. The
computed contributions are pairwise coprime and have product `n`.

Dispatch constructs each contribution, and the final fold starts with `X`.
Every accumulated degree divides `n`; a proof using the positive remaining
product shows each intermediate degree is at most `n`. Each assembly step caps
its lower coefficients by the original unary input length. The cap is inert on
valid inputs and bounds arbitrary fold states, so polynomial-time composition
and bounded-fold compilation produce the global runtime theorem. Degree zero
returns the fixed constant before executing these loops.

## Reused Mathlib proof tools and remaining validation

The pinned proof dependencies include the odd-prime-power Kummer criterion,
cyclotomic-factor degree and primitive-root results, finite-field Frobenius
periods and cardinality, minimal-polynomial divisibility, quadratic root
criteria, and `AdjoinRoot` power-basis coordinates. They justify the explicit
programs; none is substituted for an executable search or costed algorithm.

The blueprint records the arithmetic, factorization, orbit, nonresidue,
prime-power, coprime, decomposition, and uniform-constructor deliverables with
proof marks and matching guards. The complete S5 integration still requires
the plan's full-library and downstream-consumer builds and repository checks.
The ledger history is preserved, and unrelated unfinished pipeline theorems
remain outside this construction's scope.
