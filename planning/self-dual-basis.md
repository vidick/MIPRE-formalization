# `lem:self-dual-basis`: what is done, and the route for the rest

Written 2026-09-18 while working issue #105 (Chunk 2 of `planning/next-chunks.md`).

The companion adversarial-verification campaign left node `1.1.6.1.1`, Shoup's
deterministic irreducible-polynomial construction at `p = 2`, admitted and proved
the rest of `lem:self-dual-basis` over sixteen sub-nodes. The separate
[Shoup campaign](shoup-axiom-removal.md) now proves that construction in Lean.
The companion ledger history remains unchanged; its admitted status no longer
corresponds to a Lean axiom.

## Status

| piece | where | state |
|---|---|---|
| the specified Shoup construction and its contract | `MIPRE/Foundations/LowDegree/Shoup.lean` | proved, with an exact standard-axiom guard |
| `IsSelfDualBasis`, `IsNormalBasis` | `MIPRE/Foundations/LowDegree/SelfDual.lean` | done |
| the two `lem:downsize-field` identities | same | done (`coord_eq_trace`, `trace_mul_eq_dot`) |
| a field of size `2^k` with a bit representation | `MIPRE/Foundations/SAT/AdmissibleField.lean` | done (`binFieldGalois`) |
| canonical polynomial-basis fields, addition and multiplication | `LowDegree/BinaryPolynomial.lean`, `SAT/QuotientField.lean` | done, uniformly in `poly(k)`, using the proved constructor |
| nonzero inversion, Frobenius iteration and trace | `LowDegree/Binary{Power,Inverse,Trace}.lean`, `SAT/FieldTrace.lean` | done, uniformly in `poly(k)`, using the proved constructor |
| binary matrix operations, bases, consistent-system solves, inversion and kernel generators | `LowDegree/Binary{Linear,Elimination,Echelon,BasisProg,Basis,Solve,MatrixSolve,MatrixInverse,Kernel}.lean` | done, uniformly polynomial-time |
| canonical linear coordinates, Frobenius matrix and squarefree minimal polynomial | `SAT/FieldCoordinates.lean`, `SAT/FrobeniusMatrix.lean` | done, with a polynomial-time matrix program |
| trace Gram matrices, their inverses, and table transport in a supplied basis | `SAT/TraceGram.lean`, `SAT/BasisTransport.lean` | done, uniformly polynomial-time |
| self-dualization in the group algebra | `MIPRE/Foundations/LowDegree/SelfDualize.lean` | done |
| the binary cyclic group-algebra square-root program | `MIPRE/Foundations/LowDegree/BinarySquareRoot.lean` | done, with polynomial cost |
| effective self-dualization of any supplied normal basis | `LowDegree/BinaryCirculant{,Prog}.lean`, `SAT/NormalGram.lean`, `SAT/EffectiveSelfDual.lean` | done, with exact output and polynomial cost |
| a self-dual normal basis exists, `k` odd | `MIPRE/Foundations/LowDegree/NormalBasis.lean` | done (`exists_selfDualNormalBasis_two`) |
| primitive fixed-space projections and the normal element | `LowDegree/BinaryComponents{,Prog}.lean`, `SAT/NormalElement{,Prog}.lean` | done, deterministic and uniformly polynomial-time |
| the complete `poly(k)` algorithm, including multiplication tables | `SAT/EffectiveNormalBasis.lean` | **done**, using the proved constructor |

The blueprint's `lem:self-dual-basis` now carries statement and proof `\leanok`.
`effective_selfDualNormalBasis` identifies the exact encoded basis and multiplication
tables printed by a fixed ambient program and bounds its runtime by a polynomial in
the unary degree. The independent existence theorem remains available.

## The self-dualization step, and why it is short

The campaign spends two nodes (`1.1.6.1.7`, `1.1.6.1.8`) on circulant Gram self-dualization.
In the group algebra it is two short lemmas, and `SelfDualize.lean` has both.

Let `K / F` be Galois with group `G`, and let `α` be a normal element, so that `{g α}` is a
basis. Its trace-form Gram matrix is determined by

```
c ∈ F[G],    c g = tr(α · g α),
```

because `tr(g α · h α) = c (g⁻¹ h)`: the Gram matrix is *circulant*. Two facts about `c`:
it is a unit (the Gram matrix of a basis under the nondegenerate trace form is invertible),
and it is fixed by the involution `τ` of `F[G]` induced by `g ↦ g⁻¹` (the Gram matrix is
symmetric). Replacing `α` by `β = a · α` for `a ∈ F[G]` replaces `c` by `a · τ a · c`, so

> a self-dual normal basis is exactly a solution `a` of `a · τ a = c⁻¹`.

Now the point. **In characteristic two with `|G|` odd, squaring is a bijection of `F[G]`**
(`mul_self_bijective`): on `single g r` it is `single (g + g) (r * r)`, and both factors are
bijections --- the Frobenius of `F` on the coefficient, doubling on the index, which is
injective because `|G|` is odd. Hence `u := c⁻¹` has a *unique* square root `b`; `τ b` is
another square root, since `(τ b)² = τ (b²) = τ u = u`; so `τ b = b` and `a := b` solves the
equation (`exists_mul_involute_eq`). That is the whole step: no explicit circulants, no
factorization of `X^k - 1`, no norm computation in the CRT factors.

The abstract half, `exists_mul_involute_eq`, holds in any commutative ring on which squaring
is bijective, and is four lines.

## How the existence half was assembled

Three pieces of bookkeeping, none of them deep, all now in `NormalBasis.lean`:

1. **The group algebra acts.** `K` is a module over `F[G]` with `single g r` acting as
   `x ↦ r • g x`, and `a ↦ a • α` is an `F`-linear isomorphism `F[G] → K` precisely because
   `α` is normal. Mathlib's `IsGalois.normalBasis K L : Module.Basis Gal(L/K) K L` gives the
   normal element with `normalBasis_apply : normalBasis K L e = e (normalBasis K L 1)`, which
   is the index-by-the-group form this wants.
2. **The Gram identity.** `tr((a • α) · h (b • α)) = (τ a · b · c) h`. A direct computation
   once the action is in place, using that `tr ∘ g = tr`.
3. **`c` is a unit.** If `c · z = 0` then `tr(w · h (z • α)) = 0` for every `w ∈ K` and
   `h ∈ G` by the identity above, so `z • α = 0` by nondegeneracy of the trace form
   (`Algebra.traceForm_nondegenerate`, available because `K / F` is separable), so `z = 0`.
   A finite commutative ring in which `c` is not a zero divisor has `c` a unit.

`G` must be commutative for `F[G]` to be a commutative ring. For `K / F` an extension of
finite fields it is cyclic; the friction is that `Gal(K/F)` carries no `CommGroup` *instance*,
so either the development is written over `AddMonoidAlgebra F (ZMod k)` and transported, or a
local `CommGroup` instance is supplied from cyclicity. `SelfDualize.lean` takes the first
route, which is why it is stated for an additive `G`.

`NormalBasis.lean` takes the second: `attribute [local instance] IsCyclic.commGroup`, and the
group algebra is `MonoidAlgebra F Gal(K/F)`, indexed by the Galois group itself. That is what
makes `ofAlg` --- the map sending coordinates to the element they name --- literally
`(IsGalois.normalBasis F K).repr.symm`, with no transport, and it is why the file repeats the
three `SelfDualize.lean` lemmas about squaring in their multiplicative form
(`mul_self_injective`, `coeff_mul_self'`, `mul_self_bijective'`). The Gram identity is
`gramPair_ofAlg`, unitness is `isUnit_gram`, the self-dual element is
`exists_gramPair_eq_one`, and the basis is read off the Frobenius orbit through
`FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow`.

What it does **not** give is any node of the ledger: the normal element is Mathlib's
`IsGalois.normalBasis`, a theorem and not an algorithm, so node `1.1.6.1.6` is untouched, and
nothing here runs in `poly(k)`.

## Algorithmic stages

The complete algorithm now exists in the ambient cost model of
`MIPRE/Foundations/Cost/`. Its implementation follows these ledger stages, using direct
fixed-space projections in place of an explicit factorization output:

* `1.1.6.1.2` --- the `𝔽₂[T]/(f)` model now has canonical coefficient bits and uniform
  addition/multiplication programs, including Shoup's modulus construction. Binary
  exponentiation and nonzero inversion are now implemented with correctness and
  polynomial bounds. Frobenius iteration and trace computation are also implemented;
  the canonical binary linear coordinates and Frobenius matrix are now implemented;
* `1.1.6.1.3` --- the trace form and its effective Gram matrix and inverse are done;
  `F^k = I` is proved. The specialized odd-degree `tr(1) = 1` statement is not yet exposed;
* `1.1.6.1.4` --- no standalone factorization program is supplied. Fixed-space splitting
  directly constructs primitive cyclic-algebra projections, which suffice for the consumer;
* `1.1.6.1.5` --- done: the effective Frobenius matrix has minimal polynomial
  `X^k - 1`, using Mathlib's Frobenius theorem, and it is squarefree for odd `k`;
* `1.1.6.1.6` --- done: the first nonzero polynomial-basis image under each primitive
  projection is selected and their sum is proved normal. Faithfulness uses independence
  of the Frobenius automorphisms; the program does not choose an abstract normal basis;
* `1.1.6.1.7`, `1.1.6.1.8` --- self-dualization. The square-root step over the binary
  group algebra is the coefficient permutation `b(g) = u(g + g)` for `u = c⁻¹`.
  The implementation and correctness statements are `binarySquareRoot` and
  `binarySquareRoot_mul_self` in `SelfDualize.lean` (added in the classical PCP campaign).
  `BinarySquareRoot.lean` now implements this permutation as `rootBitsProg`, with
  correctness (`rootBitsProg_square`) and a polynomial bound in vector length
  (`rootBitsProg_time_le`). The trace Gram inverse is now computed by
  `shoupInverseGramProg`. The first-column square root is connected to the matrix
  inverse in `BinaryCirculant{,Prog}.lean`. `shoupSelfDualizeProg` now computes the
  complete change of basis: its exact output is proved self-dual and normal, and
  its runtime is polynomial in `k`. This whole step is done for a supplied normal basis;
* `1.1.6.1.9` --- done for any supplied basis: `shoupInBasisProg` computes its exact
  coordinates and `shoupMultiplicationTableProg` prints all `k³` table bits with a
  polynomial runtime bound in `k`;
* `1.1.6.1.10` --- done: `shoupSelfDualNormalDataProg` and
  `effective_selfDualNormalBasis` compose the unary-degree constructor and table output.

Correction, 2026-09-20: the earlier version proposed exponentiation using the order of
the unit group to compute this square root. The binary coefficient formula makes that
unnecessary: squaring fixes each coefficient and doubles its index. Factorization may
still be used in the normal-element construction; it is not needed for this square-root
step. This does not remove the remaining effective-field and normal-element obligations.

## Deliberately not attempted

Inhabiting `MIPRE.SAT.BinField` with a self-dual normal representation. `BinField` as stated
asks only for a field of size `2^k` and a `k`-bit representation with a left inverse, which
`binFieldGalois` supplies from Mathlib. Consumers that need the `\downsize` maps to be
computed by the trace form --- the downsized samplers of `lem:cl-downsize` past field size
`2` --- need more fields on `BinField` than it currently has, and adding them should wait
until such a consumer exists, so that the interface is shaped by a real use.
