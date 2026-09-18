# `lem:self-dual-basis`: what is done, and the route for the rest

Written 2026-09-18 while working issue #105 (Chunk 2 of `planning/next-chunks.md`).

`lem:self-dual-basis` is the whole of what this blueprint assumes beyond Mathlib. The
assumption is narrower than the lemma: the adversarial-verification campaign left exactly
one node admitted --- `1.1.6.1.1`, Shoup's deterministic irreducible-polynomial construction
at `p = 2` --- and proved the rest over sixteen sub-nodes. This file records what of that
rest is formalized, and the route for what is not.

## Status

| piece | where | state |
|---|---|---|
| the Shoup axiom, with its contract | `MIPRE/Foundations/LowDegree/Shoup.lean` | axiom, pinned by `#print axioms` |
| `IsSelfDualBasis`, `IsNormalBasis` | `MIPRE/Foundations/LowDegree/SelfDual.lean` | done |
| the two `lem:downsize-field` identities | same | done (`coord_eq_trace`, `trace_mul_eq_dot`) |
| a field of size `2^k` with a bit representation | `MIPRE/Foundations/SAT/AdmissibleField.lean` | done (`binFieldGalois`) |
| self-dualization in the group algebra | `MIPRE/Foundations/LowDegree/SelfDualize.lean` | done |
| a self-dual normal basis exists, `k` odd | `MIPRE/Foundations/LowDegree/NormalBasis.lean` | done (`exists_selfDualNormalBasis_two`) |
| the `poly(k)` algorithm | --- | **open** |

The blueprint's `\leanok` on `lem:self-dual-basis` waits on the one open row, because the
lemma asserts an algorithm and not an existence. The existence half is
`lem:self-dual-basis-exists`.

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

## What the algorithm still needs

This is the larger half, and it is the one the blueprint's `\leanok` waits on: everything
above is existence, and `lem:self-dual-basis` asserts a `poly(k)` *algorithm* in the ambient
cost model of `MIPRE/Foundations/Cost/`. The ledger's route, node by node:

* `1.1.6.1.2` --- the `𝔽₂[T]/(f)` model with addition, multiplication, inversion and the
  Frobenius matrix, as `PolyTimeFun`s, on top of Shoup's `f`;
* `1.1.6.1.3` --- the trace form, `F^k = I`, and `tr(1) = 1` for odd `k`;
* `1.1.6.1.4` --- binary squarefree factorization;
* `1.1.6.1.5` --- the minimal polynomial `X^k - 1` of Frobenius, and its squarefreeness for
  odd `k`;
* `1.1.6.1.6` --- the normal element, constructively (Mathlib's normal basis theorem gives
  existence, not construction);
* `1.1.6.1.7`, `1.1.6.1.8` --- self-dualization, whose *mathematics* is now done; what
  remains is computing the square root of `c⁻¹` in `poly(k)`, which is a power in the odd
  order of `F[G]^×` and needs the order, hence the factorization of `X^k - 1`;
* `1.1.6.1.9` --- table transport;
* `1.1.6.1.10` --- the interface to aim at.

Note that the short existence argument does **not** shorten the algorithm by as much: the
square root is unique and cheap to characterize but is computed by exponentiation, and
bounding that by `poly(k)` still wants the structure of `F[G]`.

## Deliberately not attempted

Inhabiting `MIPRE.SAT.BinField` with a self-dual normal representation. `BinField` as stated
asks only for a field of size `2^k` and a `k`-bit representation with a left inverse, which
`binFieldGalois` supplies from Mathlib. Consumers that need the `\downsize` maps to be
computed by the trace form --- the downsized samplers of `lem:cl-downsize` past field size
`2` --- need more fields on `BinField` than it currently has, and adding them should wait
until such a consumer exists, so that the interface is shaped by a real use.
