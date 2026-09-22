# Carrying both entangled pairs

`reports/qld-stage5-blueprint-repairs.md` records why both remaining QLD assemblies are blocked on
the same thing: the paper's expanded state has two entangled pairs, `A' A''` local to Alice and
`B' B''` local to Bob, and each remaining assembly compares two *exact Pauli* objects, so each side
needs its party's whole triple.

**The first version of this document scoped that as a retyping of `SimulPair.Phi`, and it is not
one.** The change is additive, the structure is untouched, and the record below keeps both the
wrong estimate and the reason it was wrong, because the reason is a fact about the interface worth
remembering.

## The interface already has room

`SimulPair`'s padding registers `EA` and `EB` are **arbitrary types**, constrained only by
`Fintype` and `DecidableEq`. Nothing says what is in them. So the second pair lives there:

    EA = Anc F m x EA'        EB = Anc F m x EB'

and `Phi : ((dA x Anc) x EA) x ((dB x Anc) x EB)` already *is* a state on the paper's six registers
plus padding. `Phi_reduced` is satisfiable unchanged, because it speaks of `aOp X` and `aOp Y`,
which put the identity on all of `EA` and `EB` whatever those are.

Read the factors as the paper's registers, with each pair split across the party cut the way
`hatVec` already splits the first:

* Alice's side, `(dA x Anc) x (Anc x EA')`, is `A A'` and `B'' EA'`;
* Bob's side, `(dB x Anc) x (Anc x EB')`, is `B A''` and `B' EB'`.

`Phi_reduced` pins the *first* `Anc` on each side to be the halves of the pair `hatVec` carries,
`A'` with Alice and `A''` with Bob, and says nothing about the second, which is free to be the
other pair split the other way.

## The one permutation the comparison needs

Alice's `M~` wants `A A' A''`, Bob's wants `B B' B''`. Each needs one register from the far side,
and they are **different** registers --- `A''` for Alice, `B''` for Bob --- so a single permutation
serves both: send each party's far half home. That is `pairSwapEquiv` in
`MIPRE/Background/QLD/TwoPairs.lean`, with `pairSwapVec`, `pairSwapVec_unit`,
`reindex_pairSwapEquiv` and `qform_pairSwapVec` beside it, in the pattern `regroupEquiv` and
`bornProb_regroupVec` set. After it Alice holds `A A' A''` and Bob holds `B B' B''` --- the
physical grouping --- and both exact Pauli objects are expressible on one bipartite cut, which is
what `lem:qld-pauli-selfcons`'s conclusion and `lem:qld-swap` item 1 compare.

That file builds against the tree as it stands, which is the demonstration that nothing has to be
retyped.

## What is left

1. A structure beside `SimulPair` --- not replacing it --- recording that `EA` and `EB` have the
   shape above and that the state carries the second pair there. The natural field is a mirror of
   `Phi_reduced` for the other orientation; `SB` and `SB_proj` already exist and need nothing.
2. Bob's `mTilde`, from `SB` on the mirror regrouping, as `mTildeAnc` is Alice's on `mVec`'s.
3. Then the two assemblies, in either order.

## What the wrong estimate was, and why

The first version proposed retyping `Phi` to
`(((dA x Anc) x Anc) x EA) x (((dB x Anc) x Anc) x EB)` and re-deriving the roughly 94 mentions of
`Phi` and 19 of `mVec` across some 135 declarations. That would have worked and it was a day or
more of mechanical change with a real risk of a proof that used the split grouping essentially.

It was wrong because it read `EA` and `EB` as fixed padding rather than as the free parameters they
are. The lesson generalises: when a structure carries an opaque type parameter, check what can be
put *into* it before changing the fields around it. The rejected alternative in the first version
--- a second state for the mirror orientation --- is still rejected, and for the same reason as
before: the conclusion compares the two parties' objects on **one** state.
