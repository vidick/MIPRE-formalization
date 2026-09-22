# Carrying both entangled pairs: what the change is, and what it costs

`reports/qld-stage5-blueprint-repairs.md` records why both remaining QLD assemblies are blocked on
the same thing. This is the scope of the change that unblocks them, written before any Lean is
touched so that the shape can be argued about cheaply.

## What is represented now, and why it ran out

The paper's expanded state is

    |psi-hat> = |psi>_{A B} (x) |EPR>_{A' A''} (x) |EPR>_{B' B''} ,

with `A' A''` a maximally entangled pair **local to Alice**, `B' B''` one **local to Bob**, and the
appendix's operators acting on the triples `A A' A''` and `B B' B''`.

What this formalization carries is `SimulPair.Phi`, a state on
`((dA x Anc) x EA) x ((dB x Anc) x EB)` --- four factors, one entangled pair, split across the
party cut. `hatVec psi = expVec psi epr` is that pair with one half grouped with each party, which
is the paper's cut `A A' | B A''`: Alice's local pair read with `A''` on the other side of the
bipartition. Mathematically the two readings are the same vector; only the locality story differs.

That economy was deliberate and it was right. `lem:qld-simultaneous` and `lem:qld-helper` each use
one orientation at a time, and item 1 of `lem:qld-exact-paulis` compares an exact Pauli object on
one party with a **point measurement** on the other --- and a point measurement carries no ancilla,
so it needs nothing from the far side. `inconsistency_mTilde_le` is `mTildeAt` against
`(ptAtPOVM MB W u).aOp`, which lives on `dB x EB`.

It runs out at the first comparison of **two exact Pauli objects**, and both remaining assemblies
are exactly that. `lem:qld-pauli-selfcons` concludes
`(W~^e(u-tilde))_{A A' A''} approx (W~^e(u-tilde))_{B B' B''}`; `lem:qld-swap` item 1 concludes
about `|EPR>_{A'' B''}`. Each side of each needs its party's whole triple, so all six registers at
once, and `Phi` has four.

Worse than a shortage: the two readings pull opposite ways. `mTildeAt` lives on the regrouping that
gives **Alice** both ancilla factors (`mVec`), and a Bob-side `mTilde` would need the one that gives
**Bob** both. No bipartite cut of a four-factor state supports both at once. That there is no
Bob-side `mTilde` anywhere in the tree is the same fact from the other side.

## What to represent instead

**Carry the paper's state as the paper writes it: physically grouped.**

    Phi : (((dA x Anc) x Anc) x EA) x (((dB x Anc) x Anc) x EB)

Alice holds `A A' A''` and her padding; Bob holds `B B' B''` and his. Each local pair is a vector
in `Anc x Anc` on **one** side, not split across the cut.

The split cuts the earlier stages work in then become *derived*, by the regroupings this tree
already knows how to write: `regroupEquiv` and `bornProb_regroupVec` move one ancilla factor across
the party cut, and `endEquiv` and `qform_endVec` (both merged) move two out of it. The present
design has it backwards --- it takes one split cut as primitive and derives the other groupings ---
which is why the second pair has nowhere to live.

An alternative worth one paragraph of thought and then rejecting: keeping `Phi` and adding a second
state `Phi'` for the mirror orientation. It fails because the conclusion compares the two parties'
objects **on one state**, and `Phi` and `Phi'` would be different states, each carrying a different
single pair. There is no compatibility field that repairs that.

## What changes, and what does not

Counted over the QLD tree: about 94 mentions of `Phi` and 19 of `mVec`, across roughly 135
declarations in `Simul`, `Helper`, `Multilinear`, `MTilde`, `AncTransport`, `Pulling`,
`SwapMeasure`, `ChainProbe`, plus the construction in `PaddedLIDT`.

**Does not change: the estimates.** Every one of them is about operators and a state in the
abstract and does not care how many ancilla factors there are --- `snorm_sq_sum_proj_sandwich`,
`abs_sum_qform_swap_le`, `sum_snorm_sq_insert_le`, `inconsistency_triangle`,
`sum_uniform_bornProb_fibre_le`, all of it. None of this is new mathematics.

**Changes:**

1. `Phi`'s type, and with it the structure's fields: `Phi_unit` is unchanged in form,
   `Phi_reduced` has to say what the four-factor reduction is, and `consA` / `consB` retype.
2. The transports. `bornProb_regroupVec` and the `SimulPair` wrappers over it (`mVec`,
   `bornProb_aOp_aOp`, `xSqNorm_aOp`, `bornProb_padded`, `inconsistency_padded`,
   `inconsistency_regroupVec`) are where the new grouping is actually used, and they are the real
   work. Expect each to need its own `Equiv` and one entry computation, in the pattern those
   lemmas already follow.
3. Every statement that names `Phi` or `mVec` retypes. Most proofs should go through untouched once
   (1) and (2) are in place, because they use `Phi` only through the interface.
4. `PaddedLIDT`'s construction of the `SimulPair`, which is where a second `expVec` enters.

## Order of work

1. The new `Phi` and the structure's fields, with `PaddedLIDT`'s construction updated, and nothing
   else --- the tree will not build, and that is the point: the breakage is the worklist.
2. The transports, in `MTilde`'s `Regroup` section and its `SimulPair` wrappers.
3. Walk the breakage file by file in import order: `Simul`, `Helper`, `Multilinear`, `MTilde`,
   `AncTransport`, `Pulling`, `SwapMeasure`, `ChainProbe`.
4. Only then the two assemblies, in either order.

## The risk, and the mitigation

The risk is that step 3 turns up a proof that used the *split* grouping essentially rather than
incidentally --- something that is true of `expVec psi epr` and not of the physically grouped state.
`AncTransport`'s `stateVec_hatVec_syn` and `xSqNorm_hatVec_syn` are the candidates, since they are
the ones that reason about `hatVec` as an `expVec` rather than through the interface.

The mitigation is to do step 1 and 2 and then build, before writing anything else: the error list
is the honest estimate, and it is cheap to obtain. If `AncTransport` is the only casualty, the
change is a day; if the helper's chain in `Multilinear` also breaks, it is longer. Either way the
estimate should be taken from the compiler rather than from this document.
