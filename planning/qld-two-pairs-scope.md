# Carrying both entangled pairs

`reports/qld-stage5-blueprint-repairs.md` records why both remaining QLD assemblies are blocked on
the same thing: the paper's expanded state has two entangled pairs, `A' A''` and `B' B''`, and each
remaining assembly compares two *exact Pauli* objects, so each side needs its party's whole triple
--- `A A' A''` for Alice, `B B' B''` for Bob.

This document has been wrong twice, in opposite directions, and keeps both records, because each
mistake is a fact about the interface worth remembering. The design that is now in the tree is in
the first section; the two discarded ones are at the end.

## What the paper actually says, which settles it

Three sentences of the paper decide the whole design, and reading them first would have saved both
wrong turns.

* `qld-commutation.tex`, `sec:expanding`: the state is
  `psi-hat = psi_{AB} (x) EPR_{A'A''} (x) EPR_{B'B''}`, and the six registers are partitioned into
  two parties in **two** ways --- `A A'` against `B A''`, and `B B'` against `A B''`. Every
  bipartite relation derived for one holds for the other "with the registers appropriately
  changed".
* `lem:qld-4-7` gives a pair measurement `S-hat` acting on `H (x) (C^q)^{(x) n}` **for each of the
  two players' spaces**, with the two displays `(S-hat)_{A A'} ~ (M-hat)_{B A''}` and
  `(S-hat)_{B B'} ~ (M-hat)_{A B''}`.
* `qld-separating.tex`: "If `S-hat^W_g` is viewed as an operator acting on registers `A A'` (resp.
  `B B'`) then we view `M-tilde^{W,u-tilde}_a` as an operator acting on registers `A A' A''` (resp.
  `B B' B''`)", and `lem:qld-construct-the-paulis`'s consistency is stated across
  `A A' A'' | B B' B''` --- the **physical** cut, a third grouping, distinct from both of the two
  above.

So: two cuts, one physical grouping, and `S-hat` supported on the party's own two registers.

## The design: append the pair, and mirror the structure

**A `SimulPair` is left exactly as stages 4a--4c produce it.** Its state `Phi` is on
`(dA x Anc) x EA` against `(dB x Anc) x EB` and carries only the pair `A' A''`; its `SA` is
Alice's `S-hat` on `A A'`, with no other pair's register in sight.

**The other pair is appended**, one half to each party, with `expVec _ epr`. A party register then
reads

    ((X x Anc) x E) x Anc

--- own space, own half of the pair the state carried, padding, and the half of the appended pair
this cut gives it. The ordering is the point: `mTilde` appends its Pauli register at the end of the
register its pair measurement lives on, so `mTildeAnc` built from a `SimulPair` on
`(dA x Anc) x Ea` lands on `((A x A') x Ea) x A''` --- Alice's **physical** register --- with no
`B''` in it and nothing to reindex.

**The second cut is a second `SimulPair`**, at the swapped strategy `psi'(b, a) = psi(a, b)` with
`MB` and `MA` exchanged. Its `SA` is Bob's `S-hat` on `B B'`, which is what `V_B` conjugates by.
Every lemma already proved about `SimulPair` therefore applies to Bob by instantiation: `mVec`,
`mTildeAnc`, `swapA`, `swapU_conj_mTildeAnc`, `inconsistency_mTilde_pauli_le_of_win`. There is no
mirror lemma to prove.

`MirrorSimul` in `MIPRE/Background/QLD/Mirror.lean` is the two readings together: the two groups of
`SimulPair` fields, and one field `hmirror` saying that appending the other pair to each makes them
the same state. `toFirst` and `toSecond` are the two views, `physVec` is the state on the physical
grouping, and `bornProb_physVec` is the bridge from everything proved on the first cut's `mVec`.

`MIPRE/Background/QLD/TwoPairs.lean` holds the two regroupings: `pairSwapEquiv` onto the physical
grouping, `mirrorEquiv` between the two cuts, and `pairSwapVec_mirrorVec`, which says they meet on
the nose --- so a statement proved on either cut is a statement about one physical vector.

## What is left

1. The assembly of `lem:qld-pauli-selfcons`: the eleven displays of the pulling chain, every step
   of which is in the tree (see the blueprint's comment on that lemma), now that both sides of its
   conclusion can be written down at once.
2. The assembly of `lem:qld-swap` item 2, which threads item 1 and the endgame of
   `MIPRE/Background/QLD/SwapEndgame.lean`.
3. `thm:qld`, and with it the discharge of `MirrorSimul` from `lem:qld-simultaneous` --- which is
   where the paper's "symmetric equivalents" remark has to be made good, by running stage 4 on the
   second cut as well as the first.

## Discarded design 1: retype `Phi`

The first version proposed retyping `Phi` to
`(((dA x Anc) x Anc) x EA) x (((dB x Anc) x Anc) x EB)` and re-deriving the roughly 94 mentions of
`Phi` and 19 of `mVec` across some 135 declarations. That would have worked, at a day or more of
mechanical change with a real risk of a proof that used the split grouping essentially.

It was wrong because it read `EA` and `EB` as fixed padding rather than as the free parameters they
are. The lesson generalises: **when a structure carries an opaque type parameter, check what can be
put into it before changing the fields around it.**

## Discarded design 2: hide the second pair inside `EA` and `EB`

The second version took that lesson too far: `EA = Anc x EA'` and `EB = Anc x EB'`, so that `Phi`
already is a state on all six registers with nothing retyped. `TwoPairs.lean` was first written at
that grouping and built against the tree unchanged.

It is wrong for a reason the first design did not have. With `B''` buried inside `EA`, the field
`SA : POVM (PolyPair) ((dA x Anc) x EA)` is free to act on `B''` --- which is Bob's. The paper's
`S-hat` is not: it acts on `A A'`. A measurement that may touch `B''` makes `mTilde` and the swap
unitary built from it non-local, and then `lem:qld-pauli-selfcons` cannot even be **stated**,
because its two sides do not lie on opposite sides of any cut. Recovering locality would have
needed an extra field saying `SA` is an identity extension, and with it the plumbing to push
`mTilde` through that extension --- all of it avoided by appending the pair outside the padding
instead.

That version also claimed, in the description of the pull request that introduced it, that Bob's
`mTilde` could be built from `SimulPair.SB`. It cannot: `SB` is typed on `(dB x Anc) x EB` where
that `Anc` is `A''`, so `SB` sits on `B A''`, the second party of the *first* cut. It is a real
object --- the symmetric equivalent `M-hat_{A A'} ~ S-hat_{B A''}` --- but it is not the `S-hat` on
`B B'` that `V_B` is built from. The pull request description was corrected before merge.

**Both wrong turns came from reasoning about the Lean types instead of reading the paper's register
assignments.** The three sentences in the first section were enough to settle the design, and they
were available the whole time.
