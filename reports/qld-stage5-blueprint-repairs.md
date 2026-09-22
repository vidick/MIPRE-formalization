# Stage 5 of the QLD appendix: what formalizing it found

Written 2026-09-21 while doing chunk 4 PR D (`MIPRE/Background/QLD/ExactPauli.lean`,
`SwapUnitary.lean`, `NonMultilinear.lean`). Scoped by reading the pinned paper's
`qld-separating.tex` and `qld-isometry.tex` in full, the live ledger (through
`scripts/ledger-sync.py`, never by hand), and the blueprint's stage-4 and stage-5 statements.

Two kinds of finding are separated below, because they need different actions: **blueprint repairs**,
made in this pull request, and **things to check upstream**, which are recorded and not acted on.

## Blueprint repairs made here

### 1. `lem:qld-helper` omitted a ledger-declared dependency

The live ledger gives node `1.2.2.14` the dependencies `{1.2.2.13, 1.2.2.5}`. Node `1.2.2.5` is
`lem:qld-expanded-points`. The blueprint's `\uses` list was
`{lem:qld-simultaneous, def:state-distance, def:inconsistency}` --- the self-consistency of the
expanded point measurements was missing, and it is not decoration: the paper's second display is
obtained by moving the point measurement from one party to the other, and that move is exactly what
costs the extra `eps` which is then absorbed into `delta_S`. Added.

Verified by replaying the ledger with `scripts/ledger-sync.py`'s own event handling, not by reading
node files: `read_ledger` applies `node_deps_amended`, and this dependency arrived as such an
amendment rather than in the `node_created` event.

### 2. `lem:qld-swap` omitted two dependencies, and node `1.2.2.16` declares one of them

The ledger gives node `1.2.2.16` the dependencies `{1.2.2.15, 1.2.2.4}`; node `1.2.2.4` is
`lem:qld-win`. The blueprint had `{lem:qld-exact-paulis, def:state-distance}`. The paper's proof of
the lemma's second item opens by invoking the win implications twice (Pauli-basis consistency, and
the point measurements' self-consistency) and later spends a Schwartz--Zippel step, which is where
the `md/q` in `delta_qld` comes from. Both added, along with `def:cross-distance`, which the
`simeq` relations in that proof are.

### 3. `lem:qld-swap` stated only the exact half of the paper's lemma

As written, the blueprint's lemma said the unitaries map the expanded state close to
`aux (x) EPR^M`, and that conjugation carries the exact Pauli observables to the honest Pauli
operators. The second clause is an **identity** --- it is `swapU_conj_wTilde_X` and
`swapU_conj_wTilde_Z` in the Lean, provable in three lines from projectivity and the twisted
commutation relation --- so the lemma as stated was provable without any of the appendix's
estimates, and `thm:qld`'s own second item, which is about the strategy's total Pauli measurement
being close to `tau^W_h`, was unreachable from it. The statement now has both items, the second
being that closeness, and says explicitly that the conjugation identity is a step of item 2's proof
rather than a weaker form of it.

### 4. `lem:qld-swap`: norm versus squared norm

The paper's item 1 bounds the **squared** norm; the blueprint said "maps the expanded state within
`delta_qld` of", which reads as the norm. The paper's own proof of the theorem notices the mismatch
and replaces `delta_qld` by `delta_qld^{1/2}` there, halving `b`. The blueprint now says squared
norm in the lemma and records the halving, so that `thm:qld`'s norm bound and this lemma no longer
silently disagree.

### 5. The stale "why the lemma is not yet marked as formalized" paragraph

`lem:qld-padded-lines` carries statement-level and proof-level marks with 178 guards as of PR #133,
but the paragraph below it still listed three reasons it was unmarked. Two of the three were
addressed in that PR (the error form was corrected to `poly(m) . poly(eps, md/q)` in the statement;
the second register version is `padded_lines_consistency_swap`); the third, the conditional degree
bound, stands. Rewritten to say exactly what the proof mark covers and what is conditional.

## Things to check upstream, recorded and not acted on

### A. Node `1.2.2.15`'s declared dependencies do not match the paper's current proof

The ledger gives node `1.2.2.15` (`lem:qld-exact-paulis`) the dependencies
`{1.2.2.13, 1.2.2.14, 1.2.2.7}`. Node `1.2.2.7` is `thm:linearity`, exact linearity from approximate
linearity. But the paper's current proof of this step does not use exact linearity at all --- the
exactness comes from projectivity of the simultaneous measurement together with the Pauli group law,
which is what this repository now proves unconditionally (`wTilde_eq` and its three corollaries) ---
and it does use `lem:qld-win` (node `1.2.2.4`), which the ledger does not declare. The blueprint's
`\uses` list follows the paper. Either the declared edge set for `1.2.2.15` is stale from a revision
in which the step went through Gowers--Hatami, or the paper's proof is relying on linearity somewhere
this reading missed. Worth an upstream look; the dependency graph currently says the wrong thing
either way.

### B. `lem:qld-global-linear` drops `md/q` where `lem:qld-global-separate` keeps it

`lem:qld-global-linear` claims the non-linear outcomes have total state weight `O(Delta)` with
`Delta = C(delta_ld + delta_Q)`, no `md/q`; `lem:qld-global-separate`, the next statement, carries
`sqrt(delta_ld + delta_Q) + md/q`. The paper's corresponding display has the `md/q`. The blueprint's
claim is rescued only by the absorption `md/q <= delta_ld`, which does hold because `delta_ld >=
A(md)^A q^{-b}` with `b < 1` --- but that is an unfolding of `delta_ld`'s functional form, and in
Lean it is an explicit arithmetic obligation against `deltaCL`'s constants. Two adjacent statements
treating the same term differently is a trap for whoever formalizes stage 4. Either restore the
`+ md/q` or say that the absorption is what makes the stronger form true.

### C. `lem:qld-global-robustness` asks for a repetition that is free

It says to repeat the construction on each of the two register cuts to obtain both marginal
estimates. But `MIPRE.LIDT.Adapter.clSoundness_ldc_one_deltaCL` already returns **both** register
versions from a single application. What does still need the player-symmetry transport is the input
side, and `padded_lines_consistency_swap` is that. As written the statement invites duplicating a
large construction for no reason; it should say which register version is free and which is not.

### D. `lem:qld-global-setup` does not say what its `4m | q` uses

It reads `Assume m,d>=1, admissible q, and m | q. In the regime 16md<=q, d<q and 4m | q`, which is a
derivation presented as a hypothesis list. The step needs `q = 2^k`, whence `m | q` forces `m` to be
a power of two; the paper asserts that in a `\cnote` without proof, and `def:admissible` does not say
it. A Lean formalization will need it as a lemma, so the blueprint should name it.

## What the Lean of this pull request does and does not claim

Formalized, with no error terms and no game in sight:

* the marginals of a projective pair measurement, and that they are projective;
* the appendix's `M~^{W,u}_a` and `W~^e(u)`, and the factorization
  `W~^e(u) = pvmObs S (sign) (x) tau^W(e . u)` that everything follows from;
* self-adjointness, squaring to the identity, and the twisted commutation relation with the
  **general** phase `(-1)^{tr(e e' (u . v))}` --- the paper's repaired form, with no case split;
* the swap map's unitarity, and that conjugation by it strips the measurement off the observable;
* `twirl_mul_twirl`: the product of the two Weyl twirls is the maximally entangled projector. The
  paper reaches this by induction over the `M` qudits; here `(C^q)^{(x) M}` is one matrix algebra
  indexed by `F_q^M`, so it is a single entry computation;
* the repaired arithmetic chain from two near-invariances to the overlap, and the extraction of the
  auxiliary state from a projector's weight;
* Schwartz--Zippel in the agreement direction against every multilinear polynomial at once, the
  aggregation that bounds the non-multilinear mass, and the substitution error given that mass ---
  the discharge of the critical finding at node `1.2.2.15`, to the extent it can be discharged
  without the six-register state.

Since then the approximate half of `lem:qld-exact-paulis` has been carried through to its
inequality, in `MIPRE/Background/QLD/{PauliBasis,Multilinear}.lean`:

* the non-multilinear mass bound `delta_S + sqrt(688 eps) + md/q`
  (`SimulPair.sum_bornProb_not_isInterp_le`), and
* item 1's agreement in the form the appendix's chain produces,
  `E_u sum_g <S^W_g (x) M^(Point,W),u_{coded(g).ind_m(u)}> >= 1 - delta_S - 2(delta_S +
  sqrt(688 eps) + md/q)` (`SimulPair.sum_bornProb_cubeData_ge`).

Two findings came out of doing it.

**Uniqueness of multilinear interpolation is not needed.** The chain was written with the good set
"g is multilinear", and then agreement of the two labels on it *is* uniqueness of multilinear
interpolation, which `sum_sub_le_of_eq_on` accordingly took as a hypothesis. Taking the good set to
be "g is the low-degree encoding of its own cube data" (`IsInterp`) removes the dependency
entirely: on it the two labels agree by definition, and off it `g` differs from the encoding of
*every* cube datum, which is exactly what Schwartz--Zippel needs, uniformly in the datum.
Uniqueness would say the two sets coincide; neither inclusion is used anywhere.

**Only one entangled pair is needed per orientation.** The paper's expanded state
`|psi> (x) EPR_{A'A''} (x) EPR_{B'B''}` carries two pairs and is read along two cuts,
`A A' | B A''` and `B B' | A B''`, one per orientation of `lem:qld-4-7`. Each orientation uses one
pair, and `MIPRE.QLD.hatVec` is exactly one such cut. In that cut the register the paper calls
`A''` is the opposite party's ancilla half, so `sum_g (S^W_g)_{A A'} (x) tau_{...}` --- which in the
paper's six-register picture is one operator `M~` on `A A' A''` --- is here an ordinary bipartite
pairing of Alice's `S^W_g` against Bob's point measurement convolved with his own ancilla. That is
why the inequality above needs no second pair.

**A third finding, from doing that last step: the second pair was never needed.** The bullet that
stood here said the remaining work was to adjoin the paper's second entangled pair and transport
across it. That was wrong, and in an instructive way. The paper's `A''` is not a register one has
to create --- it is already in `hatVec`, on the far side of the cut. Writing
`M~^{W,u} = sum_g S-hat^W_g (x) tau^W_{...}` as a single matrix is a *regrouping* of the same six
registers along a third cut, `A A' A'' | B`, and Born probabilities transport across it by one
entry computation (`reindex_regroupEquiv`) plus one invariance of the quadratic form
(`qform_comp_equiv`). `MIPRE/Background/QLD/MTilde.lean` does it, and
`SimulPair.inconsistency_mTilde_le` is item 1 in the paper's own `simeq_delta` form, at
`delta = delta_S + 2 (delta_S + sqrt(688 eps) + md/q)`. The instructive part is that the
obstacle was an artifact of reading the paper's register names as a demand rather than as one
choice of bipartition: `quadForm_reindex` reindexes the two parties separately and so cannot move
a factor between them, and its absence read as an impossibility. The unary companion
`qform_comp_equiv` is three lines.

With that, `lem:qld-exact-paulis` carries `leanok` at both levels.

**A fourth finding: the blueprint's paraphrase of `lem:qld-exact-paulis` dropped an item, and the
dependency graph was missing a node.** The paper's `lem:qld-construct-the-paulis` has two items:
consistency of `M~^{W,ind_m(u)}` with the point measurements, and *self-consistency* of the
observables `W~^e(u-tilde)` at a **uniform** `u-tilde`. The blueprint's statement kept only the
first. That looked harmless until item 1 of `lem:qld-swap` was assembled: the swap estimate needs
the two Weyl twirls to be near-invariances of the state, and the only thing that supplies them is
exactly the dropped item --- at a uniform `u-tilde`, not at `u-tilde = ind_m(u)`, which is all the
first item gives. So the graph said `lem:qld-swap` rested on `lem:qld-exact-paulis` and
`lem:qld-win`, and one of its real inputs appeared nowhere. Added as
`lem:qld-pauli-selfcons`, with the paper's chain as its proof sketch, `\uses` on
`lem:qld-exact-paulis`, `lem:qld-helper`, `lem:qld-win` and `lem:schwartz-zippel`, and no `leanok`.
It is kept separate from `lem:qld-exact-paulis` rather than folded back in so that the latter's
marks stay honest.

`lem:qld-swap` therefore does not carry `leanok`:
* item 1 is formalized *given* its hypothesis (`exists_auxVec_close`), and that hypothesis is
  `lem:qld-pauli-selfcons`, which is not;
* item 2 in its entirety.

The tensor bookkeeping that stood here as the obstacle to item 1 is done
(`MIPRE/Background/QLD/SwapState.lean`), and was smaller than billed: the twirl is a *projection*
(`twirl_mul_self`, from the Weyl family's group law), so no operator-norm estimate is needed, and
the range of `1 (x) |EPR><EPR|` consists of product vectors by inspection
(`bOp_eprProj_mulVec`), so the auxiliary state needs no partial trace.

Stage 4, `lem:qld-simultaneous` and its ten sub-lemmas, was untouched when this was written and
has since been done (PRs #144, #147, #150); `planning/qld-campaign.md` records how it went.

## The exact steps of `lem:qld-pauli-selfcons`, and one thing that looked out of reach

Written 2026-09-22, after the node above was added.

The chain's eleven displays are of two kinds: `approx_0` steps, which are identities, and
`approx_delta` steps, which are estimates. All the identities are now formalized
(`MIPRE/Background/QLD/AncTransport.lean`, with `syn_mul_syn` in `SwapState.lean`).

One of them is worth recording because it looked impossible and was not. Display
`eq:qld-pulling-3a` moves a generalized Pauli from one party's ancilla half to the other's, and the
paper calls the move exact. `MIPRE/Foundations/WeylEPR.lean` has that for the bare entangled state,
`stateVec_epr_syn`. But the chain runs on a `SimulPair`'s *padded* state `Phi`, and the structure
does not say `Phi` **is** an expanded state --- only that it reproduces its expectations
(`Phi_reduced`). A *vector* identity therefore seemed unavailable from the interface, which would
have meant strengthening `SimulPair`, i.e. reopening merged work.

It is available. The identity to be proved is `stateVec Phi A = stateVecB Phi B`, which is the
vanishing of `xSqNorm Phi A B` --- and a squared norm is an expectation. So
`SimulPair.xSqNorm_aOp`, which is already there, carries it from `hatVec psi` to `Phi` with no
loss. `SimulPair.stateVec_ancSyn` is that, and `SimulPair.sum_ancSyn_mulVec`
(display `eq:qld-pulling-4`) follows from it.

The general lesson for the rest of the chain: an exact statement about `Phi` that can be written as
a vanishing squared norm is reachable through `Phi_reduced`, and one that cannot is not. Every
`approx_0` step of this chain is of the first kind.

The estimates of the node are now formalized too: `eq:qld-pulling-1` (the near-identity is a
projection), `-3` (inserting the other party's outcome), `-7` and `-11` (the helper in the chain's
own indexing), `-12` (Schwartz--Zippel again), and `-10` end to end --- `fact:add-a-proj` at the
top, the orthogonal expansion and the `2 sqrt(eps)` substitution in the middle, the helper at the
bottom. What remains of the node is the assembly: the index bookkeeping that threads the eleven
displays together, and `lem:qld-povm-to-obs` at the end.

One thing found while doing the last of them is worth recording, because it is a general lesson
about this library rather than about this proof. The final passage of the node --- Item 2 of
`fact:agreement`, then `fact:data-processing`, then Item 1 of `fact:agreement` --- is
`sum_xSqNorm_map_le` in `MIPRE/Foundations/Sandwich.lean`, written for the introspection
induction and stated on bundled `POVM`s. Nothing in the QLD tree was reaching for it, because the
QLD tree speaks `IsPVM` and matrices. The two are a `simpa` apart (`povmOfIsPVM`,
`sum_xSqNorm_fibre_le`). The estimates of this appendix are not as specific as they look, and
`Foundations/Sandwich.lean` and `Foundations/Expanded.lean` are worth reading before writing
another one.

## The second entangled pair, and where it is finally needed

An earlier note in this report records that the paper's second entangled pair, `B' B''`, was not
needed for item 1 of `lem:qld-exact-paulis`: the register `A''` is already on the far side of the
`hatVec` cut, so `mTilde` as a single matrix is a regrouping of the same six registers and no new
estimate. That is still true, and the same holds for `lem:qld-simultaneous` and `lem:qld-helper`,
each of which uses one orientation at a time.

Item 2 of `lem:qld-swap` is the first consumer for which it is **not** true, and the discrepancy is
worth stating before anyone builds on the current interface.

The paper's expanded state is `|psi>_{AB} (x) |EPR>_{A'A''} (x) |EPR>_{B'B''}`, with `V_A` acting on
`A A' A''` and `V_B` on `B B' B''`, and item 1 concludes that `V_A (x) V_B |psi-hat>` is close to
`|aux>_{A A' B B'} (x) |EPR>_{A'' B''}` --- a pair made of one half from *each* party. The padded
state `SimulPair.Phi` of this formalization is on `((dA x Anc) x EA) x ((dB x Anc) x EB)`, which is
the cut `A A' | B A''`: it carries the pair `A' A''` and has no `B' B''` at all.

So item 2's threading cannot simply regroup `Phi`'s factors into item 1's cut, because the register
it needs is not there. Either the interface gains the second pair --- which means a second
`expVec`, and every statement about `Phi` re-examined for whether it survives --- or there is an
argument that one pair suffices here as it did for the lemmas above, in which case item 1's
statement as formalized (`exists_auxVec_close`, which is stated abstractly on `R x (T x T)` and so
does not commit to which halves) should be instantiated at `A' A''` and the blueprint's description
of its cut corrected.

This was found by writing `endEquiv`, a four-factor regrouping intended to *be* item 1's cut, and
then checking the register identification against `qld-isometry.tex` before building on it. The
regrouping is correct and keeps its place; the identification was not, and the blueprint entry that
asserted it has been repaired.
