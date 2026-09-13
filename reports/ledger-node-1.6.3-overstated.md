# Retracted: ledger node `1.6.3` was already repaired

**Status: retracted 2026-09-13.** The claim this file originally made — that node `1.6.3`
is marked validated while stating a false lemma — was wrong. The node was amended to the
correct transfer form on **2026-08-20**, three weeks before this file was written, after
challenge `ch-0bb5ccf596ca5ec4` caught the same defect. The ledger is fine.

## What was actually wrong, and what was not

The **mathematics** in the original write-up was right, and the maintainer's own reading
note on the node (added 2026-09-13) derives it identically: the node's *original*
statement said "if `M` does not halt in `n` steps then ... `val*(V^halt_n) <= 1/2`", and
that is false — if `M` first halts at step `T` then for `C_0 <= n < T` the hypothesis holds
while `val*(V^halt_n) = 1`, by downward propagation of compression's completeness from
levels `>= T` (since `2^n > n`), exactly as the paper's own `claim:induction-game` does.

The **blueprint repair that came out of it also stands**: `lem:dhalt-values` item 2 really
did carry the false absolute bound, and it is now the transfer form, matching both the
paper and the live ledger node. `rem:dhalt-transfer` records why the bound is wrong.

What was wrong was only the claim about the *ledger's* state.

## Root cause, so it does not happen again

The ad-hoc script used to read node statements in that session took a `node_amended`
event's new text from a field called `statement`. The events carry it as `new_statement`
(alongside `previous_statement`). Every amendment was therefore silently skipped and the
original `node_created` text was reported as live. **61 of the ledger's 123 nodes have been
amended**, so this was not a one-off risk: reading the ledger without honouring
`new_statement` misreports roughly half of it.

`scripts/ledger-sync.py` reads `new_statement` correctly, and
`planning/ledger-index.json` and the CI check were never affected. The lesson is to derive
node statements with that script — or at least its event handling — rather than by hand.

Three other blueprint claims written from the same stale reads have been corrected in the
same commit: node `1.2.1` is not marked imported wholesale (the import is node `1.2.1.7`,
the tensor-code theorem, and the reduction to it is proved in the paper); node
`1.2.1.7.2.4` is *resolved* by an approximate Takagi bridge rather than a live hazard; and
introspection leaves a `1/poly(n)` soundness gap, not a constant one.
