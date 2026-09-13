# Ledger node `1.6.3` overstates `lem:dhalt-values` item 2

Found 2026-09-13 while checking the blueprint's chapter 6 against
`paper/recursive.tex` in `vidick/mipre-proof`. The blueprint has been repaired
(`lem:dhalt-values` and the new `rem:dhalt-transfer` in
`blueprint/src/content/06_proof_structure.tex`). The ledger cannot be repaired from this
repository — `af` lives in the companion repo — so this is the record.

## The node as recorded

> `1.6.3` — lem:dhalt-values, non-halting case (item 2): if M does not halt in n steps
> then the compression guarantee applied to the verifier V (built from F's description)
> forces val*(V^halt_n) <= 1/2, via the entanglement lower bound compounding across
> scales; the induction over scales is well-founded (no circularity in the
> self-reference).

State: validated.

## Why it is false

Take a machine `M` that halts for the first time at step `T`, and any level `n` with
`C_0 <= n < T`. Then `M` does not halt within `n` steps, so the node's hypothesis holds.
But `val*(V^halt_n) = 1`, not `<= 1/2`:

- item 1 of the same lemma gives `val*(V^halt_m) = 1` with a value-1 PCC strategy for
  every `m >= T`;
- at level `n`, `V^halt_n` is `V^compr_n`, and the *completeness* clause of
  `thm:compression` says `V^compr_n` has a value-1 PCC strategy if `V^halt_{2^n}` does;
- `2^n > n`, so downward induction from the levels above `T` gives a value-1 PCC
  strategy at every level down to `C_0`.

The per-level hypothesis "does not halt in `n` steps" is simply too weak to bound the
value: the recursion looks *upward*, to level `2^n`, where `M` may well have halted.

## What the paper says

`paper/recursive.tex`, `lem:dhalt-values` item 2:

> If `M` does not halt in `n` steps then `V^halt_n` has a value-1 PCC strategy if and
> only if `V^compr_n` does. Furthermore, under the same assumption it holds that
> `Ent(V^halt_n, 1/2) = Ent(V^compr_n, 1/2)`.

A *transfer*, with no absolute bound — and its proof says why: when `M` does not halt
within `n` steps, `D^halt` accepts exactly when `D^compr` does, and the two verifiers
share the sampler, so the two games coincide up to an identification of the answer
alphabets. The absolute bound `val*(V^halt_n) <= 1/2` requires `M` never to halt and is
the *conclusion* of the recursion in `thm:halting`, not an ingredient.

Decisively, the paper's own proof of `thm:halting` applies item 2 under the hypothesis
"`M` does not halt in `n` steps" to conclude that `game_n` has value **1** — inside
`claim:induction-game`, the completeness half. So the node's reading and the paper's use
of the lemma point in opposite directions in the same regime.

## Consequences

- **In the blueprint:** the old form made the completeness half of `thm:halting`
  unprovable, since it asserted `<= 1/2` exactly where completeness needs `1`. Repaired.
- **In the ledger:** node `1.6.3` should be amended to the transfer form. Node `1.6`
  (the stage statement) is fine as written: it quantifies correctly, "if M does not halt,
  `val*(V^M_n) <= 1/2` for all n".
- **For the campaign:** worth a look at how a validated node came to carry a hypothesis
  weaker than its conclusion supports. The node text names the right mechanism (the
  entanglement lower bound compounding across scales, well-founded induction) but attaches
  it to the wrong hypothesis, which suggests the challenge rounds tested the mechanism and
  not the quantifier.

## Not a discrepancy, checked and cleared

The blueprint's `thm:compression` outputs a **7**-level verifier where the paper's outputs
a **9**-level one. This is deliberate and already documented at
`blueprint/src/content/01_introduction.tex:161`: direct repetition adds no anchoring level.
Flagged here only so the next reader does not re-open it.
