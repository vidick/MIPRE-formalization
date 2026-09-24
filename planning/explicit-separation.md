# The explicit separation of quantum and commuting-operator values: plan

Written 2026-09-24, after Tsirelson's problem was closed (#214, #219). Target: blueprint
`thm:separation` (ledger 1.8.8–1.8.11). An explicit finite bipartite game `G` with
`val*(G) ≤ 1/2` and `ω_co(G) = 1`. Its correlation clause (1.8.11): some commuting-operator
correlation has payoff `1` and lies outside `C_qa`.

Sources read: companion `paper/recursive.tex` §“separation” (`thm:separation`,
`fig:separation`) and `intro.tex` at `a459dee`. The live ledger nodes 1.8.8–1.8.11, their
challenges and dependencies, replayed with `scripts/ledger-sync.py`'s event handling. The
corollary reviews of 2026-09-13. Nothing is copied here.

## 1. Short answer

The paper's route needs a large amount of new Lean: a bipartite Schmidt-rank entanglement
version of the whole compression pipeline (§3). A different route, closer to the paper's own
remark in `intro.tex` than to its proof, needs almost nothing new. **Kleene's recursion
theorem, applied to the halting reduction and the upper semidecider that are already
proved,** gives an explicit separating game in about 40 lines. That proof has been compiled
against `main` in a scratch file (§2). The recommended plan is that route, plus the
correlation clause and the blueprint accounting (§4). The paper's route is recorded in §3 with
its cost; it is not recommended.

## 2. The fixed-point route (recommended)

**Inputs, all proved on `main`:**
- `MIPRE.Halting.halting_reduction_quantum`: a computable `g : Code → GameData` with
  `val*(g c) = 1` when `c` halts and `val*(g c) ≤ 1/2` when it does not;
- `MIPRE.commutingUpperRE`: `ω_co(G_d) < p/q` is r.e.;
- `quantumValue_le_commutingOperatorValue` and `commutingOperatorValue_le_one`;
- Mathlib's `Nat.Partrec.Code.fixed_point₂`.

**Argument.** The predicate `c ↦ ω_co(g c) < 1` is r.e. (take `p = q = 1`). The recursion
theorem gives a code `e` that halts on the empty input exactly when `ω_co(g e) < 1`.
- If `e` halted, then `val*(g e) = 1`, so `ω_co(g e) = 1`, and `e` would not halt: a
  contradiction.
- So `e` does not halt. Hence `val*(g e) ≤ 1/2`, and `ω_co(g e) ≥ 1`, so `ω_co(g e) = 1`.

**Checked.** The theorem

```text
∃ d : GameData, quantumValue d.game ≤ 1/2 ∧ commutingOperatorValue d.game = 1
```

compiles in `Scratch/SepFixedPoint.lean` (git-ignored) with only `propext`,
`Classical.choice` and `Quot.sound`.

**In what sense the game is explicit.** It is `g e` for a code `e` obtained from the
recursion theorem, uniformly from the codes of `g` and of the semidecider. That is the same
sense as the paper's game: `G^sep` also comes from self-reference, and the paper says its
proof "does not exhibit an explicit value-1 commuting-operator strategy". The two games
differ:
- the paper's `G^sep` is the compressed verifier `V^sep` at level `C₀`, which has an
  early-accept branch;
- ours is the halting-reduction game of a machine that runs the commuting-value semidecider
  on its own game.

The Lean statement is an `∃` over `GameData`, as `cor:tsirelson` is.

**Why nothing about entanglement is needed.** The paper needs Schmidt-rank growth to get
`val* ≤ 1/2` in the case `ω_co = 1`, where no level is known to be sound. Here that case is
the non-halting case of the halting reduction, whose soundness is already the value-form
(Lin) compression chain of the main theorem. The paper states this idea itself
(`intro.tex`, and the footnote to the halting section of `recursive.tex`).

## 3. The paper's route, for the record

`fig:separation` builds a machine `N`:
1. Check the question lengths.
2. Build its own decider description `D̄` with timeout `B_sep`.
3. Run the upper semidecider `A` on the succinct pair `(V̄, C₀)` for `n` steps.
4. Accept if `A` halts; otherwise compress and run the compressed decider.

The two cases are:
- **`ω_co < 1`:** `A` halts. Trivial perfect strategies at large `n` propagate down by
  compression completeness, which contradicts `val* ≤ ω_co < 1`.
- **`ω_co = 1`:** `A` never halts. The entanglement form of compression soundness gives
  `Ent(V_n, 1/2) ≥ ½ Ent(V_{2^n}, 1/2)` together with the floor `2^{2^{λn}−2}`. So `Ent`
  diverges, and `val* ≤ 1/2`.

What that would take in Lean, none of which exists:
- **Schmidt rank.** A bipartite Schmidt-rank measure `Ent_bi` with its monotonicity, and a
  rigidity-to-rank extraction from `qld_soundness`: near `EPR^{⊗M}` implies rank at least
  about `q^M`.
- **Entanglement clauses in every stage's soundness:**
  - introspection: the floor;
  - oracularization;
  - answer reduction: a factor `1/2`;
  - repetition: the paper uses **anchored** BVY repetition, whose entanglement clause
    direct repetition lacks. The Lean pipeline uses the vendored direct theorem, which is
    read-only.
- **Compression and self-reference:** a compression theorem carrying the clause; the
  string-identity self-reference at `C₀` with a dominating timeout; the `V^sep ≡ V^compr`
  identification with the answer-alphabet merge and pad (ledger 1.8.9); and the PCC and
  runtime bridges (`rem:pcc-representation-bridge`, `rem:runtime-contract-bridge`).

That is many thousands of lines. It is justified only if the paper's own `G^sep`, rather
than some explicit separating game, is the goal.

**A middle route, if a compression-shaped game is wanted.** A variant of
`compressibility_criterion_levels` (`Foundations/Compression.lean`) gives it without
entanglement, reusing the existing self-referential decider (`decFunV`). At level `n` the
decider outputs:
1. "yes" if the commuting-value semidecider on its own start-level game halts within
   `size n` steps;
2. else "no" if the lower semidecider halts;
3. else compress.

The priority order matters. Estimated at about 450 lines; reasoned through but not checked.
Not needed for `thm:separation`.

## 4. Milestones

| ID | Deliverable | Size |
|---|---|---|
| E1 | `Foundations/Tsirelson/Separation.lean`: the fixed-point theorem, stated conditionally on `HaltingReductionQuantum` and `CommutingUpperRE`; its unconditional form in `MIPRE/Tsirelson.lean` | ~80 lines |
| E2 | Correlation clause (1.8.11): payoff attains its supremum on the compact `Cqc` (`isCompact_Cqc`, `CommutingOperatorStrategy.instNonempty`), so some `p ∈ Cqc` has payoff `1`, and `p ∉ Cqa` because payoffs on `Cqa` are at most `val* ≤ 1/2` | ~60 lines |
| E3 | Blueprint and guards, below | — |
| E4 | Upstream report to the companion repository, below | — |

Blueprint changes (E3):
- **`thm:separation`:** restate it without the premises, with `\lean{}`, statement and
  proof marks, and guards. Its `\uses` become `def:commuting-upper-re`,
  `lem:valco-upper-re`, `cor:main-quantum`, `lem:correlation-sets-basic`, and
  `lem:cqc-compact` for the correlation clause.
- **Proof-route note:** keep `\ledgernode{1.8.8, 1.8.9, 1.8.10, 1.8.11}`, with a note that
  the correspondence is at the level of the conclusion. The game is not the paper's
  `G^sep`, and the ledger's route rests on the Schmidt-rank clauses of node 1.5, which the
  Lean does not use.
- **`rem:separation-premises`:** rewrite it to say the premises are those of the paper's
  construction, not of the theorem.
- **`rem:separation-which-value`:** replace its dichotomy paragraph with the fixed-point
  argument.
- **`rem:downstream-nodes`:** update its "Second" paragraph.
- **The CEP chain:** `cor:cep` and `lem:cep-implies-equal` use `cor:tsirelson`, not
  `thm:separation`, so it is unaffected.
- **Checks:** run `scripts/blueprint-edges.py --check`, `lean-coverage.py` and
  `ledger-sync.py`.

Findings to report upstream (E4), found while reading:
1. **The intro overstates the separation.** `intro.tex` promises "an explicit correlation …
   in `C_qc` but not in `C_qa`" and calls the separating game synchronous. The proof and
   ledger 1.8.11 give existence of the correlation only, and nothing proves synchronicity;
   the early-accept branch accepts every answer when it fires.
2. **Unchecked details of `fig:separation`:**
   - `λ`-boundedness of `V^sep` is asserted only "by a similar argument";
   - step 6 lacks the bounded length check that `fig:halt_f` has, so "`C_sep` dominates
     the running time of `N`" fails on over-long inputs (ledger 1.8.8 repairs this);
   - the identification with `V^compr` is unstated (ledger 1.8.9 repairs it);
   - no non-circularity remark for `C_sep`.
3. **A shorter proof exists.** The fixed-point argument of §2 proves the theorem from the
   value-form reduction alone.

**Total: about 150 lines of Lean,** one PR. After it, the remaining chapter 8 items are:
- `thm:npa-convergence` as stated;
- the broader clauses of `lem:valco-upper-re`;
- CEP and QWEP, which rest on the admitted Kirchberg node 1.8.6.1.
