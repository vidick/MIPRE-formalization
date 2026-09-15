# H4: the assembly, and how the remaining obligations are tracked

Status 2026-09-15. Written after two process failures (below) and a reading of the
companion repository's ledger nodes `1.6.*`. It says what the assembly is, which
obligations remain open, how they are marked so they cannot be forgotten, and in what order
to discharge them.

## 1. Review: what went wrong, and the rules that follow

**Two merges dropped content.** The squash merges of #57 and #58 kept the base side of six
files, so `main` lost `eqBits_ofNat` (which `Halting/Wrapper.lean` calls), two entries of
`MIPRE.lean`, and most of the blueprint text of parts 3b-i and 3b-ii. `main` did not build.
Repaired in #62; the same failure was repaired once before, in #52.

*Cause.* Squash merging collapses a branch into one commit. A branch stacked on top still
carries its own copy of those commits, so the next merge has to reconcile two versions of
the same lines, and can silently keep the wrong one.

*Rule.* **Never merge a stacked branch as-is.** After the branch below it merges, rebase:

    git fetch origin main
    git rebase --onto origin/main <old-base-commit> <branch>
    git push --force-with-lease origin <branch>

Then the branch is one commit on an identical tree and the merge cannot drop anything.
Verify with `git diff <pre-rebase-commit> HEAD` (must be empty) and, after merging, with
`git rev-parse origin/main^{tree}` against the branch tip's tree.

**`Decider.TimeBoundAt` was revised twice** (#57, #61). First from the paper's bound uniform
over all inputs, which no decider satisfying `accepts_length` can meet; then from a bound
linear in the input size, which nothing that calls the universal machine can meet.

*Cause.* Both readings were committed before anything concrete had been proved against
them. The first concrete decider whose cost had to be produced — the wrapper — refuted each
in turn.

*Rule.* **A definition that carries a bound is not finished until something inhabits it.**
Before committing such a definition, prove one concrete witness, even a trivial one. For the
notions still to come (the tabulation's budget, the compressor's time accounting) write the
witness first and let it choose the definition.

**Infrastructure was built ahead of demand.** `Halting/Serial.lean` (`parseProg`, `serProg`)
is not used by anything yet, and parts of `Halting/Arith.lean` are not either. Not wrong —
both are needed by the compressor's decider — but they were written before the consumer
existed, so nothing checked that their statements are the ones the consumer wants.

*Rule.* **Write the consumer first.** State the theorem that needs a program, with the
program's specification as a hypothesis; then build the program against that hypothesis.

## 2. The companion repository: what it is worth

Reading `vidick/mipre-proof` costs little — the paper sections relevant to a piece of work
are a few hundred lines, and the ledger nodes for one stage are a single script run — and it
has paid for itself twice:

- **`GapCompression.output_rejects_long`.** The paper (`recursive.tex`, `lem:dhalt-values`)
  claims long answers are rejected "via the timeout counter of `D^compr`". Ledger challenge
  `ch-0bb5ccf596ca5ec4` on node `1.6.3` records that this is *not* sufficient — a timeout
  alone does not preclude accepting after reading a prefix — and that the load-bearing fact
  is that the repeated decider accepts only after a full parse. The Lean statement takes the
  repaired form as a field rather than the paper's original wording.
- **The self-reference.** Node `1.6.1`'s challenge `ch-d8b5ac10f52dac75` records that
  `D^halt` must be defined by a *canonical hard-coding* rather than extensionally, because
  `lem:lambda` needs string identity between `D^halt` and the description its own Step 3
  computes. The route taken here avoids the issue entirely: the self-reference is inside
  `compressibility_criterion_levels`, through `efficient_fixed_point`, so no verifier ever
  has to quote its own description. Worth recording as a simplification the formalization
  buys.

**Rule.** Before formalizing a blueprint statement, read (a) the paper's own statement and
proof and (b) the live ledger node with `scripts/ledger-sync.py`'s event handling — node
statements must be derived honouring `node_amended`/`new_statement`, never read from a
`statement` field. A node's challenges say exactly which steps are delicate.

**One open item from the ledger, not yet reflected anywhere.** Node `1.6`'s challenge
`ch-6879ad98822a57d8` records that the paper's `|V^halt| <= lambda` claim is false as stated
for small description sizes. The route here does not use the paper's `lambda`, but the
analogous corner exists: `Verifier.IsBounded lam` requires `size <= lam`, and the wrapper's
size grows with the hard-coded description. Check the small-parameter corner when
discharging obligation **O1**.

**A departure to keep visible.** Node `1.6` says "Only the entanglement form of
`thm:compression` is used", and the paper's soundness is a compounding entanglement bound.
The blueprint deliberately takes the value form through Lin's criterion instead
(`rem:bipartite-route`, `rem:entanglement-form`). The two are different proofs of the same
theorem; the ledger accounts for the paper's, not this one.

## 3. The assembly, and the obligations it leaves

`MIPRE/Foundations/Halting/Instantiation.lean` defines the concrete objects and states the
open obligations as the fields of one structure, `MIPRE.Halting.Obligations`. There is no
`sorry` anywhere: what is unproved is exactly "this structure is inhabited", which
`#print axioms` cannot hide and which a reader can enumerate.

*The objects.* A string denotes a parameter and a decider program (`descLam`, `descDec`,
through `Data.parse`), hence a verifier `Vof x = (S^compr_{lam x}, wrap (dec x))`, hence the
two classes `classA n`, `classB n` of strings whose verifier is `n`-bounded and has
respectively a value-`1` PCC strategy or `val* <= 1/2` at index `n`.

*The obligations.*

| | Obligation | What it needs |
|---|---|---|
| **O1** | `yYes_mem`, `yNo_mem`: the two distinguished strings lie in the classes above `n₀` | the wrapper's time bound (`Halting/WrapperCost.lean`, half written), then two small decider programs |
| **O2** | `tab`, `tab_computable`, `tab_value`: the `n`-th game of a string's verifier as a computable game description with the same value | bounded evaluation of ambient programs, proved `Computable`; the question weights by running the sampler over `F_2^{s(n)}`; the acceptance table under the budget |
| **O3** | `sem_spec`: a program halting on `(x, n)` exactly when `x ∉ classB n` | O2, plus the two `Σ₁` disjuncts of `Verifier.not_inClassB_iff` merged |
| **O4** | `compr_spec`: the compressor preserves the classes across levels | the decider that reads its description by bit queries, freezes at `2n+1`, runs `Compress`, and its time accounting |

*The theorem.* `MIPRE.Halting.halting_reduction` takes `G : GapCompression` and
`O : Obligations G U` and produces the computable map from `Nat.Partrec.Code` to game
descriptions with value `1` when the machine halts and at most `1/2` when it does not — the
blueprint's `thm:halting` in `val*` form. Its proof is the per-level criterion plus O2's
value agreement; it is complete, and it is what makes the remaining work a matter of
inhabiting four fields rather than of finding an argument.

*Done 2026-09-15*, with one thing learned in the writing. The conclusion is in `val*` and
stops there. `thm:halting` item 1 claims more — the witness is a value-`1` *PCC* strategy, so
`synval = val* = 1` — and the headline `halting_reduces_to_gameValue` is stated in `synval`.
Two bridges are missing for that half, and neither belongs to this instantiation: a
synchronous strategy does not transport along a relabeling of the alphabets (there is no
counterpart of `quantumValue_eq_of_equiv`), and `MIPRE.SyncStrategy` and
`HaltingGameValue.SyncStrategy` are parallel developments with nothing relating their values.
Soundness needs neither, `synval ≤ val*` being the right direction there. Both are now named
in `rem:compression-abstract` and in the plan, so the gap between `halting_reduction` and
`thm:main` is on the record rather than a surprise waiting at the end.

## 4. Order of work

1. **O1.** Finish `Halting/WrapperCost.lean` against the definition of #61. Check the
   small-parameter corner the ledger flags. Then the two distinguished strings.
2. **O2.** The largest piece, and needed twice (by O3 and by the assembly). Write the
   consumer first: state `tab_value` and build the tabulation against it.
3. **O3.** Short once O2 is done.
4. **O4.** The second-largest, and the only one where the paper's construction is followed
   closely; read `recursive.tex` `sec:halt` and nodes `1.6.1`, `1.6.5` again before starting.

Each is one pull request, rebased onto `main` before merging, per the rule in §1.
