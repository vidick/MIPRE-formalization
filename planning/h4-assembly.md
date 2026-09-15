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
| ~~**O1**~~ | *Done 2026-09-15.* `yYes_mem`, `yNo_mem` in `Halting/Strings.lean`, on the wrapper's time bound in `WrapperCost.lean` and the `IsBounded` plumbing in `Bounded.lean` | — |
| **O2** | `tab`, `tab_computable`, `tab_match`: the `n`-th game of a string's verifier as a computable game description matching it along both alphabets | bounded evaluation of ambient programs, proved `Computable` (done, `Cost/BoundedEval.lean`); the question weights by running the sampler over `F_2^{s(n)}`; the acceptance table under the budget (decidable, done) |
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

*The two bridges, done 2026-09-15*, in `Foundations/GameTransport.lean`,
`Foundations/GameDescription.lean` and the new `Foundations/SyncTransport.lean`. Three things
found in the writing, all of them cheaper than the entry above expected.

- **The synchronous relabeling is the tensor-product one with one alphabet instead of four.**
  `SyncStrategy.relabel` is `⟨S.d, S.d_pos, S.P.reindex eX eA⟩` — `ProjectiveMeasurement.reindex`
  already existed, built for `TensorProductStrategy.relabel` — and `value_relabel` is the same
  fourfold `Fintype.sum_equiv` argument, `isPCC_relabel` one `rw` at the weight hypothesis.
  `syncValue_eq_of_equiv` is then `quantumValue_eq_of_equiv`'s two-sided `iSup` argument
  verbatim. What had to be added was `SyncStrategy.bddAbove_range_value`, which `Games.lean`
  has for `TensorProductStrategy` and `CommutingStrategy` but not for `SyncStrategy`;
  `syncValue_nonneg` and `syncValue_le_one` were missing for the same reason. Nothing about PCC
  obstructs the transport: commutation is a condition at question pairs of positive weight, and
  a relabeling with matching `μ` matches exactly those pairs.
- **The two `SyncStrategy` structures differ only in packaging, and the values agree by
  unfolding.** `MIPRE.SyncStrategy.value_eq` was already written in the shape of
  `HaltingGameValue.strategyValue`, and `MIPRE.SyncStrategy.ofPOVM` / `.povm` were already the
  two halves of the repackaging, so `value_toSyncStrategy` and `strategyValue_ofSyncStrategy`
  are each `rw [value_eq]; rfl`. Both directions go through, so
  `GameData.gameValue_eq_syncValue` is an equality and not the pair of inequalities that would
  have sufficed. Consequence worth recording: `HaltingGameValue.gameValue` inherits whatever is
  proved about `MIPRE.syncValue`, and `gameValue_nonneg`, `gameValue_le_one` and
  `gameValue_le_quantumValue` fall out. Nothing in `MIPRE/HaltingGameValue.lean` had to change,
  which matters — it is the file `thm:main` is read against.
- **The consumer needed no hypothesis the `val*` one does not already have.**
  `Verifier.syncGame_toGame` is a field-level identity, so the `μ` and `D` hypotheses of
  `quantumValue_toGame_eq_valStar` transfer to the synchronous game unchanged: the consumer is
  that theorem with `quantumValue` replaced by `syncValue`
  (`Verifier.syncValue_syncGame_eq_one`, from `exists_perfectPCC_syncGame`), and with `val* ≤ c`
  the same hypotheses give the soundness half in `HaltingGameValue.gameValue`
  (`gameValue_toGame_le_of_valStar_le`).

**A seam the bridges found in O2, since closed.** `Obligations.tab_value` concluded
`quantumValue (tab x n).game = (Vof G U x).valStar n (ansBound G x n)` — an equality of `val*`
and nothing more. Both consumers of the bridges need the *matching data* instead: the two
equivalences of the alphabets and `hμ`, `hD` along them. From the equality alone the
synchronous half is not recoverable, `synval ≤ val*` pointing the wrong way, so a value-`1` PCC
strategy of `𝒱_n` cannot be pushed onto the tabulation. It cost nothing to repair, O2 building
`tab` from `Verifier.answerEquiv` and `questionEquiv` and so having the matching data in hand:
the field is now `tab_match` and delivers it, with `Obligations.tab_value` a derived lemma
(#68). `thm:main` waits on O1–O4 alone.

Worth keeping as an instance of the rule in §1: a hypothesis structure is only as good as its
consumers, and this one had two — the assembly and the bridges — that wanted different things
from the same field. Neither would have noticed alone.

## 4. Order of work

1. ~~**O1.**~~ Done. The rule of §1 paid: `Verifier.IsBounded` had no inhabitant at all
   before this, and the wrapper — the first thing whose cost had to be produced against it —
   is what would have refuted it a third time. It did not; the definition of #61 went through
   unchanged. The small-parameter corner the ledger flags did not bite either: `|𝒱| ≤ λ` is
   free, a verifier's size being a constant, and the rest is what the threshold `n₀` absorbs.
2. **O2.** The largest piece, and needed twice (by O3 and by the assembly). Write the
   consumer first: state `tab_match` and build the tabulation against it.
3. **O3.** Short once O2 is done.
4. **O4.** The second-largest, and the only one where the paper's construction is followed
   closely; read `recursive.tex` `sec:halt` and nodes `1.6.1`, `1.6.5` again before starting.

Each is one pull request, rebased onto `main` before merging, per the rule in §1.
