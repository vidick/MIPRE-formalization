# H4: the assembly, and how the remaining obligations are tracked

Status 2026-09-15, with O1 and O2 closed. Written after two process failures (below) and a
reading of the companion repository's ledger nodes `1.6.*`. It says what the assembly is,
which obligations remain open — O3 and O4 — how they are marked so they cannot be forgotten,
and in what order to discharge them. One mark has changed kind along the way: O2 is no longer
a field of `Obligations` but a block of theorems in `Halting/Instantiation.lean` that
`halting_reduction` calls directly, while O1's fields are still there, discharged from outside
in `Halting/Strings.lean`.

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

**The same definition's third lesson, from O2: the size clause of `Verifier.IsBounded` is
load-bearing.** The time clauses of `IsBounded λ` are guarded by `2 ≤ n`, so at `n = 0` and
`n = 1` they say nothing and no budget exists — acceptance at those indices is genuinely `Σ₁`.
Nothing at the use sites supplies `2 ≤ n`. What supplies it is the clause `|𝒱| ≤ λ`: every
program encodes to a `Data.cons`, so `2 ≤ |𝒟| ≤ |𝒱| ≤ λ` (`Cost.Prog.two_le_esize`, then the
new `Verifier.IsBounded.two_le`), and a verifier that is `n`-bounded is so at an `n` that is at
least `2`. The three bridges that need a budget — `accOf_iff`, `dimOf_eq`, `margOf_eq`, hence
`tab_match` and `tab_le` — all run through it, and the lemma says so where a reader will meet
it: **drop the size clause from `IsBounded` and those three become unprovable, and with them
O2.** No change to the definition itself; the reading of #61 has now been used from both sides
and stands.

*Rule.* **A clause is not documented until something would break without it.** `IsBounded` was
written for `GapCompression`, which *supplies* it; the tabulation is the first thing that
*spends* it, and it found a clause the supplier had made free. When a definition acquires a
second consumer, re-read it from that side and write down what the reading needs — that is the
cheapest moment to discover it, and the only one before the clause is quietly dropped.

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
| ~~**O2**~~ | *Done 2026-09-15.* No longer a field: `tab`, `tab_computable`, `tab_match`, `tab_le` and `tab_value` are theorems of `Halting/Instantiation.lean`, over `Halting/Tabulate.lean` (`tabOf`, the `GameData` that two encoded programs and three numbers describe) and the new `Cost/ProgData.lean` (deciding program-hood) | — |
| **O3** | `sem`, `sem_closed`, `sem_spec`: a program halting on `(x, n)` exactly when `x ∉ classB n` | the two `Σ₁` disjuncts of `Verifier.not_inClassB_iff` merged — the `val*` one is two lines from `tab_computable` (`rePred_lt_quantumValue_comp`), the boundedness one is a search that still has to be written, and one of the two directions needs synchronicity, which `classB` does not carry; §4 has the list |
| **O4** | `compr_spec`: the compressor preserves the classes across levels | the decider that reads its description by bit queries, freezes at `2n+1`, runs `Compress`, and its time accounting |

*The theorem.* `MIPRE.Halting.halting_reduction` takes `G : GapCompression` and
`O : Obligations G U` and produces the computable map from `Nat.Partrec.Code` to game
descriptions with value `1` when the machine halts and at most `1/2` when it does not — the
blueprint's `thm:halting` in `val*` form. Its proof is the per-level criterion plus the
tabulation's value agreement — `tab_value` in the halting branch, `tab_le` in the other, both
now theorems rather than hypotheses; it is complete, and it is what makes the remaining work a
matter of inhabiting the fields that are left — O1's two strings, which are in hand, and O3 and
O4 — rather than of finding an argument.

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
the field was then `tab_match` and delivered it, with `tab_value` a derived lemma (#68); both
are now theorems of `Halting/Instantiation.lean` rather than fields. `thm:main` waits on O1, O3
and O4 alone.

Worth keeping as an instance of the rule in §1: a hypothesis structure is only as good as its
consumers, and this one had two — the assembly and the bridges — that wanted different things
from the same field. Neither would have noticed alone.

**O2, done 2026-09-15.** The tabulation is `tabOf` — a `GameData` assembled from two encoded
programs and three numbers (`Halting/Tabulate.lean`) — fed what a string supplies, and its five
theorems now sit in `Halting/Instantiation.lean` where the four fields used to be.
`halting_reduction` calls `tab_computable`, `tab_value` and `tab_le` directly and is otherwise
unchanged. Three things are worth carrying forward.

- **Nothing that mentions a `Verifier` can be `Primrec`,** so the whole computable layer is
  written in `Data`. A `Verifier` is a structure carrying proofs and `Prog` deliberately has no
  `Primcodable` instance, so: `Cost/ProgData.lean` (new) decides program-hood with `progOk` —
  four simultaneous predicates by one `Data.recD`, four because the grammar of `Prog.toData`
  reaches two levels down and a tree recursion sees its children but not its grandchildren —
  and `progNorm` is that normalization in the form a `Primrec` proof can reach. Getting the
  fallback wrong would not leave a gap but make the tabulation *wrong*: a string whose right
  component is not an encoding denotes `Prog.nil`, which accepts nothing, while a tabulation
  that ran the junk could accept. `Cost.Prog.ProgD` (`Wrapper.lean`) rebuilds the wrapper's
  syntax tree in `Data`, `dWrapCore_eq` being `rfl`, because it is the same definition seen
  through the encoding and not a second one to keep in step; and
  `PolyTimeFun.computable_encode_comp` (`Cost/Partrec.lean`) is what lets a `PolyTimeFun _ Prog`
  — `G.samplerProg` — reach a computability proof at all, no `Primcodable` on the output being
  needed. Under those, the small arithmetic a budgeted run needs: `encode_nat_rec`,
  `primrec_nat_pow` and a bridge between two `BEq` instances for `List.idxOf`
  (`Cost/Codable.lean`), the two enumerations (`Halting/Enumerate.lean`), Horner evaluation of a
  fixed polynomial for the answer bound (`Halting/Arith.lean`).
- **The field moved three times and a consumer moved it each time** (#65, #68, #72): the
  hypothesis `IsBounded n` appeared because acceptance is `Σ₁` and the field was unsatisfiable
  without it; the equality of values became *matching data* because the synchronous bridges
  cannot run on `synval ≤ val*`; and the match split into `tab_match` and `tab_le` because a
  `GameData` *is* a synchronous game and cannot match a verifier that is not. §1's rule about
  writing the consumer first paid three times on one field, and note exactly what it bought:
  each move cost a statement, never a proof.
- **The last step was shaped by elaboration, not by mathematics.** The five arguments of `tabOf`
  are assembled one declaration at a time because the nested tuple does not elaborate in one go
  within any heartbeat budget worth setting, and `tab` is made `local irreducible` before
  `halting_reduction`, which only ever feeds it to the three theorems above. Expect the same in
  O4, which builds a larger term of the same kind.

## 4. Order of work

1. ~~**O1.**~~ Done. The rule of §1 paid: `Verifier.IsBounded` had no inhabitant at all
   before this, and the wrapper — the first thing whose cost had to be produced against it —
   is what would have refuted it a third time. It did not; the definition of #61 went through
   unchanged. The small-parameter corner the ledger flags did not bite either: `|𝒱| ≤ λ` is
   free, a verifier's size being a constant, and the rest is what the threshold `n₀` absorbs.
2. ~~**O2.**~~ Done 2026-09-15. The largest piece, and needed twice, by O3 and by the assembly.
   The record is in §3; the line to carry away is that writing the consumer first did not stop
   the statement moving three times, but it did keep every move on the statement side.
3. **O3.** The cheapest piece that is left, but not free, and one item on the list is not
   plumbing. `sem_spec` asks for a program halting on `encode (x, n)` exactly when
   `x ∉ classB n`, which `Verifier.not_inClassB_iff` splits into "not `n`-bounded" and
   "`1/2 < val*`".
   1. The `val*` disjunct is two lines and has been checked:
      `rePred_lt_quantumValue_comp (tab_computable G U) 1 2` (`Foundations/ClassMIPStar.lean`,
      already general in the index type), plus an `of_eq` and `norm_num` to read `(1 : ℝ) / 2`
      off the casts, is
      `REPred fun p : BitStr × ℕ => 1 / 2 < quantumValue (tab G U p.1 p.2).game`. Only the last
      step, `exists_semidecider_lt_quantumValue`, is specialized to `BitStr`.
   2. The boundedness disjunct has to be written: `¬ (Vof G U x).IsBounded n` as an `REPred` of
      the pair. The witness is an index `m ≥ 2` together with an input `d`, and the test is
      `Machine.runForD` (`Cost/BoundedEval.lean`, O2's own tool) returning `none` at the budget
      `m ^ n * (|d| + 1) ^ n`, which contradicts `HaltsWithin` by `runForD_eq_some`. Two of the
      three clauses have to be negated *together*: the sampler's dimension is observable only
      through a budgeted query (`CL.Sampler.queryUnder_dimension`), so `dim m ≤ m ^ n` can be
      tested only where the sampler's time clause holds, and where it does not, that clause is
      the violated one. The third, `|𝒱| ≤ n`, is decidable off `sampData` and `decProgData`
      (`esize p = (encode p).size`), whose bridges `sampData_eq` and `decProgData_eq` carry no
      hypothesis.
   3. That search is *not* primitive recursive — `sampData` runs a `PolyTimeFun` through the
      machine and is only `Computable` — while `ValueApprox.REPred.of_primrecRel_exists` is
      stated for a `PrimrecRel`. Its proof uses the test only through `hq.to_comp`, so the
      generalization to a computable test is a couple of lines, but it has to be made.
   4. The two disjuncts then merge, by Mathlib's `Partrec.merge'`
      (`Mathlib/Computability/RE.lean`, whose conclusion is exactly
      `(k a).Dom ↔ (f a).Dom ∨ (g a).Dom`), or by one search over a sum-typed witness.
   5. The result is an `REPred` on `BitStr × ℕ`, and `Cost.exists_semidecider` yields a program
      halting on `encode x` for a single *bit string*. `compressibility_criterion`'s
      `.let_ Prog.fstProg S` is the precedent for adapting the input, but in the easy direction
      — there `B` does not depend on the level, so the pair is projected away. Here the
      predicate genuinely depends on both, so the pair has to be packed into one bit string by
      an ambient prologue, or `exists_semidecider` re-proved at `BitStr × ℕ` — where
      `shiftRevProg`'s obstacle, that a `ToPartrec` code cannot see the trailing zeros of its
      input, has to be dodged again.
   6. **The item that is not plumbing.** One direction of `sem_spec` does not follow from the
      tabulation at all. Halting implies `x ∉ classB n`: if the verifier is `n`-bounded then
      `tab_le` gives `1/2 < quantumValue (tab x n).game ≤ val*`, and if it is not then the other
      disjunct applies. The converse fails. From `1/2 < val*` only `tab_value` recovers the
      tabulated value, and `tab_value` needs `IsSynchronousAt n`, which `classB n` does not ask
      for (`InClassB n T := IsBounded n ∧ valStar n T ≤ 1/2`); nothing in the repository
      excludes a bounded, non-synchronous verifier with `val* > 1/2` whose *synchronized*
      tabulation has value at most `1/2`. Three ways out, and §1's rule says to choose by
      writing the proof first: make `Decider.wrap` reject unequal answers to equal questions
      (`Prog.eqBitsProg` already compares bit lists), so that every `Vof x` is synchronous at
      every index, `tab_le` becomes a corollary of `tab_value` and the question disappears — at
      the price of reopening the wrapper's cost accounting (`WrapperCost.lean`,
      `Cost.Prog.ProgD.dWrapCore`, and O1's two strings); or put `IsSynchronousAt n` into
      `classB`, which adds a third `Σ₁` disjunct, a search for an accepted `(q, q, a, b)` with
      `a ≠ b`, and moves the cost to O4 — `GapCompression` gives synchronicity of the compressed
      verifier only through `completeness`'s `HasPerfectPCC`, so its soundness branch would need
      a new field and `thm:compression` a new clause; or describe `𝒱_n` by something whose
      diagonal carries no weight, which needs invariance of `quantumValue` under questions of
      weight zero, a lemma `Foundations/GameTransport.lean` does not have, its transport being
      along bijections.
4. **O4.** The second-largest, and the only one where the paper's construction is followed
   closely; read `recursive.tex` `sec:halt` and nodes `1.6.1`, `1.6.5` again before starting.

Each is one pull request, rebased onto `main` before merging, per the rule in §1.
