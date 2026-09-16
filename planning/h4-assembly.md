# H4: the assembly, and how the remaining obligations are tracked

Status 2026-09-16, with O1, O2 and O3 closed and O4 begun — §4 item 4 has its plan. Written
after two process failures (below) and a
reading of the companion repository's ledger nodes `1.6.*`. It says what the assembly is,
which obligation remains open — O4, the compressor, the only one left with mathematics in it —
how they are marked so they cannot be forgotten, and in what order to discharge them. Two marks
have changed kind along the way. O2 is no longer a field of `Obligations` but a block of
theorems in `Halting/Instantiation.lean` that `halting_reduction` calls directly. O3 is now
`MIPRE.Halting.exists_sem` (`Halting/Semidecider.lean`), a theorem taking **no** hypotheses at
all — but its three fields `sem`, `sem_closed`, `sem_spec` are still in `Obligations`, because
`Halting/Semidecider.lean` imports `Halting/Instantiation.lean`, where the structure lives, so
nothing can discharge them where they stand; dropping them is the module move of §4 item 5.
O1's fields are still there too, discharged from outside in `Halting/Strings.lean`.

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
least `2`. One bridge needs a budget and runs through it — `accOf_iff`, hence `tab_match` and
`tab_value` — and the lemma says so where a reader will meet it: **drop the size clause from
`IsBounded` and `accOf_iff` becomes unprovable, and with it O2.** No change to the definition
itself; the reading of #61 has now been used from both sides and stands.

*Rule.* **A clause is not documented until something would break without it.** `IsBounded` was
written for `GapCompression`, which *supplies* it; the tabulation is the first thing that
*spends* it, and it found a clause the supplier had made free. When a definition acquires a
second consumer, re-read it from that side and write down what the reading needs — that is the
cheapest moment to discover it, and the only one before the clause is quietly dropped.

*Corrected later the same day, and this is the finding worth carrying forward.* The lesson
above said **three** bridges — `accOf_iff`, `dimOf_eq`, `margOf_eq` — and named `tab_le` beside
`tab_match`. Two of the three have since left and `tab_le` is deleted. `dimOf` and `margOf` were
taking the budget `n^n · (|q|+1)^n` that `IsBounded n` supplies because it was the budget in the
room, not because it was the right one for a sampler run: `GapCompression.sampler_time` is
`∀ λ n` with no hypothesis at all, and had been all along. The two runs now take the budget as
parameters, fed `(ansBound G x n, G.deg)`, and `dimOf_eq`, `margOf_eq` carry no hypothesis.
What found this was not a reading of `dimOf` — it had been read many times — but writing down
what `Verifier.ComputablyPresented (Vof G U)` asks for: the sampler's true dimension at *every*
string and *every* level, `n = 0` and `n = 1` included, which is exactly where the `IsBounded`
budget says nothing. The hypothesis could not be kept, so the consumer had to name a budget that
could replace it, and one had been sitting in `GapCompression` unused. `accOf_iff` cannot be
freed the same way and must not be: the decider of the verifier a string denotes is the string's
own, wrapped, and nothing bounds it unconditionally. So the size clause is still load-bearing,
for one bridge instead of three.

*Rule.* **Write the consumer first — and ask it again of the definitions already written.** The
rule at the end of this section is usually heard as advice about new definitions; this is that
rule applied to a finished bridge, and it found that the hypothesis the bridge carried had
never been necessary. When a second consumer arrives, do not ask what the existing statement
needs; ask what the consumer needs, and let it re-derive the hypotheses from nothing. The
budget that answered was sitting in `GapCompression` all along.

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
| ~~**O2**~~ | *Done 2026-09-15, with both payloads to O3 delivered the same day.* No longer a field: `tab`, `tab_computable`, `tab_match`, `tab_value` and `gameValue_tab_eq_one` are theorems of `Halting/Instantiation.lean`, over `Halting/Tabulate.lean` (`tabOf`, the `GameData` that two encoded programs and five numbers describe), the new `Foundations/GameDouble.lean` (the doubled question set) and `Cost/ProgData.lean` (deciding program-hood). `tab_le` is deleted: `(tab_value …).le` inhabits its exact type now that the value agreement holds in both branches | — |
| ~~**O3**~~ | `sem_spec`: a program halting on `(x, n)` exactly when `x ∉ classB n` | *Done 2026-09-15.* `MIPRE.Halting.exists_sem` (`Halting/Semidecider.lean`) takes **no** hypotheses: both `Σ₁` disjuncts of `Verifier.not_inClassB_iff` are r.e. and merged, on the cost-budget decision procedure of `Halting/CostBudget.lean` and the pair-input semidecider of `Halting/Semidecide.lean`, and the two arguments `exists_sem_of_tab` was left holding are supplied by O2 — `Halting.computablyPresented_Vof` from the re-budgeted sampler runs, and `tab_value` from the doubled question set. The fields `sem`, `sem_closed`, `sem_spec` are still in `Obligations`, which sits above its own discharge in the import order; §4 item 5 | the module move |
| **O4** | `compr_spec`: the compressor preserves the classes across levels | the decider that reads its description by bit queries, freezes at `2n+1`, runs `Compress`, and its time accounting |

*The theorem.* `MIPRE.Halting.halting_reduction` takes `G : GapCompression` and
`O : Obligations G U` and produces the computable map from `Nat.Partrec.Code` to game
descriptions with value `1` when the machine halts and at most `1/2` when it does not — the
blueprint's `thm:halting` in `val*` form. Its proof is the per-level criterion plus the
tabulation's value agreement — `tab_value` in both branches now, the doubled question set
having removed the synchronicity hypothesis that once split them, so that `tab_le` is
`(tab_value …).le` and is deleted; it is complete, and it is what makes the remaining work a
matter of inhabiting the fields that are left — O1's two strings and O3's semidecider, all
three in hand, and O4 — rather than of finding an argument.

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
programs and five numbers (`Halting/Tabulate.lean`) — fed what the string and the level supply,
and its five theorems now sit in `Halting/Instantiation.lean` where the four fields used to be.
`halting_reduction` calls `tab_computable` and `tab_value` directly and is otherwise
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
- **The last step was shaped by elaboration, not by mathematics.** The seven arguments of
  `tabOf` are assembled one declaration at a time because the nested tuple does not elaborate in
  one go within any heartbeat budget worth setting, and `tab` is made `local irreducible` before
  `halting_reduction`, which only ever feeds it to `tab_computable` and `tab_value`. Expect the
  same in O4, which builds a larger term of the same kind.

**O2's two payloads to O3, done 2026-09-15**, and each needed a different repair. #75 left
`Halting.exists_sem_of_tab` holding two arguments, both O2's; `MIPRE.Halting.exists_sem` now
takes none.

- **The sampler runs are re-budgeted**, which is what `Verifier.ComputablyPresented (Vof G U)`
  needed, and `Halting.computablyPresented_Vof` is the consequence — its three fields the two
  encoded programs and the dimension. The repair, and the question that found it, are §1's
  correction above; it is the one finding of this round to carry into O4. The cost was two `_eq`
  statements *losing* a hypothesis and `dimOf`, `margOf` growing a `(B k : ℕ)` pair of
  parameters. No proof changed. `accOf` did not follow and cannot, so `accOf_iff`, and with it
  `tab_value`, keep `IsBounded n`.
- **The question set is doubled** (`Foundations/GameDouble.lean`). A `GameData` forces
  `D x x a b` to `false` for `a ≠ b`, so a description matches `𝒱_n` only where `𝒱_n` is
  synchronous, and `classB n` does not ask for synchronicity. `Game.doubled` plays on
  `Bool × 𝒳` with Alice tagged `false` and Bob `true` and rejects everything off that block, so
  the diagonal carries no weight, the description's veto is implied by the distribution rather
  than constraining the verifier, and — the point that made it cheap — `hD` stays *total*, so
  `quantumValue_eq_of_equiv` and `SyncStrategy.isPCC_relabel` apply unchanged and no
  support-restricted version of either was needed. `quantumValue_doubled` is the familiar
  two-sided `iSup`, on `TensorProductStrategy.double`/`undouble`; `SyncStrategy.double` with
  `isPCC_double` carries completeness, the doubled support mapping *into* the original so no
  commutation obligation is added. `Foundations/SyncTransport.lean` gains `Verifier.doubledGame`
  and six lemmas on it, **added beside** the four bridges of part 6, which are untouched.
  `tab_match` now matches `(Vof G U x).doubledGame n T`; its old form is not recoverable for the
  new `tab`, the doubled question set having no equivalence with `Questions n`, and both of its
  consumers — `tab_value` and `gameValue_tab_eq_one` — are supplied.
- **Two details of the doubling that would have failed silently.** The tag is *prepended* to the
  question's bit string, so the index is `bitsToIdx (tag :: z)` and `bitsToIdx_lt`,
  `bitsToIdx_injOn` apply verbatim at `s + 1`; and the weight list still enumerates `𝔽₂^s`
  once, so the total weight is still `2^s` — enumerating the length-`s+1` strings instead would
  compile and halve every probability. Only `nX` doubles, to `2^(s+1) - 1`.
- **Two elaboration findings for O4.** First: **state every `Primrec` lemma generic in the
  ambient parameter type.** `Halting/Tabulate.lean` now does throughout, as
  `Verifier.primrec_accList` already did, and that is what let `tabOf` grow two arguments
  without re-running a single `Primrec` proof — each proof sees `α` and a projection, never the
  tuple. `Verifier.accListW` is the same move one level down, taking the two question indexings
  as parameters, with `accList = accListW _ _ bitsToIdx bitsToIdx _` by `rfl` so that nothing
  downstream of the old name changed. Second, a measurement, because the tree carries a number
  that no longer holds: `primrec_accOf` keeps `set_option maxHeartbeats 1000000` and a docstring
  saying the proof measures 210049 heartbeats, and `#count_heartbeats` says **about fifty** —
  the figure drifts by a unit or two between runs and contexts, which is itself the lesson —
  for the generic statement and for the deleted tuple-specific one alike, against a default
  of 200000. The counter is honest — at `maxHeartbeats 40` the same declaration times out at
  `isDefEq` — so the `set_option` is vestigial and the number is inherited from an earlier
  shape of the file. The generic statement is still the right one; its payoff is that a change
  to `tabOf`'s argument list never re-runs the proof, not a heartbeat saving.

## 4. Order of work

1. ~~**O1.**~~ Done. The rule of §1 paid: `Verifier.IsBounded` had no inhabitant at all
   before this, and the wrapper — the first thing whose cost had to be produced against it —
   is what would have refuted it a third time. It did not; the definition of #61 went through
   unchanged. The small-parameter corner the ledger flags did not bite either: `|𝒱| ≤ λ` is
   free, a verifier's size being a constant, and the rest is what the threshold `n₀` absorbs.
2. ~~**O2.**~~ Done 2026-09-15, payloads included. The largest piece, and needed twice, by O3
   and by the assembly. `tab`, `tab_computable`, `tab_match`, `tab_value` and
   `gameValue_tab_eq_one` are theorems of `Halting/Instantiation.lean` and the four fields have
   left `Obligations`; `tab_le` is deleted, being `(tab_value …).le`. §3 has the record,
   including the two payloads O3 was waiting on — the re-budgeted sampler runs and the doubled
   question set — which went in the same day. Writing the consumer first did not stop the
   statement moving three times, but it did keep every move on the statement side; and the
   re-budget was a fourth move of the same kind, on a neighbouring definition, found by the
   same question.
3. ~~**O3.**~~ Done 2026-09-15 — `MIPRE.Halting.exists_sem`, no hypotheses — and it was not
   "short once O2 is done"; that was wrong in two ways, both worth keeping.

   First, the *cost* budget. `Verifier.accepts_iff_runForD` decides acceptance under a bound
   by running the machine `3k` steps, which is all the tabulation needs: a program obeying its
   bound halts, so a long-enough run settles what it returns. O3 needs the opposite verdict —
   that a program does *not* halt within a given cost — and needs it exactly, `sem_spec` being
   an equivalence. A step is not a unit of cost (reading a variable or a constant is charged
   the size of the value), so `runForD` returning a value after `3k` steps says only that the
   program halted, not that it halted in budget. `Halting/CostBudget.lean` carries the cost
   along the run instead — `Machine.stepCostD`, `Machine.stepCost` on encoded configurations —
   and gets `Prog.HaltsWithin` primitive recursive in all three arguments, hence decidable.
   That is the `noncomputable` `Cost.evalWithin` made computable, as `runForD` is for
   `Machine.evalData`.

   Second, `sem_spec` is about `encode (x, n)`, and `Cost.exists_semidecider` is about bit
   strings; `encode (x, n) = cons (encode x) (encode n)` is not the encoding of any bit
   string, and the difference cannot be arranged by choosing the predicate.
   `Halting/Semidecide.lean` closes it once for every type whose `SizedEncoding` decodes primitive
   recursively, by prefixing `Prog.serProg` — the serializer that was written for O4's
   compressor — so that the `ToPartrec` translation of `Cost/Semidecide.lean`, delicate for
   its own reason, is not re-entered.

   What is proved outright is the enumerability of a *violated* universal clause:
   `Verifier.rePred_not_isBounded`, for any computably presented family of verifiers. The
   assembly `Halting.exists_sem_of_tab` then merges the two disjuncts by dovetailing
   (`REPred.or`, from Mathlib's `Partrec.merge'`, which had no such corollary).

   Two things found in the writing, both now on the record in the blueprint
   (`lem:bounded-violation-re`, `lem:halting-semidecider`) and in the `Obligations`
   docstring:

   - **The synchronicity seam is also O3's.** `exists_sem_of_tab` needs the tabulation's value
     to equal `val*` at every `n`-bounded string, in both directions. `tab_match` gives that
     only where the verifier is *synchronous* at `n` — §3's repair, and unavoidable, a
     `GameData` describing a synchronous game by construction — and `classB n` does not ask
     for synchronicity. So O2 and O3 as currently stated do not compose. Three repairs, in
     increasing order of blast radius: tabulate on the doubled question set `{0,1} × X`, Alice
     on the first copy and Bob on the second, so the distribution avoids the diagonal and the
     forced rejections there are never asked about (changes the tabulation only); make
     `Decider.wrap` reject unequal answers to equal questions, so every string names a
     synchronous verifier (changes the wrapper only, and its cost accounting); or add
     synchronicity at `n` to `classB n` and pay for it with a synchronicity clause in
     `compr_spec` (changes the classes only). The first looks cheapest and is O2's to make.

     **Made 2026-09-15, and the estimate held.** The doubling changed the tabulation and
     nothing else: `Decider.wrap` still denotes what it denoted, `classB` is unchanged, and
     `thm:compression` gained no clause. It cost one new module of 184 lines
     (`Foundations/GameDouble.lean`), 89 lines added to `Foundations/SyncTransport.lean` —
     `Verifier.doubledGame` and six lemmas, added beside the existing four, none of which was
     restated — and a rework of `Halting/Tabulate.lean` and `Halting/Instantiation.lean` that
     is mostly the two index maps and the re-budget. What made it cheap was not the size of the
     construction but that the doubled distribution leaves `hD` **total**, so the transport
     lemmas apply as they stand and no support-restricted `quantumValue_eq_of_equiv` or
     `isPCC_relabel` had to be proved; that was the thing worth checking before choosing, and
     it is what "looks cheapest" was resting on. The one surprise was in the opposite
     direction and is recorded in §3: the tag must be *prepended* to the question's bit string
     and the weight list must keep enumerating `𝔽₂^s`, or the tabulation compiles and is
     quietly wrong.
   - **`Primrec fun n : ℕ => (encode n : Data)` was missing**, natural numbers encoding in
     binary (`Nat.bits`). It is a prerequisite of `ComputablyPresented` for `Vof` — the
     sampler's dimension is read off a run of its program on `encode (n, dimension)` — hence
     of O2's `tab_computable` too, which runs the sampler at an index. `rePred_not_isBounded`
     itself avoids it by carrying the search's index as a *datum* and reading it back with
     `Data.natOf`, so the encoding it prepends is `Data.normBin` of the witness; that trick
     does not extend to a genuine `ℕ` argument. **Supplied since**, as
     `MIPRE.Cost.Data.primrec_encode_nat` (`Cost/Codable.lean`, written for the tabulation in
     #73), and it is what `computablyPresented_Vof` and every budgeted run in
     `Halting/Tabulate.lean` are built on.
4. **O4.** *Started 2026-09-16; not finished.* Two pieces landed, and one finding changed the
   shape of the rest.

   **`lem:lambda-bound` is in Lean** (`Halting/LambdaBound.lean`, `MIPRE.Halting.lambda_bound`):
   `C · (C' λ n)^C ≤ n^λ` for `λ ≥ 4 max((4C)^(8C), C log₂ C')` and `n ≥ 2`. This is what turns
   the output verifier's `poly(n, λ)` running times — the shape `GapCompression.decider_time`
   and `sampler_time` state — into the `n^λ` that `Verifier.IsBounded` asks for, and it is the
   first thing the boundedness half of O4 needs. Two deviations from the blueprint, both
   recorded there: `log` is `Nat.log 2`, and `C' ≥ 1` is dropped because the proof does not use
   it.

   **`compr_spec` was not satisfiable as stated, and the repair was local.** The field asks the
   compressor to carry `classA (2n+1)` down to `classA n`. `classA (2n+1)` supplies a value-`1`
   PCC strategy at the answer bound `ansBound G x (2n+1) = G.bound.eval (2n+1 + descLam x)`,
   while the only source of such a strategy for a compressed verifier is
   `GapCompression.completeness`, which takes its input at `(2 ^ n) ^ λ` — and `λ` is the
   parameter the compressor *writes into its output*, so it is bounded by the compressor's own
   output size and cannot be made arbitrarily large. Nothing in `IsBounded` bounds
   `descLam x`: for a `G` whose compressed sampler does not vary with `λ`, membership in either
   class is completely insensitive to it, while `ansBound` grows with it. With
   `IsSuccinctDesc`'s `x.length ≤ 2 ^ n` as the only handle, `descLam x < 2 ^ (2 ^ n)` and no
   single `λ(n)` relates the two bounds.

   What makes it work is a bound the criterion's own proof already had and threw away.
   `compressibility_criterion_levels`'s `key` (`Compression.lean`) establishes
   `t ≤ (Q₁ + Q₂ + Q₃).eval (…) ≤ n + 1` for the cost `t` of the run producing `x`, hence
   `x.length ≤ esize x ≤ t ≤ n + 1` — and then `isSuccinctDesc_hardcode` launders it into
   `x.length ≤ 2 ^ n` through `n + 1 ≤ 2 ^ n`. Carrying it over instead gives `hCompr`, and so
   `compr_spec`, the fourth hypothesis `x.length ≤ n + 1`; then `descLam x < 2 ^ (n+1)`, the
   answer bound is `2 ^ O(n)` against `(2 ^ n) ^ λ`, which `λ ≥ 2 deg(bound) + 1` dominates for
   `n` above a threshold read off `bound` as well — `exists_ansBound_le` is that step, checked,
   and the threshold is set by the polynomial `bound`, not by `G.deg`. The
   change is four lines of `Compression.lean` and one clause in three signatures; the classes,
   `ansBound` and O1–O3 are untouched.

   Worth keeping as a second instance of §1's rule, and a sharper one than the first: this
   hypothesis structure was not merely *unsatisfiable* as written — it was unsatisfiable while
   the information that fixes it sat two lines up in its own consumer's proof, discarded by a
   monotonicity step that looked free. The `2 ^ n` of `def:succinct` is the right bound for the
   *notion*; it is the wrong bound to hand a *consumer*.

   **A second gap, in the other direction, found while checking the first and *not* repaired.**
   The length bound settles the `classA` direction. The `classB` direction does not close with
   the field's hypotheses, and the reason is that it needs the answer-bound inequality the
   other way round. `G.soundness` wants `valStar (2^n) ((2^n)^λ) ≤ 1/2`; membership in
   `classB (2n+1)` gives it at `ansBound G x (2n+1)`; and `valStar_le_of_le` only *raises* the
   value with the bound, so `ansBound ≤ (2^n)^λ` — what `classA` needs, and what
   `exists_ansBound_le` proves — is exactly wrong here. One `λ` cannot satisfy both: the same
   `λ` is the parameter written into the output, so it is the same in the two conjuncts of
   `compr_spec`.

   The escape is `Verifier.valStar_eq_of_rejects`: if `x`'s decider rejects every answer longer
   than `ansBound G x (2n+1)` at index `2n+1`, then raising the bound does not move the value,
   and both directions go through the one inequality. That is not an accident — `ansBound` is
   *defined* to be the length beyond which a compressed decider of parameter `descLam x`
   rejects (`GapCompression.output_rejects_long`; the module docstring of `Instantiation.lean`
   says so), and in `compressibility_criterion_levels`'s recursion every level's string is the
   compressor's own output one level up, which the `hd` rewrite in the `hA`/`hB` branches makes
   explicit. So the criterion can supply it. It is not supplied now, and an arbitrary
   `descDec x` does not reject.

   This is recorded rather than repaired, and deliberately: unlike the length bound, the right
   *form* of the hypothesis is a design choice — "`x`'s verifier rejects beyond
   `ansBound G x (2n+1)`", or "`x = Compr (c', 2n+1)` for some `c'`", or a change to `ansBound`
   that takes the string out of it — and which one is cheapest is visible only once the
   construction exists. Settle it there. The confidence here is lower than for the length
   bound: that one was verified twice against a proof that already had the missing fact, this
   one is an argument about a construction that does not exist yet.

   **Finding 2, corroborated by the paper (2026-09-16, second reading).** The confidence caveat
   above can be dropped. The paper's `F` has the check *in its construction* — Step 6 of
   `fig:halt_f`: "Simulate `D^compr` on `(n,x,y,a,b)` if the input tuple has length at most
   `B_{D^compr}(n)` (if it has length exceeding this, reject)" — and the amended proof of
   `lem:dhalt-values` spends it exactly where the Lean gets stuck: "here we use that the answer
   alphabets may be identified, since any answer tuple of total length larger than
   `B_{D^compr}(n)` is rejected by both deciders". Ledger challenge `ch-0bb5ccf596ca5ec4` on
   node `1.6.3` recorded that fact as load-bearing. So rejection of long answers is a property
   `V^halt` has by construction in the paper, and the Lean's classes, ranging over arbitrary
   strings, lost it; `GapCompression.output_rejects_long` was added for this and bounds the
   compressor's *output*, while `compr_spec` needs it of the compressor's *input*. Of the three
   shapes listed above, one is right: **thread a well-formedness predicate through the
   criterion.** `compressibility_criterion_levels` gains `P : BitStr → ℕ → Prop` with
   `∀ m, P yYes m`, `∀ m, P yNo m` and `∀ c m, P (Compr (c, m)) m`, and `hCompr` gets
   `P x (2n+1)`; the proof has what it needs already — the functional equation `hdec`, which says
   every string of the recursion is `yYes`, `yNo` or `Compr (…, 2n+1)`, and on which the
   `hA`/`hB` branches case-split. The instantiation takes `P x m` to be "`(Vof G U x).decider`
   rejects every answer longer than `ansBound G x m` at index `m`": `yNo` rejects everything,
   `yYes` accepts only empty answers, and the output's decider runs a compressed decider, so
   `output_rejects_long` gives it. This is the alternative that `rem:compression-abstract`
   obligation (c) already names — "re-quantified over a `Compr`-closed class" — so the blueprint
   gets sharper, not longer. The other two shapes are worse: rejection in the classes reopens
   O3 (`sem_spec` would need a second `Σ₁` disjunct), and no change to `ansBound` can work,
   soundness living at the exponential bound `(2^n)^λ` that no polynomial answer bound reaches,
   while lowering a bound under `HasPerfectPCC` needs rejection as much as raising one under
   `valStar` does.

   **A fourth finding, from writing the consumer of the accounting before the program.** Every
   `IsBounded` witness so far — `ofSamplerDecider_isBounded`, hence O1 — is
   `∃ n₀, ∀ n ≥ n₀, IsBounded n` for a *fixed* program, with `HasPolyCost` quantifying its
   polynomial existentially. O4's decider depends on `(c, n)`, and `compr_spec` needs one `n₀`
   for all of them. So the cost lemma has to carry explicit constants depending only on `G` and
   `U`, with `2|c| ≤ n`, `|x| ≤ n + 1` and `descLam x < 2^(n+1)` as the only size inputs, and the
   absorption into `n'^n · (|d|+1)^n` has to be proved for every index `n' ≥ 2` — `n' = 2` and
   `n' < n` included — at `n ≥ n₀(G, U)`. The arithmetic closes: the degree in `|d|` is at most
   the constant `(G.deg + 1) · deg(U.bound)`, the coefficient is `poly(n, n')`, and
   `lambda_bound` absorbs both with its `lam` read as the level `n` and its `n` as the index
   `n'`. But it is a different *shape* from `HasPolyCost`, and `TimeBoundAt` has been revised
   three times by a first consumer of exactly this kind; state the cost lemma before writing the
   program. Two design choices fall out of the same check. `λ(n)` must be computed in binary in
   time `poly(|c| + log n)` — the compressor cannot write a unary numeral — so take
   `λ(n) := 2^(K + D · Nat.size n)`, a `1` followed by zeros, with `D` above the degrees of
   `G.samplerProg.timeBound` and `G.bound` and `2^K` absorbing the constants; it covers the
   frozen verifier's needs (`2^λ ≥ (2n+1)^(2n+1) + …`, `λ ≥ 2n+1`), and `(Vof x).size ≤ 2n+1`
   comes free from the size clause of `IsBounded (2n+1)`. The strings of the recursion are then
   of size `O(log n)` at level `n`, far under the `n + 1` bound and consistent with
   `descLam x < 2^(n+1)`.

   **Issue #77 does not block O4 mechanically, but it should be decided first.**
   `G.completeness` as stated *concludes* `HasPerfectPCC`, hence `IsSynchronousAt n` of the
   compressed decider, so O4 transfers it by `hasPerfectPCC_congr` without proving anything; the
   cost lands on chapter 6, which would have to prove of the pipeline's decider a property the
   paper never states, and nothing tracks it. Restating `HasPerfectPCC` on the doubled game
   removes the clause from `thm:compression`; it touches `GapCompression.lean`,
   `VerifierValue.lean`, `Freeze.lean`, `Classes.lean`, `SyncTransport.lean` and `Strings.lean`
   with the same proofs (`copy`, `relabel`), and doing it after O4 would reshape O4's transfer
   proof as well.

   **The plan, in pull requests** (each rebased onto `main` before merging, per §1):

   - **PR-0, the module move** — item 5 below. No mathematics.
   - **PR-1, statements first.** (a) #77: `HasPerfectPCC` on the doubled game, and blueprint
     `thm:compression` corrected at its "as the deciders of the pipeline do". (b) Finding 2: the
     predicate `P` through `compressibility_criterion_levels`; `compr_spec` gains the rejection
     hypothesis on `x`; a new field `compr_rejects : ∀ c n, RejectsLong G U (compr (c, n)) n`;
     blueprint `lem:compressible-criterion` and obligation (c) of `rem:compression-abstract`
     updated. (c) **The consumer, written first**: an abstract transfer theorem producing
     `Obligations G U` from three *named* hypotheses on a hypothetical program — acceptance
     agreement with `G.output` at index `n`, an explicit cost bound in `(n, n', |d|)`, and the
     growth of `λ(n)` — proving the class transfer once (`hasPerfectPCC_of_le` with
     `exists_ansBound_le`, `freeze_hasPerfectPCC`, `completeness`, `hasPerfectPCC_congr`;
     `valStar_eq_of_rejects`, `freeze_valStar`, `soundness`, `valStar_congr`;
     `freeze_isBounded` with `lambda_bound` for the boundedness) and pinning the exact statement
     the construction must meet. (a) and (b) change theorem statements in the blueprint and are
     the maintainer's decisions.
   - **PR-2, `Halting/Compressor.lean`, the program** — the module three toolkit docstrings
     already name. Sub-programs each with `_runs` lemmas, as `Wrapper.lean` does: the bit-query
     reading loop (`incProg` over the index, `U.univ` on the embedded `c`, stopping at the
     out-of-range marker of `bitQueryAnswer`), `parseProg`, the extraction of `(λ_x, dec_x)`,
     `dFreeze` (the `Data` form of `freezeProg`, `rfl` to `toData` as `dWrapCore_eq` is),
     `(sampP, decP)` from a run of `G.samplerProg.code` and `dWrapCore`, `G.compress.code`
     through `U`, and the compressed decider through `U` on the decider's own input. Forward
     runs and the inversion give the acceptance agreement. Expect `tabOf`'s elaboration
     trouble; build the term one declaration at a time.
   - **PR-3, the accounting** — explicit constants; `IsBounded λ(n)` of the frozen `Vof x` by
     `freeze_isBounded`; `(Vof (compr (c, n))).IsBounded n` uniformly for `n ≥ n₀(G, U)`;
     `λ(n)` computed in binary.
   - **PR-4, the assembly** — `compr` as a `PolyTimeFun` (`hardcode` of `(c, n, λ(n))` into the
     fixed program, then `serProg`), `compr_rejects`, PR-1's theorem applied, so that
     `halting_reduction` needs only `G`. Blueprint: `\lean{}` on `lem:halt-construction`,
     `lem:lambda` and `lem:dhalt-values` with a Comments paragraph on the route (no
     self-reference, freeze at `2n+1`, `λ(n)` explicit); #53 closed.
   - **PR-5, `thm:main` conditionally** — `halting_reduces_to_gameValue_of (G : GapCompression)`
     sorry-free through `gameValue_tab_eq_one` and
     `gameValue_toGame_le_of_valStar_le_doubled`; the unconditional statement keeps its `sorry`
     as the chapter-6 target, and the blueprint says so. After it the honest headline is
     *MIP\* = RE ⟸ `thm:compression`, machine-checked*: one structure is the whole remaining
     assumption, and `#print axioms` shows nothing else.

   Compare #57 and #64 for the scale of PR-2 and PR-3; together they are bigger than either.
   Read `recursive.tex` `sec:halt` and nodes `1.6.1`, `1.6.5` again before PR-2: this is the
   one obligation where the paper's construction is followed closely.
5. **PR-0, the module move.** Numbered last because it was found last; it comes *before* the
   rest of O4 in the doing, being what turns O1's and O3's discharges into a smaller
   `Obligations`. The structure and `halting_reduction` are at the end of
   `MIPRE/Foundations/Halting/Instantiation.lean`, and both `Halting/Semidecider.lean` — where
   `exists_sem` is — and `Halting/Strings.lean` — where `yYes_mem` and `yNo_mem` are — import
   that file, so `Obligations` sits *above* its own discharges and the seven O1 and O3 fields
   cannot be dropped where they stand. What moves: everything from `/-! ## The obligations -/`
   to the end of `Instantiation.lean` — the `Obligations` structure, `two_pow_iterate`,
   `primrec_two_pow`, the `attribute [local irreducible] tab` line and `halting_reduction` —
   into a new module *below* both, `MIPRE/Foundations/Halting/Reduction.lean`, importing
   `Halting.Semidecider` and `Halting.Strings`. Then drop O1's four fields and O3's three, and
   let `halting_reduction` obtain them from `yYes_mem G U`, `yNo_mem G U` and `exists_sem G U`,
   the criterion's threshold being the maximum of their two thresholds and `n₀`. `Obligations`
   is then `n₀`, `compr`, `compr_spec` — honestly O4, and the docstring of `Instantiation.lean`
   stops describing an assembly that is no longer in it. Then `lake exe mk_all`, which CI
   checks, and `scripts/lean-coverage.py --refresh`, since a module is added. Nothing else has
   to change: `MIPRE/Axioms.lean` guards `exists_sem_of_tab`, which stays in
   `Semidecider.lean`, and the blueprint's `\lean{}` tags resolve by name in the unchanged
   namespace `MIPRE.Halting`. It is a reorganization, not mathematics.

Each is one pull request, rebased onto `main` before merging, per the rule in §1.
