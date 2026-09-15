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
| ~~**O2**~~ | *Done 2026-09-15.* No longer a field: `tab`, `tab_computable`, `tab_match`, `tab_le` and `tab_value` are theorems of `Halting/Instantiation.lean`, over `Halting/Tabulate.lean` (`tabOf`, the `GameData` that two encoded programs and three numbers describe) and the new `Cost/ProgData.lean` (deciding program-hood). **Still owed to O3**: the doubled question set, so that the value agreement holds under `n`-boundedness alone (§4 item 3) | the doubling |
| **O3** | `sem_spec`: a program halting on `(x, n)` exactly when `x ∉ classB n` | *Mostly done 2026-09-15* (`Halting/Semidecider.lean`): both `Σ₁` disjuncts of `Verifier.not_inClassB_iff` are r.e. and merged, on the cost-budget decision procedure of `Halting/CostBudget.lean` and the pair-input semidecider of `Halting/Semidecide.lean`. What is left is two hypotheses of `Halting.exists_sem_of_tab`, both O2's: `Verifier.ComputablyPresented (Vof G U)`, and a tabulation whose value agrees with `val*` under `n`-boundedness **alone** — which `tab_match` does not give (see §3, the synchronicity seam) |
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
2. **O2.** *Mostly done 2026-09-15.* The largest piece, and needed twice, by O3 and by the
   assembly. `tab`, `tab_computable`, `tab_match`, `tab_le` and `tab_value` are theorems of
   `Halting/Instantiation.lean` and the four fields have left `Obligations`; §3 has the
   record. One step is left, and O3 below is what asks for it: **the doubled question set**,
   which makes the value agreement hold under `n`-boundedness alone. Writing the consumer
   first did not stop the statement moving three times, but it did keep every move on the
   statement side.
3. **O3.** *Mostly done 2026-09-15*, and it was not "short once O2 is done" — that was wrong
   in two ways, both worth keeping.

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
   - **`Primrec fun n : ℕ => (encode n : Data)` is missing**, natural numbers encoding in
     binary (`Nat.bits`). It is a prerequisite of `ComputablyPresented` for `Vof` — the
     sampler's dimension is read off a run of its program on `encode (n, dimension)` — hence
     of O2's `tab_computable` too, which runs the sampler at an index. `rePred_not_isBounded`
     itself avoids it by carrying the search's index as a *datum* and reading it back with
     `Data.natOf`, so the encoding it prepends is `Data.normBin` of the witness; that trick
     does not extend to a genuine `ℕ` argument.
4. **O4.** The second-largest, and the only one where the paper's construction is followed
   closely; read `recursive.tex` `sec:halt` and nodes `1.6.1`, `1.6.5` again before starting.

Each is one pull request, rebased onto `main` before merging, per the rule in §1.
