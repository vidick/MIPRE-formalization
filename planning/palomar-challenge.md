# The Palomar Challenge: draft and decision memo

Written 2026-09-28 against `2498541`, for phase 4 of `planning/palomar.md`. The draft is
`Palomar/Challenge.lean`: 414 lines, Mathlib-only imports, compiles with
`lake env lean Palomar/Challenge.lean` (Lean 4.33 / Mathlib v4.33.0) with exactly four
`sorry` warnings, one per compared theorem, and no error. It is outside the lakefile's globs
and is not listed in `MIPRE.lean`; nothing in `MIPRE/` was touched.

The rules it is written to (`planning/palomar.md`): every compared theorem stated with `sorry`;
every definition the statements need spelled out with a docstring; imports from Mathlib only;
warning above 300 lines, hard limit 1,000. The comparator matches `theorem_names` and
`definition_names` between the Challenge (compiled under a per-run namespace) and the
Solution, so the Solution must re-declare every Challenge definition identically and prove
the theorems about *those* declarations. This is what makes the choice of names load-bearing
(question 1 below).

## 1. What the draft states

Five parts, in the order asked, all in `namespace MIPRE.Palomar`.

1. **Games** (`Game X Y A B`): finite alphabets, a distribution `μ` on `X × Y` as a
   nonnegative real function summing to one, a decision predicate `D : X → Y → A → B → Bool`.
   Field for field this is `MIPRE.Game`. There is no separate `SynchronousGame` structure:
   the synchronous value is defined for any `Game X X A A`, and the synchronous veto is a
   property of the particular games the halting reduction outputs (part 3).
2. **Strategies and values**. `PVM X A d`: for each question, self-adjoint idempotent
   `d × d` complex matrices summing to the identity (`MIPRE.ProjectiveMeasurement` at
   `Matrix (Fin d) (Fin d) ℂ`). `TensorStrategy G`: dimensions `dA, dB`, a unit vector
   `ψ : Fin dA × Fin dB → ℂ`, a `PVM` for each player; `value` by the Born rule with the
   Kronecker product; `quantumValue G = ⨆ S, S.value` (`MIPRE.TensorProductStrategy`,
   `MIPRE.quantumValue`, same fields, same formula). `SyncStrategy G` for `G : Game X X A A`:
   `d > 0` and one `PVM`; `value` with `Tr(M^x_a M^y_b)/d`; `syncValue`. The value is exactly
   the formula of `MIPRE.SyncStrategy.value_eq` and of `HaltingGameValue.strategyValue`.
3. **Explicit games and the halting reduction**. `GameData`, `equivTuple`, the `Primcodable`
   instance, `questionWeight`, `totalWeight` are `HaltingGameValue`'s, verbatim. `toGame`
   is `HaltingGameValue.GameData.toGame` with the target `Game (Fin ..) (Fin ..) ..` in place
   of `SynchronousGame` (the veto `x = y ∧ a ≠ b → false` stays in `D`; the `synchronous`
   proof field is dropped). `HaltsOnEmptyInput c := (c.eval 0).Dom`. Theorems:
   `halting_reduces_to_value` (one computable map, both values, both directions),
   `syncValue_uncomputable`, `quantumValue_uncomputable`.
4. **RE**: `IsRE L := ∃ c : Nat.Partrec.Code, ∀ z, z ∈ L ↔ (c.eval (encode z)).Dom`.
5. **The class**: the tree-program model (`Data`, `Prog`, `WellScoped`, `Env.get`, `Eval`,
   `Prog.Runs`, `Prog.HaltsWithin`, verbatim from `MIPRE/Foundations/Cost/Basic.lean` and
   `PolyTime.lean`; the encodings `Data.ofBool`, `Data.ofBits` from `Encoding.lean`);
   `PolyVerifier` (two closed programs and a `Polynomial ℕ`), `B`, `SamplerOutputs`,
   `Accepts`, `Efficient` (verbatim from `ClassMIPStar.lean`, with `encode (z, r)` written
   out as `cons (ofBits z) (ofBits r)`); `Str n` (strings of length at most `n`), `Seed n`
   (`List.Vector Bool n`); `MIPStar L`; theorem `mipstar_eq_re : MIPStar = IsRE`.

Decisions taken in the draft, with the justification:

* **General games, not only synchronous ones.** The class is defined with a general bipartite
  game (`MIPRE.PolyVerifier.game` is a `Game` on four copies of `Answers (B z)`), so the
  Challenge needs `Game` and `quantumValue` on it anyway. The halting reduction's output is a
  synchronous game and the repository states its value both ways
  (`HaltingGameValue.halting_reduces_to_gameValue` in the synchronous value,
  `MIPRE.Halting.halting_reduction_quantum` in the quantum value); `halting_reduction_both_of`
  gives both for one map, so the Challenge states that. One structure `Game` serves all of it;
  the synchronous value is a second supremum on the same structure.
* **Tensor-product strategies, projective, finite-dimensional, all dimensions.** This is what
  `MIPRE.quantumValue` is. Commuting-operator strategies (`MIPRE.CommutingOperatorStrategy`,
  `commutingOperatorValue`) exist in the repository for the Tsirelson/Positivstellensatz
  side but the main theorems are about `quantumValue`; they are not stated.
* **The game of a verifier is characterized, not constructed.** `MIPStar` asks for a game `G`
  on `Str (B z)` whose `μ` is the seed count over `2 ^ B` and whose `D` is the decider's
  verdict, then the value conditions on `G`. The repository constructs `PolyVerifier.game`
  through `sample?` (a choice), a length check with a fallback `([], [])`, and `seedCount`
  over `Data.bitStrsOfLen`; under `Efficient z` the two agree and `G` is unique, so nothing
  is lost, and the Challenge carries no normalization proof and no fallback for the reader to
  audit.

## 2. Correspondence with the Lean

Each item is `Challenge declaration` — `Lean declaration it is proved from` — relation.

* `Game` — `MIPRE.Game` — same fields; a new structure, so a transport is needed.
* `PVM X A d` — `MIPRE.ProjectiveMeasurement X A (Matrix (Fin d) (Fin d) ℂ)` — same fields.
* `TensorStrategy`, `.value`, `quantumValue` — `MIPRE.TensorProductStrategy`, `.value`,
  `MIPRE.quantumValue` — same fields and the same formula.
* `SyncStrategy`, `.value`, `syncValue` — `MIPRE.SyncStrategy`, `SyncStrategy.value_eq`,
  `MIPRE.syncValue`, and `HaltingGameValue.gameValue` through
  `GameData.gameValue_eq_syncValue` — the same set of values; `MIPRE.SyncStrategy` is over a
  `SynchronousGame`, so the route goes through `GameData.syncGame`.
* `GameData`, `equivTuple`, `questionWeight`, `totalWeight` — `HaltingGameValue.GameData` and
  its namespace — verbatim.
* `GameData.toGame` — `HaltingGameValue.GameData.game` (= `syncGame.toGame`) — same `μ`, `D`.
* `HaltsOnEmptyInput` — `HaltingGameValue.HaltsOnEmptyInput` — verbatim.
* `halting_reduces_to_value` — `MIPRE.Halting.halting_reduction_both_of` at
  `GapCompression.ofAnswerReduction AnswerReduction.answerReduction` and `Cost.selfUniversal`
  — the unconditional instance; `MainTheorem.lean` exposes only the two halves.
* `syncValue_uncomputable`, `quantumValue_uncomputable` —
  `MIPRE.Halting.gameValue_uncomputable`, `quantumValue_uncomputable` — after rewriting the
  values.
* `IsRE` — `MIPRE.IsRE` (= `REPred (· ∈ L)`) — equivalent through
  `Nat.Partrec.Code.exists_code`; not verbatim.
* `Data`, `Data.size`, `Prog`, `Prog.WellScoped`, `Env`, `Env.get`, `Eval` — `MIPRE.Cost.*`
  (`Cost/Basic.lean`) — verbatim text, new inductive types.
* `Data.ofBool`, `Data.ofBits` — `MIPRE.Cost.Data.ofBool`, `Data.ofList ofBool`
  (= `encode : BitStr → Data`) — verbatim.
* `Prog.Runs`, `Prog.HaltsWithin` — `MIPRE.Cost.Prog.Runs`, `MIPRE.Cost.HaltsWithin` — verbatim.
* `PolyVerifier`, `.B`, `.Accepts`, `.Efficient` — `MIPRE.PolyVerifier`, `.B`, `.Accepts`,
  `.Efficient` — verbatim, with `encode (z, r)` written out as `cons (ofBits z) (ofBits r)`.
* `SamplerOutputs z r x y` — `∃ t, sampler.Runs (encode (z, r)) (encode (x, y)) t`, i.e.
  `sample? z r = some (x, y)` (`sample?_eq_some_iff`) — the same proposition.
* `Str n` — `MIPRE.Verifier.Answers n` — the same subtype; `Fintype` by `Fintype.ofFinite`
  in both.
* `Seed n` — `Data.bitStrsOfLen n` (a nodup list of the same strings) — a count to identify.
* `MIPStar` — `MIPRE.MIPStar` — equivalent; the game is characterized here and constructed
  there (`PolyVerifier.game`, `game_μ`, `game_D`, `questions_eq_of_efficient`).
* `mipstar_eq_re` — `MIPRE.Halting.mipstar_eq_re` — after `MIPStar L ↔ MIPRE.MIPStar L` and
  `IsRE L ↔ MIPRE.IsRE L`.

Not stated, deliberately: `MIPStarComputable` (the computable class, `def:mipstar-computable`)
and `mipstarComputable_eq_re`; `syncValue ≤ quantumValue`; the commuting values; the
inclusions `re_subset_mipstar` / `MIPStar.isRE` separately from the equality.

## 3. Polynomial time: the candidates

Mathlib has no polynomial-time class. The crux is the trade between how crisp the Challenge
definition is for an auditor and how large the Solution-side bridge from the repository's
`MIPStar` is. Everything the repository proves about time is in the model of
`Cost/Basic.lean` (`Prog`, `Eval`), through `PolyTimeFun` and its closure library; the class
verifier of `Halting/Paper/ClassVerifier.lean` is two `Prog`s with explicit cost polynomials.

### (a) Restate the repository's `Prog`/`Eval` model — recommended, and what the draft does

*Challenge.* 105 lines with docstrings (`Data` 20, `Prog` 25, `WellScoped` 12, `Env` 5,
`Eval` 22, `Runs`/`HaltsWithin` 6, encodings 12). A first-order language over binary trees
with seven constructs and a ten-rule timed big-step semantics; the one non-obvious point, that
reading a value costs its size, is stated in the docstring together with its consequence
(a run of cost `t` builds a result of size at most `t`) and the reason it is honest (a pointer
machine runs it in time `O(t)`). An auditor can read the whole model.

*Fidelity.* Polynomial time in this model is the standard class, by the pointer-machine
simulation of `Cost/Basic.lean`'s meta-remark, which is **not formalized**. The paper says
"Turing machine running in time `poly(|z|)`"; this must go into `formalization.yaml` under
`fidelity.divergences`. Two further readings are inherited from `MIPRE.MIPStar` and copied:
time bounds in the *total* input length with the paper's footnote (rejection of overlong
messages) as a separate clause, and a randomized machine as a deterministic program with an
explicit seed of length `B` (blueprint text after `def:mipstar`).

*Solution bridge.* The Challenge's `Data`, `Prog`, `Eval` are new inductive types, so the
Solution maps them to `MIPRE.Cost.*` (structural maps in both directions, `size` preserved,
`ofBits z = encode z`), proves `Eval env p r t ↔ Cost.Eval` by induction on derivations, both
ways (about 80 lines), transports `WellScoped` (20), then `PolyVerifier`/`Efficient`/
`Accepts`/`SamplerOutputs` (50). Everything is mechanical. **If the Challenge instead uses the
repository's own names for this part** (`MIPRE.Cost.Data`, `MIPRE.Cost.Prog`, `MIPRE.Cost.Eval`,
… — `Cost/Basic.lean` is already Mathlib-only, so the text can be identical), the comparator
sees the same inductives and this whole bridge disappears; see question 1.

### (b) Mathlib's `Turing.FinTM2` with `TM2ComputableInPolyTime`

`Mathlib.Computability.TuringMachine.Computable` (the former `TMComputable.lean`) bundles a
TM2 stack machine with finiteness conditions (`FinTM2`), `TM2OutputsInTime tm l l' m`
(reaches the halting configuration within `m` applications of `step`), and
`TM2ComputableInPolyTime ea eb f` with a `Polynomial ℕ` bound in `(ea a).length`.

*Challenge.* About 35 lines: a verifier is two `FinTM2` with input/output alphabets `≃ Bool`
(or a finite alphabet with a separator, since the input is a pair of strings), a polynomial,
and the efficiency clause is `TM2OutputsInTime` on the encoded input. Crisp only for a reader
who already knows Mathlib's TM2 (finitely many stacks, statements `push/pop/peek/load/branch/
goto/halt` over a finite internal state, one `step` per statement — which Mathlib itself notes
is "up to a constant" the fundamental step count). `TM0` (single tape, `Turing.TM0.Machine`)
is more classical and equally short, but Mathlib has no time notion for it at all; one would
iterate `TM0.step` by hand.

*Solution bridge.* Two pieces, neither started. (i) `RE ⊆ MIPStar_TM2` needs a compiler from
`Prog` to `FinTM2` with a polynomial time bound, applied to `sampProg`/`decProg`. Nothing of
the kind exists: the repository's TM track (`MIPRE/TM`, 23k lines) targets its own multi-tape
model `MIPRE.TM.MultiInput`, its interpreter `TM/Interp` runs a bespoke instruction set rather
than `Prog`, Milestone H1 of `planning/tm-infrastructure.md` (compile `Prog` to `Code i` with
time bounds) was never done, and the universal-machine issues #17/#18 were closed as not
planned. Trees on stacks, `elim` and `var` copies with the right cost, a `loop` — several
thousand lines. (ii) `MIPStar_TM2 ⊆ RE` needs the tabulation to be `Computable`: iterate
`tm.step` `P(n)` times on encoded configurations. Mathlib proves only the converse direction
(`ToPartrec`: partial recursive functions are TM2-computable); `FinTM2`'s `Λ`, `σ`, `Γ k` are
arbitrary `Type`s with `Fintype` only, so a `Primcodable` encoding of `tm.Cfg` and the
computability of `step` are new (500–1,000 lines). Months of work in total; the most standard
definition and by far the largest bridge.

### (c) `Nat.Partrec.Code` with a time notion

Not viable, and `Cost/Basic.lean`'s decision record says why: its primitives reach large
values only through `succ` chains, value-indexed `prec` and `rfind`, and `Nat.pair` is
quadratic, so under any step-count semantics `n ↦ 2n` on binary inputs is not polynomial and
nested pairs blow lengths up exponentially; `evaln`'s fuel counts unfoldings, not time. The
same record rules out `Turing.ToPartrec.Code` (Mathlib's list language): it cannot rebuild
lists, so `List.reverse` and binary addition are not polynomial there. Both remain fine as
the model of the *computability* statements, which is how the draft uses `Nat.Partrec.Code`.

### (d) Boolean circuits, uniform families; Cobham's function algebra

*Circuits.* A verifier as a family `C_n` of circuits of size `≤ P(n)` with random input bits.
Crisp (40 lines) but the uniformity condition needs a machine: polynomial-time uniformity is
circular, and mere `Computable` uniformity defines a different class in the letter of the
definition (the same languages, but that is a theorem to prove, not a definition to audit).
The bridge would be a `Prog`-run-to-circuit compiler; the repository's succinct Cook–Levin
(`MIPRE.SAT.SuccinctCookLevin`) produces satisfiability tableaux of bounded `Prog` runs, not
circuits computing the decider, so it does not shortcut this. Not recommended.

*Cobham.* The machine-independent characterization of FP: the least class of functions
`List Bool → List Bool` containing the basic functions and closed under composition and
bounded recursion on notation. About 30 lines, genuinely crisp and classical, and its
equivalence with TM polynomial time is a textbook theorem (Cobham 1965). The bridge is again a
simulation: every `PolyTimeFun` is Cobham-definable (serialize `Machine.stepData`, iterate it
`P(|x|)` times by bounded recursion — compositional proofs in the style of Mathlib's `Primrec`,
1–3k lines), plus Cobham ⊆ `Computable` (150 lines) for the other inclusion. Months, though
fewer than (b). The principled upgrade if machine-independence is wanted later.

### Recommendation

(a). It is the only candidate whose Solution bridge is bounded and mechanical (weeks, or
nothing at all with the repository's names), it states exactly what the Lean checks, and the
model is small enough to be audited in full inside the Challenge. Its cost is one declared
divergence — the class is "polynomial time in the tree-program model", equivalent to the
Turing-machine class by an unformalized standard simulation — which is honest and which
Palomar's metadata has a field for. (b) or the Cobham variant of (d) can replace it in a later
submission without changing parts 1–4.

## 4. Where the crisp definition differs from what the repository proves — questions

Each is answerable in one line.

1. **Names.** The draft is free-standing in `MIPRE.Palomar`, so every definition is a new
   declaration and the Solution bridges by transport (section 5). Alternatively the verbatim
   parts keep the repository's names (`MIPRE.Cost.{Data,Prog,Eval,…}`, `MIPRE.Game`,
   `MIPRE.quantumValue`, `HaltingGameValue.{GameData,HaltsOnEmptyInput}`) so the Solution
   imports them and the comparator sees identical declarations — zero bridge for those,
   at the price of a namespace-mixed Challenge. Which?
2. **Both values in one theorem.** `halting_reduces_to_value` gives one map with the
   synchronous and quantum values, from `halting_reduction_both_of`; `MainTheorem.lean`
   exposes the two halves separately. Keep the combined form, or mirror the two theorems?
3. **Synchronous strategies as PVMs.** `syncValue` is over `SyncStrategy` with a `PVM`
   (`MIPRE.SyncStrategy`'s packaging), not `HaltingGameValue.SyncStrategy`'s POVM with a
   projectivity certificate. Same suprema (`GameData.gameValue_eq_syncValue`). Acceptable?
4. **No `SynchronousGame` structure.** `GameData.toGame` is a general `Game` with the veto in
   `D`; `syncValue` is defined for any `Game X X A A`. The synchronicity of the halting games
   is then a fact about `toGame`, not a type. Acceptable, or restore the structure (+15 lines)?
5. **`IsRE` through `Nat.Partrec.Code`** rather than Mathlib's `REPred (· ∈ L)`
   (`MIPRE.IsRE`). Equivalent via `Nat.Partrec.Code.exists_code`, about 25 lines. Prefer
   `REPred` verbatim (zero bridge, one more Mathlib name for the reader)?
6. **The time model** is candidate (a), with the divergence recorded in
   `formalization.yaml` as stated in section 3. Agreed?
7. **The verifier's game is characterized** (`∃ G` with `μ` and `D` pinned) rather than
   constructed as in `PolyVerifier.game` (with `sample?` and the fallback). Under
   `Efficient z` it is the same unique game. Acceptable, or construct it (+30 lines, a
   normalization proof, `open Classical` choice)?
8. **Time in the total input length**, plus `rejects_long`, is copied from `MIPRE.MIPStar`
   and the blueprint's reading of the paper's `poly(|z|)`. Keep the reading, and is the
   docstring's one-sentence justification enough for a reviewer?
9. **Seeds and alphabets.** `Seed n = List.Vector Bool n` and `Str n = {s // s.length ≤ n}`
   with a noncomputable `Fintype`; the repository uses `Data.bitStrsOfLen n` and
   `Verifier.Answers n`. Acceptable?
10. **Closedness** (`sampler_closed`, `decider_closed : WellScoped 1`) is kept as in
    `MIPRE.PolyVerifier`. Dropping it would not change the class but would cost a
    re-scoping lemma in the bridge. Keep?
11. **Compared theorems.** Four: `halting_reduces_to_value`, `syncValue_uncomputable`,
    `quantumValue_uncomputable`, `mipstar_eq_re`, and nothing else. Add the two inclusions
    `RE ⊆ MIP*` and `MIP* ⊆ RE` as separate theorems, or `syncValue ≤ quantumValue`?
12. **Length.** 414 lines, above the 300-line warning and well under the limit. The only
    substantial cut is the synchronous part (−30) or the `toGame` normalization proof (which
    cannot go: a `sorry` in a definition would poison every theorem). Accept the warning?
13. **`MIPStarComputable`** (the computable class) is not in the Challenge. The paper's class
    is the headline; is the computable class wanted as a second compared statement?
14. **`Fintype (Str n)` and the `decide` in `MIPStar`** are noncomputable/classical. Harmless
    in a `Prop`, but a reviewer may ask; fine?

## 5. Solution-side work, per compared theorem

Assuming the free-standing names of the draft (question 1 answered "free-standing"). With the
repository's names for the verbatim parts, the transport rows vanish and the rest halves.

* Games and values (60–80 lines): `Palomar.Game ≃ MIPRE.Game`; `PVM ≃ ProjectiveMeasurement`
  at matrices; `TensorStrategy ≃ TensorProductStrategy` with `value` equal by `rfl` after
  unfolding; `quantumValue` equal by `iSup` over the equivalence.
* Synchronous value (50–70): `SyncStrategy ≃ MIPRE.SyncStrategy (GameData.syncGame g)`;
  `SyncStrategy.value_eq`; then `GameData.gameValue_eq_syncValue` to reach
  `HaltingGameValue.gameValue`.
* `halting_reduces_to_value` (20): instantiate `halting_reduction_both_of` at
  `GapCompression.ofAnswerReduction answerReduction` and `Cost.selfUniversal`, rewrite both
  values.
* The two uncomputability theorems (30): from `MIPRE.Halting.gameValue_uncomputable` and
  `quantumValue_uncomputable`, rewriting the values inside the `∀ d`.
* `IsRE` (25): `IsRE L ↔ REPred (· ∈ L)` through `Nat.Partrec.Code.exists_code` and `Partrec`
  on `Part.assert`.
* The cost model (120–160): maps `Data ↔ Cost.Data`, `Prog ↔ Cost.Prog`, `size`,
  `ofBits = encode`, `WellScoped`, and `Eval ↔ Cost.Eval` by induction both ways.
* Verifiers (50): `PolyVerifier ↔ MIPRE.PolyVerifier`, `B`, `Accepts`, `Efficient`,
  `SamplerOutputs ↔ sample? = some` (`sample?_eq_some_iff`, `Eval.deterministic`).
* The game (80–100): given `Efficient z`, `(V.game z).μ` equals the `List.Vector` seed count
  over `2 ^ B` (`game_μ`, `seedCount`, `questions_eq_of_efficient`, a bijection between
  `List.Vector Bool B` and the members of `bitStrsOfLen B`), `D` equal by `game_D`;
  `Str (B z)` against `Answers (B z)` by `quantumValue_eq_of_equiv` with identity equivalences.
* `MIPStar L ↔ MIPRE.MIPStar L` and `mipstar_eq_re` (40): both directions from the rows
  above, then `MIPRE.Halting.mipstar_eq_re` and `funext`.

Total: roughly 450–600 lines, all mechanical, nothing mathematical; about a week. The
Solution imports `MIPRE.MainTheorem` (the whole library, 44 minutes cold; the Palomar runner's
budget is 19,800 s, so phases 1–3 of `planning/palomar.md` — toolchain, module headers, the
71k-line split — come first).
