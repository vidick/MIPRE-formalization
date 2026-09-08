# Compression track — the abstract recursive compression theorem (K0–K5)

## Context

Goal: make the abstract recursive compression theorem of Marks–Nezhadi–Yuen ("The
recursive compression method for proving undecidability results", [MNY]; Lemma 3.1 and
its parameterized variant Lemma 5.1) an **early, sorry-free result** of the project, in
the ambient cost model, *ahead of* the universal-machine construction. User decision
2026-09-08. The TM-infrastructure roadmap (`planning/tm-infrastructure.md`) is
re-sequenced accordingly: its Milestones E–G now follow this track, and serve (among
other things) one of the two routes to the universal machine (see the gate below).

Why this can be early: the proof of [MNY, Lemma 3.1/5.1] uses only the *statements* of
the efficient universal machine, efficient s-m-n and efficient Kleene recursion
([MNY, Lemmas 2.1–2.3]) — never their constructions. In this repo those statements
already exist, sorried, in `MIPRE/Foundations/Cost/Toolkit.lean`, and the compression
lemma is stated in `MIPRE/Foundations/Compression.lean`
(`MIPRE.Cost.recursive_compression`; blueprint `lem:recursive-compression`, which the
blueprint itself calls "an ideal early milestone", `\effortEasy` given the toolkit).

### Verified facts (checked 2026-09-08 against the repo at `fbbc27e` and the paper)

1. **Existing Lean statements, all sorried (initial commit 2026-07-22).**
   - `Cost/Basic.lean`: `TimedEval` (unit-cost big-step semantics of
     `Turing.ToPartrec.Code`) with `sound`/`complete`/`deterministic`/`pos`/`length_le`
     (5 sorries, routine except `complete` for `fix`, which needs induction on the
     `PFun.fix` approximation); `HaltsWithin`, `TimeBound`.
   - `Cost/Encoding.lean`: `SizedEncoding` (bounded cells, `decode ∘ encode = id`),
     `BitStr`, binary `ℕ`, length-additive pairing `encode (a, b) = encode a ++ sep :: encode b`
     (9 routine sorries).
   - `Cost/PolyTime.lean`: `PolyTimeFun α β` bundling `toFun`, `code`, `timeBound :
     Polynomial ℕ` (data) and `computes`; only `id` and `comp` — **no closure library**.
   - `Cost/Toolkit.lean`: `Code.size`/`encodeList`/`decodeList` (the latter a sorried
     `def`), `SizedEncoding Code`, `hardcode` (s-m-n; `hardcode_eval` proved),
     `hardcode_size`/`hardcode_time`/`hardcode_time_rev`, `smn_polyTime`,
     `exists_efficient_universal`, `exists_clocked_universal` (+ `evalWithin`),
     `efficient_fixed_point`.
   - `Foundations/Compression.lean`: `bitQueryAnswer`, `IsSuccinctDesc`,
     `recursive_compression`, and the Mathlib bridges `Primcodable Code`,
     `PolyTimeFun.toFun_computable`, `exists_compile`, `recursive_compression_halting`
     (5 sorries). `MIPRE/HaltingGameValue.lean` consumes the `Nat.Partrec.Code` form.
2. **Fidelity to [MNY].** `recursive_compression` is Lemma 5.1 (the `max{f(x), n}`
   variant; conclusion: a `PolyTimeFun Code BitStr` reduction `g` with `e` halts on the
   empty input ⇒ `g e ∈ A`, otherwise `f (g e) = ⊤`). `IsSuccinctDesc c n x` is
   Definition 2.4 with the runtime bound `(n + 1) * (Nat.size m + 1)` in place of the
   paper's "≤ n for all m" (the file's departure note: a model that charges to read `m`
   makes the paper's bound vacuous for `|m| > n`; the product form is what the bit-query
   program achieves — see K3). The toolkit statements are Lemmas 2.1–2.3.
3. **What the proof consumes** ([MNY] §3 and §5, read against `Toolkit.lean`):

   | proof step | toolkit clause |
   |---|---|
   | program `a`: "run `e` on the empty input for `log n` steps" | clocked universal machine with budget `k = Nat.size n` |
   | `b(c, e, n)`: the bit-query program, assembled *at runtime* by `a` | runtime s-m-n (`smn_polyTime`) + unbounded universal machine (to evaluate `φ_c(e, n)`) |
   | `(b(c, e, n+1), n)` is a succinct description of `h(e, n+1)` for `n ≥ r(e)` | `hardcode_time` (forward transfer) + the overhead polynomials, so that `r(e) = 2^{q(|e|)}` is polynomial-time computable |
   | closing the self-reference `φ_c = φ_{s(a,c)}` | `efficient_fixed_point` applied to `F c' = hardcode a (encode c' ++ [sep])` |
   | the fixed point `c` runs in polynomial time | Kleene's clause "runs of `F e` bound runs of `e`" — and *only* that direction |
   | `g(e) = φ_c(e, r(e))` is a `PolyTimeFun` | closure library: `comp`, `pair`, `const`, size and `2^q` arithmetic |

4. **Blueprint state.** `lem:universal-tm` carries
   `\lean{MIPRE.Cost.exists_efficient_universal, MIPRE.Cost.exists_clocked_universal}`
   and `\uses{lem:bounded-universal-machine}` (the machine-level bounded UTM of the TM
   track). `lem:smn`, `lem:kleene` and `lem:recursive-compression` carried **no
   `\lean{}` tags** although their statements exist — added in K0, so the sorries beneath
   the compression theorem are all blueprint-tracked (CONTRIBUTING's sorry policy).
5. **Not consumed.** The TM track's Milestones A–D (`MultiInputTM`, `Code i`,
   serialization, evaluator) play no role in the ambient compression lemma; they matter
   here only as route α to the universal machine.

## Fixed decisions

- **K-D1 — prove from statements, discharge later.** `recursive_compression` is proved
  from the toolkit *statements*. The sorries beneath it are then exactly the
  blueprint-tracked nodes `lem:universal-tm` and `lem:kleene`; after K4, only
  `lem:universal-tm`. No new sorry is ever introduced outside those nodes.
- **K-D2 — universal machines as data, existence as the sorried node** (K0, done).
  `UniversalMachine` and `ClockedUniversalMachine` are structures bundling the program,
  its overhead polynomial and the semantic clauses; `exists_efficient_universal` /
  `exists_clocked_universal` are `Nonempty` statements (same names as before, so the
  blueprint tags stay valid). Downstream definitions (pipeline deciders that simulate
  other deciders under a budget; the λ-bookkeeping of [JNVWY, §12.2]) refer to the
  fields of an obtained machine; no `def` is ever sorried — the same principle as
  decision D13 of the TM plan. The construction chosen at the gate later provides honest
  terms.
- **K-D3 — Kleene stated in the used direction only** (K0, done).
  `efficient_fixed_point` asserts `e.eval = (F e).eval` and "runs of `F e` bound runs of
  `e`" with polynomial overhead. [MNY, Lemma 2.3] states polynomial *equivalence*; the
  converse direction is unused by the compression argument and is *not* derivable from
  an upper bound on the simulator's time. It is restorable by adding a "simulation is
  never faster than the simulated run" clause to `UniversalMachine` should a consumer
  ever need it; until then the universal-machine obligation stays minimal.
- **K-D4 — runtime s-m-n generic in the hardcoded type** (K0, done).
  `smn_polyTime α sep : ∃ S : PolyTimeFun (Code × α) Code, ∀ c a, S (c, a) = hardcode c
  (encode a ++ [sep])` for any `SizedEncoding α` (the proof hardcodes programs and
  `(Code × ℕ)` tuples, not bit strings). With `sep = pairSep α β` this is hardcoding the
  first pair component: `hardcode_pair_eval` (proved) gives
  `(hardcode c (encode a ++ [pairSep α β])).eval (encode b) = c.eval (encode (a, b))`.
- **K-D5 — succinctness bound stays `(n + 1) * (Nat.size m + 1)`** until
  `thm:compression` is stated (design knob inherited from `Compression.lean`; whatever
  is chosen must be what the compression theorem for games certifies about its output
  verifiers).
- **K-D6 — two-layer closure library, shared infrastructure.** A *program layer* on
  `Code` (combinators with `TimedEval` time-transfer lemmas, usable for programs whose
  correctness is only conditional — the bit-query program `β` runs an arbitrary input
  program through the universal machine and cannot be a total `PolyTimeFun`), and a
  *function layer* of `PolyTimeFun` combinators with explicit `timeBound` polynomials
  on top. Both live under `MIPRE/Foundations/Cost/` (a `Cost/Closure/` directory once
  they outgrow `PolyTime.lean`) and follow the interface fixed in `PolyTime.lean`.
  Everything built here is R1 infrastructure the pipeline needs anyway.
- **Policy.** Every WP is one commit on the working branch; `lake build` green;
  `lake exe mk_all` whenever a file is added; sorry-free except the blueprint-tracked
  nodes; Mathlib style, docstrings on every declaration (CONTRIBUTING). Blueprint
  `\leanok` (with proof text) is added to a node in the WP that proves it.

## Roadmap

| WP | Content | Status |
|---|---|---|
| **K0** | Statement audit and fixes: this document; `UniversalMachine`/`ClockedUniversalMachine` (K-D2); one-directional Kleene (K-D3); generic `smn_polyTime` + `pairSep`/`encode_prod`/`hardcode_pair_eval` (K-D4); blueprint `\lean{}` tags on `lem:smn`, `lem:kleene`, `lem:recursive-compression`; TM roadmap re-sequenced | ✅ 2026-09-08 |
| K1 | Foundations hygiene: the ~24 routine sorries of `Cost/Basic|Encoding|PolyTime|Toolkit` incl. the sorried `def decodeList`; **efficient s-m-n sorry-free at program level** | ☐ |
| K2 | Minimal closure library (two layers, K-D6) + `smn_polyTime` + the fixed programs of the proof as `PolyTimeFun`s | ☐ |
| K3 | **`recursive_compression` proved** from the toolkit statements; blueprint `\leanok` + proof text on `lem:recursive-compression` (and on `lem:smn`) | ☐ |
| K4 | `efficient_fixed_point` from `UniversalMachine` + s-m-n ([MNY, Lemma 2.3]); `lem:kleene` `\leanok` | ☐ |
| K5 | Mathlib bridges (`Primcodable Code`, `PolyTimeFun.toFun_computable`, `exists_compile`) → `recursive_compression_halting` sorry-free modulo `lem:universal-tm`; independent of K2–K4 | ☐ |
| gate | Universal machine: route α (TM Milestones E–G + bridge H) or route β (self-interpreter in `ToPartrec.Code`) — **decide after K3**, record in `planning/tm-infrastructure.md` | ☐ |

Milestones reached along the way: after K1 the efficient s-m-n (program level) is
sorry-free; after K3 the abstract compression theorem is sorry-free modulo two
blueprint nodes; after K4 modulo the universal machine only; after K5 the same holds
for the halting-problem corollary consumed by `MIPRE.HaltingGameValue`.

---

## K1 — foundations hygiene

Discharge, file by file, without changing any statement:

- `Cost/Basic.lean`: `TimedEval.sound` (induction on the derivation against
  `Code.eval`; `fix` via `PFun.fix` unfolding), `TimedEval.complete` (induction along
  `Code.eval`; for `fix`, induction on the `PFun.fix` approximation — the one non-trivial
  item), `deterministic`, `pos`, `length_le`.
- `Cost/Encoding.lean`: the six instance obligations, `esize_nat`
  (`Nat.size_eq_bits_len`), `vsize_encode_le`, `esize_le_vsize_encode`.
- `Cost/PolyTime.lean`: `esize_apply_le` (from `TimedEval.length_le`), `id.computes`,
  `comp.computes`.
- `Cost/Toolkit.lean`: `encodeList_length`; **implement** `decodeList` (tag-directed
  structural parser; fuel-structural so that `decide`-style tests work, as in the TM
  codec) with `decode_encode`; `cells_le_bound`; `hardcode_size`, `hardcode_time`
  (run `pushList l` then the given run), `hardcode_time_rev` (invert the `comp` rule).

**Acceptance:** `grep -rn sorry MIPRE/Foundations/Cost` lists exactly `smn_polyTime`,
`exists_efficient_universal`, `exists_clocked_universal`, `efficient_fixed_point`.

## K2 — closure library and the programs of the proof

Program layer (`Code`, relational; each with a `TimedEval` lemma of the form "a run of
the parts yields a run of the whole with cost ≤ …"): sequential `comp` (exists as the
`TimedEval.comp` rule), `hardcode`/`pushList` (exist), suffix append (`encode a ↦ encode
(a, b₀)` for a constant `b₀`), first/second projection of a pair encoding (scan to the
separator: recursion on notation via `fix`), branch on the head cell (`Code.case`), head
cell to unary, `Nat.size` of a binary number (list length), binary decrement, and
bit-indexing `bitQueryAnswer` (walk the string while decrementing the binary index —
time `O(|y| · |m|)`, which is where the product form of `IsSuccinctDesc` comes from),
`2 ^ q(n)` in binary for a polynomial `q` given as data (a program `polyProg :
Polynomial ℕ → Code`, `noncomputable` only because `Polynomial ℕ` is).

Function layer (`PolyTimeFun`): `ofCode` (bundle a program with a proved bound),
`const`, `pair`, `fst`, `snd`, `ite` on a `Bool`, plus the two derived from the
universal machines: `haltsWithin (UT) : PolyTimeFun (Code × ℕ) Bool` with `toFun (e, n)
= (evalWithin e [] (Nat.size n)).isSome` (assemble `k :: (encode e ++ [SEP])`, run
`UT.univT`, read the head cell), and the s-m-n witness of `smn_polyTime` (this WP
proves it: emit `4 :: encode c ++ encode (pushList (encode a ++ [sep]))`, linear in
the input).

**Acceptance:** `smn_polyTime` proved; the combinators above with `computes` proofs;
`grep sorry` adds nothing outside the two universal-machine nodes and Kleene.

## K3 — the compression theorem

Proof plan for `recursive_compression` (paper §5, in repo terms). Obtain
`U : UniversalMachine`, `UT : ClockedUniversalMachine` and the s-m-n witnesses from the
statements. All programs below are built from K2.

1. **Bit-query program `β` (program layer, conditional correctness).** On input
   `encode (((c', e), n), m)`: run `U.univ` on `encode c' ++ SEP :: encode (e, n)`
   to obtain `y`, then output the single cell `[bitQueryAnswer y m]`. Lemma: if
   `c'` halts on `encode (e, n)` with output `encode y` at cost `t`, then `β` halts
   on that input with output `[bitQueryAnswer y m]` within
   `Q(|c'| + |e| + Nat.size n + t) · (Nat.size m + 1)` for a fixed polynomial `Q`.
   `β` is *not* a `PolyTimeFun` (its input `c'` may diverge); this is why K-D6 has a
   program layer. `b c' e n := hardcode β (encode ((c', e), n) ++ [sep])`, and
   `(b c' e n).eval (encode m) = β.eval (encode (((c', e), n), m))` by
   `hardcode_pair_eval`.
2. **Decider `a` (function layer, total).** `decFun : PolyTimeFun (Code × (Code × ℕ))
   BitStr` with `toFun (c', (e, n)) = if haltsWithin (e, n) then y₀ else
   Compr ((S (β, ((c', e), n + 1)), n), n)`; its `computes` field *is* the
   correctness of the program `a := decFun.code`.
3. **Self-reference.** `F : PolyTimeFun Code Code`, `F c' = hardcode a (encode c' ++
   [pairSep Code (Code × ℕ)])` (K2); `obtain ⟨c, p, hc_eval, hc_time⟩ :=
   efficient_fixed_point F`. Then `c.eval (encode (e, n)) = a.eval (encode (c, (e, n)))`
   (`hardcode_pair_eval`), so `c.eval (encode (e, n)) = pure (encode (h e n))` where
   `h e n := decFun (c, (e, n))` — a plain definition, all recursion is inside `c`.
   Time: by `hc_time`, `hardcode_time` and `decFun.computes`, `c` runs on
   `encode (e, n)` within `P (|e| + Nat.size n)` for a polynomial `P`.
4. **Threshold `r`.** Arithmetic lemma (`Nat.size`/`Nat.log` estimates): for a
   polynomial `Q` there is a polynomial `q` with `n ≥ 2 ^ q(|e|) → Q(|e| + Nat.size n)
   ≤ n + 1`. Define `r e := 2 ^ q(|e|)` (a `PolyTimeFun Code ℕ`: `|e|` is the input
   length; the output is `q(|e|)` zero bits then a one). For `n ≥ r e`:
   `|h e (n + 1)| ≤ 2 ^ n` (output length ≤ input length + cost, `TimedEval.length_le`)
   and `IsSuccinctDesc (b c e (n + 1)) n (h e (n + 1))` (step 1 with `c' = c`, `t ≤ P`).
5. **Reduction `g := c ∘ (e ↦ (e, r e))`** as a `PolyTimeFun Code BitStr` via
   `ofCode`, `pair`, `comp`; `g e = h e (r e)`.
6. **Non-halting `e`.** For every `n`, `haltsWithin (e, n) = false`, so `h e n =
   Compr ((b c e (n + 1), n), n)`; for `n ≥ r e`, `hCompr` gives `f (h e n) ≥
   max (f (h e (n + 1))) n`; by induction on `k`, `f (h e n) ≥ n + k` for all `k`, hence
   `f (h e n) = ⊤` (`ENat`: `eq_top_of_forall_nat_le`-style lemma). With `n = r e`:
   `f (g e) = ⊤`.
7. **Halting `e`.** `TimedEval.complete` gives a cost `T`; for `Nat.size n ≥ T`
   (`n ≥ 2 ^ T`) `h e n = y₀ ∈ A`. Downward induction (`Nat.decreasingInduction`) from
   `N := max (r e) (2 ^ T)` to `r e`: if `haltsWithin (e, n)` then `y₀ ∈ A`, else
   `h e n = Compr ((b c e (n + 1), n), n) ∈ A` by `hCompr.2` from `h e (n + 1) ∈ A` and
   the succinct description of step 4. Hence `g e = h e (r e) ∈ A`.

Statement-level adjustments allowed in this WP (record them here when made): the
output cell of `β` may be typed through a `SizedEncoding (Fin 3)` instance
(`encode i = [i.val]`) so that `bitQueryAnswer` can be a `PolyTimeFun` output on the
conditional branch; `IsSuccinctDesc` stays as is (K-D5).

**Acceptance:** `recursive_compression` sorry-free; `#print axioms` shows no `sorryAx`
beyond `exists_efficient_universal`, `exists_clocked_universal`, `efficient_fixed_point`
(and `smn_polyTime` if K2 leaves it); blueprint `lem:recursive-compression` gets
`\leanok` and its proof text.

## K4 — efficient Kleene recursion

[MNY, Lemma 2.3] from `U : UniversalMachine` and `hardcode`: for `F`, let `d` be the
program that on input `encode x ++ SEP' :: v` computes `F (S (x, x))` (polynomial
time, K2) and then runs `U.univ` on `encode (F (S (x, x))) ++ SEP :: v`; set
`e := hardcode d (encode d ++ [SEP'])` (the first `SEP'` cell of the input is the
separator since program encodings use tags `≤ 6`). Then `e.eval v = (F e).eval v`
because `S (d, d) = e`, and a run of `F e` of cost `t` yields a run of `e` within
`U.bound (|F e| + vsize v + t) + O(1)`, the constant covering the fixed computation of
`F (S (d, d))`. Only the direction of K-D3 is stated, and only it follows.

## K5 — Mathlib bridges (independent)

`Primcodable Code` (through `encodeList`/`decodeList`), `PolyTimeFun.toFun_computable`
(partial recursiveness of `Code.eval` in the code — by structural induction on `Code`
with `Partrec.fix` for `fix`; check what `Mathlib/Computability/TMToPartrec.lean`
already provides before proving anything), `exists_compile` (a structural translation
`Nat.Partrec.Code → Code`, Mathlib's `exists_code` made into a function), then
`recursive_compression_halting` by composition. Risk: Mathlib may lack the
"eval is partrec in the code" direction; budget for proving it.

## The universal-machine gate (after K3)

Two constructions can provide `exists_efficient_universal`/`exists_clocked_universal`;
choose after K3 and record the choice in `planning/tm-infrastructure.md`:

- **Route α — TM track + bridge.** Milestones E–G build the machine-level
  `boundedUniversalCode` (`TM/Universal/Spec.lean`); a new Milestone H bridges the
  models with time bounds: H1 compiles `ToPartrec.Code` to `Code i` with polynomial
  time (a timed version of Mathlib's `TMToPartrec` compilation; also the substrate of
  `thm:succinct-sat`, requirement R3), H2 interprets TM codes in `ToPartrec.Code` with
  polynomial overhead. This is the blueprint's current edge `lem:universal-tm ←
  lem:bounded-universal-machine`. More work for *this* theorem, but H1 is needed for
  the gateway regardless.
- **Route β — self-interpreter.** A `ToPartrec.Code` program interpreting
  `encodeList c` on `v` (stack machine over one `fix`, values as lists of bounded cells;
  per-step cost polynomial in `|c|` and in the current value sizes, which are bounded by
  `vsize v + t` in length and by `max cell + t` in cell size, so the total is
  polynomial in `|c| + vsize v + t`). No bridge needed; the correctness proof is an
  invariant relating interpreter configurations to `TimedEval` derivations. Milestones
  E–G then serve only `thm:succinct-sat` and the paper-literal machine statements.

## Verification (every WP; CI-equivalent locally)

```bash
lake build                    # green; no new warnings
lake exe mk_all               # when files were added; commit MIPRE.lean
```

- `grep -rn "sorry" MIPRE/Foundations/Cost MIPRE/Foundations/Compression.lean` shrinks
  monotonically to the blueprint-tracked nodes named in each WP's acceptance.
- `grep -rn "noncomputable" MIPRE/Foundations/Cost` → only what `Polynomial ℕ` and
  `evalWithin` force (K2's `polyProg`, `PolyTimeFun` constructors).
- `#print axioms` on the headline theorem at K3/K4/K5 as stated in their acceptance.

## Risks and mitigations

1. **Closure-library sprawl (K2)** — the proof needs a dozen combinators, each with a
   `TimedEval` bound. Mitigation: two layers (K-D6), program-layer lemmas stated once
   as time-transfer rules and reused; automation deferred until the pipeline sections
   need it.
2. **Threshold arithmetic (K3 step 4)** — polynomial-versus-`2^n` estimates over `ℕ`
   are fiddly. Mitigation: one lemma with a crude `q` (degree not optimized), proved via
   `Nat.log`/`Nat.size` bounds already in Mathlib.
3. **Statement drift into `thm:compression`** — the succinctness bound (K-D5) and the
   pairing of descriptions `(c, m)` with the parameter `n` must match how the game
   compression theorem describes its verifiers. Mitigation: `thm:compression` is
   stated against `IsSuccinctDesc` when its section is formalized; changes flow back
   here as a recorded decision.
4. **K5 Mathlib gap** — see K5.
5. **Universal machine remains the deep sorry** until the gate's construction lands;
   the track is designed so that nothing above it waits.

## Progress checklist

- [x] **K0** statement audit and fixes (2026-09-08; branch `compression-track`)
- [ ] **K1** foundations hygiene
- [ ] **K2** closure library + `smn_polyTime`
- [ ] **K3** `recursive_compression` proved → **abstract compression theorem**
- [ ] **K4** `efficient_fixed_point` proved
- [ ] **K5** Mathlib bridges → `recursive_compression_halting`
- [ ] gate: universal-machine route decided and recorded

Each WP is one commit on the working branch, updating this checklist in the same commit.
