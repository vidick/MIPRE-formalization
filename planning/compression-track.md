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
([MNY, Lemmas 2.1–2.3]) — never their constructions. Those statements exist, sorried, in
`MIPRE/Foundations/Cost/Toolkit.lean`, and the compression lemma is stated in
`MIPRE/Foundations/Compression.lean` (`MIPRE.Cost.recursive_compression`; blueprint
`lem:recursive-compression`, which the blueprint itself calls "an ideal early milestone",
`\effortEasy` given the toolkit).

### The ambient model (decision K-D7, 2026-09-08)

The ambient model is the first-order list language `MIPRE.Cost.Prog` over binary trees
`MIPRE.Cost.Data`, with the timed big-step semantics `MIPRE.Cost.Eval` (`Cost/Basic.lean`,
whose docstring is the decision record). It **replaced Mathlib's `Turing.ToPartrec.Code`**
on 2026-09-08, after the attempt to build the closure library (K2) on that model exposed an
obstruction: `ToPartrec.Code`'s primitives act only on the front of a single `List ℕ` value
and pass it by value, so every output has the form `p ++ v.drop k`, and the input suffix can
only be discarded by first dropping everything built in front of it — retaining a
program-size-bounded number of cells of polynomially bounded value, i.e. `O(log t)` bits.
Hence `List.reverse`, `x ↦ x ++ [b]`, binary addition and the runtime s-m-n map are not
polynomial-time computable in that model (it is a one-stack machine with a read-only input;
trailing `0` cells are moreover invisible to programs), and `smn_polyTime`,
`exists_efficient_universal` and `exists_clocked_universal` were unprovable as stated. The
user rejected the alternative of a "zone/junk" convention on top of `ToPartrec.Code` as a
hack and chose a principled language (option (b) of the 2026-09-08 report).

`Prog` = `var i | nil | cons h t | elim i n c | let_ e b | loop b` with de Bruijn variables;
`Eval env p r t` charges one unit per rule, plus the size of the value for `var` (values are
copied when read, inspected in place by `elim`), so `Eval.size_le : r.size ≤ t`. Closed
programs are `Prog.WellScoped 1`; extra environment entries are inert for well-scoped
programs (`Eval.append_of_wellScoped`, `Eval.of_append_of_wellScoped`), which is what makes
`let_`-composition and hardcoding sound. Data encodings target `Data` directly (bits
`nil`/`cons nil nil`, lists as `cons`-chains, numbers in binary, pairs as `cons`, programs
as `Prog.toData`); sizes are additive. The design follows C. Reitwiessner's rose-tree
machine idea (CSLib issue #611) with binary trees and a time-only semantics; his code was not
ported (different semantics, closures, space accounting).

### Verified facts (checked 2026-09-08 against the repo on branch `compression-track`)

1. **Lean statements.** `Cost/Basic.lean`: `Data`, `Data.size`, `Data.toBits`, `Data.ofNat`
   (unary numerals), `Prog`, `Prog.WellScoped` (+ `mono`), `Env.get`, `Eval` with
   `pos`/`deterministic`/`size_le` and the two scoping lemmas, the fuel evaluator `evalFuel`
   with `evalFuel_sound`, `Halts`/`HaltsWithin`/`TimeBound` — all proved.
   `Cost/Encoding.lean`: `SizedEncoding` (into `Data`), `esize`, instances for `Bool`,
   `BitStr`, `ℕ` (binary, `Nat.foldr_bit_bits`), pairs (`cons`), `Prog` (`toData`/`ofData`,
   `ofData_toData`), size lemmas (`esize_bitStr_le`, `esize_nat_le`, `esize_prod`) — all
   proved. `Cost/PolyTime.lean`: `Prog.Runs`, `PolyTimeFun` (fields `toFun`, `code`,
   `closed`, `timeBound`, `computes`), `esize_apply_le`, `id`, `comp`,
   `polynomial_eval_mono` — proved. `Cost/Toolkit.lean`: `constProg` (+ `constProg_eval`,
   exactly `d.size` steps), `hardcode` with `hardcode_wellScoped`, `hardcode_time`
   (overhead `d.size + x.size + 3`), `hardcode_time_rev`, `hardcode_size`
   (`≤ esize p + 7 d.size + 21`) — proved; `smn_polyTime`, `UniversalMachine` /
   `exists_efficient_universal`, `ClockedUniversalMachine` / `exists_clocked_universal`
   (with `evalWithin`, `clockedResult`), `efficient_fixed_point` — sorried nodes.
   `Foundations/Compression.lean`: `bitQueryAnswer`, `IsSuccinctDesc`,
   `recursive_compression`, and the Mathlib bridges `Primcodable Prog`,
   `PolyTimeFun.toFun_computable`, `exists_compile`, `recursive_compression_halting`
   (5 sorries).
2. **Fidelity to [MNY].** `recursive_compression` is Lemma 5.1 (the `max{f(x), n}`
   variant; conclusion: a `PolyTimeFun Prog BitStr` reduction `g` with `Halts e nil ⇒
   g e ∈ A`, otherwise `f (g e) = ⊤`). `IsSuccinctDesc c n x` is Definition 2.4 with the
   runtime bound `(n + 1) * (Nat.size m + 1)` in place of the paper's "≤ n for all m" (a
   model that charges to read `m` makes the paper's bound vacuous for `|m| > n`) and with
   closedness of `c`. The toolkit statements are Lemmas 2.1–2.3.
3. **What the proof consumes** ([MNY] §3 and §5, read against `Toolkit.lean`):

   | proof step | toolkit clause |
   |---|---|
   | program `a`: "run `e` on the empty input for `log n` steps" | `ClockedUniversalMachine.run` with budget `Data.ofNat (Nat.size n)` |
   | `b(c, e, n)`: the bit-query program, assembled *at runtime* by `a` | `smn_polyTime` + `UniversalMachine.time_le` (to evaluate `c` on `(e, n)`) |
   | `(b(c, e, n+1), n)` is a succinct description of `h(e, n+1)` for `n ≥ r(e)` | `hardcode_time` (forward transfer) + the overhead polynomials, so that `r(e) = 2^{q(esize e)}` is polynomial-time computable |
   | closing the self-reference | `efficient_fixed_point` applied to `F c' = hardcode a (encode c')` |
   | the fixed point `c` runs in polynomial time | Kleene's clause "runs of `F e` bound runs of `e`" — and *only* that direction |
   | `g(e) = h(e, r(e))` is a `PolyTimeFun` | closure library: `comp`, `pair`, `const`, size and `2^q` arithmetic |

4. **Blueprint state.** `lem:universal-tm` carries
   `\lean{MIPRE.Cost.exists_efficient_universal, MIPRE.Cost.exists_clocked_universal}`
   and `\uses{lem:bounded-universal-machine}`; `lem:smn`, `lem:kleene` and
   `lem:recursive-compression` carry `\lean{}` tags (added in K0), so every sorry beneath
   the compression theorem is blueprint-tracked (CONTRIBUTING's sorry policy). The blueprint
   names no model ("a cost model"); its `sec:rr-computability` comments now mention `Prog`.
5. **Not consumed.** The TM track's Milestones A–D (`MultiInputTM`, `Code i`,
   serialization, evaluator) play no role in the ambient compression lemma; they matter
   here only as route α to the universal machine.
6. **complexitylib** (SamuelSchlesinger; evaluated 2026-09-08 at `edd0e9e`) has no
   ambient-model content — no relation to the project's language, no s-m-n as a computable
   map, no Kleene fixed point, no halting reduction or compression notion; its `FP` closure
   library is existential and asymptotic, on its own TM model. **No impact on this track.**
   Only `Cobham.boundedRec` (limited recursion on notation, bounded by a class function) is an
   optional packaging idea for K2. Details in `planning/tm-infrastructure.md`, update of
   2026-09-08.

## Fixed decisions

- **K-D1 — prove from statements, discharge later.** `recursive_compression` is proved
  from the toolkit *statements*. The sorries beneath it are then exactly the
  blueprint-tracked nodes `lem:universal-tm` and `lem:kleene`; after K4, only
  `lem:universal-tm`. No new sorry is ever introduced outside those nodes.
- **K-D2 — universal machines as data, existence as the sorried node** (K0).
  `UniversalMachine` and `ClockedUniversalMachine` are structures bundling the (closed)
  program, its overhead polynomial and the semantic clauses; `exists_efficient_universal` /
  `exists_clocked_universal` are `Nonempty` statements (names unchanged, so the blueprint
  tags stay valid). Downstream definitions refer to the fields of an obtained machine; no
  `def` is ever sorried — the same principle as decision D13 of the TM plan.
- **K-D3 — Kleene stated in the used direction only** (K0). `efficient_fixed_point`
  asserts that `e` and `F e` have the same input/output behavior and that "runs of `F e`
  bound runs of `e`" with polynomial overhead. [MNY, Lemma 2.3] states polynomial
  *equivalence*; the converse direction is unused by the compression argument and is *not*
  derivable from an upper bound on the simulator's time. Restorable by adding a "simulation
  is never faster" clause to `UniversalMachine` should a consumer ever need it.
- **K-D4 — runtime s-m-n generic in the hardcoded type** (K0, restated for `Prog`).
  `smn_polyTime α : ∃ S : PolyTimeFun (Prog × α) Prog, ∀ p a, S (p, a) = hardcode p
  (encode a)`; hardcoding is pairing, no separators are involved.
- **K-D5 — succinctness bound stays `(n + 1) * (Nat.size m + 1)`** until
  `thm:compression` is stated (design knob inherited from `Compression.lean`; whatever is
  chosen must be what the compression theorem for games certifies about its output
  verifiers).
- **K-D6 — two-layer closure library, shared infrastructure.** A *program layer* on
  `Prog` (combinators with `Eval`/`Runs` lemmas, usable for programs whose correctness is
  only conditional — the bit-query program `β` runs an arbitrary input program through the
  universal machine and cannot be a total `PolyTimeFun`), and a *function layer* of
  `PolyTimeFun` combinators with explicit `timeBound` polynomials on top. Both live under
  `MIPRE/Foundations/Cost/` (a `Cost/Closure/` directory once they outgrow `PolyTime.lean`).
  Everything built here is R1 infrastructure the pipeline needs anyway.
- **K-D7 — the ambient language is `MIPRE.Cost.Prog`** (above; decision record in
  `Cost/Basic.lean`). Consequences: no Mathlib evaluation bridge comes for free — K5's
  bridges go through `evalFuel` (partial recursiveness of evaluation) and a universal `Prog`
  for `Nat.Partrec.Code.eval`; R3's gateway needs a compiler `Prog → Code i` (TM track,
  Milestone H1). The TM track's Milestones A–D are unaffected.
- **K-D8 — closedness by `WellScoped`.** Specifications are runs in the environment `[x]`
  (`Prog.Runs`); `PolyTimeFun` carries `closed : code.WellScoped 1`, and the universal
  machines are closed (`scoped` is a Lean keyword, hence the field name). Weakening/strengthening (`Eval.append_of_wellScoped` /
  `Eval.of_append_of_wellScoped`) make `let_`-composition and both directions of
  `hardcode` sound; combinators must maintain `WellScoped` (routine).
- **Policy.** Every WP is one commit on the working branch; `lake build` green;
  `lake exe mk_all` whenever a file is added; sorry-free except the blueprint-tracked
  nodes; Mathlib style, docstrings on every declaration (CONTRIBUTING). Blueprint
  `\leanok` (with proof text) is added to a node in the WP that proves it.

## Roadmap

| WP | Content | Status |
|---|---|---|
| **K0** | Statement audit and fixes: `UniversalMachine`/`ClockedUniversalMachine` (K-D2); one-directional Kleene (K-D3); generic `smn_polyTime` (K-D4); blueprint `\lean{}` tags; TM roadmap re-sequenced | ✅ 2026-09-08 |
| **K1** | Foundations: the ambient language and its metatheory, encodings, `PolyTimeFun` with `id`/`comp`, efficient s-m-n at program level (`hardcode_*`) — all sorry-free; `Cost/` sorries = exactly `smn_polyTime`, `exists_efficient_universal`, `exists_clocked_universal`, `efficient_fixed_point` | ✅ 2026-09-08 (redone on `Prog` after K-D7) |
| K2 | Minimal closure library (two layers, K-D6) + `smn_polyTime` + the fixed programs of the proof as `PolyTimeFun`s | ☐ |
| K3 | **`recursive_compression` proved** from the toolkit statements; blueprint `\leanok` + proof text on `lem:recursive-compression` (and on `lem:smn`) | ☐ |
| K4 | `efficient_fixed_point` from `UniversalMachine` + s-m-n ([MNY, Lemma 2.3]); `lem:kleene` `\leanok` | ☐ |
| K5 | Mathlib bridges (`Primcodable Prog`, `PolyTimeFun.toFun_computable`, `exists_compile`) → `recursive_compression_halting` sorry-free modulo `lem:universal-tm`; independent of K2–K4 | ☐ |
| gate | Universal machine: route α (TM Milestones E–G + bridge H) or route β (self-interpreter of `Prog` in `Prog`) — **decide after K3**, record in `planning/tm-infrastructure.md` | ☐ |

Milestones reached along the way: after K1 the efficient s-m-n (program level) is
sorry-free; after K3 the abstract compression theorem is sorry-free modulo two
blueprint nodes; after K4 modulo the universal machine only; after K5 the same holds
for the halting-problem corollary consumed by `MIPRE.HaltingGameValue`.

---

## K1 — foundations (done)

What is proved, file by file, is listed in verified fact 1. Points worth knowing before
K2: `Eval.size_le` bounds every result by the cost, so `PolyTimeFun.comp`'s time bound is
`F + G ∘ F + 1` with no separate output-size bookkeeping; `constProg d` runs in exactly
`d.size` steps; `hardcode` costs `d.size + x.size + 3` on top of the run of `p` (the input
is copied once); the strengthening lemma needs `WellScoped` — keep every program closed;
`evalFuel` makes concrete programs executable (`#eval`/`decide` pins, as in the TM track).

## K2 — closure library and the programs of the proof

Program layer (raw `Prog`, `Runs`/`Eval` lemmas): projections `elim 0 nil (var 0)` /
`(var 1)` (cost `O(size of the component)`), pairing (`cons`), sequencing (`let_`),
branching on a bit or on `nil`/`cons` (`elim`), a *for* combinator (`loop` over a unary
counter `Data.ofNat k`, `k` iterations of a body with a size-bounded state), list iteration
(`loop` walking a `cons`-chain), and **tree recursion** (structural recursion on `Data` by a
`loop` with an explicit stack) — needed by `smn_polyTime` to emit `toData (constProg d)`.
Concrete programs: `Nat.size` of a binary number (unary or binary output), binary decrement,
bit-indexing `bitQueryAnswer` (walk the string while decrementing the binary index; time
`O(|y| · |m|)`, which is where the product form of `IsSuccinctDesc` comes from), `2 ^ q(n)`
in binary for a polynomial `q` given as data (a program `polyProg : Polynomial ℕ → Prog`,
`noncomputable` only because `Polynomial ℕ` is).

Function layer (`PolyTimeFun`): `ofProg` (bundle a closed program with a proved bound),
`const`, `pair`, `fst`, `snd`, `ite` on a `Bool`, plus the two derived from the universal
machines: `haltsWithin (UT) : PolyTimeFun (Prog × ℕ) Bool` with `toFun (e, n) =
(evalWithin e nil (Nat.size n)).isSome` (assemble `(ofNat (Nat.size n), (encode e, nil))`,
run `UT.univT`, inspect the flag), and the s-m-n witness of `smn_polyTime` (emit
`toData (hardcode p (encode a))` = `cons (ofNat 4) (cons (cons (ofNat 2) (cons (toData
(constProg (encode a))) (toData (var 0)))) (toData p))`).

**Acceptance:** `smn_polyTime` proved; the combinators above with `computes` proofs;
`grep sorry` adds nothing outside the two universal-machine nodes and Kleene.

## K3 — the compression theorem

Proof plan for `recursive_compression` (paper §5, in repo terms). Obtain
`U : UniversalMachine`, `UT : ClockedUniversalMachine` and the s-m-n witnesses from the
statements. All programs below are built from K2.

1. **Bit-query program `β` (program layer, conditional correctness).** On input
   `encode (((c', e), n), m)`: run `U.univ` on `cons (encode c') (encode (e, n))` to obtain
   `y`, then output `bitQueryAnswer y m`. Lemma: if `c'` is closed and runs on
   `encode (e, n)` to `encode y` at cost `t`, then `β` runs on that input to
   `bitQueryAnswer y m` within `Q(esize c' + esize e + Nat.size n + t) · (Nat.size m + 1)`
   for a fixed polynomial `Q`. `β` is *not* a `PolyTimeFun` (its input `c'` may diverge);
   this is why K-D6 has a program layer. `b c' e n := hardcode β (encode ((c', e), n))`, and
   `(b c' e n).Runs (encode m)` is `β.Runs (encode (((c', e), n), m))` up to the
   `hardcode_time` overhead.
2. **Decider `a` (function layer, total).** `decFun : PolyTimeFun (Prog × (Prog × ℕ))
   BitStr` with `toFun (c', (e, n)) = if haltsWithin (e, n) then y₀ else
   Compr ((S (β, ((c', e), n + 1)), n), n)`; its `computes` field *is* the correctness of
   the program `a := decFun.code`.
3. **Self-reference.** `F : PolyTimeFun Prog Prog`, `F c' = hardcode a (encode c')` (K2);
   `obtain ⟨c, p, hc, hc_eval, hc_time⟩ := efficient_fixed_point F`. Then `c.Runs (encode
   (e, n))` agrees with `a.Runs (encode (c, (e, n)))` (`hardcode_time`/`_rev`), so `c` runs
   on `encode (e, n)` to `encode (h e n)` where `h e n := decFun (c, (e, n))` — a plain
   definition, all recursion is inside `c`. Time: by `hc_time`, `hardcode_time` and
   `decFun.computes`, `c` runs on `encode (e, n)` within `P (esize e + Nat.size n)` for a
   polynomial `P`.
4. **Threshold `r`.** Arithmetic lemma (`Nat.size`/`Nat.log` estimates): for a polynomial
   `Q` there is a polynomial `q` with `n ≥ 2 ^ q(esize e) → Q(esize e + Nat.size n) ≤ n + 1`.
   Define `r e := 2 ^ q(esize e)` (a `PolyTimeFun Prog ℕ`: `esize e` is the size of the
   input; the output is `q(esize e)` zero bits then a one). For `n ≥ r e`:
   `|h e (n + 1)| ≤ 2 ^ n` (`Eval.size_le`) and `IsSuccinctDesc (b c e (n + 1)) n (h e (n +
   1))` (step 1 with `c' = c`, `t ≤ P`).
5. **Reduction `g := c ∘ (e ↦ (e, r e))`** as a `PolyTimeFun Prog BitStr` via `ofProg`,
   `pair`, `comp`; `g e = h e (r e)`.
6. **Non-halting `e`.** For every `n`, `haltsWithin (e, n) = false`, so `h e n =
   Compr ((b c e (n + 1), n), n)`; for `n ≥ r e`, `hCompr` gives `f (h e n) ≥
   max (f (h e (n + 1))) n`; by induction on `k`, `f (h e n) ≥ n + k` for all `k`, hence
   `f (h e n) = ⊤` (`ENat`). With `n = r e`: `f (g e) = ⊤`.
7. **Halting `e`.** A run of `e` on `nil` has some cost `T`; for `Nat.size n ≥ T`
   (`n ≥ 2 ^ T`) `h e n = y₀ ∈ A`. Downward induction (`Nat.decreasingInduction`) from
   `N := max (r e) (2 ^ T)` to `r e`: if `haltsWithin (e, n)` then `y₀ ∈ A`, else
   `h e n = Compr ((b c e (n + 1), n), n) ∈ A` by `hCompr.2` from `h e (n + 1) ∈ A` and
   the succinct description of step 4. Hence `g e = h e (r e) ∈ A`.

**Acceptance:** `recursive_compression` sorry-free; `#print axioms` shows no `sorryAx`
beyond `exists_efficient_universal`, `exists_clocked_universal`, `efficient_fixed_point`
(and `smn_polyTime` if K2 leaves it); blueprint `lem:recursive-compression` gets
`\leanok` and its proof text.

## K4 — efficient Kleene recursion

[MNY, Lemma 2.3] from `U : UniversalMachine` and `hardcode`: for `F`, let `d` be the closed
program that on input `cons x v` computes `F (hardcode x x)` (polynomial time, K2) and then
runs `U.univ` on `cons (encode (F (hardcode x x))) v`; set `e := hardcode d (encode d)`. Then
`e.Runs v` agrees with `(F e).Runs v` because `hardcode d (encode d) = e`
(`hardcode_time`/`_rev`), and a run of `F e` of cost `t` yields a run of `e` within
`U.bound (esize (F e) + v.size + t) + O(esize d)`, the constant covering the fixed
computation of `F (hardcode d (encode d))` and the copy of the input. Only the direction of
K-D3 is stated, and only it follows.

## K5 — Mathlib bridges (independent)

`Primcodable Prog` (through `Data.toBits`/tree encodings; routine), `PolyTimeFun.toFun_computable`
(partial recursiveness of `Prog` evaluation: `evalFuel` is primitive recursive in the fuel —
after `Primcodable Data`/`Prog` — and evaluation is its unbounded search over the fuel),
`exists_compile` (a fixed universal `Prog` computing `Nat.Partrec.Code.eval` on encoded
arguments, obtained from Mathlib's universality, hardcoded with the code via `hardcode`),
then `recursive_compression_halting` by composition. Risk: proving `Primrec` of a
structurally recursive evaluator over trees in Mathlib is laborious; budget for it, or route
through `Nat.Partrec.Code` directly.

## The universal-machine gate (after K3)

Two constructions can provide `exists_efficient_universal`/`exists_clocked_universal`;
choose after K3 and record the choice in `planning/tm-infrastructure.md`:

- **Route α — TM track + bridge.** Milestones E–G build the machine-level
  `boundedUniversalCode` (`TM/Universal/Spec.lean`); a new Milestone H bridges the models
  with time bounds: H1 compiles `Prog` to `Code i` with polynomial time (also the substrate
  of `thm:succinct-sat`, requirement R3), H2 interprets TM codes in `Prog` with polynomial
  overhead. This is the blueprint's current edge `lem:universal-tm ←
  lem:bounded-universal-machine`. More work for *this* theorem, but H1 is needed for the
  gateway regardless.
- **Route β — self-interpreter.** A `Prog` interpreting `toData c` on `v`: a CEK-style
  machine over `Data` (program pointer, environment as a list, continuation stack) driven by
  one `loop`; per step cost polynomial in `esize c` and in the current value sizes, which
  `Eval.size_le` bounds by the simulated cost, so the total is polynomial in
  `esize c + v.size + t`. No bridge needed; the correctness proof is an invariant relating
  interpreter configurations to `Eval` derivations. Milestones E–G then serve only
  `thm:succinct-sat` and the paper-literal machine statements.

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

1. **Closure-library sprawl (K2)** — the proof needs a dozen combinators, each with an
   `Eval` bound. Mitigation: two layers (K-D6), program-layer lemmas stated once as
   time-transfer rules and reused; automation deferred until the pipeline sections need
   it.
2. **Expressivity of `Prog`** — the model change was forced by an expressivity gap in
   `ToPartrec.Code`; `Prog` builds and destructs values freely, but this should be validated
   early in K2 by the tree-recursion combinator and by `smn_polyTime` (a genuine
   string-to-string transformation).
3. **Threshold arithmetic (K3 step 4)** — polynomial-versus-`2^n` estimates over `ℕ`
   are fiddly. Mitigation: one lemma with a crude `q` (degree not optimized), proved via
   `Nat.log`/`Nat.size` bounds already in Mathlib.
4. **Statement drift into `thm:compression`** — the succinctness bound (K-D5) and the
   pairing of descriptions `(c, m)` with the parameter `n` must match how the game
   compression theorem describes its verifiers. Mitigation: `thm:compression` is
   stated against `IsSuccinctDesc` when its section is formalized; changes flow back
   here as a recorded decision.
5. **K5 Mathlib gap** — see K5.
6. **Universal machine remains the deep sorry** until the gate's construction lands;
   the track is designed so that nothing above it waits.

## Progress checklist

- [x] **K0** statement audit and fixes (2026-09-08; branch `compression-track`)
- [x] **K1** foundations on `ToPartrec.Code` (2026-09-08, commit `b24731c`) — superseded
  the same day by K-D7
- [x] **K1** foundations on `Prog` (2026-09-08): language, metatheory, encodings,
  `PolyTimeFun`, program-level s-m-n, all sorry-free; `Cost/` sorries = the four blueprint
  nodes. Lessons: keep every program closed (`WellScoped`) — the strengthening direction
  of hardcode needs it; `Eval.size_le` replaces all output-size bookkeeping; state
  instance-law and evaluator proofs with `obtain`/`rcases` on the discriminants rather than
  bare `simp`.
- [ ] **K2** closure library + `smn_polyTime`
- [ ] **K3** `recursive_compression` proved → **abstract compression theorem**
- [ ] **K4** `efficient_fixed_point` proved
- [ ] **K5** Mathlib bridges → `recursive_compression_halting`
- [ ] gate: universal-machine route decided and recorded

Each WP is one commit on the working branch, updating this checklist in the same commit.
